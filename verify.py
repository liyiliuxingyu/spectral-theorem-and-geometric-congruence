#!/usr/bin/env python3
"""Verify the extracted project or the ZIP itself (Python 3.8+)."""
import argparse
import hashlib
import json
import posixpath
from pathlib import Path, PurePosixPath
import re
import stat
import sys
from zipfile import BadZipFile, ZipFile

ROOT = Path(__file__).resolve().parent
MAIN = "谱定理与全等.tex"
PDF = "谱定理与全等_逐节例题加强版.pdf"
MANIFEST = "SHA256SUMS"
REQUIRED = {MAIN, PDF, "接续说明.md", "接续状态.md", "工具链记录.md",
            "编译说明.txt", "build.py", "verify.py", "lean/README.md",
            "lean/lean-toolchain", "lean/lakefile.toml", "lean/lake-manifest.json",
            "lean/MatrixCertificate.lean", "lean/EllipseCongruence.lean",
            "lean/check.py"}
REQUIRED.update({"lean/" + name + ".lean" for name in ('RotationAngle', 'OrthogonalCoordinates', 'SpectralTheorem', 'SpectralCongruence', 'Example21', 'Example22', 'Example23', 'Example24', 'Example25', 'EllipseCenter', 'EllipseForward', 'ChordLandmarks', 'EllipseClassification')})
REFS = re.compile(r"\\(input|include|includegraphics)\*?\s*(?:\[[^]]*\]\s*)?\{([^{}]+)\}")


def safe(name):
    p = PurePosixPath(name)
    if (not name or p.is_absolute() or ".." in p.parts or "\\" in name
            or p.as_posix() != name or any(":" in k for k in p.parts)):
        raise ValueError(f"不安全的文件名：{name!r}")
    return p


def from_folder(root):
    list_path = root / MANIFEST
    if list_path.is_symlink():
        raise ValueError(f"{MANIFEST} 不应是符号链接")
    files = {MANIFEST: list_path.read_bytes()}
    for line in files[MANIFEST].decode("utf-8").splitlines():
        _, sep, name = line.partition("  ")
        if not sep:
            raise ValueError(f"无效清单行：{line!r}")
        p = root
        for part in safe(name).parts:
            p = p / part
            if p.is_symlink():
                raise ValueError(f"不允许符号链接：{name}")
        files[name] = p.read_bytes()
    return files


def from_archive(path):
    with ZipFile(path) as z:
        mapping, prefixes = {}, set()
        for info in z.infolist():
            if info.is_dir():
                safe(info.filename.rstrip("/"))
                continue
            p = safe(info.filename)
            if len(p.parts) < 2 or stat.S_ISLNK(info.external_attr >> 16):
                raise ValueError(f"ZIP 路径不合规：{p}")
            prefixes.add(p.parts[0])
            name = PurePosixPath(*p.parts[1:]).as_posix()
            if name in mapping:
                raise ValueError(f"ZIP 有重复路径：{name}")
            mapping[name] = info
        if len(prefixes) != 1:
            raise ValueError("ZIP 须只有一个工程根目录")
        bad = z.testzip()
        if bad:
            raise ValueError(f"ZIP CRC 校验失败：{bad}")
        return {name: z.read(info) for name, info in mapping.items()}


def check(files):
    expected = {}
    for line in files[MANIFEST].decode("utf-8").splitlines():
        h, sep, name = line.partition("  ")
        safe(name)
        if not sep or not re.fullmatch(r"[0-9a-f]{64}", h) or name in expected or name == MANIFEST:
            raise ValueError(f"无效清单行：{line!r}")
        expected[name] = h
    if not REQUIRED <= expected.keys():
        raise ValueError(f"缺少交付文件：{sorted(REQUIRED - expected.keys())}")
    if files.keys() != expected.keys() | {MANIFEST}:
        raise ValueError("文件与清单不一致")
    for name, h in expected.items():
        if hashlib.sha256(files[name]).hexdigest() != h:
            raise ValueError(f"SHA-256 不匹配：{name}")
    # Ensure the Lake project and its lock refer to the code actually shipped.
    lake = files["lean/lakefile.toml"].decode()
    roots = re.search(r"(?m)^roots\s*=\s*(\[[^\]]*\])", lake)
    if not roots:
        raise ValueError("lakefile.toml 未声明 Lean 根模块")
    modules = json.loads(roots.group(1))
    if len(modules) != len(set(modules)) or {
            "lean/" + m.replace(".", "/") + ".lean" for m in modules
    } != {n for n in expected if n.startswith("lean/") and n.endswith(".lean")}:
        raise ValueError("Lake 根模块与包内 Lean 源码不一致")
    manifest = json.loads(files["lean/lake-manifest.json"])
    mathlib = [d for d in manifest["packages"] if d["name"] == "mathlib"]
    rev = re.search(r'(?m)^rev\s*=\s*"([0-9a-f]{40})"', lake)
    if len(mathlib) != 1 or rev is None or mathlib[0]["rev"] != rev.group(1):
        raise ValueError("Mathlib 版本与锁文件不一致")
    # Lean itself checks transitive imports. Here verify local documentation links.
    for n in expected:
        if n.endswith(".md"):
            for href in re.findall(r"\[[^\]\n]*\]\(([^)\s]+)\)", files[n].decode()):
                if "://" in href or href.startswith("#"):
                    continue
                dest = posixpath.normpath(posixpath.join(posixpath.dirname(n), href.split("#", 1)[0]))
                if dest not in expected:
                    raise ValueError(f"{n} 的相对链接无效：{href}")
    if any(n != PDF and n.lower().endswith(".pdf") and v == files[PDF] for n, v in files.items()):
        raise ValueError("工程包含相同的完整答案 PDF 的重复副本")
    if not files[PDF].startswith(b"%PDF-"):
        raise ValueError("PDF 文件头不正确")
    counted, seen, visiting, content_sections = [0, 0], set(), set(), []

    def walk(name):
        if name in visiting:
            raise ValueError(f"循环引用：{name}")
        if name in seen:
            return
        visiting.add(name)
        s = re.sub(r"(?<!\\)%[^\n]*", "", files[name].decode("utf-8"))
        if name == MAIN and not re.search(r"\\documentclass(?:\[[^]]*\])?\{ctexbook\}", s):
            raise ValueError("主文件未使用 ctexbook")
        counted[0] += s.count(r"\begin{example}")
        counted[1] += s.count(r"\begin{solution}")
        # Count pairs in their actual order, including chapter files with many examples.
        tags = re.findall(r"\\(begin|end)\{(example|solution)\}", s)
        pair = [("begin", "example"), ("end", "example"), ("begin", "solution"), ("end", "solution")]
        if tags != pair * s.count(r"\begin{example}"):
            raise ValueError(f"{name} 中例题和解析未按顺序配对")
        for title, body in re.findall(r"\\section\{([^{}]+)\}(.+?)(?=\\section\{|\Z)", s, re.S):
            if name == MAIN and title == "符号与阅读路线":
                continue  # Navigation and notation, not an exercise section.
            if r"\begin{example}" not in body or r"\begin{solution}" not in body:
                raise ValueError(f"{name} 的教学小节「{title}」缺少例题或解析")
            content_sections.append(title)
        for kind, target in REFS.findall(s):
            safe(target)
            if kind == "includegraphics":
                options = [target] if PurePosixPath(target).suffix else [
                    target + e for e in (".pdf", ".png", ".jpg", ".jpeg", ".eps")]
                if not any(c in expected for c in options):
                    raise ValueError(f"{name} 的图形引用无效：{target}")
            else:
                t = target if PurePosixPath(target).suffix else target + ".tex"
                if t not in expected:
                    raise ValueError(f"{name} 的分章引用无效：{target}")
                walk(t)
        visiting.remove(name)
        seen.add(name)

    walk(MAIN)
    if {n for n in expected if n.endswith(".tex")} != seen:
        raise ValueError("有未接入主文件的 TeX 源码")
    if counted != [48, 48]:
        raise ValueError(f"本版期望 48 道例题、48 份解析，实得 {counted}")
    print(f"通过：{len(expected)} 个文件的 SHA-256，{len(seen)} 个 TeX 文件的引用，{len(content_sections)} 个教学小节、48 对例题与解析，PDF 文件头，{len(modules)} 个 Lean 根模块、Mathlib 锁和文档相对链接。")


def repack(root, output, additions):
    """Refresh checksums for tracked files and build a checked, lossless ZIP."""
    from tempfile import TemporaryDirectory
    from zipfile import ZIP_DEFLATED

    root, output = root.resolve(), output.resolve()
    if root == output or root in output.parents or output.suffix.lower() != ".zip":
        raise ValueError("请将新 ZIP 写到工程目录以外，文件名须以 .zip 结尾")
    files = from_folder(root)
    for name in additions:
        rel = safe(name)
        if name != ".gitignore" and any(part.startswith(".") or part in {"build", "__pycache__"} for part in rel.parts):
            raise ValueError(f"新资源不能指向缓存或隐藏目录：{name}")
        if name == MANIFEST or rel.suffix.lower() in {".zip", ".olean", ".ilean", ".pyc"}:
            raise ValueError(f"不能作为工程资源加入：{name}")
        path = root
        for part in rel.parts:
            path = path / part
            if path.is_symlink():
                raise ValueError(f"不允许符号链接：{name}")
        files[name] = path.read_bytes()
    files[MANIFEST] = "".join(
        hashlib.sha256(files[n]).hexdigest() + "  " + n + "\n"
        for n in sorted(files) if n != MANIFEST).encode("utf-8")
    # Fail before touching the existing release if an added module or resource
    # was not registered or a tracked reference is now broken.
    check(files)
    output.parent.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=output.parent) as tmpdir:
        temp = Path(tmpdir) / "verified.zip"
        with ZipFile(temp, "w", compression=ZIP_DEFLATED, compresslevel=9) as z:
            for n in sorted(files):
                z.writestr(f"{root.name}/{n}", files[n])
        check(from_archive(temp))
        temp.replace(output)
    (root / MANIFEST).write_bytes(files[MANIFEST])
    print(f"已写入：{output}")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("target", nargs="?", default=ROOT, type=Path,
                   help="工程根目录或 ZIP；省略时校验脚本所在目录")
    p.add_argument("--pack", type=Path, metavar="OUTPUT.zip",
                   help="更新现行清单，另存一个仅含清单项目且通过核验的 ZIP")
    p.add_argument("--add", action="append", default=[], metavar="RELATIVE_PATH",
                   help="重打包时显式加入一个新源码或资源；可重复指定")
    args = p.parse_args()
    target = args.target
    try:
        if args.pack:
            if not target.is_dir():
                raise ValueError("--pack 的输入须为解压后的工程目录")
            repack(target, args.pack, args.add)
            return 0
        if args.add:
            raise ValueError("--add 须与 --pack 同用")
        check(from_folder(target) if target.is_dir() else from_archive(target))
    except (OSError, ValueError, KeyError, UnicodeError, BadZipFile) as err:
        print(f"校验失败：{err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
