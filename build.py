#!/usr/bin/env python3
"""Compile the editable book into build/ without replacing the supplied PDF."""
import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
MAIN = "谱定理与全等.tex"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--xelatex", default=os.environ.get("XELATEX", "xelatex"),
                        help="XeLaTeX 可执行文件的绝对路径或 PATH 中的命令名")
    engine = shutil.which(parser.parse_args().xelatex)
    if not engine:
        print("未找到 XeLaTeX；请按《编译说明.txt》安装。", file=sys.stderr)
        return 1
    engine = str(Path(engine).absolute())
    output = ROOT / "build"
    output.mkdir(exist_ok=True)
    cmd = [engine, "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error",
           "-file-line-error", f"-output-directory={output}", MAIN]
    for n in range(1, 4):
        log = output / f"xelatex-pass-{n}.txt"
        with log.open("wb") as out:
            status = subprocess.run(cmd, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT).returncode
        if status:
            print(log.read_text(encoding="utf-8", errors="replace")[-5000:], file=sys.stderr)
            print(f"第 {n} 次编译失败；日志：{log}", file=sys.stderr)
            return status
    log = output / Path(MAIN).with_suffix(".log")
    last = log.read_text(encoding="utf-8", errors="replace")
    if re.search(r"There were undefined (?:references|citations)|Label\(s\) may have changed"
                 r"|Rerun to get (?:cross-references|outlines|/PageLabels) right|Missing character:", last):
        print(f"编译完成但仍有引用或缺字问题，请检查：{log}", file=sys.stderr)
        return 1
    pdf = output / Path(MAIN).with_suffix(".pdf")
    if not pdf.is_file() or not pdf.read_bytes().startswith(b"%PDF-"):
        print(f"未找到有效的编译输出：{pdf}", file=sys.stderr)
        return 1
    print(f"编译完成：{pdf}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
