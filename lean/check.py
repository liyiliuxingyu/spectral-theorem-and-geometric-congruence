#!/usr/bin/env python3
"""Typecheck the certificates and audit the axioms reported by Lean."""
import argparse
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
VERSION = "4.19.0"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = {
    "MatrixCertificate.lean": {
        "SpectralExample.IntegerCertificate." + n: set()
        for n in ("transpose_mul", "mul_transpose", "diagonalizes")
    },
    "EllipseCongruence.lean": {
        "SpectralExample.example01": STANDARD_AXIOMS,
        "SpectralExample.longAxisEndpoints": STANDARD_AXIOMS,
        "SpectralExample.standardAxisExtrema": STANDARD_AXIOMS,
        "SpectralExample.originalLongAxisLength": STANDARD_AXIOMS,
        "SpectralExample.shortNormalization_sq": STANDARD_AXIOMS,
        "SpectralExample.standardShortAxisExtrema": STANDARD_AXIOMS,
        "SpectralExample.shortAxisEndpoints": STANDARD_AXIOMS,
        "SpectralExample.originalShortAxisLength": STANDARD_AXIOMS,
    },
    "RotationAngle.lean": {
        "SpectralExample.rotationAngle_bounds": STANDARD_AXIOMS,
        "SpectralExample.rotationAngle_cos_sin": STANDARD_AXIOMS,
        "SpectralExample.forward_is_rotation": STANDARD_AXIOMS,
    },
    "OrthogonalCoordinates.lean": {
        "OrthogonalCoordinates.transpose_mul_self": STANDARD_AXIOMS,
        "OrthogonalCoordinates.coordinateEquiv": STANDARD_AXIOMS,
        "OrthogonalCoordinates.distance_preserved": STANDARD_AXIOMS,
        "OrthogonalCoordinates.intertwining_level_congruence": STANDARD_AXIOMS,
        "OrthogonalCoordinates.conjugacy_level_congruence": STANDARD_AXIOMS,
    },
    "SpectralTheorem.lean": {
        "SpectralBook.real_symmetric_spectral_theorem": STANDARD_AXIOMS,
        "SpectralBook.real_symmetric_orthogonal_diagonalization": STANDARD_AXIOMS,
    },
    "SpectralCongruence.lean": {
        "SpectralBook.quadraticValue_spectralCoordinates": STANDARD_AXIOMS,
        "SpectralBook.spectralLevelIsometry": STANDARD_AXIOMS,
        "SpectralBook.spectralLevelIsometry_preserves_distance": STANDARD_AXIOMS,
        "SpectralBook.real_symmetric_level_sets_congruent": STANDARD_AXIOMS,
    },
    "Example21.lean": {
        "SpectralExample.Example21.characteristic_polynomial": STANDARD_AXIOMS,
        "SpectralExample.Example21.characteristic_roots": STANDARD_AXIOMS,
        "SpectralExample.Example21.eigenvalue_six_equation": STANDARD_AXIOMS,
        "SpectralExample.Example21.eigenvalue_one_equation": STANDARD_AXIOMS,
        "SpectralExample.Example21.normalized_eigenvectors": STANDARD_AXIOMS,
        "SpectralExample.Example21.real_transpose_mul": STANDARD_AXIOMS,
        "SpectralExample.Example21.real_mul_transpose": STANDARD_AXIOMS,
        "SpectralExample.Example21.real_diagonalizes": STANDARD_AXIOMS,
        "SpectralExample.Example21.determinant_Q": STANDARD_AXIOMS,
        "SpectralExample.Example21.quadratic_standard_form": STANDARD_AXIOMS,
        "SpectralExample.Example21.arbitrary_points_distance": STANDARD_AXIOMS,
        "SpectralExample.Example21.sample_points_on_standard": STANDARD_AXIOMS,
        "SpectralExample.Example21.sample_point_images": STANDARD_AXIOMS,
        "SpectralExample.Example21.sample_points_on_original": STANDARD_AXIOMS,
        "SpectralExample.Example21.sample_squared_distance": STANDARD_AXIOMS,
        "SpectralExample.Example21.sample_euclidean_distance": STANDARD_AXIOMS,
        "SpectralExample.Example21.sample_radical_image": STANDARD_AXIOMS,
    },
    "Example22.lean": {
        "SpectralExample.Hyperbola.standardForm": STANDARD_AXIOMS,
        "SpectralExample.Hyperbola.levelCongruence": STANDARD_AXIOMS,
        "SpectralExample.Hyperbola.vertices": STANDARD_AXIOMS,
        "SpectralExample.Hyperbola.vertexImages": STANDARD_AXIOMS,
        "SpectralExample.Hyperbola.axesCorrespond": STANDARD_AXIOMS,
        "SpectralExample.Hyperbola.axesAsymptotic": STANDARD_AXIOMS,
        "SpectralExample.Hyperbola.unboundedBranches": STANDARD_AXIOMS,
        "SpectralExample.Hyperbola.eigenpairs": STANDARD_AXIOMS,
    },
    "Example23.lean": {
        "SpectralExample.Example23.B_identity_rank_one": STANDARD_AXIOMS,
        "SpectralExample.Example23.quadratic_rank_one": STANDARD_AXIOMS,
        "SpectralExample.Example23.eigenspace_four": STANDARD_AXIOMS,
        "SpectralExample.Example23.eigenspace_one": STANDARD_AXIOMS,
        "SpectralExample.Example23.eigenvectors": STANDARD_AXIOMS,
        "SpectralExample.Example23.orthonormal_columns": STANDARD_AXIOMS,
        "SpectralExample.Example23.coordinates_fromCoordinates": STANDARD_AXIOMS,
        "SpectralExample.Example23.fromCoordinates_coordinates": STANDARD_AXIOMS,
        "SpectralExample.Example23.normSquared_fromCoordinates": STANDARD_AXIOMS,
        "SpectralExample.Example23.distanceSquared_fromCoordinates": STANDARD_AXIOMS,
        "SpectralExample.Example23.diagonal_quadratic": STANDARD_AXIOMS,
        "SpectralExample.Example23.central_plane_form": STANDARD_AXIOMS,
        "SpectralExample.Example23.central_circle": STANDARD_AXIOMS,
        "SpectralExample.Example23.form_on_axes": STANDARD_AXIOMS,
        "SpectralExample.Example23.axis_intersections": STANDARD_AXIOMS,
        "SpectralExample.Example23.semiaxis_lengths": STANDARD_AXIOMS,
    },
    "Example24.lean": {
        "SpectralExample.Example24.P6_polynomial": STANDARD_AXIOMS,
        "SpectralExample.Example24.P1_complement": STANDARD_AXIOMS,
        "SpectralExample.Example24.orthogonal_projection_identities": STANDARD_AXIOMS,
        "SpectralExample.Example24.mutually_annihilating": STANDARD_AXIOMS,
        "SpectralExample.Example24.projections_sum_to_identity": STANDARD_AXIOMS,
        "SpectralExample.Example24.projections_self_adjoint": STANDARD_AXIOMS,
        "SpectralExample.Example24.orthogonal_ranges": STANDARD_AXIOMS,
        "SpectralExample.Example24.vector_decomposition": STANDARD_AXIOMS,
        "SpectralExample.Example24.images_are_eigenvectors": STANDARD_AXIOMS,
        "SpectralExample.Example24.P6_fixed_iff": STANDARD_AXIOMS,
        "SpectralExample.Example24.P1_fixed_iff": STANDARD_AXIOMS,
        "SpectralExample.Example24.spectral_decomposition": STANDARD_AXIOMS,
        "SpectralExample.Example24.squared_spectral_decomposition": STANDARD_AXIOMS,
        "SpectralExample.Example24.components_of_e": STANDARD_AXIOMS,
        "SpectralExample.Example24.components_of_e_sum_and_orthogonal": STANDARD_AXIOMS,
        "SpectralExample.Example24.A_squared_e": STANDARD_AXIOMS,
        "SpectralExample.Example24.A_applied_twice_e": STANDARD_AXIOMS,
    },
}
AUDIT = re.compile(
    r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$",
    re.MULTILINE,
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", help="Use this installed Lean binary with the current LEAN_PATH")
    part = parser.add_mutually_exclusive_group()
    part.add_argument("--coordinates-only", action="store_true",
                      help="Check only the finite-sum proof for a given orthogonal matrix")
    part.add_argument("--certificate-only", action="store_true",
                        help="Check only the integer matrix certificate, without Mathlib")
    args = parser.parse_args()
    if not (args.lean or args.certificate_only):
        # Resolve the locked environment once, then give fresh project objects
        # precedence over all caches (including any installed earlier version).
        try:
            return subprocess.run(
                ["lake", "env", sys.executable, str(Path(__file__).resolve()), "--lean", "lean"]
                + (["--coordinates-only"] if args.coordinates_only else []),
                cwd=ROOT).returncode
        except OSError as err:
            print(err, file=sys.stderr)
            return 1
    compiler = args.lean or "lean"
    if os.path.dirname(compiler):
        compiler = str(Path(compiler).resolve())
    cmd = [compiler]
    targets = (["MatrixCertificate.lean"] if args.certificate_only else
               ["OrthogonalCoordinates.lean"] if args.coordinates_only else list(TARGETS))
    try:
        ver = subprocess.run(cmd + ["--version"], cwd=ROOT, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True)
        print(ver.stdout.strip(), flush=True)
        if not re.search(rf"\bversion {re.escape(VERSION)}(?:[, )])", ver.stdout):
            raise ValueError("Use the Lean version pinned in lean-toolchain.")
        with tempfile.TemporaryDirectory(prefix="spectral-proofs-") as source_cache:
            inherited = os.environ.get("LEAN_PATH")
            env = dict(os.environ, LEAN_PATH=source_cache + (os.pathsep + inherited if inherited else ""))
            for filename in targets:
                target = Path(source_cache) / Path(filename).with_suffix(".olean")
                proc = subprocess.run(cmd + ["-j1", "-o", str(target), filename], cwd=ROOT, env=env, text=True,
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                print(proc.stdout, end="", flush=True)
                if proc.returncode or "sorryAx" in proc.stdout or re.search(r": (?:warning|error):", proc.stdout):
                    raise ValueError(f"Lean check failed for {filename}.")
                audited = {name: {x.strip() for x in axioms.split(",") if x.strip()}
                           for name, axioms in AUDIT.findall(proc.stdout)}
                for name, allowed in TARGETS[filename].items():
                    if name not in audited or not audited[name] <= allowed:
                        raise ValueError(f"Missing axiom audit or unexpected axioms: {name}")
    except subprocess.CalledProcessError as err:
        print(err.stdout or err, file=sys.stderr)
        return 1
    except (OSError, ValueError) as err:
        print(err, file=sys.stderr)
        return 1
    print(f"Lean proof check and axiom audit passed: {len(targets)} source file(s), "
          f"{sum(len(TARGETS[f]) for f in targets)} audited declaration(s).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
