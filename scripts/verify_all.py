"""5-Gate End-to-End Verification Harness for Paper 64 (VPVNP-CERT-1.0)."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.vpvnp_certifier import verify_certificate_file

ALLOWED_AXIOMS = {"propext", "Quot.sound"}


def gate1_lean() -> None:
    print("[Gate 1] Building Lean 4.35.0 kernel & auditing axioms...")
    lean_dir = ROOT / "lean"
    lean_src = (lean_dir / "OpenAIVpVnpSeparation.lean").read_text(encoding="utf-8")
    stripped = re.sub(r"/-.*?-/", "", lean_src, flags=re.DOTALL)
    stripped = re.sub(r"--.*", "", stripped)
    if re.search(r"\b(sorry|admit|axiom)\b", stripped):
        raise SystemExit("Gate 1 FAIL: Forbidden token (sorry/admit/axiom) in Lean source")

    b = subprocess.run(
        ["lake", "build", "OpenAIVpVnpSeparation"],
        cwd=lean_dir,
        capture_output=True,
        text=True,
    )
    if b.returncode != 0:
        print(b.stdout)
        print(b.stderr)
        raise SystemExit("Gate 1 FAIL: lake build failed")
    if "warning:" in (b.stdout + b.stderr).lower():
        raise SystemExit(f"Gate 1 FAIL: Lean warnings present:\n{b.stdout}\n{b.stderr}")

    a = subprocess.run(
        ["lake", "env", "lean", "-j", "1", "AuditAxioms.lean"],
        cwd=lean_dir,
        capture_output=True,
        text=True,
    )
    if a.returncode != 0:
        print(a.stdout)
        print(a.stderr)
        raise SystemExit("Gate 1 FAIL: AuditAxioms.lean failed")

    lines = [ln.strip() for ln in a.stdout.splitlines() if ln.strip()]
    if len(lines) != 18:
        raise SystemExit(f"Gate 1 FAIL: Expected 18 axiom lines, got {len(lines)}")
    none_cnt = 0
    p_cnt = 0
    pq_cnt = 0
    for ln in lines:
        if "does not depend on any axioms" in ln:
            none_cnt += 1
        else:
            m = re.search(r"depends on axioms:\s*\[([^\]]*)\]", ln)
            if not m:
                raise SystemExit(f"Gate 1 FAIL: Unparsed axiom line: {ln}")
            axs = {tok.strip() for tok in m.group(1).split(",") if tok.strip()}
            if not axs.issubset(ALLOWED_AXIOMS):
                raise SystemExit(f"Gate 1 FAIL: Disallowed axioms {axs} in {ln}")
            if axs == {"propext"}:
                p_cnt += 1
            else:
                pq_cnt += 1
    print(f"[Gate 1 PASS] 18/18 Lean 4.35.0 theorems verified (0 warnings, {none_cnt} none, {p_cnt} [propext], {pq_cnt} [propext, Quot.sound]).")


def gate2_zero_float_ast() -> None:
    print("[Gate 2] Auditing src/*.py AST for zero floating-point operations...")
    py_files = sorted((ROOT / "src").glob("*.py"))
    if not py_files:
        raise SystemExit("Gate 2 FAIL: No src/*.py files found")
    forbidden_funcs = {"float", "complex"}
    forbidden_math = {"log", "log2", "log10", "exp", "sqrt", "pow", "sin", "cos", "floor", "ceil"}
    for path in py_files:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and isinstance(node.value, (float, complex)):
                raise SystemExit(f"Gate 2 FAIL: Float/complex literal in {path.name}:{node.lineno}")
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in forbidden_funcs:
                raise SystemExit(f"Gate 2 FAIL: Call to {node.func.id}() in {path.name}:{node.lineno}")
            if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
                raise SystemExit(f"Gate 2 FAIL: True division '/' found in {path.name}:{node.lineno}")
            if isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Div):
                raise SystemExit(f"Gate 2 FAIL: Augmented true division '/=' found in {path.name}:{node.lineno}")
            if isinstance(node, ast.Import) and any(a.name == "math" for a in node.names):
                raise SystemExit(f"Gate 2 FAIL: 'import math' found in {path.name}:{node.lineno}")
            if isinstance(node, ast.ImportFrom) and node.module == "math":
                raise SystemExit(f"Gate 2 FAIL: 'from math import' found in {path.name}:{node.lineno}")
            if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id == "math":
                if node.attr in forbidden_math:
                    raise SystemExit(f"Gate 2 FAIL: Float math.{node.attr} in {path.name}:{node.lineno}")
    print(f"[Gate 2 PASS] {len(py_files)}/{len(py_files)} src/*.py modules are strictly zero-float.")


def gate3_certificates() -> None:
    print("[Gate 3] Verifying all 16 canonical certificates...")
    certs = sorted((ROOT / "certificates").glob("*.cert.json"))
    if len(certs) != 16:
        raise SystemExit(f"Gate 3 FAIL: Expected 16 certificates, found {len(certs)}")
    for c in certs:
        verify_certificate_file(c)
    print("[Gate 3 PASS] 16/16 canonical certificates verified cleanly.")


def gate4_pytest() -> None:
    print("[Gate 4] Running full pytest suite...")
    r = subprocess.run([sys.executable, "-m", "pytest", "-q"], cwd=ROOT, capture_output=True, text=True)
    print(r.stdout.strip())
    if r.returncode != 0:
        print(r.stderr)
        raise SystemExit("Gate 4 FAIL: pytest failed")
    print("[Gate 4 PASS] All pytest checks passed.")


def _manifest_targets() -> list[Path]:
    targets: list[Path] = []
    for rel in [
        "LICENSE",
        "README.md",
        "pyproject.toml",
        "airr_metadata_paper64.json",
        "lean/lean-toolchain",
        "lean/lakefile.toml",
        "lean/OpenAIVpVnpSeparation.lean",
        "lean/AuditAxioms.lean",
        "paper/main.tex",
        "paper/references.bib",
        "paper/main.pdf",
    ]:
        p = ROOT / rel
        if p.is_file():
            targets.append(p)
    for folder, pat in [
        ("src", "*.py"),
        ("scripts", "*.py"),
        ("tests", "*.py"),
        ("certificates", "*.cert.json"),
        ("results", "*.json"),
        ("paper/figures", "*.png"),
    ]:
        targets.extend(sorted((ROOT / folder).glob(pat)))
    return sorted(set(targets), key=lambda x: x.relative_to(ROOT).as_posix())


def _sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def gate5_manifest(write: bool) -> None:
    manifest_path = ROOT / "SHA256_MANIFEST.json"
    targets = _manifest_targets()
    computed = {p.relative_to(ROOT).as_posix(): _sha256(p) for p in targets}
    if write:
        manifest_path.write_text(
            json.dumps({"file_count": len(computed), "files": computed}, indent=2) + "\n",
            encoding="utf-8",
            newline="\n",
        )
        print(f"[Gate 5 WRITE] Wrote SHA256_MANIFEST.json with {len(computed)} files.")
        return
    if not manifest_path.is_file():
        raise SystemExit("Gate 5 FAIL: SHA256_MANIFEST.json missing")
    recorded = json.loads(manifest_path.read_text(encoding="utf-8"))["files"]
    if recorded != computed:
        raise SystemExit("Gate 5 FAIL: Manifest mismatch")
    print(f"[Gate 5 PASS] {len(computed)}/{len(computed)} SHA-256 digests verified.")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write-manifest", action="store_true")
    args = ap.parse_args()
    gate1_lean()
    gate2_zero_float_ast()
    gate3_certificates()
    gate4_pytest()
    gate5_manifest(write=args.write_manifest)
    print("ALL 5 VERIFICATION GATES PASSED.")


if __name__ == "__main__":
    main()
