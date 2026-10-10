"""Compare the maintained QRH endpoints to independently elaborated Mathlib targets."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path
from typing import Any

from scripts.analytic_dependency import load_artifact_manifests, source_digest

TARGET_CHECK = """
import QRHMathlibTarget
import Solution

set_option autoImplicit false

example : PrimeFactorOscillations.QRHSpecification.zetaSevenEighths :=
  PrimeFactorOscillations.QRH.zeta_ne_zero

example : PrimeFactorOscillations.QRHSpecification.dirichletSevenEighths :=
  PrimeFactorOscillations.QRH.dirichletL_ne_zero

#check "QRH_CANONICAL_TYPES_IDENTICAL"
"""


def check_qrh_statements(lean: str, environment: dict[str, str], directory: Path) -> dict[str, Any]:
    """Compile the specification without OAI, then consume the actual Solution."""
    _, extensions, _ = load_artifact_manifests()
    extension = extensions[-1]
    if extension["kind"] != "append_only_verified_source_port":
        raise ValueError("missing verified QRH source manifest")
    canonical = extension["endpoint_audit"]["canonical_specification"]
    spec_root = directory / "qrh-spec"
    spec_root.mkdir(exist_ok=True)
    if any(not p.name.startswith("QRHMathlibTarget.") for p in spec_root.iterdir()):
        raise ValueError("unexpected namespace in the canonical specification directory")
    specification = spec_root / "QRHMathlibTarget.lean"
    specification.write_text(canonical["source_text"], encoding="utf-8", newline="\n")
    if source_digest(specification) != canonical["source_sha256"]:
        raise ValueError("canonical specification source hash mismatch")
    code = TARGET_CHECK.lstrip()
    if not code.isascii() or "!=" in code or "import Mathlib\n" in code:
        raise ValueError("canonical audit source policy failure")
    target = directory / "QRHCanonicalTypes.lean"
    target.write_text(code, encoding="utf-8", newline="\n")
    output = spec_root / "QRHMathlibTarget.olean"
    logs: dict[str, str] = {}
    for source, extra, roots in (
        (specification, ["-o", str(output)], environment["LEAN_PATH"]),
        (target, [], os.pathsep.join([str(spec_root), environment["LEAN_PATH"]])),
    ):
        completed = subprocess.run(
            [lean, "--stdin", "-j", "1", "-s", "65536", "-M", "8192", *extra, str(source)],
            cwd=Path(__file__).resolve().parents[1],
            env={**environment, "LEAN_PATH": roots},
            input=source.read_text(encoding="utf-8"),
            check=False,
            capture_output=True,
            text=True,
            encoding="utf-8",
        )
        log = directory / (source.stem + ".log")
        log.write_text(completed.stdout + completed.stderr, encoding="utf-8")
        if completed.returncode != 0:
            raise ValueError(f"QRH canonical target failed ({completed.returncode}); see {log}")
        logs[source.stem] = source_digest(log)
    if '"QRH_CANONICAL_TYPES_IDENTICAL" : String' not in (
        directory / "QRHCanonicalTypes.log"
    ).read_text(encoding="utf-8"):
        raise ValueError("missing QRH canonical target completion marker")
    return {
        "status": "verified",
        "specification_source_sha256": source_digest(specification),
        "specification_object_sha256": source_digest(output),
        "consumer_source_sha256": source_digest(target),
        "log_sha256": logs,
    }
