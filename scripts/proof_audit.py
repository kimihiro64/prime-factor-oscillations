"""Audit compiled statement identity and the headline's dependency axioms."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, cast

ROOT = Path(__file__).resolve().parents[1]
if __package__ in {None, ""}:
    sys.path.insert(0, str(ROOT))

from scripts.analytic_dependency import MANIFEST_SHA256, source_digest  # noqa: E402
from scripts.prebuilt_dependency import TOOLCHAIN  # noqa: E402

THEOREMS = (
    "PrimeGaps.eventually_many_prime_windows_600",
    "PrimeFactorOscillations.both_reversal_bounds_of_quantitative_prime_windows",
    "PrimeFactorOscillations.doubleExponentialReversalBounds",
    "PrimeFactorOscillations.publicDoubleExponentialReversalBounds",
    "PrimeFactorOscillations.ReciprocalSmoothLaw.exists_sharp_reversal_rate_all_ranks",
    "PrimeFactorOscillations.AffineSumFamily.exists_sharp_arithmetic_reversal_rate_all_ranks",
    "PrimeFactorOscillations.exists_affine_arithmetic_rate_recovers_full_gap_class",
    "PrimeFactorOscillations.publicAffinePrimePairSpectrum",
    "PrimeFactorOscillations.recurrent_short_gaps_iff_late_ascents",
    "PrimeFactorOscillations.late_ascent_critical_scale",
    "PrimeFactorOscillations.ascent_above_one_fifth_forces_twins",
    "PrimeFactorOscillations.infinitely_many_twins_of_late_ascent_supply",
)
FOUNDATIONS = frozenset(("propext", "Classical.choice", "Quot.sound"))
BOUNDARY = """
import Lean.Elab.Command

set_option autoImplicit false

#eval do
  let challenge <- Lean.importModules #[{ module := `Challenge }] {}
  let solution <- Lean.importModules #[{ module := `Solution }] {}
  let names : Array Lean.Name := #[
    `PrimeFactorOscillations.publicDoubleExponentialReversalBounds,
    `PrimeFactorOscillations.publicAffinePrimePairSpectrum]
  for name in names do
    let some expected := challenge.find? name
      | throw (IO.userError "missing Challenge declaration")
    let some actual := solution.find? name
      | throw (IO.userError "missing Solution declaration")
    unless expected.type == actual.type do
      throw (IO.userError "compiled public statement mismatch")
    unless expected.levelParams == actual.levelParams do
      throw (IO.userError "compiled universe parameter mismatch")
  IO.println "COMPILED_PUBLIC_TYPES_IDENTICAL"
"""


def axiom_sets(log: str) -> dict[str, list[str]]:
    """Require exactly the requested reports and no research or sorry axioms."""
    pairs = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
    result = {name: sorted(x.strip() for x in body.split(",") if x.strip()) for name, body in pairs}
    if len(pairs) != len(THEOREMS) or set(result) != set(THEOREMS):
        raise ValueError("missing, duplicate, or unexpected axiom report")
    for name, axioms in result.items():
        if not set(axioms).issubset(FOUNDATIONS):
            raise ValueError(f"nonfoundational assumption in {name}: {axioms}")
    return result


def check_built_sources(report: dict[str, Any]) -> None:
    """Reject an audit if any owned input changed since the successful build."""
    cache = json.loads((ROOT / ".lake/build/owned-module-cache.json").read_text(encoding="utf-8"))
    for name in report["checked_owned_modules"]:
        row = cache["modules"][name]
        source = ROOT / (name.replace(".", "/") + ".lean")
        obj = ROOT / ".lake/build/lib/lean" / (name.replace(".", "/") + ".olean")
        if row["source_sha256"] != source_digest(source) or row["object_sha256"] != source_digest(
            obj
        ):
            raise ValueError(f"stale build for {name}")


def main() -> int:
    """Run concise audits with the exact successful public build environment."""
    try:
        report_path = ROOT / ".lake/build/project-build.json"
        report = cast(dict[str, Any], json.loads(report_path.read_text(encoding="utf-8")))
        if (
            report["toolchain"] != TOOLCHAIN
            or report["analytic_manifest_sha256"] != MANIFEST_SHA256
        ):
            raise ValueError("build environment differs from the current pin")
        if report["dependency_builds"] != 0:
            raise ValueError("unexpected dependency build")
        check_built_sources(report)
        environment = os.environ.copy()
        environment["LEAN_PATH"] = report["lean_path"]
        environment["ELAN_TOOLCHAIN"] = TOOLCHAIN
        lean = report["compiler_executable"]
        version = subprocess.run(
            [lean, "--version"], check=True, capture_output=True, text=True, encoding="utf-8"
        ).stdout.strip()
        if version != report["version"]:
            raise ValueError("compiler changed since the successful build")
        directory = ROOT / ".research/audits/public-integration"
        directory.mkdir(parents=True, exist_ok=True)
        challenge_source = ROOT / "Challenge.lean"
        challenge_object = ROOT / ".lake/build/lib/lean/Challenge.olean"
        challenge = subprocess.run(
            [
                lean,
                "-j",
                "1",
                "-s",
                "65536",
                "-M",
                "8192",
                "-o",
                str(challenge_object),
                str(challenge_source),
            ],
            cwd=ROOT,
            env=environment,
            check=False,
            capture_output=True,
            text=True,
            encoding="utf-8",
        )
        (directory / "Challenge.log").write_text(
            challenge.stdout + challenge.stderr, encoding="utf-8"
        )
        if challenge.returncode != 0:
            raise ValueError(
                f"Challenge failed ({challenge.returncode}); see {directory / 'Challenge.log'}"
            )
        sources = {
            "PublicTypes": BOUNDARY,
            "PublicAxioms": "import Solution\n\n"
            + "\n".join(f"#check {name}\n#print axioms {name}" for name in THEOREMS)
            + "\n",
        }
        logs: dict[str, str] = {}
        for name, source in sources.items():
            if not source.isascii() or "import Mathlib\n" in source or "!=" in source:
                raise ValueError("generated Lean source policy failure")
            path = directory / f"{name}.lean"
            path.write_text(source.lstrip(), encoding="utf-8")
            completed = subprocess.run(
                [lean, "-j", "1", "-s", "65536", "-M", "8192", str(path)],
                cwd=ROOT,
                env=environment,
                check=False,
                capture_output=True,
                text=True,
                encoding="utf-8",
            )
            log = completed.stdout + completed.stderr
            (directory / f"{name}.log").write_text(log, encoding="utf-8")
            if completed.returncode != 0:
                raise ValueError(
                    f"{name} failed ({completed.returncode}); see {directory / (name + '.log')}"
                )
            logs[name] = log
        if "COMPILED_PUBLIC_TYPES_IDENTICAL" not in logs["PublicTypes"]:
            raise ValueError("missing compiled-boundary success marker")
        axioms = axiom_sets(logs["PublicAxioms"])
        result = {
            "status": "verified",
            "compiled_type_identity": True,
            "compiled_statement_count": 2,
            "challenge_source_sha256": source_digest(challenge_source),
            "challenge_object_sha256": source_digest(challenge_object),
            "axioms": axioms,
            "compiler": lean,
            "version": version,
            "analytic_manifest_sha256": MANIFEST_SHA256,
            "build_report_sha256": source_digest(report_path),
            "owned_cache_sha256": source_digest(ROOT / ".lake/build/owned-module-cache.json"),
            "official_comparator_nanoda": "not run; separate registry/release validation",
        }
        (directory / "report.json").write_text(
            json.dumps(result, indent=2) + "\n", encoding="utf-8"
        )
        print(
            f"Two public compiled types identical; {len(THEOREMS)} theorem closures "
            "use standard foundations only."
        )
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"proof audit failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
