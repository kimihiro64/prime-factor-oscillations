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

from scripts.analytic_dependency import (  # noqa: E402
    MANIFEST_SHA256,
    source_digest,
    verify_environment,
)
from scripts.artifact_extensions import require_report_environment  # noqa: E402
from scripts.prebuilt_dependency import TOOLCHAIN  # noqa: E402

THEOREMS = (
    "PrimeFactorOscillations.exists_eventually_densityRatio_signed_thetaClock_margin",
    "PrimeFactorOscillations.exists_eventually_floor_densityRatio_signed_margin",
    "PrimeFactorOscillations.densityRatio_thetaClock_two_sided_power_excursions_of_zero",
    "PrimeFactorOscillations.publicFalseRHMovingRankPowerExcursions",
    "PrimeFactorOscillations.nicolasThetaError_bounds_of_power_peak",
    "PrimeFactorOscillations.nicolasLog_lower_of_power_peak",
    "PrimeFactorOscillations.nicolasLog_power_unbounded_of_K_integer_excursions",
    "PrimeFactorOscillations.nicolasK_nat_gt_power_of_real",
    "PrimeFactorOscillations.nicolasLog_two_sided_power_excursions_of_zero",
    "PrimeFactorOscillations.exists_nicolasLog_two_sided_power_excursions_of_not_RH",
    "PrimeFactorOscillations.publicZeroDependentLogarithmExcursions",
    "PrimeFactorOscillations.publicFalseRHLogarithmExcursions",
    "PrimeFactorOscillations.exists_eventually_nicolasHeightTangentError_log_bound",
    "PrimeFactorOscillations.exists_eventually_nicolasLog_sub_K_le_log_cube",
    "PrimeFactorOscillations.publicRHLogarithmicCorrection",
    "PrimeFactorOscillations.exists_nicolasLogDegreeError_le_mass",
    "PrimeFactorOscillations.exists_nicolasPsiError_le_sqrt_log_sq",
    "PrimeFactorOscillations.exists_nicolasThetaError_le_sqrt_log_sq",
    "PrimeFactorOscillations.publicRHPointwiseLogarithmicBound",
    "PrimeFactorOscillations.exists_nicolasZeroCoefficient_log_bound",
    "PrimeFactorOscillations.publicRHWeightedZeroCoefficientBound",
    "PrimeFactorOscillations.nicolasXi_finite_zero_ball",
    "PrimeFactorOscillations.nicolasXi_zero_count_logarithmic",
    "PrimeFactorOscillations.publicXiZeroCounting",
    "PrimeFactorOscillations.nicolasXi_right_growth",
    "PrimeFactorOscillations.nicolasXi_log_growth",
    "PrimeFactorOscillations.publicXiLogarithmicGrowth",
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
    "PrimeFactorOscillations.eventually_densityRatio_thetaClock_lt_reference_of_RH",
    "PrimeFactorOscillations.riemannHypothesis_of_eventually_densityRatio_thetaClock_lt_reference",
    "PrimeFactorOscillations.riemannHypothesis_iff_eventually_densityRatio_thetaClock_lt_reference",
    "PrimeFactorOscillations.publicMovingRankRHCriterion",
    "PrimeFactorOscillations.riemannHypothesis_iff_eventually_nicolasLog_neg",
    "PrimeFactorOscillations.riemannHypothesis_iff_eventually_theta_lt_primeProductClock",
    "PrimeFactorOscillations.riemannHypothesis_iff_eventually_thetaTailIntegral_neg",
    "PrimeFactorOscillations.publicThetaTailRHCriterion",
    "PrimeFactorOscillations.publicPrimeProductClockRHCriterion",
    "PrimeFactorOscillations.exists_eventually_densityRatio_real_thetaClock_linearization",
    "PrimeFactorOscillations.publicDensityRatioLinearization",
    "PrimeFactorOscillations.eventually_densityRatio_thetaClock_lt_reference_uniform_of_RH",
    "PrimeFactorOscillations.ordinary_ascent_reference_gap_bound_of_RH",
    "PrimeFactorOscillations.publicRHAscentReferenceBound",
    "PrimeFactorOscillations.exists_primeProfile_reference_value_bound",
    "PrimeFactorOscillations.exists_primeProfile_reference_local_crossing",
    "PrimeFactorOscillations.publicReferenceCrossing",
    "PrimeFactorOscillations.exists_ordinary_ascent_theta_envelope_of_RH",
    "PrimeFactorOscillations.publicRHAllAscentEnvelope",
    "PrimeFactorOscillations.finite_primeThetaEndpoints",
    "PrimeFactorOscillations.reversal_count_le_prime_endpoint_card",
    "PrimeFactorOscillations.reversal_count_le_primeThetaEndpointCount",
    "PrimeFactorOscillations.exists_last_ascent_of_nonincreasing_tail",
    "PrimeFactorOscillations.reversal_count_le_primeCounting_of_ascent_bound",
    "PrimeFactorOscillations.primeCounting_le_primeThetaEndpointCount",
    "PrimeFactorOscillations.ordinary_eventually_last_ascent_with_reversal_number",
    "PrimeFactorOscillations.exists_ordinary_last_ascent_and_capacity_of_RH",
    "PrimeFactorOscillations.publicRHLastAscentAndCapacity",
    "PrimeFactorOscillations.primeCounting_isEquivalent_div_log",
    "PrimeFactorOscillations.tendsto_primeCounting_div_mainTerm",
    "PrimeFactorOscillations.tendsto_thetaPrefix_div_endpoint",
    "PrimeFactorOscillations.eventually_thetaPrefix_and_primeCounting_bounds",
    "PrimeFactorOscillations.eventually_count_log_count_le_thetaPrefix",
    "PrimeFactorOscillations.ordinary_eventually_last_ascent_lower_location",
    "PrimeFactorOscillations.exists_ordinary_last_ascent_location_sandwich_of_RH",
    "PrimeFactorOscillations.publicLastAscentLowerLocation",
    "PrimeFactorOscillations.publicRHLastAscentLocationSandwich",
    "PrimeFactorOscillations.tendsto_primeCounting_scaled_mainTerm",
    "PrimeFactorOscillations.eventually_primeThetaEndpointCount_sandwich",
    "PrimeFactorOscillations.tendsto_primeThetaEndpointCount_div_mainTerm",
    "PrimeFactorOscillations.exists_ordinary_last_ascent_asymptotic_capacity_of_RH",
    "PrimeFactorOscillations.publicRHLastAscentAsymptoticCapacity",
    "Nat.descFactorial_coefficient_value_error",
    "PrimeFactorOscillations.exists_primeProfile_normalized_value_deriv_errors",
    "PrimeFactorOscillations.exists_primeProfile_normalized_secondOrder_error",
    "PrimeFactorOscillations.publicPrimeProfileSecondOrderExpansion",
    "PrimeFactorOscillations.exists_primeProfile_reference_root_shift_bound",
    "PrimeFactorOscillations.exists_primeProfile_reference_sharp_crossing",
    "PrimeFactorOscillations.exists_ordinary_last_ascent_sharp_reference_of_RH",
    "PrimeFactorOscillations.publicSharpReferenceCrossing",
    "PrimeFactorOscillations.publicRHLastAscentSharpReference",
    "Real.logLog_exp_exp_envelope",
    "PrimeFactorOscillations.eventually_primeThetaEndpointCount_loglog_error",
    "PrimeFactorOscillations.exists_primeThetaEndpointCount_loglog_rank_error",
    "PrimeFactorOscillations.exists_primeThetaEndpointCount_near_rank_loglog_error",
    "PrimeFactorOscillations.exists_primeProfile_reference_loglog_capacity",
    "PrimeFactorOscillations.exists_ordinary_last_ascent_loglog_capacity_of_RH",
    "PrimeFactorOscillations.publicReferenceLogCapacity",
    "PrimeFactorOscillations.publicRHReversalCountLogBound",
    "PrimeFactorOscillations.ordinary_ascent_eventually_in_clock_window",
    "PrimeFactorOscillations.mem_ordinaryReferenceEligiblePrimes",
    "PrimeFactorOscillations.reversal_count_le_reference_eligible",
    "PrimeFactorOscillations.ordinary_reversal_count_reference_bound_of_RH",
    "PrimeFactorOscillations.ordinary_reference_eligible_supply_of_RH",
    "PrimeFactorOscillations.publicRHGapFilteredCounts",
    "PrimeFactorOscillations.norm_nicolasSpectralAtom_le",
    "PrimeFactorOscillations.summable_nicolasSpectralAtom",
    "PrimeFactorOscillations.norm_nicolasSpectralTail_le",
    "PrimeFactorOscillations.nicolasSpectral_kernel_split",
    "PrimeFactorOscillations.nicolasJ_spectral_explicit_error",
    "PrimeFactorOscillations.abs_nicolasZeroWave_le",
    "PrimeFactorOscillations.nicolasJ_wave_explicit_error",
    "PrimeFactorOscillations.nicolasZeroWave_eq_spectral_sum",
    "PrimeFactorOscillations.nicolasJ_wave_uniform_error",
    "PrimeFactorOscillations.publicRHSpectralPsiExpansion",
    "PrimeFactorOscillations.nicolasPsiRootTail_upper",
    "PrimeFactorOscillations.nicolasPrimePowerTail_square_sandwich",
    "PrimeFactorOscillations.nicolasRealKernel_upper",
    "PrimeFactorOscillations.nicolasRealKernel_higher_root_bound",
    "PrimeFactorOscillations.nicolasPrimePowerTail_higher_roots_bound",
    "PrimeFactorOscillations.nicolasHalfKernel_explicit_error",
    "PrimeFactorOscillations.nicolasPsiSquareTail_explicit_error",
    "PrimeFactorOscillations.nicolasPsiSquareTail_uniform_error",
    "PrimeFactorOscillations.nicolasPrimePowerTail_uniform_square_bias",
    "PrimeFactorOscillations.nicolasK_wave_uniform_error",
    "PrimeFactorOscillations.publicRHThetaSpectralExpansion",
    "PrimeFactorOscillations.summable_nicolasThreeHalfZeroWeight",
    "PrimeFactorOscillations.norm_nicolasZeroCoefficient_le_sqrt_degree",
    "PrimeFactorOscillations.nicolasDegreeRemainderScalar_le",
    "PrimeFactorOscillations.norm_nicolasDegreeZeroKernel_le",
    "PrimeFactorOscillations.norm_tsum_nicolasDegreeZeroKernel_le",
    "PrimeFactorOscillations.abs_nicolasDegreeError_le",
    "PrimeFactorOscillations.publicRHDegreeErrorBound",
    "PrimeFactorOscillations.nicolasDegreeError_sub_eq_band",
    "PrimeFactorOscillations.nicolasDegreeMass_sub_eq_band",
    "PrimeFactorOscillations.nicolasDegreeError_band_sandwich",
    "PrimeFactorOscillations.nicolasDegreeMass_pos",
    "PrimeFactorOscillations.nicolasDegreeMass_eq_inv",
    "PrimeFactorOscillations.nicolasDegreeMass_halving",
    "PrimeFactorOscillations.abs_nicolasDegreeError_le_mass",
    "PrimeFactorOscillations.nicolasDegree_band_pointwise_bounds",
    "PrimeFactorOscillations.nicolasDegree_dilation_power",
    "PrimeFactorOscillations.abs_nicolasPsiError_le_degree",
    "PrimeFactorOscillations.abs_nicolasPsiError_le_two_thirds",
    "PrimeFactorOscillations.abs_nicolasThetaError_le_two_thirds",
    "PrimeFactorOscillations.publicRHPointwisePowerBound",
    "Real.logLog_remainder_bounds_of_le",
    "Real.logLog_remainder_abs_le",
    "PrimeFactorOscillations.eventually_nicolasHeight_domain",
    "PrimeFactorOscillations.eventually_abs_nicolasHeightTangentError_le",
    "PrimeFactorOscillations.nicolasLogSpectralConstant_pos",
    "PrimeFactorOscillations.eventually_nicolasLog_wave_uniform_error",
    "PrimeFactorOscillations.publicRHLogSpectralExpansion",
    "PrimeFactorOscillations.nicolasPrimeProductClock_eq_theta_mul_exp",
    "PrimeFactorOscillations.eventually_abs_nicolasLog_scaled_error_le",
    "PrimeFactorOscillations.tendsto_nicolasLog_scaled_error",
    "PrimeFactorOscillations.tendsto_nicolasLog_mul_log",
    "PrimeFactorOscillations.tendsto_nicolasLog_zero",
    "PrimeFactorOscillations.tendsto_nicolasPrimeProductClock_normalized_error",
    "PrimeFactorOscillations.publicRHSpatialClockExpansion",
    "PrimeFactorOscillations.exists_primePrefixProfile_spatial_sign_transfer",
    "PrimeFactorOscillations.nicolasPrimeProductClock_nat_eq_prefix_clock",
    "PrimeFactorOscillations.exists_densityRatio_spatial_sign_transfer",
    "PrimeFactorOscillations.exists_densityRatio_local_spatial_threshold",
    "PrimeFactorOscillations.publicLocalDensityRatioThreshold",
    "PrimeFactorOscillations.exists_primePrefixProfile_log_error",
    "PrimeFactorOscillations.primePrefixProfile_log_eq_sum",
    "PrimeFactorOscillations.nicolasTiltedLog_nat_eq_components",
    "PrimeFactorOscillations.exists_nicolasTiltedLog_nat_error",
    "PrimeFactorOscillations.riemannHypothesis_iff_eventually_nicolasTiltedLog_nat_neg",
    "PrimeFactorOscillations.nicolasTiltedLog_natFloor",
    "PrimeFactorOscillations.riemannHypothesis_iff_eventually_nicolasTiltedLog_neg",
    "PrimeFactorOscillations.nicolasTiltedProduct_pos",
    "PrimeFactorOscillations.log_nicolasTiltedProduct",
    "PrimeFactorOscillations.riemannHypothesis_iff_eventually_nicolasTiltedProduct_lt_one",
    "PrimeFactorOscillations.publicTiltedPrimeProductCriterion",
    "PrimeFactorOscillations.primePrefixProfile_log_tail_bounds",
    "PrimeFactorOscillations.primeProfile_log_tail_bounds",
    "PrimeFactorOscillations.nicolasTiltedLog_nat_tail_bounds",
    "PrimeFactorOscillations.eventually_forall_pos_nicolasTiltedLog_nat_neg_of_RH",
    "PrimeFactorOscillations.riemannHypothesis_iff_eventually_all_positive_tiltedProducts_lt_one",
    "PrimeFactorOscillations.publicAllPositiveTiltedPrimeProductCriterion",
    "PrimeFactorOscillations.summable_primeProfile_logFactor",
    "PrimeFactorOscillations.log_primeProfile_eq_tsum",
    "PrimeFactorOscillations.primeProfile_log_tail_eq_tsum",
    "PrimeFactorOscillations.primeProfile_log_tail_nonneg",
    "PrimeFactorOscillations.primeProfile_log_tail_nonpos",
    "PrimeFactorOscillations.publicTiltedLogTail",
    "PrimeFactorOscillations.hasDerivAt_nicolasTiltedWeight",
    "PrimeFactorOscillations.nicolasTiltedKernel_pos",
    "PrimeFactorOscillations.nicolasTiltedKernel_error",
    "PrimeFactorOscillations.publicTiltedKernelComparison",
    "PrimeFactorOscillations.nicolasTiltedIntegralErrorConstant_nonneg",
    "PrimeFactorOscillations.nicolasTiltedIntegrand_error",
    "PrimeFactorOscillations.nicolasTiltedIntegrand_error_majorant",
    "PrimeFactorOscillations.integrableOn_nicolasTiltedIntegral_error",
    "PrimeFactorOscillations.integrableOn_nicolasTiltedIntegral",
    "PrimeFactorOscillations.nicolasTiltedIntegral_sub_mul_K",
    "PrimeFactorOscillations.nicolasTiltedIntegral_error",
    "PrimeFactorOscillations.eventually_nicolasTiltedIntegral_neg_of_RH",
    "PrimeFactorOscillations.riemannHypothesis_iff_eventually_nicolasTiltedIntegral_neg",
    "PrimeFactorOscillations.publicTiltedIntegralCriterion",
    "PrimeFactorOscillations.nicolasTiltedIntegral_wave_normalized_error",
    "PrimeFactorOscillations.tendsto_nicolasTiltedIntegral_wave_error",
    "PrimeFactorOscillations.publicTiltedIntegralSpectralExpansion",
    "PrimeFactorOscillations.nicolasPsi_isEquivalent_id",
    "PrimeFactorOscillations.tendsto_nicolasPsi_ratio",
    "PrimeFactorOscillations.tendsto_nicolasHalfKernel_scaled",
    "PrimeFactorOscillations.eventually_nicolasPsiSquareTail_relative_error",
    "PrimeFactorOscillations.tendsto_nicolasPsiSquareTail_scaled",
    "PrimeFactorOscillations.tendsto_nicolasPrimePowerTail_sub_square_scaled",
    "PrimeFactorOscillations.tendsto_nicolasPrimePowerTail_scaled",
    "PrimeFactorOscillations.publicPrimePowerTailAsymptotic",
    "PrimeFactorOscillations.nicolasJ_omegaMinus_of_zero_at_exponent",
    "PrimeFactorOscillations.nicolasJ_arbitrary_negative_excursions_of_zero",
    "PrimeFactorOscillations.nicolasK_two_sided_power_excursions_of_zero",
    "PrimeFactorOscillations.nicolasTiltedIntegral_two_sided_power_excursions_of_zero",
    "PrimeFactorOscillations.publicZeroDependentIntegralExcursions",
    "PrimeFactorOscillations.publicFalseRHWeightedIntegralExcursions",
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
    if cache.get("analytic_environment") != report.get("analytic_environment"):
        raise ValueError("owned cache environment differs from the successful build report")
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
        analytic = verify_environment()
        current_environment = analytic.snapshot(ROOT / ".lake/build/lib/lean", lean)
        require_report_environment(report, current_environment)
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
            "analytic_environment": current_environment,
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
