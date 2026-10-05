/-
Copyright (c) 2026 Matteo Cipollina and Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasXiLogGrowth
/-!
# Logarithmic counting of canonical xi zeros

The fixed logarithmic growth estimate and Jensen's formula bound the number
of zero indices in a ball by C R log(R+2), for every R >= 1. The index
retains analytic multiplicity. Finiteness is exposed separately so that
the natural cardinal is an actual finite count.

The cached counting and Jensen declarations come from the Apache-2.0 PNT
sources HadamardFactorization/Summability.lean, DivisorConvergence.lean,
and ValueDistribution/LogCounting/Growth.lean at
f6147e7572ab3abe5428101bc0b13627bcb005df. The local ASCII syntax expands
to those exact declarations, including their subscript-zero names; it
introduces no definitions, hypotheses, or axioms. This is a classical
counting bound used by the sharper degree-localization argument.
-/

set_option autoImplicit false
set_option Elab.async false

-- ASCII spellings expand to the exact cached declarations, without a new axiom.
local macro "xiCardMassBound" : term => do
  return Lean.mkIdent (("Complex.Hadamard.card_ball_le_divisorMassClosedBall" ++
    String.singleton (Char.ofNat 8320)).toName)

local macro "xiLogMassBound" : term => do
  return Lean.mkIdent (("Complex.Hadamard.log_two_mul_divisorMassClosedBall" ++
    String.singleton (Char.ofNat 8320) ++ "_le_logCounting_two_mul").toName)

local macro "xiFiniteBall" : term => do
  return Lean.mkIdent (("Complex.Hadamard.finite_divisorZeroIndex" ++
    String.singleton (Char.ofNat 8320) ++ "_subtype_norm_le").toName)


noncomputable section

namespace PrimeFactorOscillations

/-- Every bounded ball contains finitely many canonical zero indices. -/
theorem nicolasXi_finite_zero_ball (R : Real) :
    Finite {p : RiemannXiDivisorZeroIndex //
      norm (riemannXiDivisorZeroValue p) <= R} := by
  exact xiFiniteBall R (Set.subset_univ _)

/-- Jensen counts the canonical zero indices, hence retains multiplicity. -/
theorem nicolasXi_zero_count_logarithmic :
    Exists fun C : Real => And (0 < C) (forall R : Real, 1 <= R ->
      (Nat.card {p : RiemannXiDivisorZeroIndex //
        norm (riemannXiDivisorZeroValue p) <= R} : Real) <=
          C * R * Real.log (R + 2)) := by
  choose G hG hGrowth using nicolasXi_log_growth
  let K : Real := abs (Real.log (norm
    (meromorphicTrailingCoeffAt Complex.riemannXi 0)))
  let C : Real := (6 * G + K / Real.log 2 + 1) / Real.log 2
  have hLog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 <= K := abs_nonneg _
  have hKG : 0 <= K / Real.log 2 := div_nonneg hK hLog2.le
  have hC : 0 < C := by dsimp [C]; positivity
  refine Exists.intro C (And.intro hC ?_)
  intro R hR
  have hRpos : 0 < R := by linarith
  have h2R : 0 < 2 * R := by positivity
  have hCard := xiCardMassBound Complex.differentiable_riemannXi hRpos
  have hMass := xiLogMassBound Complex.differentiable_riemannXi hR
  have hJensen :=
    Complex.Hadamard.jensen_formula_logCounting_eq_circleAverage_sub_log_trailingCoeff
      Complex.differentiable_riemannXi h2R.ne'
  have hMeromorphic : MeromorphicOn Complex.riemannXi
      (Metric.sphere (0 : Complex) (abs (2 * R))) := by
    intro z hz
    exact (Complex.differentiable_riemannXi.analyticAt z).meromorphicAt
  have hIntegral := MeromorphicOn.circleIntegrable_log_norm hMeromorphic
  have hCircle : Real.circleAverage (fun z : Complex =>
      Real.log (norm (Complex.riemannXi z))) 0 (2 * R) <=
        G * (1 + 2 * R) * Real.log (2 + 2 * R) := by
    apply Real.circleAverage_mono_on_of_le_circle hIntegral
    intro z hz
    have hzNorm : norm z = 2 * R := by
      simpa only [Metric.mem_sphere, dist_zero_right, abs_of_pos h2R] using hz
    by_cases hZero : Complex.riemannXi z = 0
    . simp only [hZero, norm_zero, Real.log_zero]
      exact mul_nonneg (by positivity)
        (Real.log_nonneg (by linarith))
    . have hLog := Real.log_le_log (norm_pos_iff.mpr hZero)
        (show norm (Complex.riemannXi z) <= 1 + norm (Complex.riemannXi z) by linarith)
      have hGrow := hGrowth z
      rw [hzNorm] at hGrow
      exact hLog.trans hGrow
  have hCardLog := mul_le_mul_of_nonneg_left hCard hLog2.le
  have hRaw : Real.log 2 *
      (Nat.card {p : RiemannXiDivisorZeroIndex //
        norm (riemannXiDivisorZeroValue p) <= R} : Real) <=
      G * (1 + 2 * R) * Real.log (2 + 2 * R) + K := by
    rw [hJensen] at hMass
    change Real.log 2 *
      (Nat.card {p : RiemannXiDivisorZeroIndex //
        norm (riemannXiDivisorZeroValue p) <= R} : Real) <= _ at hCardLog
    have hNeg := neg_le_abs (Real.log (norm
      (meromorphicTrailingCoeffAt Complex.riemannXi 0)))
    change -Real.log (norm (meromorphicTrailingCoeffAt Complex.riemannXi 0)) <= K at hNeg
    linarith
  have hL : 0 <= Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hL2 : Real.log 2 <= Real.log (R + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hLogDouble : Real.log (2 + 2 * R) <= 2 * Real.log (R + 2) := by
    have hBetter := Real.log_le_log (show 0 < 2 + 2 * R by positivity)
      (show 2 + 2 * R <= (R + 2) ^ (2 : Nat) by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hBetter
  have hGrowthBound : G * (1 + 2 * R) * Real.log (2 + 2 * R) <=
      6 * G * R * Real.log (R + 2) := by
    have h := mul_le_mul
      (mul_le_mul_of_nonneg_left (show 1 + 2 * R <= 3 * R by linarith) hG.le)
      hLogDouble (Real.log_nonneg (by linarith)) (by positivity)
    nlinarith [h]
  have hWeight : Real.log 2 <= R * Real.log (R + 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) hL]
  have hPayment := mul_le_mul_of_nonneg_left hWeight hKG
  have hPaid : K / Real.log 2 * Real.log 2 = K := by field_simp [hLog2.ne']
  rw [hPaid] at hPayment
  have hTotal : Real.log 2 *
      (Nat.card {p : RiemannXiDivisorZeroIndex //
        norm (riemannXiDivisorZeroValue p) <= R} : Real) <=
      (6 * G + K / Real.log 2 + 1) * (R * Real.log (R + 2)) := by
    nlinarith [hRaw, hGrowthBound, hPayment, mul_nonneg hRpos.le hL]
  have hCeq : Real.log 2 * C = 6 * G + K / Real.log 2 + 1 := by
    dsimp [C]
    field_simp [hLog2.ne']
  rw [<- hCeq, mul_assoc] at hTotal
  have h := le_of_mul_le_mul_left hTotal hLog2
  nlinarith only [h]

end PrimeFactorOscillations
