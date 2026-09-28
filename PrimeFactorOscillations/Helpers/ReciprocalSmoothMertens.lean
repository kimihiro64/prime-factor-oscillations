import PrimeFactorOscillations.Helpers.GenericOddMertens
import PrimeFactorOscillations.Helpers.ReciprocalSmoothOdds
import PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Group.InverseSquare

/-! # Uniform actual-law Mertens comparison on the exact prime prefix -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.ReciprocalSmoothLaw

/-- The summed error is bounded independently of the prime cutoff, with every
finite exceptional prime retained in the field-valued odds sum. -/
theorem odds_sum_reciprocal_comparison (law : ReciprocalSmoothLaw) :
    exists C : Real, 0 < C /\ forall x : Nat,
      abs ((Nat.primesBelow x).sum (fun p => law.eta p / (1 - law.eta p)) -
        law.nu * PrimeFactorUnimodality.reciprocalPrimeSumBelow x) <= C := by
  choose D hD hpoint using law.odds_global_error
  refine Exists.intro (2 * D) (And.intro (by linarith only [hD]) ?_)
  intro x
  have hsubset : forall p, Membership.mem (Nat.primesBelow x) p ->
      Membership.mem (Finset.range x) p := by
    intro p hp
    change Membership.mem ((Finset.range x).filter Nat.Prime) p at hp
    exact (Finset.mem_filter.mp hp).1
  have herr : forall p, Membership.mem (Nat.primesBelow x) p ->
      abs (law.eta p / (1 - law.eta p) - law.nu / p) <= D / (p : Real) ^ 2 := by
    intro p hp
    change Membership.mem ((Finset.range x).filter Nat.Prime) p at hp
    exact hpoint p (Finset.mem_filter.mp hp).2
  have h := Finset.abs_sum_le_inverse_square_budget (Nat.primesBelow x) x hsubset
    (fun p => law.eta p / (1 - law.eta p) - law.nu / p) D hD.le herr
  have heq : (Nat.primesBelow x).sum
      (fun p => law.eta p / (1 - law.eta p) - law.nu / p) =
      (Nat.primesBelow x).sum (fun p => law.eta p / (1 - law.eta p)) -
        law.nu * PrimeFactorUnimodality.reciprocalPrimeSumBelow x := by
    rw [Finset.sum_sub_distrib]
    unfold PrimeFactorUnimodality.reciprocalPrimeSumBelow
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    ring
  rwa [heq] at h

/-- For each fixed reciprocal-smooth law, the summed odds equal nu log log n
up to one constant, uniformly for all n>=2. This is an actual theorem from the
local-law hypothesis and the proved Mertens input, not a ratio assumption. -/
theorem odds_sum_mertens_bound (law : ReciprocalSmoothLaw) :
    exists C : Real, 0 < C /\ forall n : Nat, 2 <= n ->
      abs ((Nat.primesBelow (n + 1)).sum (fun p => law.eta p / (1 - law.eta p)) -
        law.nu * Real.log (Real.log n)) <= C := by
  choose A hA hcompare using law.odds_sum_reciprocal_comparison
  let B := abs Mertens.M + PrimeFactorUnimodality.mertensErrorConstant / Real.log 2
  have hlog2 : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 <= B := add_nonneg (abs_nonneg _)
    (div_nonneg PrimeFactorUnimodality.mertensErrorConstant_nonneg hlog2.le)
  refine Exists.intro (A + law.nu * B) (And.intro
    (add_pos_of_pos_of_nonneg hA (mul_nonneg law.nu_pos.le hB)) ?_)
  intro n hn
  have hlo := PrimeFactorUnimodality.reciprocalPrimeSumBelow_lower_of_estimate
    PrimeFactorUnimodality.hasMertensReciprocalPrimeEstimate hn
  have hhi := PrimeFactorUnimodality.reciprocalPrimeSumBelow_upper_of_estimate
    PrimeFactorUnimodality.hasMertensReciprocalPrimeEstimate hn
  have hlog : Real.log 2 <= Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have he := div_le_div_of_nonneg_left
    PrimeFactorUnimodality.mertensErrorConstant_nonneg hlog2 hlog
  have hrec : abs (PrimeFactorUnimodality.reciprocalPrimeSumBelow (n + 1) -
      Real.log (Real.log n)) <= B := by
    have hmlo := neg_abs_le Mertens.M
    have hmhi := le_abs_self Mertens.M
    dsimp [B]
    apply abs_le.mpr
    constructor <;> linarith only [hlo, hhi, he, hmlo, hmhi]
  have ha := hcompare (n + 1)
  have hmul := mul_le_mul_of_nonneg_left hrec law.nu_pos.le
  calc
    abs ((Nat.primesBelow (n + 1)).sum (fun p => law.eta p / (1 - law.eta p)) -
        law.nu * Real.log (Real.log n)) =
      abs (((Nat.primesBelow (n + 1)).sum (fun p => law.eta p / (1 - law.eta p)) -
        law.nu * PrimeFactorUnimodality.reciprocalPrimeSumBelow (n + 1)) +
        law.nu * (PrimeFactorUnimodality.reciprocalPrimeSumBelow (n + 1) -
        Real.log (Real.log n))) := by congr 1; ring
    _ <= abs ((Nat.primesBelow (n + 1)).sum (fun p => law.eta p / (1 - law.eta p)) -
        law.nu * PrimeFactorUnimodality.reciprocalPrimeSumBelow (n + 1)) +
        abs (law.nu * (PrimeFactorUnimodality.reciprocalPrimeSumBelow (n + 1) -
        Real.log (Real.log n))) := abs_add_le _ _
    _ <= A + law.nu * B := by
      rw [abs_mul, abs_of_pos law.nu_pos]
      exact add_le_add ha hmul

end PrimeFactorOscillations.ReciprocalSmoothLaw
