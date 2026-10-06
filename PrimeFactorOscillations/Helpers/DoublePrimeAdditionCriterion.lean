/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.DoublePrimeAdditionProbability
import PrimeFactorOscillations.Helpers.QuadraticPrimeCriterion

/-!
# Sharp full-profile comparison after two independent prime additions

Every finite base family lies between the attained profiles for p+q+1 and
p+q, at every nonnegative tilt and admissible cutoff. Both convergent
normalizations and all prefix factors are retained. The bound is uniform
over the base family, so changing its complexity cannot improve the lower
endpoint. This theorem proves no independent RH or prime-gap supply.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations

namespace QuadraticPrimeLaw

theorem logError_le_of_weight_tail (lo hi : QuadraticPrimeLaw)
    (N : Nat) (z : Real) (hz : 0 <= z)
    (hTheta : 1 < Chebyshev.theta (N : Real))
    (hNu : lo.nu = hi.nu)
    (hWeight : forall p : Nat.Primes, N < (p : Nat) -> lo.weight p <= hi.weight p) :
    lo.logError N z <= hi.logError N z := by
  classical
  have hRest (law : QuadraticPrimeLaw) :
      law.logProfile z - (primeProfilePrefixSet N).sum (law.logFactor z) =
        tsum (fun p : {p : Nat.Primes // N < (p : Nat)} => law.logFactor z p.val) := by
    have hSum := @Summable.sum_add_tsum_subtype_compl Real Nat.Primes
      _ _ _ _ _ (law.logFactor z) (law.summable_logFactor z hz)
      (primeProfilePrefixSet N)
    have hPredicate :
        (fun p : Nat.Primes => Not (Membership.mem (primeProfilePrefixSet N) p)) =
        (fun p : Nat.Primes => N < (p : Nat)) := by
      funext p
      apply propext
      exact (not_congr (mem_primeProfilePrefixSet p N)).trans not_le
    rw [hPredicate] at hSum
    dsimp only [logProfile]
    linarith only [hSum]
  rw [lo.logError_eq_signal_add_tail N z hTheta,
    hi.logError_eq_signal_add_tail N z hTheta, hRest lo, hRest hi, hNu]
  apply add_le_add le_rfl
  apply Summable.tsum_le_tsum _ ((lo.summable_logFactor z hz).subtype _)
    ((hi.summable_logFactor z hz).subtype _)
  intro p
  unfold logFactor
  rw [hNu]
  apply sub_le_sub_right
  apply Real.log_le_log
  . have hw := mul_nonneg (lo.weight_nonneg p.val) hz
    linarith
  . have hw := mul_le_mul_of_nonneg_right (hWeight p.val p.property) hz
    linarith

end QuadraticPrimeLaw

namespace FinitePrimeResidueFamily

theorem twoPrimeProbability_lt_one (F : FinitePrimeResidueFamily)
    (p : Nat.Primes) (hp : 2 < (p : Nat)) : F.twoPrimeProbability p < 1 := by
  have hr := F.zeroProbability_bounds p
  have hpR : (2 : Real) < (p : Nat) := by exact_mod_cast hp
  have hden : 0 < (((p : Nat) : Real) - 1) ^ 2 := sq_pos_of_pos (by linarith)
  rw [F.twoPrimeProbability_formula]
  apply (div_lt_one hden).mpr
  nlinarith

theorem twoPrimeProbability_bracket (F : FinitePrimeResidueFamily) (p : Nat.Primes) :
    (constantPrimeResidueFamily 1).twoPrimeProbability p <= F.twoPrimeProbability p /\
    F.twoPrimeProbability p <= (constantPrimeResidueFamily 0).twoPrimeProbability p := by
  have hr := F.zeroProbability_bounds p
  rw [F.twoPrimeProbability_formula,
    (constantPrimeResidueFamily 0).twoPrimeProbability_formula,
    (constantPrimeResidueFamily 1).twoPrimeProbability_formula,
    constantPrimeResidueFamily_zeroProbability_one,
    constantPrimeResidueFamily_zeroProbability_zero]
  constructor <;> apply div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

theorem twoPrimeLaw_weight_bracket (F : FinitePrimeResidueFamily)
    (p : Nat.Primes) (hp : 2 < (p : Nat)) :
    (constantPrimeResidueFamily 1).twoPrimeLaw.weight p <= F.twoPrimeLaw.weight p /\
    F.twoPrimeLaw.weight p <= (constantPrimeResidueFamily 0).twoPrimeLaw.weight p := by
  have hProb := F.twoPrimeProbability_bracket p
  have hF := F.twoPrimeProbability_lt_one p hp
  have hLo := (constantPrimeResidueFamily 1).twoPrimeProbability_lt_one p hp
  have hHi := (constantPrimeResidueFamily 0).twoPrimeProbability_lt_one p hp
  rw [F.twoPrimeLaw_weight, (constantPrimeResidueFamily 0).twoPrimeLaw_weight,
    (constantPrimeResidueFamily 1).twoPrimeLaw_weight]
  have hOdds (x : Real) (hx : x < 1) : x / (1 - x) = 1 / (1 - x) - 1 := by
    field_simp [(sub_pos.mpr hx).ne']
    <;> ring
  rw [hOdds _ hLo, hOdds _ hF, hOdds _ hHi]
  constructor
  . apply sub_le_sub_right
    exact one_div_le_one_div_of_le (sub_pos.mpr hF) (by linarith only [hProb.1])
  . apply sub_le_sub_right
    exact one_div_le_one_div_of_le (sub_pos.mpr hHi) (by linarith only [hProb.2])

theorem doublePrimeAddition_logError_bracket (F : FinitePrimeResidueFamily)
    (N : Nat) (hN : 2 <= N) (z : Real) (hz : 0 <= z)
    (hTheta : 1 < Chebyshev.theta (N : Real)) :
    (constantPrimeResidueFamily 1).twoPrimeLaw.logError N z <= F.twoPrimeLaw.logError N z /\
      F.twoPrimeLaw.logError N z <= (constantPrimeResidueFamily 0).twoPrimeLaw.logError N z := by
  constructor
  . apply QuadraticPrimeLaw.logError_le_of_weight_tail _ _ N z hz hTheta (by rfl)
    intro p hp
    exact (F.twoPrimeLaw_weight_bracket p (lt_of_le_of_lt hN hp)).1
  . apply QuadraticPrimeLaw.logError_le_of_weight_tail _ _ N z hz hTheta (by rfl)
    intro p hp
    exact (F.twoPrimeLaw_weight_bracket p (lt_of_le_of_lt hN hp)).2

end FinitePrimeResidueFamily

end PrimeFactorOscillations
