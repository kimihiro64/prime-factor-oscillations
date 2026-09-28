import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

set_option autoImplicit false

/-! # Placement and size of the double-exponential index cutoff -/

namespace PrimeFactorOscillations

/-- Leave half of epsilon available to absorb the natural ceiling. -/
noncomputable def upperCutoffValue (epsilon : Real) (k : Nat) : Real :=
  Real.exp (Real.exp (((1 : Real) / 3 + epsilon / 2) * k))

/-- An inclusive tail index whose preceding-prime cutoff lies above the scale. -/
noncomputable def upperCutoffIndex (epsilon : Real) (k : Nat) : Nat :=
  Nat.ceil (upperCutoffValue epsilon k) + 1

/-- A simple linear lower bound suffices for all fixed finite corrections. -/
theorem upperCutoffValue_ge_linear (epsilon : Real) (he : 0 <= epsilon) (k : Nat) :
    (k : Real) / 3 + 2 <= upperCutoffValue epsilon k := by
  have hinner := Real.add_one_le_exp (((1 : Real) / 3 + epsilon / 2) * k)
  have houter := Real.add_one_le_exp (Real.exp (((1 : Real) / 3 + epsilon / 2) * k))
  have hnonneg := mul_nonneg he (Nat.cast_nonneg k : (0 : Real) <= k)
  unfold upperCutoffValue
  nlinarith

/-- Exact ceiling cost in the natural index. -/
theorem upperCutoffIndex_cast_lt (epsilon : Real) (k : Nat) :
    (upperCutoffIndex epsilon k : Real) < upperCutoffValue epsilon k + 2 := by
  have hceil := Nat.ceil_lt_add_one
    (le_of_lt (Real.exp_pos (Real.exp (((1 : Real) / 3 + epsilon / 2) * k))))
  change ((Nat.ceil (upperCutoffValue epsilon k) + 1 : Nat) : Real) <
    upperCutoffValue epsilon k + 2
  rw [Nat.cast_add, Nat.cast_one]
  change ((Nat.ceil (upperCutoffValue epsilon k)) : Real) <
    upperCutoffValue epsilon k + 1 at hceil
  linarith

/-- The epsilon margin absorbs both the ceiling and its added unit. -/
theorem upperCutoffIndex_le_doubleExp (epsilon : Real) (k : Nat)
    (he : 0 <= epsilon) (hscale : (2 : Real) <= epsilon * k) :
    (upperCutoffIndex epsilon k : Real) <=
      Real.exp (Real.exp (((1 : Real) / 3 + epsilon) * k)) := by
  let A := upperCutoffValue epsilon k
  have hA : (2 : Real) <= A := by
    have h := upperCutoffValue_ge_linear epsilon he k
    have hk : (0 : Real) <= (k : Real) := Nat.cast_nonneg k
    change (k : Real) / 3 + 2 <= A at h
    linarith
  have hpoly := mul_nonneg (sub_nonneg.mpr hA) (show (0 : Real) <= A + 1 by linarith)
  have hceil : (upperCutoffIndex epsilon k : Real) <= A ^ 2 := by
    have h := (upperCutoffIndex_cast_lt epsilon k).le
    change (upperCutoffIndex epsilon k : Real) <= A + 2 at h
    nlinarith
  have hdelta : (2 : Real) <= Real.exp (epsilon * k / 2) := by
    have h := Real.add_one_le_exp (epsilon * k / 2)
    linarith
  have hfactor : Real.exp (((1 : Real) / 3 + epsilon) * k) =
      Real.exp (((1 : Real) / 3 + epsilon / 2) * k) * Real.exp (epsilon * k / 2) := by
    rw [show ((1 : Real) / 3 + epsilon) * k =
      ((1 : Real) / 3 + epsilon / 2) * k + epsilon * k / 2 by ring, Real.exp_add]
  have hinner :
      Real.exp (((1 : Real) / 3 + epsilon / 2) * k) +
        Real.exp (((1 : Real) / 3 + epsilon / 2) * k) <=
      Real.exp (((1 : Real) / 3 + epsilon) * k) := by
    rw [hfactor]
    have h := mul_le_mul_of_nonneg_left hdelta
      (le_of_lt (Real.exp_pos (((1 : Real) / 3 + epsilon / 2) * k)))
    linarith
  have hsq : A ^ 2 <= Real.exp (Real.exp (((1 : Real) / 3 + epsilon) * k)) := by
    simpa only [A, upperCutoffValue, Real.exp_add, pow_two] using Real.exp_le_exp.mpr hinner
  exact hceil.trans hsq

/-- Every prime at or beyond the chosen inclusive index is above two. -/
theorem upperCutoff_prime_gt_two (epsilon : Real) (k i : Nat)
    (hi : upperCutoffIndex epsilon k <= i) : 2 < PrimeFactorUnimodality.primeAt i := by
  have hbase : i + 2 <= PrimeFactorUnimodality.primeAt i := Nat.add_two_le_nth_prime i
  unfold upperCutoffIndex at hi
  omega

/-- The preceding natural cutoff has precisely the logarithmic scale required
by the Mertens ratio theorem. -/
theorem upperCutoff_loglog (epsilon : Real) (k i : Nat)
    (hi : upperCutoffIndex epsilon k <= i) :
    ((1 : Real) / 3 + epsilon / 2) * k <=
      Real.log (Real.log ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real)) := by
  have hbase : i + 2 <= PrimeFactorUnimodality.primeAt i := Nat.add_two_le_nth_prime i
  have hnat : Nat.ceil (upperCutoffValue epsilon k) <=
      PrimeFactorUnimodality.primeAt i - 1 := by
    unfold upperCutoffIndex at hi
    omega
  have hge : upperCutoffValue epsilon k <=
      ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnat)
  have hlog := Real.log_le_log (Real.exp_pos _) hge
  rw [Real.log_exp] at hlog
  have h := Real.log_le_log (Real.exp_pos _) hlog
  simpa only [Real.log_exp] using h

/-- The generic reciprocal correction is smaller than an arbitrary fixed
positive margin once the rank obeys its explicit linear condition. -/
theorem upperCutoff_reciprocal_lt (epsilon delta : Real) (k i : Nat)
    (he : 0 <= epsilon) (hd : 0 < delta) (hdk : (3 : Real) <= delta * k)
    (hi : upperCutoffIndex epsilon k <= i) :
    1 / ((PrimeFactorUnimodality.primeAt i : Real) - 2) < delta := by
  have hp := upperCutoff_prime_gt_two epsilon k i hi
  have hbase : i + 2 <= PrimeFactorUnimodality.primeAt i := Nat.add_two_le_nth_prime i
  have hnat : Nat.ceil (upperCutoffValue epsilon k) + 1 <=
      PrimeFactorUnimodality.primeAt i - 2 := by
    unfold upperCutoffIndex at hi
    omega
  have hreal : (Nat.ceil (upperCutoffValue epsilon k) : Real) + 1 <=
      (PrimeFactorUnimodality.primeAt i : Real) - 2 := by
    have h : ((Nat.ceil (upperCutoffValue epsilon k) + 1 : Nat) : Real) <=
        ((PrimeFactorUnimodality.primeAt i - 2 : Nat) : Real) := by exact_mod_cast hnat
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub (show 2 <=
      PrimeFactorUnimodality.primeAt i by omega), Nat.cast_ofNat] using h
  have hlinear : (k : Real) / 3 < (PrimeFactorUnimodality.primeAt i : Real) - 2 := by
    have hceil := Nat.le_ceil (upperCutoffValue epsilon k)
    have hvalue := upperCutoffValue_ge_linear epsilon he k
    linarith
  have hscaled := div_le_div_of_nonneg_right hdk
    (le_of_lt (mul_pos hd (by norm_num : (0 : Real) < 3)))
  have hcancel : (3 : Real) / (delta * 3) = 1 / delta := by
    simpa only [one_mul] using mul_div_mul_right (1 : Real) delta (by norm_num : Not ((3 : Real) = 0))
  rw [hcancel, mul_div_mul_left _ _ (ne_of_gt hd)] at hscaled
  have h := one_div_lt_one_div_of_lt (div_pos (by norm_num) hd) (hscaled.trans_lt hlinear)
  simpa only [one_div, inv_inv] using h

end PrimeFactorOscillations
