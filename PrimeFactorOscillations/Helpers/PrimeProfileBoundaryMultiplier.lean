/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Definitions.PrimeProfile

/-!
# Boundary multipliers for ordered prime cycles

A completed cycle preserves its finite generating product. An incomplete
increasing cycle leaves only its first and next prime factors. When the
cutoff is at most twice the first prime, this multiplier is uniformly close
to one, independently of the number of primes and their spacing.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

/-- Analytic multiplier left by the incomplete prefix of an increasing cycle. -/
noncomputable def primeProfileBoundaryMultiplier (p q : Nat) (z : Complex) : Complex :=
  (1 + (primeProfileWeight q : Complex) * z) /
    (1 + (primeProfileWeight p : Complex) * z)

/-- A multiplicative diameter bound controls the first prime weight. -/
theorem primeProfileWeight_le_four_div_cutoff (p N : Nat) (hp : Nat.Prime p)
    (hN : 0 < N) (hNp : N <= 2 * p) :
    primeProfileWeight p <= 4 / (N : Real) := by
  have hp1 : 1 <= p := le_trans (by decide) hp.two_le
  have hp2 : (2 : Real) <= (p : Real) := by exact_mod_cast hp.two_le
  have hden : (p : Real) = ((p - 1 : Nat) : Real) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hp1).symm
  have hNpR : (N : Real) <= 2 * (p : Real) := by exact_mod_cast hNp
  have hscale : (N : Real) / 4 <= ((p - 1 : Nat) : Real) := by linarith
  change 1 / ((p - 1 : Nat) : Real) <= 4 / (N : Real)
  calc
    _ <= 1 / ((N : Real) / 4) :=
      one_div_le_one_div_of_le (by positivity) hscale
    _ = 4 / (N : Real) := by ring

/-- Prime predecessor weights are nonnegative and decrease along increasing primes. -/
theorem primeProfileWeight_ordered (p q : Nat) (hp : Nat.Prime p)
    (hpq : p <= q) :
    0 <= primeProfileWeight q /\ primeProfileWeight q <= primeProfileWeight p := by
  have hden : (0 : Real) < ((p - 1 : Nat) : Real) := by
    exact_mod_cast (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide) hp.two_le))
  have hle : ((p - 1 : Nat) : Real) <= ((q - 1 : Nat) : Real) := by
    exact_mod_cast (Nat.sub_le_sub_right hpq 1)
  refine And.intro ?_ ?_
  { unfold primeProfileWeight
    positivity }
  { exact one_div_le_one_div_of_le hden hle }

/-- The boundary denominator stays away from zero, and the multiplier error is
at most `8 * R / N` on a fixed disc. No division by the full prime product occurs. -/
theorem primeProfileBoundaryMultiplier_error (p q N : Nat) (hp : Nat.Prime p)
    (hpq : p <= q) (hN : 0 < N) (hNp : N <= 2 * p)
    (R : Real) (hR : 0 <= R) (hNR : 8 * R <= (N : Real))
    (z : Complex) (hz : norm z <= R) :
    (1 / 2 : Real) <= norm (1 + (primeProfileWeight p : Complex) * z) /\
      norm (primeProfileBoundaryMultiplier p q z - 1) <= 8 * R / (N : Real) := by
  have hNpos : (0 : Real) < (N : Real) := by exact_mod_cast hN
  have hNne : Not ((N : Real) = 0) := ne_of_gt hNpos
  have hwp : 0 <= primeProfileWeight p := by unfold primeProfileWeight; positivity
  have hwq := primeProfileWeight_ordered p q hp hpq
  have hweight := primeProfileWeight_le_four_div_cutoff p N hp hN hNp
  have hsmall : (4 / (N : Real)) * R <= 1 / 2 := by
    apply le_of_mul_le_mul_right (a := (N : Real)) ?_ hNpos
    calc
      (4 / (N : Real) * R) * (N : Real) = 4 * R := by field_simp
      _ <= (1 / 2 : Real) * (N : Real) := by linarith
  have hwpR : primeProfileWeight p * R <= (4 / (N : Real)) * R :=
    mul_le_mul_of_nonneg_right hweight hR
  have hnormwp : norm (primeProfileWeight p : Complex) = primeProfileWeight p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwp]
  have hnorm : norm ((primeProfileWeight p : Complex) * z) <=
      primeProfileWeight p * R := by
    rw [norm_mul, hnormwp]
    exact mul_le_mul_of_nonneg_left hz hwp
  have htri := norm_add_le (1 + (primeProfileWeight p : Complex) * z)
    (-((primeProfileWeight p : Complex) * z))
  have hcancel : (1 + (primeProfileWeight p : Complex) * z) +
      (-((primeProfileWeight p : Complex) * z)) = 1 := by ring
  rw [hcancel, norm_one, norm_neg] at htri
  have hlower : (1 / 2 : Real) <= norm (1 + (primeProfileWeight p : Complex) * z) := by
    linarith
  have hden : Not (1 + (primeProfileWeight p : Complex) * z = 0) :=
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hlower)
  have hdiff : norm ((primeProfileWeight q : Complex) - (primeProfileWeight p : Complex))
      <= primeProfileWeight p := by
    rw [<- Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hwq.2)]
    linarith [hwq.1]
  have hnum : norm (((primeProfileWeight q : Complex) - (primeProfileWeight p : Complex)) * z)
      <= primeProfileWeight p * R := by
    rw [norm_mul]
    exact mul_le_mul hdiff hz (norm_nonneg _) hwp
  have hid : primeProfileBoundaryMultiplier p q z - 1 =
      (((primeProfileWeight q : Complex) - (primeProfileWeight p : Complex)) * z) /
        (1 + (primeProfileWeight p : Complex) * z) := by
    unfold primeProfileBoundaryMultiplier
    calc
      _ = (1 + (primeProfileWeight q : Complex) * z) /
          (1 + (primeProfileWeight p : Complex) * z) -
          (1 + (primeProfileWeight p : Complex) * z) /
            (1 + (primeProfileWeight p : Complex) * z) := by rw [div_self hden]
      _ = ((1 + (primeProfileWeight q : Complex) * z) -
          (1 + (primeProfileWeight p : Complex) * z)) /
            (1 + (primeProfileWeight p : Complex) * z) := (sub_div _ _ _).symm
      _ = _ := by congr 1; ring
  have hinv : 1 / norm (1 + (primeProfileWeight p : Complex) * z) <= 2 := by
    calc
      _ <= 1 / (1 / 2 : Real) := one_div_le_one_div_of_le (by norm_num) hlower
      _ = 2 := by norm_num
  refine And.intro hlower ?_
  rw [hid, norm_div]
  calc
    _ = norm (((primeProfileWeight q : Complex) - (primeProfileWeight p : Complex)) * z) *
        (1 / norm (1 + (primeProfileWeight p : Complex) * z)) := by ring
    _ <= (primeProfileWeight p * R) * 2 :=
      mul_le_mul hnum hinv (by positivity) (mul_nonneg hwp hR)
    _ <= ((4 / (N : Real)) * R) * 2 :=
      mul_le_mul_of_nonneg_right hwpR (by norm_num)
    _ = 8 * R / (N : Real) := by ring

/-- Exact cancellation for an incomplete increasing cycle. This identity also
holds at every zero of either finite product. -/
theorem primeProfile_cycle_prefix_cross (p : Nat -> Nat) (m : Nat) (z : Complex) :
    (Finset.range m).prod (fun j => 1 + (primeProfileWeight (p (j + 1)) : Complex) * z) *
        (1 + (primeProfileWeight (p 0) : Complex) * z) =
      (Finset.range m).prod (fun j => 1 + (primeProfileWeight (p j) : Complex) * z) *
        (1 + (primeProfileWeight (p m) : Complex) * z) := by
  calc
    _ = (Finset.range (m + 1)).prod
        (fun j => 1 + (primeProfileWeight (p j) : Complex) * z) :=
      (Finset.prod_range_succ' _ m).symm
    _ = _ := Finset.prod_range_succ _ m

/-- Once the boundary denominator is nonzero, the shifted finite product is
the canonical finite product times the explicitly defined boundary multiplier. -/
theorem primeProfile_cycle_prefix_multiplier (p : Nat -> Nat) (m : Nat) (z : Complex)
    (hden : Not (1 + (primeProfileWeight (p 0) : Complex) * z = 0)) :
    (Finset.range m).prod (fun j => 1 + (primeProfileWeight (p (j + 1)) : Complex) * z) =
      (Finset.range m).prod (fun j => 1 + (primeProfileWeight (p j) : Complex) * z) *
        primeProfileBoundaryMultiplier (p 0) (p m) z := by
  have h := congrArg (fun t : Complex =>
    t / (1 + (primeProfileWeight (p 0) : Complex) * z))
    (primeProfile_cycle_prefix_cross p m z)
  rw [mul_div_assoc, div_self hden, mul_one] at h
  simpa only [primeProfileBoundaryMultiplier, mul_div_assoc] using h

/-- The exact multiplier transports the canonical normalized prefix estimate
without dividing by a product that can vanish. -/
theorem primeProfileBoundaryMultiplier_prefix_error
    (p q N : Nat) (hp : Nat.Prime p) (hpq : p <= q)
    (hN : 0 < N) (hNp : N <= 2 * p)
    (R : Real) (hR : 0 <= R) (hNR : 8 * R <= (N : Real))
    (B C : Real) (hB : 0 <= B) (z : Complex) (hz : norm z <= R)
    (hprefix : norm (primePrefixProfile N z) <= B)
    (herror : norm (primePrefixProfile N z - primeProfile z) <= C / (N : Real)) :
    norm (primePrefixProfile N z * primeProfileBoundaryMultiplier p q z - primeProfile z)
      <= (C + 8 * R * B) / (N : Real) := by
  have hmult := (primeProfileBoundaryMultiplier_error p q N hp hpq hN hNp R hR hNR z hz).2
  have hid : primePrefixProfile N z * primeProfileBoundaryMultiplier p q z - primeProfile z =
      primePrefixProfile N z * (primeProfileBoundaryMultiplier p q z - 1) +
        (primePrefixProfile N z - primeProfile z) := by ring
  rw [hid]
  calc
    _ <= norm (primePrefixProfile N z * (primeProfileBoundaryMultiplier p q z - 1)) +
        norm (primePrefixProfile N z - primeProfile z) := norm_add_le _ _
    _ = norm (primePrefixProfile N z) * norm (primeProfileBoundaryMultiplier p q z - 1) +
        norm (primePrefixProfile N z - primeProfile z) := by rw [norm_mul]
    _ <= B * (8 * R / (N : Real)) + C / (N : Real) :=
      add_le_add (mul_le_mul hprefix hmult (norm_nonneg _) hB) herror
    _ = (C + 8 * R * B) / (N : Real) := by ring

end PrimeFactorOscillations
