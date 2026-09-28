import PrimeFactorOscillations.Helpers.LocalFirstDifference

set_option autoImplicit false

/-!
# Comparing generic odd and ordinary weights

The exact reciprocal correction makes the two weight sums differ by a
convergent positive series. This is the finite algebraic input for transferring
the leading log-log term, not an assumption of the desired asymptotic.
-/

namespace PrimeFactorOscillations

/-- The denominator of the generic odd odds ratio is positive for p > 2. -/
theorem genericOdd_weightDenominator_pos (p : Nat) (hp : 2 < p) :
    0 < (p : Rat) ^ 2 - 3 * (p : Rat) + 3 := by
  have hp3 : (3 : Rat) <= (p : Rat) := by exact_mod_cast hp
  nlinarith [mul_nonneg (show (0 : Rat) <= (p : Rat) by linarith)
    (show (0 : Rat) <= (p : Rat) - 3 by linarith)]

/-- The failure probability is positive, so the local odds are well defined. -/
theorem genericOddEta_lt_one (p : Nat) (hp : 2 < p) : genericOddEta p < 1 := by
  have hpR : (2 : Rat) < (p : Rat) := by exact_mod_cast hp
  have h1 : Not ((p : Rat) - 1 = 0) := by linarith
  have hid : 1 - genericOddEta p =
      ((p : Rat) ^ 2 - 3 * (p : Rat) + 3) / ((p : Rat) - 1) ^ 2 := by
    simp only [genericOddEta, ite_eq_right (ne_of_gt hp)]
    field_simp
    ring
  have hpos : 0 < 1 - genericOddEta p := by
    rw [hid]
    exact div_pos (genericOdd_weightDenominator_pos p hp) (sq_pos_of_ne_zero h1)
  exact sub_pos.mp hpos

/-- Exact difference of the ordinary and generic odd odds weights. -/
theorem ordinary_sub_genericOdd_weight (p : Nat) (hp : 2 < p) :
    1 / ((p : Rat) - 1) - genericOddEta p / (1 - genericOddEta p) =
      1 / (((p : Rat) - 1) * ((p : Rat) ^ 2 - 3 * (p : Rat) + 3)) := by
  have hpR : (2 : Rat) < (p : Rat) := by exact_mod_cast hp
  have h1 : Not ((p : Rat) - 1 = 0) := by linarith
  have hD := ne_of_gt (genericOdd_weightDenominator_pos p hp)
  have hDnf : Not ((3 : Rat) - (p : Rat) * 3 + (p : Rat) ^ 2 = 0) := by
    intro hz
    apply hD
    nlinarith
  have hfail : 1 - genericOddEta p =
      ((p : Rat) ^ 2 - 3 * (p : Rat) + 3) / ((p : Rat) - 1) ^ 2 := by
    simp only [genericOddEta, ite_eq_right (ne_of_gt hp)]
    field_simp
    ring
  rw [hfail]
  simp only [genericOddEta, ite_eq_right (ne_of_gt hp)]
  have hcancel : ((3 : Rat) - (p : Rat) * 3 + (p : Rat) ^ 2) *
      (1 / ((3 : Rat) - (p : Rat) * 3 + (p : Rat) ^ 2)) = 1 := by
    rw [<- mul_div_assoc, mul_one, div_self hDnf]
  field_simp [h1, hD, hDnf]
  ring_nf at hcancel
  ring_nf
  nlinarith only [hcancel]

/-- The correction is positive and bounded by a reciprocal-square correction.
The upper inequality is cross-multiplied; p > 2 guarantees a positive p^2. -/
theorem genericOdd_weight_correction_bound (p : Nat) (hp : 2 < p) :
    0 < 1 / ((p : Rat) - 1) - genericOddEta p / (1 - genericOddEta p) /\
    (p : Rat) ^ 2 *
        (1 / ((p : Rat) - 1) - genericOddEta p / (1 - genericOddEta p)) <= 2 := by
  rw [ordinary_sub_genericOdd_weight p hp]
  have hp3 : (3 : Rat) <= (p : Rat) := by exact_mod_cast hp
  have hp1 : (0 : Rat) < (p : Rat) - 1 := by linarith
  have hD := genericOdd_weightDenominator_pos p hp
  have hden := mul_pos hp1 hD
  have hd : (0 : Rat) <
      1 / (((p : Rat) - 1) * ((p : Rat) ^ 2 - 3 * (p : Rat) + 3)) :=
    div_pos (by norm_num) hden
  refine And.intro hd ?_
  have hDp : (p : Rat) <= (p : Rat) ^ 2 - 3 * (p : Rat) + 3 := by
    nlinarith [mul_nonneg (le_of_lt hp1) (show (0 : Rat) <= (p : Rat) - 3 by linarith)]
  have hb : (p : Rat) ^ 2 <=
      2 * (((p : Rat) - 1) * ((p : Rat) ^ 2 - 3 * (p : Rat) + 3)) := by
    nlinarith [mul_nonneg (le_of_lt hp1) (sub_nonneg.mpr hDp)]
  have hc := mul_le_mul_of_nonneg_right hb (le_of_lt hd)
  have hi : (((p : Rat) - 1) * ((p : Rat) ^ 2 - 3 * (p : Rat) + 3)) *
      (1 / (((p : Rat) - 1) * ((p : Rat) ^ 2 - 3 * (p : Rat) + 3))) = 1 := by
    rw [<- mul_div_assoc, mul_one, div_self (ne_of_gt hden)]
  nlinarith [hc, hi]

/-- Normalized correction bound for summing over a prime prefix. -/
theorem genericOdd_weight_correction_le (p : Nat) (hp : 2 < p) :
    1 / ((p : Rat) - 1) - genericOddEta p / (1 - genericOddEta p) <=
      2 / (p : Rat) ^ 2 := by
  have hpR : (2 : Rat) < (p : Rat) := by exact_mod_cast hp
  have hpp : (0 : Rat) < (p : Rat) ^ 2 :=
    sq_pos_of_ne_zero (by linarith)
  have hcancel : (p : Rat) ^ 2 * (1 / (p : Rat) ^ 2) = 1 := by
    rw [<- mul_div_assoc, mul_one, div_self (ne_of_gt hpp)]
  have hmul := mul_le_mul_of_nonneg_right (genericOdd_weight_correction_bound p hp).2
    (le_of_lt (div_pos (show (0 : Rat) < 1 by norm_num) hpp))
  calc
    1 / ((p : Rat) - 1) - genericOddEta p / (1 - genericOddEta p) =
        ((p : Rat) ^ 2 * (1 / (p : Rat) ^ 2)) *
          (1 / ((p : Rat) - 1) - genericOddEta p / (1 - genericOddEta p)) := by
            rw [hcancel, one_mul]
    _ = ((p : Rat) ^ 2 *
          (1 / ((p : Rat) - 1) - genericOddEta p / (1 - genericOddEta p))) *
        (1 / (p : Rat) ^ 2) := by ring
    _ <= 2 * (1 / (p : Rat) ^ 2) := hmul
    _ = 2 / (p : Rat) ^ 2 := by ring

end PrimeFactorOscillations
