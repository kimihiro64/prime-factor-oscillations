import PrimeFactorOscillations.Helpers.GenericOddWeightSums

set_option autoImplicit false

/-! # Monotonicity of the generic odd law and its odds -/

namespace PrimeFactorOscillations

/-- The local probabilities decrease on the complete integer domain above two. -/
theorem genericOddEta_antitone {p q : Nat} (hp : 2 < p) (hpq : p <= q) :
    genericOddEta q <= genericOddEta p := by
  have hq : 2 < q := hp.trans_le hpq
  have hpR : (3 : Rat) <= (p : Rat) := by exact_mod_cast (show 3 <= p by omega)
  have hpqR : (p : Rat) <= (q : Rat) := by exact_mod_cast hpq
  have hqR : (3 : Rat) <= (q : Rat) := hpR.trans hpqR
  have hpD : (0 : Rat) < ((p : Rat) - 1) ^ 2 := pow_pos (by linarith) 2
  have hqD : (0 : Rat) < ((q : Rat) - 1) ^ 2 := pow_pos (by linarith) 2
  have hproduct : 0 <= ((p : Rat) - 2) * ((q : Rat) - 2) - 1 := by
    have h := mul_nonneg (show (0 : Rat) <= (p : Rat) - 3 by linarith)
      (show (0 : Rat) <= (q : Rat) - 3 by linarith)
    nlinarith
  have hfactor := mul_nonneg (sub_nonneg.mpr hpqR) hproduct
  have hcross : ((q : Rat) - 2) * ((p : Rat) - 1) ^ 2 <=
      ((q : Rat) - 1) ^ 2 * ((p : Rat) - 2) := by nlinarith only [hfactor]
  have hdiv := div_le_div_of_nonneg_right hcross (le_of_lt (mul_pos hqD hpD))
  rw [genericOddEta, genericOddEta, ite_eq_right (ne_of_gt hq),
    ite_eq_right (ne_of_gt hp)]
  simpa only [mul_div_mul_right _ _ (ne_of_gt hpD),
    mul_div_mul_left _ _ (ne_of_gt hqD)] using hdiv

/-- Passing from probabilities to odds preserves this decreasing order. -/
theorem genericOddWeight_antitone {p q : Nat} (hp : 2 < p) (hpq : p <= q) :
    genericOddWeight q <= genericOddWeight p := by
  have hq : 2 < q := hp.trans_le hpq
  have hqp := genericOddEta_antitone hp hpq
  have hp0 := genericOddEta_pos p hp
  have hp1 := genericOddEta_lt_one p hp
  have hq1 := genericOddEta_lt_one q hq
  unfold genericOddWeight
  exact (div_le_div_of_nonneg_right hqp (le_of_lt (sub_pos.mpr hq1))).trans
    (div_le_div_of_nonneg_left (le_of_lt hp0) (sub_pos.mpr hp1) (by linarith))

end PrimeFactorOscillations
