/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdBandIntegerCost

/-! # Strict arithmetic gain on a feasible even two-atom moment family -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem thresholdIntegerCorrection_pos (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hK : 0 < K) (hKM : K <= M)
    (he : 0 < thresholdBandGap d (M - K * thresholdPositiveRoot d M K)) :
    0 < thresholdIntegerCorrection d M K := by
  have hz := (thresholdPositiveRoot_bounds d M K hd hM hK hKM).2
  have hc := thresholdBand_constants_pos d _ hd hz
  unfold thresholdIntegerCorrection
  rw [if_pos hKM]
  exact thresholdBandPenalty_pos _ _ _ hc.1 (div_pos hK hc.2) he

theorem thresholdBand_two_atom_gap (d u v : Real)
    (hd : And (0 < d) (d < 1 / 2)) (hu : And (0 < u) (u < d)) (hv : 1 <= v)
    (hMoment : u ^ 2 + v ^ 2 = u + v) :
    And (0 < thresholdBandGap d (2 * (u + v) - 2 * thresholdPositiveRoot d (2 * (u + v)) 2))
      (0 < thresholdIntegerCorrection d (2 * (u + v)) 2) := by
  have hd' : And (0 < d) (d < 1) := And.intro hd.1 (by linarith only [hd.2])
  have hM : 0 < 2 * (u + v) := by linarith only [hu.1, hv]
  have hKM : (2 : Real) < 2 * (u + v) := by linarith only [hu.1, hv]
  let z := thresholdPositiveRoot d (2 * (u + v)) 2
  have hz := thresholdPositiveRoot_gt_one d (2 * (u + v)) 2 hd' hM (by norm_num) hKM
  have hr := thresholdPositiveRoot_relation d (2 * (u + v)) 2 hd' hM (by norm_num)
  have hpFormula := (thresholdPositiveRoot_band_prediction d (2 * (u + v)) 2 hd' hM (by norm_num) hKM.le).1
  have hp : 0 < 2 * (u + v) - 2 * z := by
    rw [hpFormula]
    exact div_pos (mul_pos (mul_pos (by norm_num) (by exact lt_trans (by norm_num) hz))
      (sub_pos.mpr hz)) (by linarith only [hd.2])
  have hId : (z - (u + v - d)) * (z + u + v - 2 * d) = -2 * (u - d) * (v - d) := by
    change 2 * z * (z - d) = (1 - d) * (2 * (u + v)) at hr
    nlinarith only [hr, hMoment]
  have hRight : 0 < -2 * (u - d) * (v - d) :=
    mul_pos (by linarith only [hu.2]) (by linarith only [hv, hd.2])
  have hFactor : 0 < z + u + v - 2 * d := by
    change 1 < z at hz
    linarith only [hz, hu.1, hv, hd.2]
  have hzLow : u + v - d < z := by
    by_contra h
    have hm := mul_nonpos_of_nonpos_of_nonneg (show z - (u + v - d) <= 0 by linarith only [h]) hFactor.le
    linarith only [hm, hId, hRight]
  have he := thresholdBandGap_pos_small d (2 * (u + v) - 2 * z) hd.1
    (And.intro hp (by linarith only [hzLow]))
  exact And.intro he (thresholdIntegerCorrection_pos d _ 2 hd' hM (by norm_num) hKM.le he)

theorem thresholdBand_two_atom_exists (d : Real) (hd : And (0 < d) (d < 1 / 2)) :
    exists u v : Real, And (And (0 < u) (u < d)) (And (1 < v)
      (And (u ^ 2 + v ^ 2 = u + v) (0 < thresholdIntegerCorrection d (2 * (u + v)) 2))) := by
  let u := d / 2
  let v := (1 + Real.sqrt (1 + 4 * u * (1 - u))) / 2
  have hu : And (0 < u) (u < d) := by dsimp [u]; constructor <;> linarith only [hd.1]
  have hU : u < 1 := by dsimp [u]; linarith only [hd.2]
  have hD : 1 < 1 + 4 * u * (1 - u) := by
    have hp := mul_pos hu.1 (sub_pos.mpr hU)
    nlinarith only [hp]
  have hSq := Real.sq_sqrt (show 0 <= 1 + 4 * u * (1 - u) by linarith only [hD])
  have hRoot := Real.sqrt_nonneg (1 + 4 * u * (1 - u))
  have hv : 1 < v := by dsimp [v]; nlinarith only [hSq, hRoot, hD]
  have hm : u ^ 2 + v ^ 2 = u + v := by dsimp [v]; nlinarith only [hSq]
  have hg := (thresholdBand_two_atom_gap d u v hd hu hv.le hm).2
  exact Exists.intro u (Exists.intro v (And.intro hu (And.intro hv (And.intro hm hg))))

end PrimeFactorOscillations
