/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.EvenDirectionalWeightTuning
import PrimeFactorOscillations.Helpers.ThresholdLatticeProfile

/-! # Admissible exact moments arbitrarily close to a lattice boundary profile -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem thresholdLattice_perturbation (d k m z eps : Real)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hm : 0 <= m) (hz : 1 <= z) (heps : 0 < eps) :
    exists e : Real, And (And (0 < e) (e < d))
      (And (And (0 <= thresholdLatticeResidual d k m z e) (thresholdLatticeResidual d k m z e < d))
        (And (d < thresholdLatticeHigh d k m z e)
          (And (0 < thresholdLatticeDisc d k m z e)
            (thresholdLatticeEnergy d k m z e < thresholdLatticeEnergy d k m z 0 + eps)))) := by
  have hkOne : Not (k + 1 = 0) := by linarith only [hk]
  have hzPos : 0 < z := lt_of_lt_of_le (by norm_num) hz
  have hzD : d < z := lt_of_lt_of_le hd.2 hz
  have hcR : Continuous (fun e : Real => thresholdLatticeR k m z e) := by
    unfold thresholdLatticeR
    fun_prop
  have hcS : Continuous (fun e : Real => thresholdLatticeS d k m z e) := by
    unfold thresholdLatticeS
    fun_prop
  have hcD : Continuous (fun e : Real => thresholdLatticeDisc d k m z e) := by
    unfold thresholdLatticeDisc
    fun_prop
  have hcW : Continuous (fun e : Real => thresholdLatticeResidual d k m z e) := by
    unfold thresholdLatticeResidual
    fun_prop
  have hcV : Continuous (fun e : Real => thresholdLatticeHigh d k m z e) := by
    unfold thresholdLatticeHigh
    fun_prop
  have hcE : Continuous (fun e : Real => thresholdLatticeEnergy d k m z e) := by
    unfold thresholdLatticeEnergy
    fun_prop
  let margin := fun e : Real => min (thresholdLatticeDisc d k m z e)
    (min (thresholdLatticeHigh d k m z e - d)
      (min (d - thresholdLatticeResidual d k m z e)
        (thresholdLatticeEnergy d k m z 0 + eps - thresholdLatticeEnergy d k m z e)))
  have hcMargin : ContinuousAt margin 0 := by
    dsimp [margin]
    fun_prop
  have hZero : 0 < margin 0 := by
    dsimp [margin]
    rw [thresholdLatticeDisc_zero, thresholdLatticeHigh_zero d k m z hk hzPos.le,
      thresholdLatticeResidual_zero d k m z hk hzPos.le]
    apply lt_min (sq_pos_of_pos (mul_pos hk hzPos))
    apply lt_min (sub_pos.mpr hzD)
    apply lt_min (by linarith only [hd.1])
    linarith only [heps]
  choose radius hRadius hNear using (Metric.continuousAt_iff.mp hcMargin)
    (margin 0 / 2) (by linarith only [hZero])
  let e := min (radius / 2) (d / 2)
  have he : 0 < e := lt_min (by linarith only [hRadius]) (by linarith only [hd.1])
  have heD : e < d := lt_of_le_of_lt (min_le_right _ _) (by linarith only [hd.1])
  have heRadius : e < radius := lt_of_le_of_lt (min_le_left _ _) (by linarith only [hRadius])
  have hDist : dist e 0 < radius := by
    rw [Real.dist_eq, sub_zero, abs_of_pos he]
    exact heRadius
  have hNear' := hNear hDist
  rw [Real.dist_eq] at hNear'
  have hMargin : 0 < margin e := by
    have hLower := (abs_lt.mp hNear').1
    linarith only [hLower, hZero]
  have hD := lt_of_lt_of_le hMargin (min_le_left _ _)
  have hV := lt_of_lt_of_le hMargin (le_trans (min_le_right _ _) (min_le_left _ _))
  have hW := lt_of_lt_of_le hMargin (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hE := lt_of_lt_of_le hMargin (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hNonneg := thresholdLatticeResidual_nonneg d k m z e hk hm (And.intro hzPos hzD) he.le hD.le
  exact Exists.intro e (And.intro (And.intro he heD) (And.intro
    (And.intro hNonneg (by linarith only [hW])) (And.intro (by linarith only [hV])
      (And.intro hD (by linarith only [hE])))))

end PrimeFactorOscillations
