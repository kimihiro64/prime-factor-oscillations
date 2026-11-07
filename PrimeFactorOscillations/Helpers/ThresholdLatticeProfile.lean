/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdBandSharpness

/-! # Exact three-atom perturbations at lattice boundary masses -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdLatticeR (k m z e : Real) : Real := k * z + m * e

def thresholdLatticeS (d k m z e : Real) : Real := k * z ^ 2 + 2 * m * d * e - m * e ^ 2

def thresholdLatticeDisc (d k m z e : Real) : Real :=
  k * ((k + 1) * thresholdLatticeS d k m z e - (thresholdLatticeR k m z e) ^ 2)

def thresholdLatticeResidual (d k m z e : Real) : Real :=
  (thresholdLatticeR k m z e - Real.sqrt (thresholdLatticeDisc d k m z e)) / (k + 1)

def thresholdLatticeHigh (d k m z e : Real) : Real :=
  (thresholdLatticeR k m z e - thresholdLatticeResidual d k m z e) / k

def thresholdLatticeEnergy (d k m z e : Real) : Real :=
  2 * m * (d - e) * (d - e - 1) ^ 2 +
    2 * k * thresholdLatticeHigh d k m z e * (thresholdLatticeHigh d k m z e - 1) ^ 2 +
      2 * thresholdLatticeResidual d k m z e * (thresholdLatticeResidual d k m z e - 1) ^ 2

theorem thresholdLatticeDisc_zero (d k m z : Real) :
    thresholdLatticeDisc d k m z 0 = (k * z) ^ 2 := by
  unfold thresholdLatticeDisc thresholdLatticeR thresholdLatticeS
  ring

theorem thresholdLatticeResidual_zero (d k m z : Real) (hk : 0 < k) (hz : 0 <= z) :
    thresholdLatticeResidual d k m z 0 = 0 := by
  unfold thresholdLatticeResidual
  rw [thresholdLatticeDisc_zero, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hk.le hz)]
  simp [thresholdLatticeR]

theorem thresholdLatticeHigh_zero (d k m z : Real) (hk : 0 < k) (hz : 0 <= z) :
    thresholdLatticeHigh d k m z 0 = z := by
  unfold thresholdLatticeHigh
  rw [thresholdLatticeResidual_zero d k m z hk hz]
  dsimp [thresholdLatticeR]
  field_simp [hk.ne']
  <;> ring

theorem thresholdLatticeResidual_quadratic (d k m z e : Real) (hk : 0 < k)
    (hDisc : 0 <= thresholdLatticeDisc d k m z e) :
    (k + 1) * (thresholdLatticeResidual d k m z e) ^ 2 -
      2 * thresholdLatticeR k m z e * thresholdLatticeResidual d k m z e +
        (thresholdLatticeR k m z e) ^ 2 - k * thresholdLatticeS d k m z e = 0 := by
  have hDen : Not (k + 1 = 0) := by linarith only [hk]
  have hi : (k + 1) * (thresholdLatticeResidual d k m z e) ^ 2 -
      2 * thresholdLatticeR k m z e * thresholdLatticeResidual d k m z e +
        (thresholdLatticeR k m z e) ^ 2 - k * thresholdLatticeS d k m z e =
      ((Real.sqrt (thresholdLatticeDisc d k m z e)) ^ 2 - thresholdLatticeDisc d k m z e) / (k + 1) := by
    unfold thresholdLatticeResidual thresholdLatticeDisc
    field_simp [hDen]
    <;> ring
  rw [hi, Real.sq_sqrt hDisc, sub_self, zero_div]

theorem thresholdLattice_first_moment (d k m z e : Real) (hk : 0 < k) :
    2 * m * (d - e) + 2 * k * thresholdLatticeHigh d k m z e +
      2 * thresholdLatticeResidual d k m z e = 2 * (k * z + m * d) := by
  unfold thresholdLatticeHigh thresholdLatticeR
  field_simp [hk.ne']
  <;> ring

theorem thresholdLattice_second_moment (d k m z e : Real) (hk : 0 < k)
    (hDisc : 0 <= thresholdLatticeDisc d k m z e)
    (hMoment : k * z * (z - 1) = m * d * (1 - d)) :
    2 * m * (d - e) ^ 2 + 2 * k * (thresholdLatticeHigh d k m z e) ^ 2 +
      2 * (thresholdLatticeResidual d k m z e) ^ 2 = 2 * (k * z + m * d) := by
  have hQ := thresholdLatticeResidual_quadratic d k m z e hk hDisc
  have hi : k * (thresholdLatticeHigh d k m z e) ^ 2 +
      (thresholdLatticeResidual d k m z e) ^ 2 - thresholdLatticeS d k m z e =
      ((k + 1) * (thresholdLatticeResidual d k m z e) ^ 2 -
        2 * thresholdLatticeR k m z e * thresholdLatticeResidual d k m z e +
          (thresholdLatticeR k m z e) ^ 2 - k * thresholdLatticeS d k m z e) / k := by
    unfold thresholdLatticeHigh
    field_simp [hk.ne']
    <;> ring
  rw [hQ, zero_div] at hi
  dsimp [thresholdLatticeS] at hi
  nlinarith only [hi, hMoment]

theorem thresholdLatticeResidual_nonneg (d k m z e : Real)
    (hk : 0 < k) (hm : 0 <= m) (hz : And (0 < z) (d < z)) (he : 0 <= e)
    (hDisc : 0 <= thresholdLatticeDisc d k m z e) :
    0 <= thresholdLatticeResidual d k m z e := by
  have hR : 0 < thresholdLatticeR k m z e := add_pos_of_pos_of_nonneg (mul_pos hk hz.1) (mul_nonneg hm he)
  have hId : (thresholdLatticeR k m z e) ^ 2 - thresholdLatticeDisc d k m z e =
      (k + 1) * (2 * k * m * (z - d) * e + m * (m + k) * e ^ 2) := by
    unfold thresholdLatticeDisc thresholdLatticeS thresholdLatticeR
    ring
  have hPos : 0 <= (k + 1) * (2 * k * m * (z - d) * e + m * (m + k) * e ^ 2) := by
    apply mul_nonneg (by linarith only [hk])
    exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk.le) hm)
      (sub_nonneg.mpr hz.2.le)) he) (mul_nonneg (mul_nonneg hm (by linarith only [hm, hk])) (sq_nonneg e))
  have hSq := Real.sq_sqrt hDisc
  have hRoot := Real.sqrt_nonneg (thresholdLatticeDisc d k m z e)
  have hUpper : Real.sqrt (thresholdLatticeDisc d k m z e) <= thresholdLatticeR k m z e := by
    nlinarith only [hId, hPos, hSq, hRoot, hR]
  exact div_nonneg (sub_nonneg.mpr hUpper) (by linarith only [hk])

theorem thresholdLatticeEnergy_zero (d k m z : Real) (hk : 0 < k) (hz : 0 <= z)
    (hMoment : k * z * (z - 1) = m * d * (1 - d)) :
    thresholdLatticeEnergy d k m z 0 = 2 * (k * z + m * d) * (1 - d) * (z - 1) := by
  unfold thresholdLatticeEnergy
  rw [thresholdLatticeHigh_zero d k m z hk hz, thresholdLatticeResidual_zero d k m z hk hz]
  have hh := congrArg (fun q : Real => 2 * (z + d - 2) * q) hMoment
  nlinarith only [hh]

end PrimeFactorOscillations
