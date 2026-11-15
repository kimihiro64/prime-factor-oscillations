/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermanentGammaRange

/-! # One root-scale window for every region of the actual rook integral

The same inverse eighth-root width meets the local hypotheses and makes
both the annular and outer exponents negative. No region is discarded.
The hypotheses are supplied uniformly for every fixed polylogarithmic cap.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

structure HamiltonianGammaRootWindowData (n : Nat) (a delta : Real) : Prop where
  root_pos : 0 < hamiltonianGammaCoreRoot (n : Real)
  root_eighth : hamiltonianGammaCoreRoot (n : Real) ^ 8 = (n : Real)
  width_pos : 0 < hamiltonianGammaCoreWidth (n : Real)
  width_small : hamiltonianGammaCoreWidth (n : Real) <= delta / 64
  core_large : 4 <= (n : Real) * hamiltonianGammaCoreWidth (n : Real)
  covariance_small : 2 * (a - 1) * hamiltonianGammaCoreWidth (n : Real) <= delta
  physical_large : 32 <= (n : Real) * delta
  core_exponent : -((n : Real) + 1) * hamiltonianGammaCoreWidth (n : Real) ^ 2 / 72 <=
    -(hamiltonianGammaCoreRoot (n : Real) ^ 6) / 72
  annular_exponent :
    6 * a * Real.sqrt (n : Real) / delta -
        ((n : Real) + 1) * hamiltonianGammaCoreWidth (n : Real) ^ 2 / 36 <=
      -(hamiltonianGammaCoreRoot (n : Real) ^ 6) / 72
  outer_exponent :
    -(n : Real) * delta ^ 2 / 36864 +
        (40 / (3 * delta)) * Real.sqrt ((n : Real) * (a - 1)) <=
      -(n : Real) * delta ^ 2 / 73728

theorem hamiltonian_gamma_root_window_data (n : Nat) (a delta : Real)
    (hn : 16 <= n) (ha : 1 <= a) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hRoot : 64 / delta <= hamiltonianGammaCoreRoot (n : Real))
    (hCap : a <= delta ^ 3 * hamiltonianGammaCoreRoot (n : Real) / 1000000) :
    HamiltonianGammaRootWindowData n a delta := by
  let r := hamiltonianGammaCoreRoot (n : Real)
  let eps := hamiltonianGammaCoreWidth (n : Real)
  have hN : (16 : Real) <= (n : Real) := by exact_mod_cast hn
  have hN0 : 0 < (n : Real) := by linarith only [hN]
  have hr : 0 < r := Real.rpow_pos_of_pos hN0 _
  have hr8 : r ^ 8 = (n : Real) := by
    dsimp only [r, hamiltonianGammaCoreRoot]
    calc
      _ = ((n : Real) ^ (1 / 8 : Real)) ^ (8 : Real) :=
        (Real.rpow_natCast _ 8).symm
      _ = (n : Real) ^ ((1 / 8 : Real) * 8) :=
        (Real.rpow_mul hN0.le _ _).symm
      _ = _ := by norm_num
  have hSqrt : Real.sqrt (n : Real) = r ^ 4 := by
    rw [<- hr8, show r ^ 8 = (r ^ 4) ^ 2 by ring, Real.sqrt_sq (pow_nonneg hr.le 4)]
  have hRD : 64 <= delta * r := by
    have h := mul_le_mul_of_nonneg_left hRoot hDelta0.le
    have hCancel : delta * (64 / delta) = 64 := by field_simp [ne_of_gt hDelta0]
    rw [hCancel] at h
    exact h
  have hr64 : 64 <= r := by
    have h := mul_le_mul_of_nonneg_right hDelta1 hr.le
    nlinarith only [hRD, h]
  have hr1 : 1 <= r := by linarith only [hr64]
  have hPowers : forall k l : Nat, k <= l -> r ^ k <= r ^ l := by
    intro k l hkl
    simpa only [one_pow, one_mul] using
      hamiltonian_polynomial_power_bound 1 r r k l
        (by norm_num) hr1 hr.le (by linarith) hkl
  have hD2 : delta ^ 2 <= 1 := wick_unit_power_le_one delta hDelta0.le hDelta1 2
  have hD3 : delta ^ 3 <= delta := by
    have h := mul_le_mul_of_nonneg_left hD2 hDelta0.le
    nlinarith only [h]
  have hEps : eps = 1 / r := rfl
  have hEps0 : 0 < eps := by rw [hEps]; positivity
  have hWidth : eps <= delta / 64 := by
    rw [hEps]
    have hProduct : (1 / r) * r <= (delta / 64) * r := by
      calc
        (1 / r) * r = 1 := by field_simp [ne_of_gt hr]
        _ <= (delta / 64) * r := by linarith only [hRD]
    exact le_of_mul_le_mul_right hProduct hr
  have hNEps : (n : Real) * eps = r ^ 7 := by
    rw [<- hr8, hEps]
    field_simp [ne_of_gt hr] <;> ring
  have hLarge : 4 <= (n : Real) * eps := by
    have h := hPowers 1 7 (by omega)
    rw [pow_one] at h
    rw [hNEps]
    linarith only [h, hr64]
  have hSmall : 2 * (a - 1) * eps <= delta := by
    rw [hEps]
    apply le_of_mul_le_mul_right (a := r) _ hr
    have hD3r := mul_le_mul_of_nonneg_right hD3 hr.le
    calc
      _ = 2 * (a - 1) := by field_simp [ne_of_gt hr]
      _ <= 2 * (delta ^ 3 * r / 1000000) := by linarith only [hCap]
      _ <= _ := by nlinarith only [hD3r, mul_nonneg hDelta0.le hr.le]
  have hPhysical : 32 <= (n : Real) * delta := by
    have hRToN := hPowers 1 8 (by omega)
    rw [pow_one, hr8] at hRToN
    have h := mul_le_mul_of_nonneg_right hRToN hDelta0.le
    nlinarith only [hRD, h]
  have hSpreadId : (n : Real) * eps ^ 2 = r ^ 6 := by
    rw [<- hr8, hEps]
    field_simp [ne_of_gt hr] <;> ring
  have hSpread : r ^ 6 <= ((n : Real) + 1) * eps ^ 2 := by
    rw [<- hSpreadId]
    exact mul_le_mul_of_nonneg_right (by linarith : (n : Real) <= (n : Real) + 1)
      (sq_nonneg eps)
  have hCoreExponent : -((n : Real) + 1) * eps ^ 2 / 72 <= -(r ^ 6) / 72 := by
    linarith only [hSpread]
  have hAnnularSupply : 6 * a * Real.sqrt (n : Real) / delta <= r ^ 6 / 72 := by
    rw [hSqrt]
    calc
      _ <= 6 * (delta ^ 3 * r / 1000000) * r ^ 4 / delta :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hCap (by norm_num)) (pow_nonneg hr.le 4))
          hDelta0.le
      _ = 6 * delta ^ 2 * r ^ 5 / 1000000 := by field_simp [ne_of_gt hDelta0] <;> ring
      _ <= 6 * r ^ 5 / 1000000 := by
        have h := mul_le_mul_of_nonneg_right hD2 (pow_nonneg hr.le 5)
        nlinarith only [h]
      _ <= 6 * r ^ 6 / 1000000 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hPowers 5 6 (by omega)) (by norm_num)) (by norm_num)
      _ <= _ := by nlinarith only [pow_nonneg hr.le 6]
  have hAnnular :
      6 * a * Real.sqrt (n : Real) / delta - ((n : Real) + 1) * eps ^ 2 / 36 <=
        -(r ^ 6) / 72 := by linarith only [hAnnularSupply, hSpread]
  have hOuterSupply :
      (40 / (3 * delta)) * Real.sqrt ((n : Real) * (a - 1)) <=
        (n : Real) * delta ^ 2 / 73728 := by
    calc
      _ <= (40 / (3 * delta)) * (a * Real.sqrt (n : Real)) :=
        mul_le_mul_of_nonneg_left
          (hamiltonian_sqrt_product_bound (n : Real) a hN0.le ha) (by positivity)
      _ <= (40 / (3 * delta)) *
          ((delta ^ 3 * r / 1000000) * Real.sqrt (n : Real)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hCap (Real.sqrt_nonneg _)) (by positivity)
      _ = 40 * delta ^ 2 * r ^ 5 / 3000000 := by
        rw [hSqrt]
        field_simp [ne_of_gt hDelta0] <;> ring
      _ <= 40 * delta ^ 2 * r ^ 8 / 3000000 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hPowers 5 8 (by omega))
            (by positivity : 0 <= 40 * delta ^ 2)) (by norm_num)
      _ <= delta ^ 2 * r ^ 8 / 73728 := by
        nlinarith only [mul_nonneg (sq_nonneg delta) (pow_nonneg hr.le 8)]
      _ = _ := by rw [hr8]; ring
  have hOuter : -(n : Real) * delta ^ 2 / 36864 +
      (40 / (3 * delta)) * Real.sqrt ((n : Real) * (a - 1)) <=
        -(n : Real) * delta ^ 2 / 73728 := by linarith only [hOuterSupply]
  exact {
    root_pos := hr
    root_eighth := hr8
    width_pos := hEps0
    width_small := hWidth
    core_large := hLarge
    covariance_small := hSmall
    physical_large := hPhysical
    core_exponent := hCoreExponent
    annular_exponent := hAnnular
    outer_exponent := hOuter }

end PrimeFactorOscillations
