/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauPsiMellin
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianUniformZeroResponse

/-!
# A cofinal sparse deletion count excludes zeros to its right

The count condition concerns the literal fixed greedy deleted-prime class.
Its witnesses need only be cofinal integer cutoffs. The unconditional
uniform zero response supplies the incompatible eventual lower bound.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem greedyDeletedPrimeClass_zero_strip_of_sparse_power_count
    (eta : Real) (hEta : (1 / 2 : Real) <= eta)
    (hSparse : forall epsilon : Real, 0 < epsilon -> forall N : Nat,
      Exists fun n : Nat => And (max N 2 <= n)
        (((primeClassPrefix greedyDeletedPrimeClass n).card : Real) <=
          (n : Real) ^ (eta + epsilon))) :
    forall rho : Complex, riemannZeta rho = 0 ->
      And (0 < rho.re) (rho.re < 1) -> rho.re <= eta := by
  intro rho hZero hStrip
  by_contra hFail
  have hBeta : eta < rho.re := lt_of_not_ge hFail
  let epsilon : Real := (rho.re - eta) / 4
  have he : 0 < epsilon := by
    dsimp only [epsilon]
    linarith only [hBeta]
  have hGap : eta + epsilon < rho.re - epsilon := by
    dsimp only [epsilon]
    linarith only [hBeta]
  choose d hd X0 hLower using
    greedyDeletedPrimeClass_uniform_zero_response rho hZero hStrip
      (hEta.trans_lt hBeta) epsilon he
  have hNat : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hRatio : Tendsto (fun n : Nat =>
      (n : Real) ^ (eta + epsilon) / (n : Real) ^ (rho.re - epsilon))
      atTop (nhds 0) :=
    (gaussian_power_ratio_tendsto (eta + epsilon) (rho.re - epsilon) hGap).comp hNat
  have hTogether : forall n : Nat, max 2 (Nat.ceil X0) <= n ->
      d * (n : Real) ^ (rho.re - epsilon) <=
        ((primeClassPrefix greedyDeletedPrimeClass n).card : Real) := by
    intro n hn
    have hX : X0 <= (n : Real) :=
      (Nat.le_ceil X0).trans (Nat.cast_le.mpr ((le_max_right 2 (Nat.ceil X0)).trans hn))
    simpa only [Nat.floor_natCast] using hLower (n : Real) hX
  have hRatioSmall : Filter.Eventually (fun n : Nat =>
      (n : Real) ^ (eta + epsilon) / (n : Real) ^ (rho.re - epsilon) < d) atTop :=
    hRatio.eventually (eventually_lt_nhds hd)
  choose N hN using Filter.eventually_atTop.mp hRatioSmall
  choose n hn using hSparse epsilon he (max N (max 2 (Nat.ceil X0)))
  have hNn : N <= n :=
    (le_max_left N (max 2 (Nat.ceil X0))).trans ((le_max_left _ 2).trans hn.1)
  have hLn : max 2 (Nat.ceil X0) <= n :=
    (le_max_right N (max 2 (Nat.ceil X0))).trans ((le_max_left _ 2).trans hn.1)
  have hnTwo : 2 <= n := (le_max_left 2 (Nat.ceil X0)).trans hLn
  have hx : (0 : Real) < (n : Real) := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 < (n : Real) ^ (rho.re - epsilon) := Real.rpow_pos_of_pos hx _
  have hMul := mul_lt_mul_of_pos_right (hN n hNn) hp
  have hCancel : ((n : Real) ^ (eta + epsilon) /
      (n : Real) ^ (rho.re - epsilon)) * (n : Real) ^ (rho.re - epsilon) =
        (n : Real) ^ (eta + epsilon) := by field_simp [hp.ne']
  rw [hCancel] at hMul
  exact (not_lt_of_ge ((hTogether n hLn).trans hn.2)) hMul

theorem riemannHypothesis_of_sparse_greedyDeletedPrimeClass_count
    (hSparse : forall epsilon : Real, 0 < epsilon -> forall N : Nat,
      Exists fun n : Nat => And (max N 2 <= n)
        (((primeClassPrefix greedyDeletedPrimeClass n).card : Real) <=
          (n : Real) ^ ((1 / 2 : Real) + epsilon))) :
    RiemannHypothesis := by
  by_contra hNotRH
  choose rho hZero hRight hOne using
    Robin1984.exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNotRH
  have hStrip : And (0 < rho.re) (rho.re < 1) :=
    And.intro (by linarith only [hRight]) hOne
  have hLe := greedyDeletedPrimeClass_zero_strip_of_sparse_power_count
    (1 / 2 : Real) (le_refl _) hSparse rho hZero hStrip
  exact (not_lt_of_ge hLe) hRight

end PrimeFactorOscillations.PrimeClassDeletion
