/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGammaTaylor
import PrimeFactorOscillations.Helpers.HamiltonianPermanentCutoffChoice
import PrimeFactorOscillations.Helpers.HamiltonianRookGammaTail

/-! # Exact original-rook Gamma regions

The original signed rook polynomial controls the annulus and far tail.
No determinant or covariance approximation is extended past its physical
window. The central signed permanent correction is left intact.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem stochastic_rook_physical_window_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta s : Real)
    (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hs : abs s <= hamiltonianWindowScale delta) :
    abs (hamiltonianRookPolynomial (centeredKernel T q) s) <=
      Real.exp (6 * a * Real.sqrt (n : Real) / delta) := by
  have hb := hamiltonian_window_scale_bounds delta hDelta0 hDelta1
  have hArg := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hDelta1)
  have hDen : delta / 2 <= 1 - abs s * (1 - delta) := by
    unfold hamiltonianWindowScale at hArg
    nlinarith only [hArg, sq_nonneg delta, hDelta0]
  have hGap : 0 < 1 - abs s * (1 - delta) :=
    lt_of_lt_of_le (by positivity) hDen
  have hNum : 2 * abs s <= 3 := by linarith only [hs, hb.2]
  have hRatio : 2 * abs s / (1 - abs s * (1 - delta)) <= 6 / delta := by
    calc
      _ <= 3 / (1 - abs s * (1 - delta)) :=
        div_le_div_of_nonneg_right hNum hGap.le
      _ <= 3 / (delta / 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hDen
      _ = _ := by ring
  have h := hamiltonianComplexRookPolynomial_stochastic_bound T q a (1 - delta)
    (s : Complex) hq ha hRow hCol hNonneg hUpper hNorm
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hGap)
  rw [hamiltonianComplexRookPolynomial_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
  have hExp : 2 * abs s / (1 - abs s * (1 - delta)) *
      Real.sqrt ((n : Real) * (a - 1)) <= 6 * a * Real.sqrt (n : Real) / delta := by
    have hProduct := mul_le_mul hRatio
      (hamiltonian_sqrt_product_bound (n : Real) a (Nat.cast_nonneg n) ha)
      (Real.sqrt_nonneg _) (by positivity : (0 : Real) <= 6 / delta)
    calc
      _ <= (6 / delta) * (a * Real.sqrt (n : Real)) := hProduct
      _ = _ := by ring
  apply le_trans h
  apply Real.exp_le_exp.mpr
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hExp

theorem hamiltonianRookPolynomial_abs_gamma_integrable {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) :
    GammaInverseIntegrable n (fun s => abs (hamiltonianRookPolynomial B s)) := by
  have hRaw : GammaInverseIntegrable n (hamiltonianRookPolynomial B) := by
    unfold GammaInverseIntegrable
    simpa only [Fintype.card_fin] using hamiltonianRookPolynomial_integrable B
  apply hRaw.norm.congr
  apply (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  dsimp only
  rw [norm_mul, norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (pow_nonneg (show 0 <= t from ht.le) n),
    Real.norm_eq_abs]

theorem stochastic_rook_gamma_annulus_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real)
    (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hEps0 : 0 < eps) (hEps1 : eps <= 1 / 2)
    (hLarge : 4 <= (n : Real) * eps) :
    abs (gammaInverseAverage n
      (Set.indicator
        (Set.diff (Set.Icc (1 - delta / 16) (1 + delta / 16))
          {s : Real | abs (s - 1) <= eps})
        (hamiltonianRookPolynomial (centeredKernel T q)))) <=
      2 * Real.exp (6 * a * Real.sqrt (n : Real) / delta -
        ((n : Real) + 1) * eps ^ 2 / 36) := by
  let I : Set Real := Set.Icc (1 - delta / 16) (1 + delta / 16)
  let C : Set Real := {s | abs (s - 1) <= eps}
  let E : Set Real := {s | eps < abs (s - 1)}
  let H := Real.exp (6 * a * Real.sqrt (n : Real) / delta)
  let R := hamiltonianRookPolynomial (centeredKernel T q)
  have hH : 0 <= H := (Real.exp_pos _).le
  have hMap : Measurable (fun s : Real => abs (s - 1)) := by
    simpa only [Real.norm_eq_abs] using (measurable_sub_const (1 : Real)).norm
  have hE : MeasurableSet E := measurableSet_lt measurable_const hMap
  have hInt := gammaInverseIntegrable_smul n H (Set.indicator E (fun _ => (1 : Real)))
    (gammaInverseIntegrable_indicator n (fun _ => (1 : Real))
      (gammaInverseIntegrable_const n 1) E hE)
  have hBound := gammaInverseAverage_abs_le n (Set.indicator (Set.diff I C) R)
    (fun s => H * Set.indicator E (fun _ => (1 : Real)) s) hInt (by
      intro s hs0
      by_cases hs : Membership.mem (Set.diff I C) s
      case pos =>
        have hsE : Membership.mem E s := by
          change eps < abs (s - 1)
          exact lt_of_not_ge hs.2
        rw [Set.indicator_of_mem hs, Set.indicator_of_mem hsE, mul_one]
        apply stochastic_rook_physical_window_bound T q a delta s hq ha
          hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm
        unfold hamiltonianWindowScale
        apply abs_le.mpr
        exact And.intro (by linarith only [hs.1.1, hDelta0])
          (by linarith only [hs.1.2])
      case neg =>
        rw [Set.indicator_of_notMem hs, abs_zero]
        by_cases hsE : Membership.mem E s
        case pos => rw [Set.indicator_of_mem hsE, mul_one]; exact hH
        case neg => rw [Set.indicator_of_notMem hsE, mul_zero])
  rw [gammaInverseAverage_smul] at hBound
  have hTail := gammaInverseAverage_outside_window n eps hEps0 hEps1 hLarge
  have hMul := mul_le_mul_of_nonneg_left hTail hH
  calc
    _ <= H * gammaInverseAverage n (Set.indicator E (fun _ => (1 : Real))) := hBound
    _ <= H * (2 * Real.exp (-((n : Real) + 1) * eps ^ 2 / 36)) := hMul
    _ = _ := by
      dsimp only [H]
      rw [show -((n : Real) + 1) * eps ^ 2 / 36 =
        -(((n : Real) + 1) * eps ^ 2 / 36) by ring, Real.exp_sub]
      rw [Real.exp_neg]
      field_simp
      <;> ring


theorem stochastic_rook_gamma_outer_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta : Real)
    (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hLarge : 32 <= (n : Real) * delta) :
    abs (gammaInverseAverage n
      (Set.indicator (Set.compl (Set.Icc (1 - delta / 16) (1 + delta / 16)))
        (hamiltonianRookPolynomial (centeredKernel T q)))) <=
      3 * Real.exp (-(n : Real) * delta ^ 2 / 36864 +
        40 / (3 * delta) * Real.sqrt ((n : Real) * (a - 1))) := by
  let R := hamiltonianRookPolynomial (centeredKernel T q)
  let O : Set Real := Set.compl (Set.Icc (1 - delta / 16) (1 + delta / 16))
  have hInt := gammaInverseIntegrable_indicator n (fun s => abs (R s))
    (hamiltonianRookPolynomial_abs_gamma_integrable (centeredKernel T q))
    O measurableSet_Icc.compl
  have hNormR := gammaInverseAverage_abs_le n (Set.indicator O R)
    (Set.indicator O (fun s => abs (R s))) hInt (by
      intro s hs0
      by_cases hs : Membership.mem O s
      case pos => rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
      case neg => rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, abs_zero])
  have hSmallGap : norm (centeredKernel T q) <= 1 - delta / 4 := by
    linarith only [hNorm, hDelta0]
  have hOutside := hamiltonianRookInverseGammaOutside_stochastic_bound T q a (delta / 4)
    hq ha hRow hCol hNonneg hUpper hSmallGap (by positivity)
    (by linarith only [hDelta1]) (by nlinarith only [hLarge])
  have hLeft : (1 : Real) - (delta / 4) / 4 = 1 - delta / 16 := by ring
  have hRight : (1 : Real) + (delta / 4) / 4 = 1 + delta / 16 := by ring
  rw [hLeft, hRight] at hOutside
  calc
    _ <= gammaInverseAverage n (Set.indicator O (fun s => abs (R s))) := hNormR
    _ <= 3 * Real.exp (-(n : Real) * (delta / 4) ^ 2 / 2304 +
        10 / (3 * (delta / 4)) * Real.sqrt ((n : Real) * (a - 1))) := hOutside
    _ = _ := by congr 1; congr 1; field_simp [ne_of_gt hDelta0]; ring

theorem stochastic_rook_gamma_full_to_core {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real)
    (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hEps0 : 0 < eps) (hEps1 : eps <= delta / 16)
    (hLarge : 4 <= (n : Real) * eps) (hOuter : 32 <= (n : Real) * delta) :
    abs (gammaInverseAverage n (hamiltonianRookPolynomial (centeredKernel T q)) -
      gammaInverseAverage n
        (Set.indicator {s : Real | abs (s - 1) <= eps}
          (hamiltonianRookPolynomial (centeredKernel T q)))) <=
      2 * Real.exp (6 * a * Real.sqrt (n : Real) / delta -
        ((n : Real) + 1) * eps ^ 2 / 36) +
      3 * Real.exp (-(n : Real) * delta ^ 2 / 36864 +
        40 / (3 * delta) * Real.sqrt ((n : Real) * (a - 1))) := by
  let R := hamiltonianRookPolynomial (centeredKernel T q)
  let I : Set Real := Set.Icc (1 - delta / 16) (1 + delta / 16)
  let C : Set Real := {s | abs (s - 1) <= eps}
  let M := Set.diff I C
  let O := Set.compl I
  have hMap : Measurable (fun s : Real => abs (s - 1)) := by
    simpa only [Real.norm_eq_abs] using (measurable_sub_const (1 : Real)).norm
  have hC : MeasurableSet C := measurableSet_le hMap measurable_const
  have hI : MeasurableSet I := measurableSet_Icc
  have hM : MeasurableSet M := hI.diff hC
  have hO : MeasurableSet O := hI.compl
  have hSubset : forall s, Membership.mem C s -> Membership.mem I s := by
    intro s hs
    change abs (s - 1) <= eps at hs
    have hRange := abs_le.mp hs
    exact And.intro (by linarith only [hRange.1, hEps1])
      (by linarith only [hRange.2, hEps1])
  have hR : GammaInverseIntegrable n R := by
    unfold GammaInverseIntegrable
    simpa only [Fintype.card_fin] using hamiltonianRookPolynomial_integrable (centeredKernel T q)
  have hRC := gammaInverseIntegrable_indicator n R hR C hC
  have hRM := gammaInverseIntegrable_indicator n R hR M hM
  have hRO := gammaInverseIntegrable_indicator n R hR O hO
  have hRCM := gammaInverseIntegrable_add n _ _ hRC hRM
  have hFun : R = (fun s => (Set.indicator C R s + Set.indicator M R s) +
      Set.indicator O R s) := by
    funext s
    by_cases hsC : Membership.mem C s
    case pos =>
      have hsI := hSubset s hsC
      have hsM : Not (Membership.mem M s) := fun h => h.2 hsC
      have hsO : Not (Membership.mem O s) := fun h => h hsI
      simp only [Set.indicator_of_mem hsC, Set.indicator_of_notMem hsM,
        Set.indicator_of_notMem hsO, add_zero]
    case neg =>
      by_cases hsI : Membership.mem I s
      case pos =>
        have hsM : Membership.mem M s := And.intro hsI hsC
        have hsO : Not (Membership.mem O s) := fun h => h hsI
        simp only [Set.indicator_of_notMem hsC, Set.indicator_of_mem hsM,
          Set.indicator_of_notMem hsO, zero_add, add_zero]
      case neg =>
        have hsM : Not (Membership.mem M s) := fun h => hsI h.1
        have hsO : Membership.mem O s := hsI
        simp only [Set.indicator_of_notMem hsC, Set.indicator_of_notMem hsM,
          Set.indicator_of_mem hsO, zero_add]
  have hSplit := congrArg (gammaInverseAverage n) hFun
  rw [gammaInverseAverage_add n _ _ hRCM hRO,
    gammaInverseAverage_add n _ _ hRC hRM] at hSplit
  have hIdentity : gammaInverseAverage n R - gammaInverseAverage n (Set.indicator C R) =
      gammaInverseAverage n (Set.indicator M R) + gammaInverseAverage n (Set.indicator O R) := by
    linarith only [hSplit]
  have hEpsHalf : eps <= 1 / 2 := by linarith only [hEps1, hDelta1]
  have hAnnulus := stochastic_rook_gamma_annulus_bound T q a delta eps hq ha hRow hCol
    hNonneg hUpper hDelta0 hDelta1 hNorm hEps0 hEpsHalf hLarge
  have hOutside := stochastic_rook_gamma_outer_bound T q a delta hq ha hRow hCol
    hNonneg hUpper hDelta0 hDelta1 hNorm hOuter
  change abs (gammaInverseAverage n R - gammaInverseAverage n (Set.indicator C R)) <= _
  rw [hIdentity]
  exact le_trans (abs_add_le _ _) (add_le_add hAnnulus hOutside)

end PrimeFactorOscillations
