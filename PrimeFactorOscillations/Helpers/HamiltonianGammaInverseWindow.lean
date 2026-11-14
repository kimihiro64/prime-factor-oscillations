/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.HamiltonianGammaConcentration

/-! # The actual inverse-Gamma central window

Both Gamma tails are transferred through S=n/T with the shape n+1 retained.
The union bound is proved for the actual normalized Euler integral. The
result supplies the exponentially small central-window mass needed before
averaging locally defined determinant factors.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem gammaIndicator_integrable (n : Nat) (E : Set Real) (hE : MeasurableSet E) :
    MeasureTheory.Integrable
      (fun t : Real => Real.exp (-t) * t ^ n *
        Set.indicator E (fun _ => (1 : Real)) t) gammaHalfLine := by
  have hFun :
      (fun t : Real => Real.exp (-t) * t ^ n *
        Set.indicator E (fun _ => (1 : Real)) t) =
      Set.indicator E (fun t : Real => Real.exp (-t) * t ^ n) := by
    funext t
    by_cases ht : Membership.mem E t
    case pos => simp [Set.indicator, ht]
    case neg => simp [Set.indicator, ht]
  rw [hFun]
  exact (gammaKernel_integrable n).indicator hE

theorem gammaDirectAverage_indicator_cover (n : Nat) (E L U : Set Real)
    (hE : MeasurableSet E) (hL : MeasurableSet L) (hU : MeasurableSet U)
    (hCover : forall t, 0 < t -> Membership.mem E t ->
      Or (Membership.mem L t) (Membership.mem U t)) :
    gammaDirectAverage n (Set.indicator E (fun _ => (1 : Real))) <=
      gammaDirectAverage n (Set.indicator L (fun _ => (1 : Real))) +
        gammaDirectAverage n (Set.indicator U (fun _ => (1 : Real))) := by
  have hNonneg : forall (A : Set Real) (t : Real),
      0 <= Set.indicator A (fun _ => (1 : Real)) t := by
    intro A t
    by_cases ht : Membership.mem A t
    case pos => simp [Set.indicator, ht]
    case neg => simp [Set.indicator, ht]
  have hPoint : forall t, 0 < t ->
      Set.indicator E (fun _ => (1 : Real)) t <=
        Set.indicator L (fun _ => (1 : Real)) t +
          Set.indicator U (fun _ => (1 : Real)) t := by
    intro t ht
    by_cases hEt : Membership.mem E t
    case neg =>
      simp only [Set.indicator_of_notMem hEt]
      exact add_nonneg (hNonneg L t) (hNonneg U t)
    case pos =>
      rcases hCover t ht hEt with hLt | hUt
      case inl =>
        simp only [Set.indicator_of_mem hEt, Set.indicator_of_mem hLt]
        linarith only [hNonneg U t]
      case inr =>
        simp only [Set.indicator_of_mem hEt, Set.indicator_of_mem hUt]
        linarith only [hNonneg L t]
  have hFun :
      (fun t : Real => Real.exp (-t) * t ^ n *
        (Set.indicator L (fun _ => (1 : Real)) t +
          Set.indicator U (fun _ => (1 : Real)) t)) =
      (fun t : Real => Real.exp (-t) * t ^ n *
          Set.indicator L (fun _ => (1 : Real)) t +
        Real.exp (-t) * t ^ n * Set.indicator U (fun _ => (1 : Real)) t) := by
    funext t
    ring
  have hLeft := gammaIndicator_integrable n E hE
  have hIntL := gammaIndicator_integrable n L hL
  have hIntU := gammaIndicator_integrable n U hU
  have hRight : MeasureTheory.Integrable
      (fun t : Real => Real.exp (-t) * t ^ n *
        (Set.indicator L (fun _ => (1 : Real)) t +
          Set.indicator U (fun _ => (1 : Real)) t)) gammaHalfLine := by
    rw [hFun]
    exact hIntL.add hIntU
  have hDom : Filter.Eventually
      (fun t : Real => Real.exp (-t) * t ^ n *
          Set.indicator E (fun _ => (1 : Real)) t <=
        Real.exp (-t) * t ^ n *
          (Set.indicator L (fun _ => (1 : Real)) t +
            Set.indicator U (fun _ => (1 : Real)) t))
      (MeasureTheory.ae gammaHalfLine) :=
    (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => mul_le_mul_of_nonneg_left (hPoint t ht)
        (mul_nonneg (le_of_lt (Real.exp_pos _)) (pow_nonneg (le_of_lt ht) n)))
  unfold gammaDirectAverage
  calc
    _ <= Inv.inv (n.factorial : Real) *
        MeasureTheory.integral gammaHalfLine
          (fun t : Real => Real.exp (-t) * t ^ n *
            (Set.indicator L (fun _ => (1 : Real)) t +
              Set.indicator U (fun _ => (1 : Real)) t)) :=
      mul_le_mul_of_nonneg_left (MeasureTheory.integral_mono_ae hLeft hRight hDom)
        (inv_nonneg.mpr (Nat.cast_nonneg n.factorial))
    _ = _ := by
      rw [hFun, MeasureTheory.integral_add hIntL hIntU]
      ring

theorem inverseGamma_central_band (n eps t : Real) (hn0 : 0 <= n)
    (hEps0 : 0 < eps) (hEps1 : eps <= 1 / 2) (hLarge : 4 <= n * eps)
    (ht : 0 < t)
    (hLow : (n + 1) * (1 - eps / 2) <= t)
    (hUp : t <= (n + 1) * (1 + eps / 2)) :
    abs (n / t - 1) <= eps := by
  let M : Real := n + 1
  have hM0 : 0 <= M := add_nonneg hn0 (by norm_num)
  have hEpsLe : eps <= 1 := by linarith only [hEps1]
  have hUpperSlack : 0 <= M * eps * (1 - eps) :=
    mul_nonneg (mul_nonneg hM0 (le_of_lt hEps0)) (sub_nonneg.mpr hEpsLe)
  have hUpperProd : n <= (1 + eps) * (M * (1 - eps / 2)) := by
    dsimp [M] at hUpperSlack
    dsimp [M]
    nlinarith only [hUpperSlack]
  have hLowerSlack : 0 <= M * eps ^ 2 := mul_nonneg hM0 (sq_nonneg eps)
  have hLowerProd : (1 - eps) * (M * (1 + eps / 2)) <= n := by
    dsimp [M] at hLowerSlack
    dsimp [M]
    nlinarith only [hLarge, hEps0, hLowerSlack]
  have hProductLower : (1 - eps) * t <= n :=
    le_trans (mul_le_mul_of_nonneg_left hUp (sub_nonneg.mpr hEpsLe)) hLowerProd
  have hProductUpper : n <= (1 + eps) * t :=
    le_trans hUpperProd
      (mul_le_mul_of_nonneg_left hLow (by linarith only [hEps0]))
  have hRelation : (n / t) * t = n := by field_simp [ne_of_gt ht]
  have hLower : 1 - eps <= n / t := by
    by_contra hNot
    have hStrict := mul_lt_mul_of_pos_right (lt_of_not_ge hNot) ht
    rw [hRelation] at hStrict
    exact (not_lt_of_ge hProductLower) hStrict
  have hUpper : n / t <= 1 + eps := by
    by_contra hNot
    have hStrict := mul_lt_mul_of_pos_right (lt_of_not_ge hNot) ht
    rw [hRelation] at hStrict
    exact (not_lt_of_ge hProductUpper) hStrict
  apply abs_le.mpr
  constructor
  case left => linarith only [hLower]
  case right => linarith only [hUpper]

theorem gammaInverseAverage_outside_window
    (n : Nat) (eps : Real) (hEps0 : 0 < eps) (hEps1 : eps <= 1 / 2)
    (hLarge : 4 <= (n : Real) * eps) :
    gammaInverseAverage n
      (Set.indicator {s : Real | eps < abs (s - 1)} (fun _ => (1 : Real))) <=
      2 * Real.exp (-((n : Real) + 1) * eps ^ 2 / 36) := by
  let M : Real := (n : Real) + 1
  let E : Set Real := {t | eps < abs ((n : Real) / t - 1)}
  let L : Set Real := Set.Iic (M * (1 - eps / 2))
  let U : Set Real := Set.Ici (M * (1 + eps / 2))
  have hRaw : Measurable (fun t : Real => (n : Real) / t - 1) :=
    (measurable_const.div measurable_id).sub measurable_const
  have hMap : Measurable (fun t : Real => abs ((n : Real) / t - 1)) := by
    simpa only [Real.norm_eq_abs] using hRaw.norm
  have hE : MeasurableSet E := measurableSet_lt measurable_const hMap
  have hCover : forall t, 0 < t -> Membership.mem E t ->
      Or (Membership.mem L t) (Membership.mem U t) := by
    intro t ht hEt
    by_contra hNot
    have hNotL : Not (t <= M * (1 - eps / 2)) :=
      fun h => hNot (Or.inl h)
    have hNotU : Not (M * (1 + eps / 2) <= t) :=
      fun h => hNot (Or.inr h)
    have hBand := inverseGamma_central_band (n : Real) eps t
      (Nat.cast_nonneg n) hEps0 hEps1 hLarge ht
      (le_of_lt (lt_of_not_ge hNotL)) (le_of_lt (lt_of_not_ge hNotU))
    exact (not_lt_of_ge hBand) hEt
  have hInverse :
      gammaInverseAverage n
        (Set.indicator {s : Real | eps < abs (s - 1)} (fun _ => (1 : Real))) =
      gammaDirectAverage n (Set.indicator E (fun _ => (1 : Real))) := by
    rw [gammaInverseAverage_as_direct]
    congr 1
  have hDelta0 : 0 <= eps / 2 := div_nonneg (le_of_lt hEps0) (by norm_num)
  have hDelta1 : eps / 2 < 1 := by linarith only [hEps1]
  have hLower :
      gammaDirectAverage n (Set.indicator L (fun _ => (1 : Real))) <=
        Real.exp (-M * (eps / 2) ^ 2 / 4) :=
    gammaDirectAverage_lower_central n (eps / 2) hDelta0 hDelta1
  have hUpper :
      gammaDirectAverage n (Set.indicator U (fun _ => (1 : Real))) <=
        Real.exp (-M * (eps / 2) ^ 2 / 9) :=
    gammaDirectAverage_upper_central n (eps / 2) hDelta0 (le_of_lt hDelta1)
  have hM0 : 0 <= M := add_nonneg (Nat.cast_nonneg n) (by norm_num)
  have hLowerExp : Real.exp (-M * (eps / 2) ^ 2 / 4) <=
      Real.exp (-M * eps ^ 2 / 36) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hM0 (sq_nonneg eps)]
  have hUpperExp : Real.exp (-M * (eps / 2) ^ 2 / 9) =
      Real.exp (-M * eps ^ 2 / 36) := by
    congr 1
    ring
  calc
    _ = gammaDirectAverage n (Set.indicator E (fun _ => (1 : Real))) := hInverse
    _ <= gammaDirectAverage n (Set.indicator L (fun _ => (1 : Real))) +
          gammaDirectAverage n (Set.indicator U (fun _ => (1 : Real))) :=
      gammaDirectAverage_indicator_cover n E L U hE measurableSet_Iic measurableSet_Ici hCover
    _ <= Real.exp (-M * (eps / 2) ^ 2 / 4) +
          Real.exp (-M * (eps / 2) ^ 2 / 9) := add_le_add hLower hUpper
    _ <= Real.exp (-M * eps ^ 2 / 36) + Real.exp (-M * eps ^ 2 / 36) :=
      add_le_add hLowerExp (le_of_eq hUpperExp)
    _ = 2 * Real.exp (-M * eps ^ 2 / 36) := by ring

end PrimeFactorOscillations
