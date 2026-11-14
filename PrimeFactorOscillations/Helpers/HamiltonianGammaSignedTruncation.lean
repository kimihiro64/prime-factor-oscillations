/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.HamiltonianGammaInverseWindow
import PrimeFactorOscillations.Helpers.HamiltonianGammaMomentBounds

/-! # Signed inverse-Gamma truncation

The local determinant expansion must be averaged only on its central
window. These estimates bound the discarded tail while retaining the
signed first and third central moments. All averages use the actual
normalized Euler density; no concentration or moment premise is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def GammaInverseIntegrable (n : Nat) (f : Real -> Real) : Prop :=
  MeasureTheory.Integrable
    (fun t : Real => Real.exp (-t) * t ^ n * f ((n : Real) / t))
    gammaHalfLine

theorem gammaInverseAverage_add (n : Nat) (f g : Real -> Real)
    (hf : GammaInverseIntegrable n f) (hg : GammaInverseIntegrable n g) :
    gammaInverseAverage n (fun s => f s + g s) =
      gammaInverseAverage n f + gammaInverseAverage n g := by
  unfold gammaInverseAverage
  simp_rw [mul_add]
  rw [MeasureTheory.integral_add hf hg]
  ring

theorem gammaInverseAverage_smul (n : Nat) (a : Real) (f : Real -> Real) :
    gammaInverseAverage n (fun s => a * f s) =
      a * gammaInverseAverage n f := by
  unfold gammaInverseAverage
  have hFun : (fun t : Real =>
      Real.exp (-t) * t ^ n * (a * f ((n : Real) / t))) =
      (fun t : Real => a * (Real.exp (-t) * t ^ n * f ((n : Real) / t))) := by
    funext t
    ring
  rw [hFun, MeasureTheory.integral_const_mul]
  ring

theorem gammaInverseAverage_mono (n : Nat) (f g : Real -> Real)
    (hf : GammaInverseIntegrable n f) (hg : GammaInverseIntegrable n g)
    (hfg : forall s, 0 <= s -> f s <= g s) :
    gammaInverseAverage n f <= gammaInverseAverage n g := by
  unfold gammaInverseAverage
  apply mul_le_mul_of_nonneg_left
    (MeasureTheory.integral_mono_ae hf hg _)
    (inv_nonneg.mpr (Nat.cast_nonneg n.factorial))
  apply (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  have hw : 0 <= Real.exp (-t) * t ^ n :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (pow_nonneg (le_of_lt ht) n)
  exact mul_le_mul_of_nonneg_left
    (hfg _ (div_nonneg (Nat.cast_nonneg n) (le_of_lt ht))) hw

theorem gammaInverseIntegrable_indicator (n : Nat) (f : Real -> Real)
    (hf : GammaInverseIntegrable n f) (E : Set Real) (hE : MeasurableSet E) :
    GammaInverseIntegrable n (Set.indicator E f) := by
  have hm : Measurable (fun t : Real => (n : Real) / t) :=
    measurable_const.div measurable_id
  have hFun : (fun t : Real => Real.exp (-t) * t ^ n *
      Set.indicator E f ((n : Real) / t)) =
      Set.indicator (Set.preimage (fun t : Real => (n : Real) / t) E)
        (fun t : Real => Real.exp (-t) * t ^ n * f ((n : Real) / t)) := by
    funext t
    by_cases ht : Membership.mem E ((n : Real) / t)
    case pos => simp [Set.indicator, ht]
    case neg => simp [Set.indicator, ht]
  unfold GammaInverseIntegrable
  rw [hFun]
  exact hf.indicator (hE.preimage hm)

private theorem real_power_mono_nonnegative (a b : Real) (ha : 0 <= a)
    (hab : a <= b) (j : Nat) : a ^ j <= b ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (pow_nonneg (le_trans ha hab) j)

theorem abs_centered_pow_le (s : Real) (hs : 0 <= s) (j : Nat) :
    abs (s - 1) ^ j <= s ^ j + 1 := by
  by_cases h : 1 <= s
  case pos =>
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hPow : (s - 1) ^ j <= s ^ j :=
      real_power_mono_nonnegative (s - 1) s (sub_nonneg.mpr h) (by linarith) j
    linarith
  case neg =>
    have hS : s <= 1 := le_of_lt (lt_of_not_ge h)
    rw [abs_of_nonpos (sub_nonpos.mpr hS)]
    have hPow : (-(s - 1)) ^ j <= (1 : Real) ^ j :=
      real_power_mono_nonnegative (-(s - 1)) 1 (by linarith) (by linarith) j
    have hOther : 0 <= s ^ j := pow_nonneg hs j
    simp only [one_pow] at hPow
    linarith

theorem gammaInverseIntegrable_add (n : Nat) (f g : Real -> Real)
    (hf : GammaInverseIntegrable n f) (hg : GammaInverseIntegrable n g) :
    GammaInverseIntegrable n (fun s => f s + g s) := by
  unfold GammaInverseIntegrable at *
  have hInt := hf.add hg
  change MeasureTheory.Integrable (fun t : Real =>
    Real.exp (-t) * t ^ n * f ((n : Real) / t) +
      Real.exp (-t) * t ^ n * g ((n : Real) / t)) gammaHalfLine at hInt
  simpa only [mul_add] using hInt

theorem gammaInverseIntegrable_smul (n : Nat) (a : Real) (f : Real -> Real)
    (hf : GammaInverseIntegrable n f) :
    GammaInverseIntegrable n (fun s => a * f s) := by
  have hFun : (fun t : Real =>
      Real.exp (-t) * t ^ n * (a * f ((n : Real) / t))) =
      (fun t : Real => a * (Real.exp (-t) * t ^ n * f ((n : Real) / t))) := by
    funext t
    ring
  unfold GammaInverseIntegrable
  rw [hFun]
  exact hf.const_mul a

theorem gammaInverseIntegrable_const (n : Nat) (a : Real) :
    GammaInverseIntegrable n (fun _ => a) := by
  unfold GammaInverseIntegrable
  simpa only [mul_comm] using (gammaKernel_integrable n).const_mul a

theorem gammaInverseAverage_const (n : Nat) (a : Real) :
    gammaInverseAverage n (fun _ => a) = a := by
  calc
    _ = gammaInverseAverage n (fun s : Real => a * s ^ 0) := by
      congr 1
      funext s
      ring
    _ = a * gammaInverseAverage n (fun s : Real => s ^ 0) :=
      gammaInverseAverage_smul n a (fun s : Real => s ^ 0)
    _ = a := by rw [gammaInverseAverage_pow_zero]; ring

theorem gammaInverseAverage_abs_le (n : Nat) (f g : Real -> Real)
    (hg : GammaInverseIntegrable n g)
    (hfg : forall s, 0 <= s -> abs (f s) <= g s) :
    abs (gammaInverseAverage n f) <= gammaInverseAverage n g := by
  have hFactor : 0 <= Inv.inv (n.factorial : Real) :=
    inv_nonneg.mpr (Nat.cast_nonneg n.factorial)
  unfold gammaInverseAverage
  rw [abs_mul, abs_of_nonneg hFactor]
  apply mul_le_mul_of_nonneg_left _ hFactor
  change norm (MeasureTheory.integral gammaHalfLine
      (fun t : Real => Real.exp (-t) * t ^ n * f ((n : Real) / t))) <= _
  apply MeasureTheory.norm_integral_le_of_norm_le hg
  apply (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  have hw : 0 <= Real.exp (-t) * t ^ n :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (pow_nonneg (le_of_lt ht) n)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left
    (hfg _ (div_nonneg (Nat.cast_nonneg n) (le_of_lt ht))) hw

theorem gammaInverseIntegrable_of_power_bound (n j : Nat) (hj : j <= n)
    (f : Real -> Real) (hf : Measurable f)
    (hBound : forall s, 0 <= s -> abs (f s) <= s ^ j + 1) :
    GammaInverseIntegrable n f := by
  have hInt : GammaInverseIntegrable n (fun s : Real => s ^ j + 1) :=
    gammaInverseIntegrable_add n _ _ (gammaInversePower_integrable n j hj)
      (gammaInverseIntegrable_const n 1)
  have hm : Measurable (fun t : Real =>
      Real.exp (-t) * t ^ n * f ((n : Real) / t)) :=
    ((Real.continuous_exp.measurable.comp measurable_id.neg).mul
      (measurable_id.pow_const n)).mul
        (hf.comp (measurable_const.div measurable_id))
  apply hInt.mono' hm.aestronglyMeasurable
  apply (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  have hw : 0 <= Real.exp (-t) * t ^ n :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (pow_nonneg (le_of_lt ht) n)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left
    (hBound _ (div_nonneg (Nat.cast_nonneg n) (le_of_lt ht))) hw

theorem gammaInverseIntegrable_centered (n k : Nat) (hk : k <= n) :
    GammaInverseIntegrable n (fun s : Real => (s - 1) ^ k) := by
  have hm : Measurable (fun s : Real => s - 1) :=
    measurable_sub_const (1 : Real)
  apply gammaInverseIntegrable_of_power_bound n k hk
    (fun s : Real => (s - 1) ^ k) (hm.pow_const k)
  intro s hs
  simpa only [abs_pow] using abs_centered_pow_le s hs k

theorem gammaInverseIntegrable_abs_centered (n k : Nat) (hk : k <= n) :
    GammaInverseIntegrable n (fun s : Real => abs (s - 1) ^ k) := by
  have hm : Measurable (fun s : Real => abs (s - 1)) := by
    simpa only [Real.norm_eq_abs] using (measurable_sub_const (1 : Real)).norm
  apply gammaInverseIntegrable_of_power_bound n k hk _ (hm.pow_const k)
  intro s hs
  rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) k)]
  exact abs_centered_pow_le s hs k

theorem gammaInverseAverage_abs_centered_le (n k : Nat) (hk : 2 * k <= n) :
    gammaInverseAverage n (fun s : Real => abs (s - 1) ^ k) <=
      (2 : Real) ^ k + 1 := by
  have hkN : k <= n := by omega
  have hInt : GammaInverseIntegrable n (fun s : Real => s ^ k + 1) :=
    gammaInverseIntegrable_add n _ _ (gammaInversePower_integrable n k hkN)
      (gammaInverseIntegrable_const n 1)
  have hLe := gammaInverseAverage_mono n
    (fun s : Real => abs (s - 1) ^ k) (fun s : Real => s ^ k + 1)
    (gammaInverseIntegrable_abs_centered n k hkN) hInt
    (fun s hs => abs_centered_pow_le s hs k)
  have hEq : gammaInverseAverage n (fun s : Real => s ^ k + 1) =
      gammaInverseAverage n (fun s : Real => s ^ k) + 1 := by
    simpa only [gammaInverseAverage_const] using gammaInverseAverage_add n
      (fun s : Real => s ^ k) (fun _ : Real => 1)
      (gammaInversePower_integrable n k hkN) (gammaInverseIntegrable_const n 1)
  rw [hEq] at hLe
  have hRaw := gammaInverseAverage_pow_le_two_pow n k hk
  linarith only [hLe, hRaw]

theorem gammaInverseAverage_abs_centered_tail (n k : Nat) (hk : 4 * k <= n)
    (eps : Real) (hEps0 : 0 < eps) (hEps1 : eps <= 1 / 2)
    (hLarge : 4 <= (n : Real) * eps) :
    gammaInverseAverage n
      (Set.indicator {s : Real | eps < abs (s - 1)}
        (fun s : Real => abs (s - 1) ^ k)) <=
      Real.exp (-((n : Real) + 1) * eps ^ 2 / 72) *
        ((2 : Real) ^ (2 * k) + 3) := by
  let E : Set Real := {s | eps < abs (s - 1)}
  let a : Real := Real.exp (-((n : Real) + 1) * eps ^ 2 / 72)
  have ha : 0 < a := Real.exp_pos _
  have hMap : Measurable (fun s : Real => abs (s - 1)) := by
    simpa only [Real.norm_eq_abs] using (measurable_sub_const (1 : Real)).norm
  have hE : MeasurableSet E := measurableSet_lt measurable_const hMap
  have hkN : k <= n := by omega
  have hDoubleN : 2 * k <= n := by omega
  have hTailInt := gammaInverseIntegrable_indicator n
    (fun s : Real => abs (s - 1) ^ k)
    (gammaInverseIntegrable_abs_centered n k hkN) E hE
  have hMassInt := gammaInverseIntegrable_indicator n (fun _ : Real => 1)
    (gammaInverseIntegrable_const n 1) E hE
  have hBigInt := gammaInverseIntegrable_abs_centered n (2 * k) hDoubleN
  have hScaledInt := gammaInverseIntegrable_smul n (a ^ 2)
    (fun s : Real => abs (s - 1) ^ (2 * k)) hBigInt
  have hDomInt := gammaInverseIntegrable_add n _ _ hScaledInt hMassInt
  have hPoint : forall s : Real, 0 <= s ->
      a * Set.indicator E (fun z : Real => abs (z - 1) ^ k) s <=
        a ^ 2 * abs (s - 1) ^ (2 * k) +
          Set.indicator E (fun _ : Real => 1) s := by
    intro s hs
    by_cases hsE : Membership.mem E s
    case pos =>
      simp only [Set.indicator_of_mem hsE]
      have hy0 : 0 <= a * abs (s - 1) ^ k :=
        mul_nonneg (le_of_lt ha) (pow_nonneg (abs_nonneg _) k)
      have hPow : (abs (s - 1) ^ k) ^ 2 = abs (s - 1) ^ (2 * k) := by
        rw [<- pow_mul, Nat.mul_comm k 2]
      have hSq := sq_nonneg (a * abs (s - 1) ^ k - 1)
      rw [sub_sq, mul_pow, hPow] at hSq
      nlinarith only [hSq, hy0]
    case neg =>
      simp only [Set.indicator_of_notMem hsE, mul_zero, add_zero]
      exact mul_nonneg (sq_nonneg a) (pow_nonneg (abs_nonneg _) (2 * k))
  have hScale := gammaInverseAverage_mono n
    (fun s : Real => a * Set.indicator E (fun z : Real => abs (z - 1) ^ k) s)
    (fun s : Real => a ^ 2 * abs (s - 1) ^ (2 * k) +
      Set.indicator E (fun _ : Real => 1) s)
    (gammaInverseIntegrable_smul n a _ hTailInt) hDomInt hPoint
  rw [gammaInverseAverage_add n
    (fun s : Real => a ^ 2 * abs (s - 1) ^ (2 * k))
    (Set.indicator E (fun _ : Real => 1)) hScaledInt hMassInt,
    gammaInverseAverage_smul, gammaInverseAverage_smul] at hScale
  have hRaw := gammaInverseAverage_abs_centered_le n (2 * k) (by omega)
  have hRawScaled := mul_le_mul_of_nonneg_left hRaw (sq_nonneg a)
  have hMass := gammaInverseAverage_outside_window n eps hEps0 hEps1 hLarge
  have hExp : a ^ 2 = Real.exp (-((n : Real) + 1) * eps ^ 2 / 36) := by
    dsimp [a]
    rw [pow_two, <- Real.exp_add]
    congr 1
    ring
  rw [<- hExp] at hMass
  have hFinal :
      a * gammaInverseAverage n
        (Set.indicator E (fun s : Real => abs (s - 1) ^ k)) <=
      a * (a * ((2 : Real) ^ (2 * k) + 3)) := by
    nlinarith only [hScale, hRawScaled, hMass]
  have hCancel : gammaInverseAverage n
      (Set.indicator E (fun s : Real => abs (s - 1) ^ k)) <=
      a * ((2 : Real) ^ (2 * k) + 3) := by
    by_contra hNot
    exact (not_lt_of_ge hFinal)
      (mul_lt_mul_of_pos_left (lt_of_not_ge hNot) ha)
  exact hCancel

theorem gammaInverseAverage_signed_window_error (n k : Nat) (hk : 4 * k <= n)
    (eps : Real) (hEps0 : 0 < eps) (hEps1 : eps <= 1 / 2)
    (hLarge : 4 <= (n : Real) * eps) :
    abs (gammaInverseAverage n (fun s : Real => (s - 1) ^ k) -
      gammaInverseAverage n
        (Set.indicator {s : Real | abs (s - 1) <= eps}
          (fun s : Real => (s - 1) ^ k))) <=
      Real.exp (-((n : Real) + 1) * eps ^ 2 / 72) *
        ((2 : Real) ^ (2 * k) + 3) := by
  let C : Set Real := {s | abs (s - 1) <= eps}
  let E : Set Real := {s | eps < abs (s - 1)}
  have hMap : Measurable (fun s : Real => abs (s - 1)) := by
    simpa only [Real.norm_eq_abs] using (measurable_sub_const (1 : Real)).norm
  have hC : MeasurableSet C := measurableSet_le hMap measurable_const
  have hE : MeasurableSet E := measurableSet_lt measurable_const hMap
  have hkN : k <= n := by omega
  have hInt := gammaInverseIntegrable_centered n k hkN
  have hCoreInt := gammaInverseIntegrable_indicator n
    (fun s : Real => (s - 1) ^ k) hInt C hC
  have hTailInt := gammaInverseIntegrable_indicator n
    (fun s : Real => (s - 1) ^ k) hInt E hE
  have hFun : (fun s : Real => (s - 1) ^ k) =
      (fun s : Real => Set.indicator C (fun z : Real => (z - 1) ^ k) s +
        Set.indicator E (fun z : Real => (z - 1) ^ k) s) := by
    funext s
    by_cases hsE : eps < abs (s - 1)
    case pos =>
      have hsC : Not (abs (s - 1) <= eps) := not_le_of_gt hsE
      simp [C, E, Set.indicator, hsC, hsE]
    case neg =>
      have hsC : abs (s - 1) <= eps := le_of_not_gt hsE
      simp [C, E, Set.indicator, hsC, hsE]
  have hSplit := congrArg (gammaInverseAverage n) hFun
  rw [gammaInverseAverage_add n
    (Set.indicator C (fun s : Real => (s - 1) ^ k))
    (Set.indicator E (fun s : Real => (s - 1) ^ k)) hCoreInt hTailInt] at hSplit
  have hDiff : gammaInverseAverage n (fun s : Real => (s - 1) ^ k) -
      gammaInverseAverage n (Set.indicator C (fun s : Real => (s - 1) ^ k)) =
      gammaInverseAverage n (Set.indicator E (fun s : Real => (s - 1) ^ k)) := by
    linarith only [hSplit]
  change abs (gammaInverseAverage n (fun s : Real => (s - 1) ^ k) -
    gammaInverseAverage n (Set.indicator C (fun s : Real => (s - 1) ^ k))) <= _
  rw [hDiff]
  have hAbs := gammaInverseAverage_abs_le n
    (Set.indicator E (fun s : Real => (s - 1) ^ k))
    (Set.indicator E (fun s : Real => abs (s - 1) ^ k))
    (gammaInverseIntegrable_indicator n _ (gammaInverseIntegrable_abs_centered n k hkN) E hE)
    (by
      intro s hs
      by_cases hsE : Membership.mem E s
      case pos => simp only [Set.indicator_of_mem hsE, abs_pow]; exact le_rfl
      case neg => simp only [Set.indicator_of_notMem hsE, abs_zero]; exact le_rfl)
  exact le_trans hAbs
    (gammaInverseAverage_abs_centered_tail n k hk eps hEps0 hEps1 hLarge)

end PrimeFactorOscillations
