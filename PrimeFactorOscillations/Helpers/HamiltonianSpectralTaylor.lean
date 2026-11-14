/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import PrimeFactorOscillations.Helpers.HamiltonianGammaTaylor
import PrimeFactorOscillations.Helpers.HamiltonianSpectralFactorFourth

/-! # The actual spectral-factor Taylor and Gamma consumer

Local differentiability is proved off the finitely many singular
denominators. The successive explicit derivatives agree with Lean's
iterated derivatives. The finite smoothness order is four throughout.
These statements discharge the analytic averaging hypotheses rather than
postulating the determinant-average estimate itself.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*}

private theorem spectralDenominator_contDiff (lam : Real) :
    ContDiff Real 4 (fun x : Real => 1 - x ^ 2 * lam) := by
  have hPow : ContDiff Real 4 (fun x : Real => x ^ 2) := contDiff_id.pow 2
  exact contDiff_const.sub (hPow.mul contDiff_const)

theorem spectralFactors_contDiffAt (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hDen : forall i, Membership.mem S i -> Not (1 - s ^ 2 * lam i = 0)) :
    ContDiffAt Real 4 (spectralFactors S lam) s := by
  have hCoord : forall i, Membership.mem S i ->
      ContDiffAt Real 4 (spectralCoordinate0 (lam i)) s := by
    intro i hi
    unfold spectralCoordinate0
    have hLog : ContDiffAt Real 4
        (fun x : Real => Real.log (1 - x ^ 2 * lam i)) s :=
      ((spectralDenominator_contDiff (lam i)).contDiffAt).log (hDen i hi)
    exact contDiffAt_const.mul hLog
  have hLog : ContDiffAt Real 4 (spectralLogFactors S lam) s :=
    ContDiffAt.sum (fun i hi => hCoord i hi)
  exact hLog.exp

theorem spectralFactors_measurable (S : Finset Iota) (lam : Iota -> Real) :
    Measurable (spectralFactors S lam) := by
  have hCoord : forall i, Membership.mem S i -> Measurable (spectralCoordinate0 (lam i)) := by
    intro i hi
    unfold spectralCoordinate0
    exact measurable_const.mul
      (Real.measurable_log.comp (spectralDenominator_contDiff (lam i)).continuous.measurable)
  have hLog : Measurable (spectralLogFactors S lam) :=
    Finset.measurable_sum S (fun i hi => hCoord i hi)
  exact Real.measurable_exp.comp hLog

theorem spectralDenominators_eventually (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hDen : forall i, Membership.mem S i -> Not (1 - s ^ 2 * lam i = 0)) :
    Filter.Eventually
      (fun y : Real => forall i, Membership.mem S i -> Not (1 - y ^ 2 * lam i = 0))
      (nhds s) := by
  apply (Filter.eventually_all_finset S).mpr
  intro i hi
  exact (spectralDenominator_contDiff (lam i)).continuous.continuousAt.eventually_ne (hDen i hi)

theorem spectralFactors_iterated_one (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hDen : forall i, Membership.mem S i -> Not (1 - s ^ 2 * lam i = 0)) :
    iteratedDeriv 1 (spectralFactors S lam) s = spectralFactorJet1 S lam s := by
  rw [iteratedDeriv_one]
  exact (spectralFactors_hasDerivAt S lam s hDen).deriv

theorem spectralFactors_iterated_two (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hDen : forall i, Membership.mem S i -> Not (1 - s ^ 2 * lam i = 0)) :
    iteratedDeriv 2 (spectralFactors S lam) s = spectralFactorJet2 S lam s := by
  have hEq := (spectralDenominators_eventually S lam s hDen).mono
    (fun y hy => spectralFactors_iterated_one S lam y hy)
  rw [iteratedDeriv_succ (n := 1)]
  exact (Filter.EventuallyEq.deriv_eq hEq).trans
    (spectralFactorJet1_hasDerivAt S lam s hDen).deriv

theorem spectralFactors_iterated_three (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hDen : forall i, Membership.mem S i -> Not (1 - s ^ 2 * lam i = 0)) :
    iteratedDeriv 3 (spectralFactors S lam) s = spectralFactorJet3 S lam s := by
  have hEq := (spectralDenominators_eventually S lam s hDen).mono
    (fun y hy => spectralFactors_iterated_two S lam y hy)
  rw [iteratedDeriv_succ (n := 2)]
  exact (Filter.EventuallyEq.deriv_eq hEq).trans
    (spectralFactorJet2_hasDerivAt S lam s hDen).deriv

theorem spectralFactors_iterated_four (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hDen : forall i, Membership.mem S i -> Not (1 - s ^ 2 * lam i = 0)) :
    iteratedDeriv 4 (spectralFactors S lam) s = spectralFactorJet4 S lam s := by
  have hEq := (spectralDenominators_eventually S lam s hDen).mono
    (fun y hy => spectralFactors_iterated_three S lam y hy)
  rw [iteratedDeriv_succ (n := 3)]
  exact (Filter.EventuallyEq.deriv_eq hEq).trans
    (spectralFactorJet3_hasDerivAt S lam s hDen).deriv

def spectralTaylorCubic (S : Finset Iota) (lam : Iota -> Real) (s : Real) : Real :=
  gammaCubic (spectralFactors S lam 1) (spectralFactorJet1 S lam 1)
    (spectralFactorJet2 S lam 1 / 2) (spectralFactorJet3 S lam 1 / 6) s

def spectralTaylorRemainderBound (S : Finset Iota) (lam : Iota -> Real) (delta : Real) : Real :=
  2049 * Real.exp 1 * spectralFactors S lam 1 *
    (1 + Finset.sum S lam) ^ 4 / (24 * delta ^ 4)

theorem spectralTaylorWithin_eq (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hNE : Not ((1 : Real) = s))
    (hDen : forall i, Membership.mem S i -> Not (1 - (1 : Real) ^ 2 * lam i = 0)) :
    taylorWithinEval (spectralFactors S lam) 3 (Set.uIcc 1 s) 1 s =
      spectralTaylorCubic S lam s := by
  have hUnique := uniqueDiffOn_uIcc hNE
  have hMem : Membership.mem (Set.uIcc (1 : Real) s) (1 : Real) :=
    And.intro (min_le_left _ _) (le_max_left _ _)
  have hSmooth := spectralFactors_contDiffAt S lam 1 hDen
  have hW1 : iteratedDerivWithin 1 (spectralFactors S lam) (Set.uIcc 1 s) 1 =
      spectralFactorJet1 S lam 1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 1) hUnique
      (hSmooth.of_le (by norm_num)) hMem]
    exact spectralFactors_iterated_one S lam 1 hDen
  have hW2 : iteratedDerivWithin 2 (spectralFactors S lam) (Set.uIcc 1 s) 1 =
      spectralFactorJet2 S lam 1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 2) hUnique
      (hSmooth.of_le (by norm_num)) hMem]
    exact spectralFactors_iterated_two S lam 1 hDen
  have hW3 : iteratedDerivWithin 3 (spectralFactors S lam) (Set.uIcc 1 s) 1 =
      spectralFactorJet3 S lam 1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 3) hUnique
      (hSmooth.of_le (by norm_num)) hMem]
    exact spectralFactors_iterated_three S lam 1 hDen
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, hW1, hW2, hW3,
    spectralTaylorCubic, gammaCubic, smul_eq_mul] <;> ring

theorem spectralWindow_uIcc (eps s x : Real) (hs : abs (s - 1) <= eps)
    (hx : Membership.mem (Set.uIcc (1 : Real) s) x) :
    abs (x - 1) <= eps := by
  have hRange := abs_le.mp hs
  apply abs_le.mpr
  by_cases hOrder : (1 : Real) <= s
  case pos =>
    rw [Set.uIcc_of_le hOrder] at hx
    exact And.intro (by linarith only [hx.1, hRange.1, hRange.2])
      (by linarith only [hx.2, hRange.2])
  case neg =>
    have hOrder' : s <= (1 : Real) := le_of_lt (lt_of_not_ge hOrder)
    rw [Set.uIcc_of_ge hOrder'] at hx
    exact And.intro (by linarith only [hx.1, hRange.1])
      (by linarith only [hx.2, hRange.1, hRange.2])

theorem spectralFactors_taylor_remainder (S : Finset Iota) (lam : Iota -> Real)
    (delta eps s : Real) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hEps0 : 0 <= eps) (hEps1 : eps <= delta / 4)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hSmall : 2 * (Finset.sum S lam) * eps <= delta)
    (hs : abs (s - 1) <= eps) :
    abs (spectralFactors S lam s - spectralTaylorCubic S lam s) <=
      spectralTaylorRemainderBound S lam delta * (s - 1) ^ 4 := by
  by_cases hsOne : s = 1
  case pos =>
    subst s
    simp [spectralTaylorCubic, gammaCubic]
  case neg =>
    have hNE : Not ((1 : Real) = s) := fun h => hsOne h.symm
    have hDen : forall x : Real, Membership.mem (Set.uIcc (1 : Real) s) x ->
        forall i, Membership.mem S i -> Not (1 - x ^ 2 * lam i = 0) := by
      intro x hx i hi
      have hStrip := spectralFactor_strip delta eps (lam i) x hDelta0 hDelta1
        hEps0 hEps1 (hLam0 i hi) (hLam1 i hi) (spectralWindow_uIcc eps s x hs hx)
      exact ne_of_gt (lt_of_lt_of_le hDelta0 hStrip.2.2.2)
    have hSmooth : ContDiffOn Real 4 (spectralFactors S lam) (Set.uIcc 1 s) :=
      fun x hx => (spectralFactors_contDiffAt S lam x (hDen x hx)).contDiffWithinAt
    have hDenOne := hDen 1 (And.intro (min_le_left _ _) (le_max_left _ _))
    have hTaylor := spectralTaylorWithin_eq S lam s hNE hDenOne
    have hRem := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := spectralFactors S lam) (n := 3) hNE hSmooth
    cases hRem with
    | intro y hy =>
      have hyClosed : Membership.mem (Set.uIcc (1 : Real) s) y :=
        And.intro (le_of_lt hy.1.1) (le_of_lt hy.1.2)
      have hyWindow := spectralWindow_uIcc eps s y hs hyClosed
      have hEq := hy.2
      norm_num only [Nat.factorial, Nat.cast_ofNat] at hEq
      rw [hTaylor, spectralFactors_iterated_four S lam y (hDen y hyClosed)] at hEq
      have hBound := spectralFactorJet4_central_bound S lam delta eps y
        hDelta0 hDelta1 hEps0 hEps1 hLam0 hLam1 hSmall hyWindow
      have hPow : 0 <= (s - 1) ^ 4 := by positivity
      have hMul := mul_le_mul_of_nonneg_right hBound hPow
      have hDiv := mul_le_mul_of_nonneg_right hMul
        (by norm_num : (0 : Real) <= Inv.inv 24)
      calc
        _ = abs (spectralFactorJet4 S lam y) * (s - 1) ^ 4 / 24 := by
          rw [hEq, abs_div, abs_mul, abs_of_nonneg hPow]
          norm_num
        _ <= ((2049 * Real.exp 1 * spectralFactors S lam 1 *
            (1 + Finset.sum S lam) ^ 4) / delta ^ 4) * (s - 1) ^ 4 / 24 := by
          simpa only [div_eq_mul_inv] using hDiv
        _ = _ := by
          unfold spectralTaylorRemainderBound
          field_simp [ne_of_gt hDelta0] <;> ring

def spectralTaylorTailCoefficient (S : Finset Iota) (lam : Iota -> Real) : Real :=
  4 * abs (spectralFactors S lam 1) + 7 * abs (spectralFactorJet1 S lam 1) +
    19 * abs (spectralFactorJet2 S lam 1 / 2) + 67 * abs (spectralFactorJet3 S lam 1 / 6)

theorem spectralFactors_gamma_window (S : Finset Iota) (lam : Iota -> Real)
    (n : Nat) (hn : 16 <= n) (delta eps : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hEps0 : 0 < eps) (hEpsHalf : eps <= 1 / 2) (hEps1 : eps <= delta / 4)
    (hLarge : 4 <= (n : Real) * eps)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hSmall : 2 * (Finset.sum S lam) * eps <= delta) :
    abs (gammaInverseAverage n
        (Set.indicator {s : Real | abs (s - 1) <= eps} (spectralFactors S lam)) -
      (spectralFactors S lam 1 +
        (spectralFactorJet2 S lam 1 / 2) / ((n : Real) - 1) +
        4 * (spectralFactorJet3 S lam 1 / 6) /
          (((n : Real) - 1) * ((n : Real) - 2)))) <=
      spectralTaylorRemainderBound S lam delta *
        (3 * ((n : Real) + 6) /
          (((n : Real) - 1) * ((n : Real) - 2) * ((n : Real) - 3))) +
      Real.exp (-((n : Real) + 1) * eps ^ 2 / 72) *
        spectralTaylorTailCoefficient S lam := by
  have hPos : 0 < spectralFactors S lam 1 := Real.exp_pos _
  have hM : 0 <= spectralTaylorRemainderBound S lam delta := by
    unfold spectralTaylorRemainderBound
    positivity
  exact gammaInverseAverage_local_cubic_of_measurable n hn eps hEps0 hEpsHalf hLarge
    (spectralFactors S lam) (spectralFactors_measurable S lam)
    (spectralFactors S lam 1) (spectralFactorJet1 S lam 1)
    (spectralFactorJet2 S lam 1 / 2) (spectralFactorJet3 S lam 1 / 6)
    (spectralTaylorRemainderBound S lam delta) hM
    (fun s hs => spectralFactors_taylor_remainder S lam delta eps s
      hDelta0 hDelta1 (le_of_lt hEps0) hEps1 hLam0 hLam1 hSmall hs)

end PrimeFactorOscillations
