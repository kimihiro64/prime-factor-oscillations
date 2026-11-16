/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBalancedCutRepair

/-! # Full uniform balanced-cut repair from the vanishing log-fifth cap

The actual finite counts and positive witnesses are packaged together.
The eventual statement quantifies over every matrix at each scale and
every distinct endpoint pair, retaining the full original support.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def HamiltonianBalancedCutRepairAtCap (m : Nat) (alpha A delta : Real) : Prop :=
  forall (P : Matrix (Fin (2 * m)) (Fin (2 * m)) Real),
    P.transpose = P ->
    (forall i, Finset.univ.sum (fun j => P i j) = 1) ->
    (forall i j, 0 <= P i j) ->
    (forall i j, P i j <= alpha) ->
    norm (centeredKernel P (1 / (Fintype.card (Fin (2 * m)) : Real))) <= 1 - delta ->
    let B := hamiltonianJointCutBadSigns
      (centeredKernel P (1 / (Fintype.card (Fin (2 * m)) : Real))) P alpha A
    ((1 - (Fintype.card (Fin (2 * m)) : Real) ^ (-A)) *
        ((hamiltonianBalancedSigns (I := Fin (2 * m)) m).card : Real) <=
      ((SDiff.sdiff (hamiltonianBalancedSigns (I := Fin (2 * m)) m) B).card : Real)) /\
    (forall a b : Fin (2 * m), Not (a = b) ->
      (1 - (Fintype.card (Fin (2 * m)) : Real) ^ (-A)) *
        ((hamiltonianPrescribedBalancedSigns m a b).card : Real) <=
      ((SDiff.sdiff (hamiltonianPrescribedBalancedSigns m a b) B).card : Real)) /\
    forall (e : Fin (2 * m) -> Bool) (hBalanced : (hamiltonianSignCut e).card = m),
      Not (Membership.mem B e) ->
    let l := hamiltonianBalancedLeftCoordinates e m hBalanced
    let r := hamiltonianBalancedRightCoordinates e m hBalanced (by simp only [Fintype.card_fin])
    let T := hamiltonianBalancedCrossBlock P e l r
    let eps := Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card (Fin (2 * m)) : Real)))
    let K := hamiltonianNormalizedScalingCost (delta / 2) *
      eps * Real.log (4 * ((Fintype.card (Fin (2 * m)) : Real) * alpha))
    exists z : Sum (Fin m) (Fin m) -> Real,
      norm z <= K /\
      (forall i, 0 < 1 + z i) /\
      (forall i j, 0 <= hamiltonianScaledCross T z i j) /\
      (forall i, Finset.univ.sum (fun j => hamiltonianScaledCross T z i j) = 1) /\
      (forall j, Finset.univ.sum (fun i => hamiltonianScaledCross T z i j) = 1) /\
      (forall i j, hamiltonianScaledCross T z i j = 0 <-> T i j = 0) /\
      (forall i j, hamiltonianScaledCross T z i j <= 4 * alpha) /\
      norm (hamiltonianScaledCross T z - T) <= K /\
      norm (centeredKernel (hamiltonianScaledCross T z)
        (1 / (Fintype.card (Fin m) : Real))) <= 1 - delta / 2

theorem hamiltonian_full_finite_balanced_cut_repair
    (m : Nat) (hm : 1 <= m) (alpha A delta : Real)
    (ha0 : 0 <= alpha) (ha1 : alpha <= 1) (hA : 0 < A)
    (hd0 : 0 < delta) (hd1 : delta <= 1)
    (hBudget : alpha * Real.log (2 * (Fintype.card (Fin (2 * m)) : Real)) ^ 5 <=
      hamiltonianBalancedCutBudget delta A) :
    HamiltonianBalancedCutRepairAtCap m alpha A delta := by
  letI : NeZero m := NeZero.mk (by omega)
  letI : NeZero (2 * m) := NeZero.mk (by omega)
  intro P hP hRows hNonneg hCap hNorm
  have hnPos : 0 < (Fintype.card (Fin (2 * m)) : Real) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hq : (Fintype.card (Fin (2 * m)) : Real) *
      (1 / (Fintype.card (Fin (2 * m)) : Real)) = 1 := by
    field_simp [ne_of_gt hnPos]
  have hNorm1 : norm (centeredKernel P (1 / (Fintype.card (Fin (2 * m)) : Real))) <= 1 :=
    hNorm.trans (by linarith only [hd0])
  have hSize : Fintype.card (Fin (2 * m)) = 2 * m := Fintype.card_fin _
  refine And.intro ?_ (And.intro ?_ ?_)
  . exact hamiltonian_actual_balanced_good_cut_count P _ alpha A hq hP hRows
      hNonneg hCap ha0 hA hNorm1 m hm hSize
  . intro a b hab
    exact hamiltonian_actual_prescribed_good_cut_count P _ alpha A hq hP hRows
      hNonneg hCap ha0 hA hNorm1 a b hab m hm hSize
  . intro e hBalanced hGood
    let l := hamiltonianBalancedLeftCoordinates e m hBalanced
    let r := hamiltonianBalancedRightCoordinates e m hBalanced hSize
    exact hamiltonian_small_cap_actual_cut_scaling P alpha A delta e l r
      hP hRows hNonneg hCap
      (by simp only [Fintype.card_fin]) hd0 hd1 hNorm ha0 ha1 hA
      (by simp only [Fintype.card_fin]; omega) hBudget hGood

theorem hamiltonian_eventual_balanced_cut_repair
    (alpha : Nat -> Real) (A delta : Real)
    (ha0 : forall m, 0 <= alpha m) (ha1 : forall m, alpha m <= 1)
    (hA : 0 < A) (hd0 : 0 < delta) (hd1 : delta <= 1)
    (hLimit : Filter.Tendsto
      (fun m => alpha m * Real.log (2 * (Fintype.card (Fin (2 * m)) : Real)) ^ 5)
      Filter.atTop (nhds (0 : Real))) :
    Filter.Eventually (fun m => HamiltonianBalancedCutRepairAtCap m (alpha m) A delta)
      Filter.atTop := by
  have hPos := hamiltonian_balanced_cut_budget_positive delta A hd0 hd1 hA
  have hBudget := (tendsto_order.1 hLimit).2 (hamiltonianBalancedCutBudget delta A) hPos
  have hM : Filter.Eventually (fun m : Nat => 1 <= m) Filter.atTop :=
    Filter.eventually_ge_atTop 1
  exact Filter.Eventually.mono (Filter.Eventually.and hBudget hM) (fun m hm =>
    hamiltonian_full_finite_balanced_cut_repair m hm.2 (alpha m) A delta
      (ha0 m) (ha1 m) hA hd0 hd1 (le_of_lt hm.1))

end PrimeFactorOscillations
