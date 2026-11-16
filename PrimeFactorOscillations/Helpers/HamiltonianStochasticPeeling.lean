/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.HamiltonianStochasticMatching

/-! # Exact stochastic peeling with a strictly smaller positive support -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianPermutationCross (f : Equiv.Perm Iota) : Matrix Iota Iota Real :=
  fun i j => if j = f i then 1 else 0

def hamiltonianPositiveCrossSupport (P : Matrix Iota Iota Real) :
    Finset (Prod Iota Iota) :=
  Finset.univ.filter (fun e => 0 < P e.1 e.2)

def hamiltonianStochasticPeel (P : Matrix Iota Iota Real)
    (f : Equiv.Perm Iota) (w : Real) : Matrix Iota Iota Real :=
  fun i j => (P i j - w * hamiltonianPermutationCross f i j) / (1 - w)

theorem hamiltonian_permutation_cross_stochastic (f : Equiv.Perm Iota) :
    (forall i j, 0 <= hamiltonianPermutationCross f i j) /\
    (forall i, Finset.univ.sum (fun j => hamiltonianPermutationCross f i j) = 1) /\
    (forall j, Finset.univ.sum (fun i => hamiltonianPermutationCross f i j) = 1) := by
  constructor
  . intro i j
    unfold hamiltonianPermutationCross
    split_ifs <;> norm_num
  constructor
  . intro i
    simp [hamiltonianPermutationCross]
  . intro j
    have hIff (i : Iota) : j = f i <-> i = f.symm j := by
      constructor
      . intro h
        rw [h, Equiv.symm_apply_apply]
      . intro h
        rw [h, Equiv.apply_symm_apply]
    simp_rw [hamiltonianPermutationCross, hIff]
    simp

theorem hamiltonian_stochastic_matched_minimum [Nonempty Iota]
    (P : Matrix Iota Iota Real) (f : Equiv.Perm Iota)
    (hP : forall i j, 0 <= P i j)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hSupport : forall i, 0 < P i (f i)) :
    exists w : Real, 0 < w /\ w <= 1 /\
      (forall i, w <= P i (f i)) /\ exists k, P k (f k) = w := by
  classical
  let S := Finset.univ.image (fun i => P i (f i))
  have hS : S.Nonempty := Finset.univ_nonempty.image _
  let w := S.min' hS
  have hMem : Membership.mem S w := Finset.min'_mem S hS
  choose k hk using Finset.mem_image.mp hMem
  have hw : 0 < w := by rw [<- hk.2]; exact hSupport k
  have hEach (i : Iota) : w <= P i (f i) :=
    Finset.min'_le S _ (Finset.mem_image.mpr
      (Exists.intro i (And.intro (Finset.mem_univ i) rfl)))
  have hkOne : P k (f k) <= 1 := by
    calc
      _ <= Finset.univ.sum (fun j => P k j) :=
        Finset.single_le_sum (fun j _ => hP k j) (Finset.mem_univ (f k))
      _ = 1 := hRows k
  exact Exists.intro w (And.intro hw (And.intro ((hEach k).trans hkOne)
    (And.intro hEach (Exists.intro k hk.2))))

theorem hamiltonian_stochastic_peel_exact
    (P : Matrix Iota Iota Real) (f : Equiv.Perm Iota) (w : Real) (k : Iota)
    (hP : forall i j, 0 <= P i j)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (hw0 : 0 < w) (hw1 : w < 1)
    (hEach : forall i, w <= P i (f i)) (hk : P k (f k) = w) :
    (forall i j, 0 <= hamiltonianStochasticPeel P f w i j) /\
    (forall i, Finset.univ.sum (fun j => hamiltonianStochasticPeel P f w i j) = 1) /\
    (forall j, Finset.univ.sum (fun i => hamiltonianStochasticPeel P f w i j) = 1) /\
    (hamiltonianPositiveCrossSupport (hamiltonianStochasticPeel P f w)).card <
      (hamiltonianPositiveCrossSupport P).card /\
    P = SMul.smul w (hamiltonianPermutationCross f) +
      SMul.smul (1 - w) (hamiltonianStochasticPeel P f w) := by
  classical
  have hDen : 0 < 1 - w := sub_pos.mpr hw1
  have hPerm := hamiltonian_permutation_cross_stochastic f
  have hNumerator (i j : Iota) :
      0 <= P i j - w * hamiltonianPermutationCross f i j := by
    by_cases hij : j = f i
    . simp only [hamiltonianPermutationCross, hij, ite_true, mul_one]
      exact sub_nonneg.mpr (hEach i)
    . simp only [hamiltonianPermutationCross, hij, ite_false, mul_zero, sub_zero]
      exact hP i j
  have hNonneg (i j : Iota) : 0 <= hamiltonianStochasticPeel P f w i j :=
    div_nonneg (hNumerator i j) hDen.le
  have hRRows (i : Iota) :
      Finset.univ.sum (fun j => hamiltonianStochasticPeel P f w i j) = 1 := by
    unfold hamiltonianStochasticPeel
    simp_rw [div_eq_mul_inv]
    rw [<- Finset.sum_mul, Finset.sum_sub_distrib, <- Finset.mul_sum, hRows, hPerm.2.1]
    simp only [mul_one]
    simpa only [div_eq_mul_inv] using (div_self (ne_of_gt hDen))
  have hRCols (j : Iota) :
      Finset.univ.sum (fun i => hamiltonianStochasticPeel P f w i j) = 1 := by
    unfold hamiltonianStochasticPeel
    simp_rw [div_eq_mul_inv]
    rw [<- Finset.sum_mul, Finset.sum_sub_distrib, <- Finset.mul_sum, hCols, hPerm.2.2]
    simp only [mul_one]
    simpa only [div_eq_mul_inv] using (div_self (ne_of_gt hDen))
  have hSub : hamiltonianPositiveCrossSupport (hamiltonianStochasticPeel P f w) <=
      hamiltonianPositiveCrossSupport P := by
    intro e he
    have hR := (Finset.mem_filter.mp he).2
    change 0 < (P e.1 e.2 - w * hamiltonianPermutationCross f e.1 e.2) / (1 - w) at hR
    have hN : 0 < P e.1 e.2 - w * hamiltonianPermutationCross f e.1 e.2 :=
      (div_pos_iff_of_pos_right hDen).mp hR
    have hW := mul_nonneg hw0.le (hPerm.1 e.1 e.2)
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) (by linarith only [hN, hW]))
  have hOld : Membership.mem (hamiltonianPositiveCrossSupport P) (k, f k) := by
    apply Finset.mem_filter.mpr
    exact And.intro (Finset.mem_univ _) (by simpa only [hk] using hw0)
  have hNew : Not (Membership.mem
      (hamiltonianPositiveCrossSupport (hamiltonianStochasticPeel P f w)) (k, f k)) := by
    simp [hamiltonianPositiveCrossSupport, hamiltonianStochasticPeel,
      hamiltonianPermutationCross, hk]
  have hStrict : (hamiltonianPositiveCrossSupport (hamiltonianStochasticPeel P f w)).card <
      (hamiltonianPositiveCrossSupport P).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine And.intro hSub ?_
    intro hEq
    exact hNew (Eq.mpr (congrArg (fun S => Membership.mem S (k, f k)) hEq) hOld)
  refine And.intro hNonneg (And.intro hRRows (And.intro hRCols (And.intro hStrict ?_)))
  ext i j
  change P i j = w * hamiltonianPermutationCross f i j +
    (1 - w) * ((P i j - w * hamiltonianPermutationCross f i j) / (1 - w))
  field_simp [ne_of_gt hDen]
  ring

end PrimeFactorOscillations
