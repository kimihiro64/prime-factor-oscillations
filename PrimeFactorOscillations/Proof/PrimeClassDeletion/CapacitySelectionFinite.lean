/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CapacitySelection

/-!
# Literal finite-set form of greedy rank optimality

The recursive counts and costs equal the paper's actual prefix cardinalities
and weight sums. This transports the exact signed slack, arbitrary-budget
greedy invariant, and zero-based rank comparison to their literal statements.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def selectionPrefix (a : Nat -> Prop) (n : Nat) : Finset Nat := by
  classical
  exact (Finset.range n).filter a

theorem selectionCount_eq_card_selectionPrefix (a : Nat -> Prop) (n : Nat) :
    selectionCount a n = (selectionPrefix a n).card := by
  classical
  unfold selectionPrefix
  have hsum : (Finset.range n).sum (fun i => if a i then (1 : Nat) else 0) =
      ((Finset.range n).filter a).card := by
    simp only [Finset.sum_boole, Nat.cast_id]
  rw [<- hsum]
  clear hsum
  induction n with
  | zero => simp [selectionCount]
  | succ n ih => rw [selectionCount, Finset.sum_range_succ, ih]

theorem selectionCost_eq_sum_selectionPrefix (a : Nat -> Prop) (w : Nat -> Real) (n : Nat) :
    selectionCost a w n = (selectionPrefix a n).sum w := by
  classical
  unfold selectionPrefix
  rw [Finset.sum_filter]
  induction n with
  | zero => simp [selectionCost]
  | succ n ih => rw [selectionCost, Finset.sum_range_succ, ih]

noncomputable def prefixSlack (g t : Nat -> Prop) (w : Nat -> Real) (n : Nat) : Real :=
  (((selectionPrefix g n).card : Real) - ((selectionPrefix t n).card : Real)) * w n -
    ((selectionPrefix g n).sum w - (selectionPrefix t n).sum w)

theorem prefixSlack_step (g t : Nat -> Prop) (w : Nat -> Real) (n : Nat) :
    prefixSlack g t w (n + 1) - prefixSlack g t w n =
      (((selectionPrefix g (n + 1)).card : Real) -
        ((selectionPrefix t (n + 1)).card : Real)) * (w (n + 1) - w n) := by
  have h := selection_slack_step g t w n
  simp only [selectionCount_eq_card_selectionPrefix,
    selectionCost_eq_sum_selectionPrefix] at h
  unfold prefixSlack
  linarith only [h]

theorem prefixSlack_sum (g t : Nat -> Prop) (w : Nat -> Real) (n : Nat) :
    prefixSlack g t w n = (Finset.range n).sum (fun j =>
      (((selectionPrefix g (j + 1)).card : Real) -
        ((selectionPrefix t (j + 1)).card : Real)) * (w (j + 1) - w j)) := by
  unfold prefixSlack
  simpa only [selectionCount_eq_card_selectionPrefix,
    selectionCost_eq_sum_selectionPrefix] using selection_slack_sum g t w n

theorem greedySelection_iff_prefix_budget (w b : Nat -> Real) (i : Nat) :
    greedySelection w b i <->
      (selectionPrefix (greedySelection w b) i).sum w + w i <= b i := by
  rw [<- selectionCost_eq_sum_selectionPrefix, selectionCost_greedySelection]
  rfl

theorem greedySelection_finset_prefix_optimality
    (t : Nat -> Prop) (w b : Nat -> Real) (hw : Monotone w)
    (ht : forall i, t i -> (selectionPrefix t i).sum w + w i <= b i) (n : Nat) :
    And ((selectionPrefix t n).card <= (selectionPrefix (greedySelection w b) n).card)
      (And ((selectionPrefix (greedySelection w b) n).sum w -
          (selectionPrefix t n).sum w <=
        (((selectionPrefix (greedySelection w b) n).card : Real) -
          ((selectionPrefix t n).card : Real)) * w n)
        (And (0 <= prefixSlack (greedySelection w b) t w n)
          (And (n - (selectionPrefix (greedySelection w b) n).card <=
              n - (selectionPrefix t n).card)
            ((selectionPrefix (greedySelection w b) n).card = (selectionPrefix t n).card ->
              (selectionPrefix (greedySelection w b) n).sum w <=
                (selectionPrefix t n).sum w)))) := by
  have ht' : forall i, t i -> selectionCost t w i + w i <= b i := by
    simpa only [selectionCost_eq_sum_selectionPrefix] using ht
  have h := greedySelection_prefix_majorization t w b hw ht' n
  simp only [selectionCount_eq_card_selectionPrefix,
    selectionCost_eq_sum_selectionPrefix] at h
  refine And.intro h.1 (And.intro h.2 (And.intro ?_ (And.intro ?_ ?_)))
  case refine_1 =>
    unfold prefixSlack
    linarith only [h.2]
  case refine_2 =>
    exact Nat.sub_le_sub_left h.1 n
  case refine_3 =>
    intro heq
    have hc := h.2
    rw [heq] at hc
    simpa only [sub_self, zero_mul, sub_nonpos] using hc

theorem greedySelection_finset_rank_le
    (t : Nat -> Prop) (w b : Nat -> Real) (hw : Monotone w)
    (ht : forall i, t i -> (selectionPrefix t i).sum w + w i <= b i)
    (i : Nat) (hi : t i) :
    Exists fun j => And (j <= i) (And (greedySelection w b j)
      ((selectionPrefix (greedySelection w b) j).card = (selectionPrefix t i).card)) := by
  have ht' : forall j, t j -> selectionCost t w j + w j <= b j := by
    simpa only [selectionCost_eq_sum_selectionPrefix] using ht
  simpa only [selectionCount_eq_card_selectionPrefix] using
    greedySelection_rank_le t w b hw ht' i hi

end PrimeFactorOscillations.PrimeClassDeletion
