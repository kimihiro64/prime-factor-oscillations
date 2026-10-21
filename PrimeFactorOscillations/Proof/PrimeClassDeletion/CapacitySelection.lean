/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Capped capacity selection

The finite construction used in the reverse prime-capacity criterion:
fill a target from finitely many integer capacities, retain support,
and expose the exact nonnegative deficit. The ordered-stream construction
also proves greedy count and rank optimality through its signed count-cost
invariant, allowing arbitrary time-dependent budgets. No analytic estimate
is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem exists_capped_selection {I : Type*} (S : Finset I)
    (a : I -> Nat) (T : Nat) :
    Exists fun v : I -> Nat =>
      (forall i, v i <= a i) /\
      (forall i, Not (Membership.mem S i) -> v i = 0) /\
      S.sum v = min T (S.sum a) /\
      S.sum v + (T - S.sum a) = T := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine Exists.intro (fun _ => 0) ?_
      simp
  | @insert i S hi ih =>
      cases ih with
      | intro v hv =>
        let b := min (a i) (T - S.sum a)
        let w : I -> Nat := fun x => if x = i then b else v x
        have hsum : S.sum w = S.sum v := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxi : Not (x = i) := by
            intro h
            subst x
            exact hi hx
          simp [w, hxi]
        have hwi : w i = b := by simp [w]
        have hb : b <= a i := Nat.min_le_left _ _
        have htotal :
            (insert i S).sum w = min T ((insert i S).sum a) := by
          calc
            (insert i S).sum w = w i + S.sum w := Finset.sum_insert hi
            _ = b + S.sum w := congrArg (fun z => z + S.sum w) hwi
            _ = b + min T (S.sum a) :=
              congrArg (fun z => b + z) (hsum.trans hv.2.2.1)
            _ = min T (a i + S.sum a) := by
              dsimp only [b]
              omega
            _ = min T ((insert i S).sum a) := by rw [Finset.sum_insert hi]
        have hwcap : forall x, w x <= a x := by
          intro x
          by_cases hxi : x = i
          case pos =>
            subst x
            exact hwi.le.trans hb
          case neg =>
            simpa [w, hxi] using hv.1 x
        have hwsupport :
            forall x, Not (Membership.mem (insert i S) x) -> w x = 0 := by
          intro x hx
          have hxi : Not (x = i) := by
            intro h
            subst x
            exact hx (Finset.mem_insert_self i S)
          have hxs : Not (Membership.mem S x) := by
            intro h
            exact hx (Finset.mem_insert_of_mem h)
          simpa [w, hxi] using hv.2.1 x hxs
        have hfinish : (insert i S).sum w + (T - (insert i S).sum a) = T := by
          rw [htotal]
          omega
        exact Exists.intro w
          (And.intro hwcap (And.intro hwsupport (And.intro htotal hfinish)))

/-- Prefix cardinality of a selection from an ordered stream. -/
noncomputable def selectionCount (a : Nat -> Prop) : Nat -> Nat
  | 0 => 0
  | n + 1 => by
      classical
      exact selectionCount a n + if a n then 1 else 0

/-- Prefix cost, with the item at n excluded from prefix n. -/
noncomputable def selectionCost (a : Nat -> Prop) (w : Nat -> Real) : Nat -> Real
  | 0 => 0
  | n + 1 => by
      classical
      exact selectionCost a w n + if a n then w n else 0

theorem selectionCount_le_length (a : Nat -> Prop) (n : Nat) :
    selectionCount a n <= n := by
  classical
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
      by_cases h : a n <;> simp [selectionCount, h] <;> omega

/-- Exact signed increment of the count-cost slack, before using any
greedy rule or monotonicity estimate. -/
theorem selection_slack_step (g t : Nat -> Prop) (w : Nat -> Real) (n : Nat) :
    ((selectionCount g (n + 1) : Real) - (selectionCount t (n + 1) : Real)) *
        w (n + 1) - (selectionCost g w (n + 1) - selectionCost t w (n + 1)) =
      ((selectionCount g n : Real) - (selectionCount t n : Real)) * w n -
        (selectionCost g w n - selectionCost t w n) +
        ((selectionCount g (n + 1) : Real) - (selectionCount t (n + 1) : Real)) *
          (w (n + 1) - w n) := by
  classical
  by_cases hgn : g n <;> by_cases htn : t n <;>
    simp [selectionCount, selectionCost, hgn, htn] <;> nlinarith

/-- Full Abel ledger: every prefix-count gap contributes with its actual
weight increment; no absolute values or omitted endpoint terms. -/
theorem selection_slack_sum (g t : Nat -> Prop) (w : Nat -> Real) (n : Nat) :
    ((selectionCount g n : Real) - (selectionCount t n : Real)) * w n -
        (selectionCost g w n - selectionCost t w n) =
      (Finset.range n).sum (fun j =>
        ((selectionCount g (j + 1) : Real) - (selectionCount t (j + 1) : Real)) *
          (w (j + 1) - w j)) := by
  classical
  induction n with
  | zero => simp [selectionCount, selectionCost]
  | succ n ih => rw [selection_slack_step, ih, Finset.sum_range_succ]

/-- Count and cost must be kept together: at equal counts the greedy prefix
has no larger cost. No monotonicity of the available budget is required. -/
theorem selection_prefix_majorization
    (g t : Nat -> Prop) (w b : Nat -> Real) (hw : Monotone w)
    (hg : forall i, g i <-> selectionCost g w i + w i <= b i)
    (ht : forall i, t i -> selectionCost t w i + w i <= b i)
    (n : Nat) :
    selectionCount t n <= selectionCount g n /\
      selectionCost g w n - selectionCost t w n <=
        ((selectionCount g n : Real) - (selectionCount t n : Real)) * w n := by
  classical
  induction n with
  | zero => simp [selectionCount, selectionCost]
  | succ n ih =>
      have hcount : selectionCount t (n + 1) <= selectionCount g (n + 1) := by
        by_cases hgn : g n
        case pos =>
          by_cases htn : t n
          case pos =>
            simpa only [selectionCount, ite_eq_left hgn, ite_eq_left htn] using
              Nat.add_le_add_right ih.1 1
          case neg =>
            simp only [selectionCount, ite_eq_left hgn, ite_eq_right htn, Nat.add_zero]
            omega
        case neg =>
          by_cases htn : t n
          case pos =>
            have hstrict : selectionCount t n < selectionCount g n := by
              by_contra hnot
              have heq : selectionCount t n = selectionCount g n := by omega
              have hcost := ih.2
              rw [heq] at hcost
              have hreject : b n < selectionCost g w n + w n :=
                lt_of_not_ge (fun h => hgn ((hg n).mpr h))
              have hfeasible := ht n htn
              simp only [sub_self, zero_mul] at hcost
              linarith only [hcost, hreject, hfeasible]
            simp only [selectionCount, ite_eq_right hgn, ite_eq_left htn, Nat.add_zero]
            omega
          case neg =>
            simpa only [selectionCount, ite_eq_right hgn, ite_eq_right htn, Nat.add_zero] using ih.1
      have hdiff :
          0 <= (selectionCount g (n + 1) : Real) - (selectionCount t (n + 1) : Real) :=
        sub_nonneg.mpr (Nat.cast_le.mpr hcount)
      have hslack := selection_slack_step g t w n
      have hmono := mul_le_mul_of_nonneg_left (hw (Nat.le_succ n)) hdiff
      refine And.intro hcount ?_
      nlinarith only [ih.2, hmono, hslack]

theorem selection_rank_exists (a : Nat -> Prop) (n k : Nat)
    (hk : k < selectionCount a n) :
    Exists fun j => j < n /\ a j /\ selectionCount a j = k := by
  classical
  induction n with
  | zero => simp [selectionCount] at hk
  | succ n ih =>
      by_cases hold : k < selectionCount a n
      case pos =>
        cases ih hold with
        | intro j hj =>
            exact Exists.intro j
              (And.intro (hj.1.trans (Nat.lt_succ_self n)) hj.2)
      case neg =>
        have ha : a n := by
          by_contra h
          simp only [selectionCount, ite_eq_right h, Nat.add_zero] at hk
          exact hold hk
        have heq : selectionCount a n = k := by
          simp only [selectionCount, ite_eq_left ha] at hk
          omega
        exact Exists.intro n (And.intro (Nat.lt_succ_self n) (And.intro ha heq))

/-- The actual greedy cost recursion; no existence assumption is hidden in
the comparison certificate. -/
noncomputable def greedySelectionCost (w b : Nat -> Real) : Nat -> Real
  | 0 => 0
  | n + 1 => by
      classical
      exact if greedySelectionCost w b n + w n <= b n then
        greedySelectionCost w b n + w n else greedySelectionCost w b n

noncomputable def greedySelection (w b : Nat -> Real) (n : Nat) : Prop :=
  greedySelectionCost w b n + w n <= b n

theorem selectionCost_greedySelection (w b : Nat -> Real) (n : Nat) :
    selectionCost (greedySelection w b) w n = greedySelectionCost w b n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [selectionCost, greedySelection, ih, greedySelectionCost]
      by_cases h : greedySelectionCost w b n + w n <= b n <;> simp [h]

theorem greedySelection_prefix_majorization
    (t : Nat -> Prop) (w b : Nat -> Real) (hw : Monotone w)
    (ht : forall i, t i -> selectionCost t w i + w i <= b i) (n : Nat) :
    selectionCount t n <= selectionCount (greedySelection w b) n /\
      selectionCost (greedySelection w b) w n - selectionCost t w n <=
        ((selectionCount (greedySelection w b) n : Real) -
          (selectionCount t n : Real)) * w n := by
  apply selection_prefix_majorization (greedySelection w b) t w b hw _ ht n
  intro i
  simp only [greedySelection, selectionCost_greedySelection]

/-- Every competitor's kth selection is preceded by the kth greedy selection.
The ranks are zero based, and the witness is an actual selected stream item. -/
theorem greedySelection_rank_le
    (t : Nat -> Prop) (w b : Nat -> Real) (hw : Monotone w)
    (ht : forall i, t i -> selectionCost t w i + w i <= b i)
    (i : Nat) (hi : t i) :
    Exists fun j => j <= i /\ greedySelection w b j /\
      selectionCount (greedySelection w b) j = selectionCount t i := by
  classical
  have hstep : selectionCount t i < selectionCount t (i + 1) := by
    simp only [selectionCount, ite_eq_left hi]
    omega
  have hcount := (greedySelection_prefix_majorization t w b hw ht (i + 1)).1
  cases selection_rank_exists (greedySelection w b) (i + 1)
      (selectionCount t i) (hstep.trans_le hcount) with
  | intro j hj =>
      exact Exists.intro j (And.intro (Nat.lt_succ_iff.mp hj.1) hj.2)

theorem greedySelection_deleted_count_le
    (t : Nat -> Prop) (w b : Nat -> Real) (hw : Monotone w)
    (ht : forall i, t i -> selectionCost t w i + w i <= b i) (n : Nat) :
    n - selectionCount (greedySelection w b) n <= n - selectionCount t n := by
  exact Nat.sub_le_sub_left
    (greedySelection_prefix_majorization t w b hw ht n).1 n

theorem greedySelection_equal_count_cost_le
    (t : Nat -> Prop) (w b : Nat -> Real) (hw : Monotone w)
    (ht : forall i, t i -> selectionCost t w i + w i <= b i)
    (n : Nat) (hcount : selectionCount (greedySelection w b) n = selectionCount t n) :
    selectionCost (greedySelection w b) w n <= selectionCost t w n := by
  have h := (greedySelection_prefix_majorization t w b hw ht n).2
  rw [hcount] at h
  simpa only [sub_self, zero_mul, sub_nonpos] using h

end PrimeFactorOscillations.PrimeClassDeletion

