/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Capped capacity selection

The finite construction used in the reverse prime-capacity criterion:
fill a target from finitely many integer capacities, retain support,
and expose the exact nonnegative deficit. No analytic estimate is assumed.
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

end PrimeFactorOscillations.PrimeClassDeletion

