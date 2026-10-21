/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

/-!
# Exact support function of real capped capacities

This is the signed atomic term in the capped moment dual:
the maximum over 0 <= v_i <= a_i is sum_i a_i * max(c_i, 0).
Negative coefficients are retained; no absolute-value envelope is used.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem capped_dot_le_positive_part {I : Type*} (S : Finset I)
    (a v c : I -> Real) (hv0 : forall i, 0 <= v i)
    (hva : forall i, v i <= a i) :
    S.sum (fun i => v i * c i) <=
      S.sum (fun i => a i * max (c i) 0) := by
  apply Finset.sum_le_sum
  intro i _hi
  by_cases hc : 0 <= c i
  case pos =>
    rw [max_eq_left hc]
    exact mul_le_mul_of_nonneg_right (hva i) hc
  case neg =>
    have hc0 : c i <= 0 := (lt_of_not_ge hc).le
    rw [max_eq_right hc0, mul_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (hv0 i) hc0

theorem exists_capped_support_maximizer {I : Type*} (S : Finset I)
    (a c : I -> Real) (ha : forall i, 0 <= a i) :
    Exists fun v : I -> Real =>
      (forall i, 0 <= v i) /\
      (forall i, v i <= a i) /\
      (forall i, Not (Membership.mem S i) -> v i = 0) /\
      S.sum (fun i => v i * c i) =
        S.sum (fun i => a i * max (c i) 0) /\
      (forall u : I -> Real,
        (forall i, 0 <= u i) ->
        (forall i, u i <= a i) ->
        S.sum (fun i => u i * c i) <= S.sum (fun i => v i * c i)) := by
  classical
  let v : I -> Real := fun i =>
    if Membership.mem S i /\ 0 <= c i then a i else 0
  have hv0 : forall i, 0 <= v i := by
    intro i
    by_cases h : Membership.mem S i /\ 0 <= c i
    case pos => simpa [v, h] using ha i
    case neg => simp [v, h]
  have hva : forall i, v i <= a i := by
    intro i
    by_cases h : Membership.mem S i /\ 0 <= c i
    case pos => simp [v, h]
    case neg => simpa [v, h] using ha i
  have hsupport : forall i, Not (Membership.mem S i) -> v i = 0 := by
    intro i hi
    simp [v, hi]
  have heq :
      S.sum (fun i => v i * c i) =
        S.sum (fun i => a i * max (c i) 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hc : 0 <= c i
    case pos => simp [v, hi, hc]
    case neg =>
      have hc0 : c i <= 0 := (lt_of_not_ge hc).le
      simp [v, hi, hc, max_eq_right hc0]
  have hmax : forall u : I -> Real,
      (forall i, 0 <= u i) ->
      (forall i, u i <= a i) ->
      S.sum (fun i => u i * c i) <= S.sum (fun i => v i * c i) := by
    intro u hu0 hua
    rw [heq]
    exact capped_dot_le_positive_part S a u c hu0 hua
  exact Exists.intro v
    (And.intro hv0 (And.intro hva (And.intro hsupport (And.intro heq hmax))))

end PrimeFactorOscillations.PrimeClassDeletion

