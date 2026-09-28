/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Exp.DoubleExpGrowth

/-! # Finite sums preserve upper double-exponential growth coefficients -/

set_option autoImplicit false
set_option Elab.async false

namespace Real

/-- A finite sum of eventual bounds at coefficient a has an eventual bound
at every b>a; neither the cardinality nor the fixed additive cost changes
the limiting coefficient. -/
theorem eventually_le_double_exp_of_finite_sum {I : Type*}
    (s : Finset I) (f : I -> Nat -> Real) (n : Nat -> Real)
    (a b C : Real) (ha : 0 <= a) (hab : a < b) (hC : 0 <= C)
    (hf : forall i, Membership.mem s i -> exists K : Nat,
      forall k : Nat, K <= k -> f i k <= Real.exp (Real.exp (a * k)))
    (hn : exists K : Nat, forall k : Nat, K <= k ->
      n k <= C + s.sum (fun i => f i k)) :
    exists K : Nat, forall k : Nat, K <= k ->
      n k <= Real.exp (Real.exp (b * k)) := by
  classical
  choose Ks hKs using (fun i : {i : I // Membership.mem s i} => hf i.val i.property)
  choose K0 hK0 using hn
  let D : Real := C + (s.card : Real) + 1
  have hD : 0 <= D := by dsimp only [D]; positivity
  choose K1 hK1 using eventually_mul_double_exp_add_one_le a b D ha hab hD
  let K2 : Nat := s.attach.sup Ks
  refine Exists.intro (max K0 (max K1 K2)) ?_
  intro k hk
  have hk0 := (le_max_left K0 (max K1 K2)).trans hk
  have hrest := (le_max_right K0 (max K1 K2)).trans hk
  have hk1 := (le_max_left K1 K2).trans hrest
  have hk2 := (le_max_right K1 K2).trans hrest
  have hsum : s.sum (fun i => f i k) <=
      (s.card : Real) * Real.exp (Real.exp (a * k)) := by
    calc
      s.sum (fun i => f i k) <= s.sum (fun _ => Real.exp (Real.exp (a * k))) := by
        apply Finset.sum_le_sum
        intro i hi
        let j : {i : I // Membership.mem s i} := Subtype.mk i hi
        have hj : Membership.mem s.attach j := Finset.mem_attach _ _
        have hsup : Ks j <= K2 := Finset.le_sup (f := Ks) hj
        exact hKs j k (hsup.trans hk2)
      _ = (s.card : Real) * Real.exp (Real.exp (a * k)) := by simp
  have hnum : n k <= C + (s.card : Real) * Real.exp (Real.exp (a * k)) := by
    linarith only [hK0 k hk0, hsum]
  have hcard : (0 : Real) <= s.card := Nat.cast_nonneg s.card
  have hE := Real.exp_pos (Real.exp (a * k))
  have hprod := mul_nonneg hC hE.le
  have hmajor : n k <= D * (Real.exp (Real.exp (a * k)) + 1) := by
    dsimp only [D]
    nlinarith only [hnum, hcard, hE, hprod]
  exact hmajor.trans (hK1 k hk1)

end Real
