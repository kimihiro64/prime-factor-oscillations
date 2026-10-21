/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial variation certificates for actual prime moment grids

The interpolation and derivative formulas are proved directly from cached
polynomial APIs. No dependency rebuild or Lagrange-module artifact is needed.
The derivative constant retains every actual node separation. This supplies
the quantitative input to positive-objective norming, not an arithmetic
estimate on the optimized prime repair weights.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

variable {I : Type*} [Fintype I] [DecidableEq I]

def primeNodeDenominator (v : I -> Real) (i : I) : Real :=
  (Finset.univ.erase i).prod (fun j => v i - v j)

noncomputable def primeNodeKernel (v : I -> Real) (i : I) : Polynomial Real :=
  (Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (v j))

noncomputable def primeNodeInterpolant (v a : I -> Real) : Polynomial Real :=
  Finset.univ.sum (fun i =>
    Polynomial.C (a i / primeNodeDenominator v i) * primeNodeKernel v i)

noncomputable def primeNodeDerivativeConstant (v : I -> Real) : Real :=
  Finset.univ.sum (fun i =>
    ((Fintype.card I - 1 : Nat) : Real) / abs (primeNodeDenominator v i))

theorem primeNodeDenominator_ne_zero (v : I -> Real)
    (hv : Function.Injective v) (i : I) :
    Not (primeNodeDenominator v i = 0) := by
  unfold primeNodeDenominator
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro hij
  exact (Finset.mem_erase.mp hj).1 (hv hij).symm

theorem primeNodeKernel_eval_self (v : I -> Real) (i : I) :
    (primeNodeKernel v i).eval (v i) = primeNodeDenominator v i := by
  unfold primeNodeKernel primeNodeDenominator
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j _hj
  simp

theorem primeNodeKernel_eval_other (v : I -> Real) (i j : I)
    (hji : Not (j = i)) :
    (primeNodeKernel v i).eval (v j) = 0 := by
  unfold primeNodeKernel
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr
    (And.intro hji (Finset.mem_univ j)))
  simp

theorem primeNodeInterpolant_eval (v a : I -> Real)
    (hv : Function.Injective v) (i : I) :
    (primeNodeInterpolant v a).eval (v i) = a i := by
  calc
    (primeNodeInterpolant v a).eval (v i) =
        (Polynomial.C (a i / primeNodeDenominator v i) *
          primeNodeKernel v i).eval (v i) := by
      unfold primeNodeInterpolant
      rw [Polynomial.eval_finsetSum]
      exact Finset.sum_eq_single i
        (fun j _hj hji => by
          rw [Polynomial.eval_mul, Polynomial.eval_C,
            primeNodeKernel_eval_other v j i (Ne.symm hji), mul_zero])
        (fun hi => False.elim (hi (Finset.mem_univ i)))
    _ = a i := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, primeNodeKernel_eval_self]
      exact div_mul_cancel_of_imp
        (fun h => False.elim (primeNodeDenominator_ne_zero v hv i h))

theorem primeNodeKernel_natDegree_le (v : I -> Real) (i : I) :
    (primeNodeKernel v i).natDegree <= Fintype.card I - 1 := by
  unfold primeNodeKernel
  calc
    ((Finset.univ.erase i).prod
      (fun j => Polynomial.X - Polynomial.C (v j))).natDegree <=
        (Finset.univ.erase i).sum
          (fun j => (Polynomial.X - Polynomial.C (v j)).natDegree) :=
      Polynomial.natDegree_prod_le _ _
    _ = Fintype.card I - 1 := by
      simp [Finset.card_erase_of_mem]

theorem primeNodeInterpolant_natDegree_le (v a : I -> Real) :
    (primeNodeInterpolant v a).natDegree <= Fintype.card I - 1 := by
  unfold primeNodeInterpolant
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _hi
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (primeNodeKernel_natDegree_le v i)

theorem primeNode_interpolation_eq (v : I -> Real)
    (hv : Function.Injective v) (P : Polynomial Real)
    (hP : P.natDegree < Fintype.card I) :
    P = primeNodeInterpolant v (fun i => P.eval (v i)) := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hv
  case heval =>
    intro i
    exact (primeNodeInterpolant_eval v (fun j => P.eval (v j)) hv i).symm
  case hcard =>
    have hN : 0 < Fintype.card I := lt_of_le_of_lt (Nat.zero_le _) hP
    have hQ : (primeNodeInterpolant v (fun i => P.eval (v i))).natDegree <
        Fintype.card I :=
      lt_of_le_of_lt (primeNodeInterpolant_natDegree_le _ _)
        (Nat.sub_lt hN Nat.zero_lt_one)
    exact max_lt_iff.mpr (And.intro hP hQ)

theorem primeNodeInterpolant_derivative_eval (v a : I -> Real) (x : Real) :
    (primeNodeInterpolant v a).derivative.eval x =
      Finset.univ.sum (fun i =>
        (a i / primeNodeDenominator v i) *
          (Finset.univ.erase i).sum (fun j =>
            ((Finset.univ.erase i).erase j).prod (fun l => x - v l))) := by
  simp only [primeNodeInterpolant, Polynomial.derivative_sum,
    Polynomial.derivative_C_mul, primeNodeKernel,
    Polynomial.derivative_prod_finset, Polynomial.derivative_X_sub_C,
    mul_one, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]

theorem primeNode_derivative_eval (v : I -> Real)
    (hv : Function.Injective v) (P : Polynomial Real)
    (hP : P.natDegree < Fintype.card I) (x : Real) :
    P.derivative.eval x =
      Finset.univ.sum (fun i =>
        (P.eval (v i) / primeNodeDenominator v i) *
          (Finset.univ.erase i).sum (fun j =>
            ((Finset.univ.erase i).erase j).prod (fun l => x - v l))) := by
  calc
    P.derivative.eval x =
        (primeNodeInterpolant v (fun i => P.eval (v i))).derivative.eval x :=
      congrArg (fun Q : Polynomial Real => Q.derivative.eval x)
        (primeNode_interpolation_eq v hv P hP)
    _ = _ := primeNodeInterpolant_derivative_eval _ _ _

theorem abs_finite_prod_le_pow {J : Type*} (S : Finset J)
    (f : J -> Real) (h : Real) (hh : 0 <= h)
    (hf : forall j, Membership.mem S j -> abs (f j) <= h) :
    abs (S.prod f) <= h ^ S.card := by
  classical
  revert hf
  induction S using Finset.induction_on with
  | empty =>
    intro _hf
    simp
  | @insert j S hj ih =>
    intro hf
    rw [Finset.prod_insert hj, abs_mul, Finset.card_insert_of_notMem hj, pow_succ]
    have hjb := hf j (Finset.mem_insert_self j S)
    have hsb : abs (S.prod f) <= h ^ S.card := by
      apply ih
      intro l hl
      exact hf l (Finset.mem_insert_of_mem hl)
    calc
      abs (f j) * abs (S.prod f) <= h * h ^ S.card :=
        mul_le_mul hjb hsb (abs_nonneg _) hh
      _ = h ^ S.card * h := mul_comm _ _

theorem primeNode_derivative_abs_le (v : I -> Real)
    (hv : Function.Injective v) (P : Polynomial Real)
    (hP : P.natDegree < Fintype.card I)
    (hv01 : forall i, 0 <= v i /\ v i <= 1)
    (x : Real) (hx : 0 <= x /\ x <= 1)
    (L : Real) (hL : 0 <= L)
    (hvalues : forall i, abs (P.eval (v i)) <= L) :
    abs (P.derivative.eval x) <= L * primeNodeDerivativeConstant v := by
  have hdist : forall i, abs (x - v i) <= 1 := by
    intro i
    apply abs_le.mpr
    exact And.intro (by linarith [(hv01 i).2, hx.1])
      (by linarith [(hv01 i).1, hx.2])
  have hinner : forall i,
      abs ((Finset.univ.erase i).sum (fun j =>
        ((Finset.univ.erase i).erase j).prod (fun l => x - v l))) <=
          ((Fintype.card I - 1 : Nat) : Real) := by
    intro i
    calc
      _ <= (Finset.univ.erase i).sum (fun j =>
          abs (((Finset.univ.erase i).erase j).prod (fun l => x - v l))) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= (Finset.univ.erase i).sum (fun _j => (1 : Real)) := by
        apply Finset.sum_le_sum
        intro j _hj
        simpa using abs_finite_prod_le_pow ((Finset.univ.erase i).erase j)
          (fun l => x - v l) 1 zero_le_one (fun l _hl => hdist l)
      _ = ((Fintype.card I - 1 : Nat) : Real) := by
        simp [Finset.card_erase_of_mem]
  rw [primeNode_derivative_eval v hv P hP x]
  calc
    _ <= Finset.univ.sum (fun i =>
        abs ((P.eval (v i) / primeNodeDenominator v i) *
          (Finset.univ.erase i).sum (fun j =>
            ((Finset.univ.erase i).erase j).prod (fun l => x - v l)))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.univ.sum (fun i =>
        (L / abs (primeNodeDenominator v i)) *
          ((Fintype.card I - 1 : Nat) : Real)) := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [abs_mul, abs_div]
      exact mul_le_mul
        (div_le_div_of_nonneg_right (hvalues i) (abs_nonneg _))
        (hinner i) (abs_nonneg _) (div_nonneg hL (abs_nonneg _))
    _ = L * primeNodeDerivativeConstant v := by
      unfold primeNodeDerivativeConstant
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [div_eq_mul_inv]
      ring

theorem pow_le_abs_finite_prod {J : Type*} (S : Finset J)
    (f : J -> Real) (h : Real) (hh : 0 <= h)
    (hf : forall j, Membership.mem S j -> h <= abs (f j)) :
    h ^ S.card <= abs (S.prod f) := by
  classical
  revert hf
  induction S using Finset.induction_on with
  | empty =>
    intro _hf
    simp
  | @insert j S hj ih =>
    intro hf
    rw [Finset.prod_insert hj, abs_mul, Finset.card_insert_of_notMem hj, pow_succ]
    have hjb := hf j (Finset.mem_insert_self j S)
    have hsb : h ^ S.card <= abs (S.prod f) := by
      apply ih
      intro l hl
      exact hf l (Finset.mem_insert_of_mem hl)
    calc
      h ^ S.card * h <= abs (S.prod f) * abs (f j) :=
        mul_le_mul hsb hjb hh (abs_nonneg _)
      _ = abs (f j) * abs (S.prod f) := mul_comm _ _

theorem primeNodeDenominator_abs_ge_of_separation (v : I -> Real)
    (delta : Real) (hdelta : 0 < delta)
    (hsep : forall i j, Not (i = j) -> delta <= abs (v i - v j)) (i : I) :
    delta ^ (Fintype.card I - 1) <= abs (primeNodeDenominator v i) := by
  have h := pow_le_abs_finite_prod (Finset.univ.erase i)
    (fun j => v i - v j) delta hdelta.le
    (fun j hj => hsep i j (fun hij => (Finset.mem_erase.mp hj).1 hij.symm))
  simpa only [primeNodeDenominator,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] using h

theorem primeNodeDerivativeConstant_le_of_separation (v : I -> Real)
    (delta : Real) (hdelta : 0 < delta)
    (hsep : forall i j, Not (i = j) -> delta <= abs (v i - v j)) :
    primeNodeDerivativeConstant v <=
      ((Fintype.card I : Real) * ((Fintype.card I - 1 : Nat) : Real)) /
        delta ^ (Fintype.card I - 1) := by
  unfold primeNodeDerivativeConstant
  calc
    _ <= Finset.univ.sum (fun _i : I =>
        ((Fintype.card I - 1 : Nat) : Real) /
          delta ^ (Fintype.card I - 1)) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (pow_pos hdelta _) (primeNodeDenominator_abs_ge_of_separation v delta hdelta hsep i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]
      ring

theorem primeNode_derivative_abs_le_of_separation (v : I -> Real)
    (hv : Function.Injective v) (P : Polynomial Real)
    (hP : P.natDegree < Fintype.card I)
    (hv01 : forall i, 0 <= v i /\ v i <= 1)
    (x : Real) (hx : 0 <= x /\ x <= 1)
    (L : Real) (hL : 0 <= L)
    (hvalues : forall i, abs (P.eval (v i)) <= L)
    (delta : Real) (hdelta : 0 < delta)
    (hsep : forall i j, Not (i = j) -> delta <= abs (v i - v j)) :
    abs (P.derivative.eval x) <=
      L * (((Fintype.card I : Real) * ((Fintype.card I - 1 : Nat) : Real)) /
        delta ^ (Fintype.card I - 1)) := by
  exact (primeNode_derivative_abs_le v hv P hP hv01 x hx L hL hvalues).trans
    (mul_le_mul_of_nonneg_left
      (primeNodeDerivativeConstant_le_of_separation v delta hdelta hsep) hL)

end PrimeFactorOscillations.PrimeClassDeletion
