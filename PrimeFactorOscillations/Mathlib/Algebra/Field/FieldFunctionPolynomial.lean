/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Basic

/-!
# Explicit reduced polynomials for finite-field functions

The Fermat indicator kernel represents any function with degree at most
cardinality minus one. The zero-count bound is stated on the complete
finite field for the exact-minimum square-transport degree consumer.
These interpolation and root-count ingredients are classical.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Polynomial
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def fieldFunctionPolynomial (f : F -> F) : Polynomial F :=
  Finset.univ.sum (fun a : F => C (f a)*(1-(X-C a)^(Fintype.card F-1)))

theorem fieldFunctionPolynomial_eval (hq : 2<=Fintype.card F)
    (f : F -> F) (x : F) : (fieldFunctionPolynomial f).eval x=f x := by
  have hn : Not (Fintype.card F-1=0) :=
    Nat.ne_of_gt (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1<2) hq))
  have ht (a : F) :
      (evalRingHom x) (C (f a)*(1-(X-C a)^(Fintype.card F-1)))=
        if a=x then f x else 0 := by
    change (C (f a)*(1-(X-C a)^(Fintype.card F-1))).eval x=_
    simp only [eval_mul,eval_C,eval_sub,eval_one,eval_pow,eval_X]
    by_cases ha : a=x
    . subst a
      rw [sub_self,zero_pow hn,sub_zero,mul_one,ite_eq_left rfl]
    . have hxa : Not (x-a=0) := sub_ne_zero.mpr (Ne.symm ha)
      rw [FiniteField.pow_card_sub_one_eq_one (x-a) hxa,sub_self,mul_zero,ite_eq_right ha]
  change (evalRingHom x)
    (Finset.univ.sum fun a : F => C (f a)*(1-(X-C a)^(Fintype.card F-1)))=f x
  rw [map_sum]
  simp_rw [ht]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem fieldFunctionPolynomial_natDegree_le (f : F -> F) :
    (fieldFunctionPolynomial f).natDegree<=Fintype.card F-1 := by
  have ht (a : F) :
      (C (f a)*(1-(X-C a)^(Fintype.card F-1))).natDegree<=Fintype.card F-1 := by
    have hp : ((X-C a)^(Fintype.card F-1)).natDegree=Fintype.card F-1 := by
      rw [natDegree_pow,natDegree_X_sub_C,mul_one]
    have hs : (1-(X-C a)^(Fintype.card F-1)).natDegree<=Fintype.card F-1 := by
      apply (natDegree_sub_le _ _).trans
      rw [natDegree_one,hp]
      exact max_le (Nat.zero_le _) (Nat.le_refl _)
    have hm := natDegree_mul_le (p := C (f a))
      (q := 1-(X-C a)^(Fintype.card F-1))
    rw [natDegree_C,zero_add] at hm
    exact hm.trans hs
  have hs (s : Finset F) :
      (s.sum fun a : F => C (f a)*(1-(X-C a)^(Fintype.card F-1))).natDegree<=
        Fintype.card F-1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (natDegree_add_le _ _).trans (max_le (ht a) ih)
  exact hs Finset.univ

theorem card_eval_zero_le_natDegree (P : Polynomial F) (hP : Not (P=0)) :
    (Finset.univ.filter fun x : F => P.eval x=0).card<=P.natDegree := by
  have hm : (Finset.univ.filter fun x : F => P.eval x=0)<=P.roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr
      ((mem_roots hP).mpr (Finset.mem_filter.mp hx).2)
  exact (Finset.card_le_card hm).trans
    ((Multiset.toFinset_card_le P.roots).trans P.card_roots')

end Polynomial
