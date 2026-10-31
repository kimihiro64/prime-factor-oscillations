/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# Weighted pushforward of finite product factors

Arbitrary functions of all coordinate statistics are retained. Equality
of each local weighted fiber sum gives equality for every coupled joint
statistic, with no factorization assumption on that statistic.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Fintype
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {K L : I -> Type*} [forall i, Fintype (K i)] [forall i, Fintype (L i)]
variable [forall i, DecidableEq (L i)]
variable {R : Type*} [CommSemiring R]

theorem sum_prod_mul_comp_eq
    (f : (i : I) -> K i -> L i) (u : (i : I) -> K i -> R)
    (g : ((i : I) -> L i) -> R) :
    (Finset.univ.sum fun x : (i : I) -> K i =>
      (Finset.univ.prod fun i => u i (x i)) * g (fun i => f i (x i))) =
    (Finset.univ.sum fun y : (i : I) -> L i =>
      (Finset.univ.prod fun i =>
        ((Finset.univ.filter fun c : K i => f i c = y i).sum (u i))) * g y) := by
  classical
  have hp (y : (i : I) -> L i) (x : (i : I) -> K i) :
      (if (fun i => f i (x i)) = y then
        (Finset.univ.prod fun i => u i (x i)) * g (fun i => f i (x i)) else 0) =
      (Finset.univ.prod fun i => if f i (x i) = y i then u i (x i) else 0) * g y := by
    by_cases he : (fun i => f i (x i)) = y
    . have hi (i : I) : f i (x i) = y i := congrFun he i
      simp only [hi, ite_true]
    . have hn : exists i, Not (f i (x i) = y i) :=
        not_forall.mp (fun ha => he (funext ha))
      let i : I := Classical.choose hn
      have hi : Not (f i (x i) = y i) := Classical.choose_spec hn
      have hz : (Finset.univ.prod fun j => if f j (x j) = y j then u j (x j) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
      rw [ite_eq_right he, hz, zero_mul]
  calc
    _ = Finset.univ.sum (fun y : (i : I) -> L i =>
        Finset.univ.sum fun x : (i : I) -> K i =>
          if (fun i => f i (x i)) = y then
            (Finset.univ.prod fun i => u i (x i)) * g (fun i => f i (x i)) else 0) := by
      simpa only [Finset.sum_filter] using
        (Finset.sum_fiberwise Finset.univ (fun x : (i : I) -> K i => fun i => f i (x i))
          (fun x => (Finset.univ.prod fun i => u i (x i)) * g (fun i => f i (x i)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      simp_rw [hp y]
      rw [<- Finset.sum_mul,
        <- Fintype.prod_sum (fun (i : I) (c : K i) => if f i c = y i then u i c else 0)]
      simp only [Finset.sum_filter]

theorem sum_prod_mul_comp_eq_of_fiber_sums
    (f : (i : I) -> K i -> L i) (u v : (i : I) -> K i -> R)
    (hf : forall i y,
      ((Finset.univ.filter fun c : K i => f i c = y).sum (u i)) =
        ((Finset.univ.filter fun c : K i => f i c = y).sum (v i)))
    (g : ((i : I) -> L i) -> R) :
    (Finset.univ.sum fun x : (i : I) -> K i =>
      (Finset.univ.prod fun i => u i (x i)) * g (fun i => f i (x i))) =
    (Finset.univ.sum fun x : (i : I) -> K i =>
      (Finset.univ.prod fun i => v i (x i)) * g (fun i => f i (x i))) := by
  rw [sum_prod_mul_comp_eq f u g, sum_prod_mul_comp_eq f v g]
  simp_rw [hf]

end Fintype
