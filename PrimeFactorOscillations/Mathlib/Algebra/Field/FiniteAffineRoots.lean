/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import PrimeFactorOscillations.Mathlib.Algebra.Group.FiniteSumFibers

/-! # Exact residue counts for products of distinct affine forms -/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

private theorem affine_factor_zero_iff {K : Type*} [Field K]
    (c d x : K) (hc : Not (c = 0)) :
    c * x + d = 0 <-> x = -d / c := by
  constructor
  next =>
    intro h
    field_simp [hc]
    linear_combination h
  next =>
    intro h
    rw [h]
    field_simp [hc]
    simp

private theorem affine_product_zero_iff {K I : Type*} [Field K] [Fintype I]
    (c d : I -> K) (hc : forall i : I, Not (c i = 0)) (x : K) :
    (Finset.univ.prod (fun i : I => c i * x + d i)) = 0 <->
      exists i : I, x = -d i / c i := by
  classical
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  next =>
    intro h
    choose i hi using h
    exact Exists.intro i ((affine_factor_zero_iff (c i) (d i) x (hc i)).mp hi)
  next =>
    intro h
    choose i hi using h
    exact Exists.intro i ((affine_factor_zero_iff (c i) (d i) x (hc i)).mpr hi)

/-- Nonzero coefficients and nonzero pairwise determinants give exactly one
distinct root per affine form, without a degree-counting approximation. -/
theorem card_affine_product_roots {K I : Type*} [Field K] [Fintype K] [Fintype I]
    [DecidableEq K] (c d : I -> K) (hc : forall i : I, Not (c i = 0))
    (hdet : forall i j : I, Not (i = j) -> Not (c i * d j = c j * d i)) :
    ((Finset.univ.filter (fun x : K =>
      (Finset.univ.prod (fun i : I => c i * x + d i)) = 0))).card = Fintype.card I := by
  classical
  have hinj : Function.Injective (fun i : I => -d i / c i) := by
    intro i j heq
    by_contra hne
    apply hdet i j hne
    field_simp [hc i, hc j] at heq
    linear_combination heq
  have hset : (Finset.univ.filter (fun x : K =>
      (Finset.univ.prod (fun i : I => c i * x + d i)) = 0)) =
      Finset.univ.image (fun i : I => -d i / c i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, affine_product_zero_iff c d hc]
    constructor
    next =>
      intro h
      choose i hi using h
      exact Exists.intro i hi.symm
    next =>
      intro h
      choose i hi using h
      exact Exists.intro i hi.symm
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ]

/-- The exact nonzero-pair residue count for a product of distinct affine
forms. The zero-root correction is retained explicitly. -/
theorem card_nonzero_affine_product_sum {K I : Type*} [Field K] [Fintype K] [Fintype I]
    [DecidableEq K] (hq : 2 <= Fintype.card K)
    (c d : I -> K) (hc : forall i : I, Not (c i = 0))
    (hdet : forall i j : I, Not (i = j) -> Not (c i * d j = c j * d i)) :
    (((Finset.univ.erase (0 : K)).product (Finset.univ.erase (0 : K))).filter
      (fun ab : Prod K K =>
        (Finset.univ.prod (fun i : I => c i * (ab.1 + ab.2) + d i)) = 0)).card =
      Fintype.card I * (Fintype.card K - 2) +
        if (exists i : I, d i = 0) then 1 else 0 := by
  classical
  let R := Finset.univ.filter (fun x : K =>
    (Finset.univ.prod (fun i : I => c i * x + d i)) = 0)
  have hR : R.card = Fintype.card I := card_affine_product_roots c d hc hdet
  have hzero : Membership.mem R 0 <-> exists i : I, d i = 0 := by
    dsimp only [R]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mul_zero, zero_add,
      Finset.prod_eq_zero_iff]
  have hset :
      (((Finset.univ.erase (0 : K)).product (Finset.univ.erase (0 : K))).filter
        (fun ab : Prod K K =>
          (Finset.univ.prod (fun i : I => c i * (ab.1 + ab.2) + d i)) = 0)) =
      (((Finset.univ.erase (0 : K)).product (Finset.univ.erase (0 : K))).filter
        (fun ab : Prod K K => Membership.mem R (ab.1 + ab.2))) := by
    ext ab
    simp [R]
  rw [hset, Finset.card_nonzero_sum_mem hq R, hR]
  simp only [hzero]

end Finset
