/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCycleExponentialLower
import PrimeFactorOscillations.Helpers.HamiltonianCycleOrientation
import PrimeFactorOscillations.Helpers.HamiltonianPrescribedPathMinor

/-! # Exact integer path counts and the full edge-scaling normalization -/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

def hamiltonianPrescribedGraphPaths (R : I -> I -> Prop) (a b : I) :
    Finset (Equiv.Perm I) :=
  hamiltonianDirectedCycles (fun i j => if j = a then i = b else R i j)

def hamiltonianGraphPathCount (R : I -> I -> Prop) (a b : I) : Nat :=
  (hamiltonianPrescribedGraphPaths R a b).card

theorem hamiltonian_mem_directed_cycles (R : I -> I -> Prop) (f : Equiv.Perm I) :
    Membership.mem (hamiltonianDirectedCycles R) f <->
      (hamiltonianPermutationOrbits f).card = 1 /\ forall i, R (f i) i := by
  classical
  simp only [hamiltonianDirectedCycles, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_hamiltonianPrescribedGraphPaths (R : I -> I -> Prop)
    (a b : I) (f : Equiv.Perm I) :
    Membership.mem (hamiltonianPrescribedGraphPaths R a b) f <->
      (hamiltonianPermutationOrbits f).card = 1 /\ f a = b /\
        forall i, Not (i = a) -> R (f i) i := by
  have hFilter := hamiltonian_mem_directed_cycles
    (fun i j => if j = a then i = b else R i j) f
  constructor
  case mp =>
    intro hf
    have h := hFilter.mp hf
    have hEnd := h.2 a
    simp only [ite_true] at hEnd
    refine And.intro h.1 (And.intro hEnd ?_)
    intro i hi
    simpa only [hi, ite_false] using h.2 i
  case mpr =>
    intro h
    apply hFilter.mpr
    refine And.intro h.1 ?_
    intro i
    by_cases hi : i = a
    case pos => subst i; simpa only [ite_true] using h.2.1
    case neg => simpa only [hi, ite_false] using h.2.2 i hi

theorem hamiltonian_indicator_path_count
    (R : I -> I -> Prop) [DecidableRel R] (a b : I) :
    hamiltonianPrescribedPathSum (fun i j => if R i j then (1 : Real) else 0) a b =
      (hamiltonianGraphPathCount R a b : Real) := by
  have hMatrix :
      hamiltonianPathClosingKernel (fun i j => if R i j then (1 : Real) else 0) a b =
      (fun i j => if (if j = a then i = b else R i j) then (1 : Real) else 0) := by
    ext i j
    by_cases hj : j = a
    case pos =>
      by_cases hi : i = b <;> simp only [hamiltonianPathClosingKernel, hj, hi,
        ite_true, ite_false]
    case neg => simp only [hamiltonianPathClosingKernel, hj, ite_false]
  unfold hamiltonianPrescribedPathSum
  rw [hMatrix, hamiltonian_indicator_cycle_count]
  rfl

theorem hamiltonian_path_sum_scalar (M : Matrix I I Real) (a b : I) (c : Real) :
    hamiltonianPrescribedPathSum (fun i j => c * M i j) a b =
      c ^ (Fintype.card I - 1) * hamiltonianPrescribedPathSum M a b := by
  let v := fun j : I => if j = a then (1 : Real) else c
  have hKernel : hamiltonianPathClosingKernel (fun i j => c * M i j) a b =
      hamiltonianCrossScaled (hamiltonianPathClosingKernel M a b) (fun _ => 1) v := by
    ext i j
    by_cases hj : j = a
    case pos =>
      by_cases hi : i = b <;>
        simp only [hamiltonianPathClosingKernel, hamiltonianCrossScaled, v,
          hj, hi, ite_true, ite_false, one_mul, mul_one, mul_zero]
    case neg =>
      simp only [hamiltonianPathClosingKernel, hamiltonianCrossScaled, v,
        hj, ite_false, one_mul]
      ring
  have hErase : (Finset.univ.erase a).prod v = Finset.univ.prod v := by
    apply Finset.prod_subset (Finset.erase_subset a Finset.univ)
    intro j hj hNot
    have he : j = a := by
      apply Classical.byContradiction
      intro hne
      exact hNot (Finset.mem_erase.mpr (And.intro hne hj))
    simp only [v, he, ite_true]
  have hProd : Finset.univ.prod v = c ^ (Fintype.card I - 1) := by
    rw [<- hErase]
    calc
      _ = (Finset.univ.erase a).prod (fun _ => c) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact if_neg (Finset.mem_erase.mp hj).1
      _ = _ := by
        simp only [Finset.prod_const,
          Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
  unfold hamiltonianPrescribedPathSum
  rw [hKernel, hamiltonian_cycle_sum_two_sided_scaling, hProd]
  simp only [Finset.prod_const, one_pow, one_mul]

end PrimeFactorOscillations
