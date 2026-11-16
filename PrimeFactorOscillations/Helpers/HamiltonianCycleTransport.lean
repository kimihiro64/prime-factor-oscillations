/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianLiuIdentity

/-! # Exact transport of the full single-cycle sum

Permutation conjugation transports every orbit, including fixed-point
orbits. Thus arbitrary vertex relabeling preserves the actual weighted
single-cycle sum, with no counting or analytic error.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota R : Type*}
variable [Fintype Iota] [DecidableEq Iota]
variable [Fintype Jota] [DecidableEq Jota]

def hamiltonianRelabelPermutation (e : Equiv Jota Iota) (f : Equiv.Perm Jota) :
    Equiv.Perm Iota := e.symm.trans (f.trans e)

def hamiltonianRelabelPermutationEquiv (e : Equiv Jota Iota) :
    Equiv (Equiv.Perm Jota) (Equiv.Perm Iota) where
  toFun := hamiltonianRelabelPermutation e
  invFun := hamiltonianRelabelPermutation e.symm
  left_inv := by
    intro f
    apply Equiv.ext
    intro x
    simp only [hamiltonianRelabelPermutation, Equiv.trans_apply,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  right_inv := by
    intro f
    apply Equiv.ext
    intro x
    simp only [hamiltonianRelabelPermutation, Equiv.trans_apply,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply]

theorem hamiltonian_relabel_permutation_power (e : Equiv Jota Iota)
    (f : Equiv.Perm Jota) (k : Nat) (x : Jota) :
    (hamiltonianRelabelPermutation e f ^ k) (e x) = e ((f ^ k) x) := by
  induction k generalizing x with
  | zero => simp only [pow_zero, Equiv.Perm.one_apply]
  | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply]
      have hStep : hamiltonianRelabelPermutation e f (e x) = e (f x) := by
        simp only [hamiltonianRelabelPermutation, Equiv.trans_apply, e.symm_apply_apply]
      rw [hStep, ih, pow_succ, Equiv.Perm.mul_apply]

theorem hamiltonian_relabel_same_cycle (e : Equiv Jota Iota) (f : Equiv.Perm Jota)
    (x y : Jota) :
    (hamiltonianRelabelPermutation e f).SameCycle (e x) (e y) <-> f.SameCycle x y := by
  constructor
  case mp =>
    intro h
    let w := h.exists_nat_pow_eq
    refine Exists.intro (w.choose : Int) ?_
    rw [zpow_natCast]
    apply e.injective
    rw [<- hamiltonian_relabel_permutation_power]
    exact w.choose_spec
  case mpr =>
    intro h
    let w := h.exists_nat_pow_eq
    refine Exists.intro (w.choose : Int) ?_
    rw [zpow_natCast, hamiltonian_relabel_permutation_power, w.choose_spec]

theorem hamiltonian_relabel_orbit (e : Equiv Jota Iota) (f : Equiv.Perm Jota) (x : Jota) :
    hamiltonianPermutationOrbit (hamiltonianRelabelPermutation e f) (e x) =
      (hamiltonianPermutationOrbit f x).image e := by
  apply Finset.ext
  intro y
  constructor
  case mp =>
    intro h
    refine Finset.mem_image.mpr (Exists.intro (e.symm y) (And.intro ?_ (e.apply_symm_apply y)))
    apply (mem_hamiltonianPermutationOrbit f x (e.symm y)).mpr
    apply (hamiltonian_relabel_same_cycle e f x (e.symm y)).mp
    simpa only [e.apply_symm_apply] using
      (mem_hamiltonianPermutationOrbit (hamiltonianRelabelPermutation e f) (e x) y).mp h
  case mpr =>
    intro h
    let w := Finset.mem_image.mp h
    have hx : Membership.mem (hamiltonianPermutationOrbit f x) w.choose := w.choose_spec.1
    have hy : e w.choose = y := w.choose_spec.2
    rw [<- hy, mem_hamiltonianPermutationOrbit]
    exact (hamiltonian_relabel_same_cycle e f x w.choose).mpr
      ((mem_hamiltonianPermutationOrbit f x w.choose).mp hx)

theorem hamiltonian_relabel_orbit_family (e : Equiv Jota Iota) (f : Equiv.Perm Jota) :
    hamiltonianPermutationOrbits (hamiltonianRelabelPermutation e f) =
      (hamiltonianPermutationOrbits f).image (fun S => S.image e) := by
  apply Finset.ext
  intro A
  constructor
  case mp =>
    intro h
    let w := Finset.mem_image.mp h
    let x := e.symm w.choose
    have hOrbit : hamiltonianPermutationOrbit (hamiltonianRelabelPermutation e f) (e x) = A := by
      simpa only [x, e.apply_symm_apply] using w.choose_spec.2
    refine Finset.mem_image.mpr (Exists.intro (hamiltonianPermutationOrbit f x)
      (And.intro (hamiltonianPermutationOrbit_mem f x) ?_))
    exact (hamiltonian_relabel_orbit e f x).symm.trans hOrbit
  case mpr =>
    intro h
    let w := Finset.mem_image.mp h
    have hS : Membership.mem (hamiltonianPermutationOrbits f) w.choose := w.choose_spec.1
    let v := Finset.mem_image.mp hS
    have hSource : hamiltonianPermutationOrbit f v.choose = w.choose := v.choose_spec.2
    have hTarget : w.choose.image e = A := w.choose_spec.2
    have hOrbit : hamiltonianPermutationOrbit (hamiltonianRelabelPermutation e f) (e v.choose) = A :=
      (hamiltonian_relabel_orbit e f v.choose).trans
        ((congrArg (fun S : Finset Jota => S.image e) hSource).trans hTarget)
    rw [<- hOrbit]
    exact hamiltonianPermutationOrbit_mem _ _

theorem hamiltonian_relabel_orbit_count (e : Equiv Jota Iota) (f : Equiv.Perm Jota) :
    (hamiltonianPermutationOrbits (hamiltonianRelabelPermutation e f)).card =
      (hamiltonianPermutationOrbits f).card := by
  rw [hamiltonian_relabel_orbit_family]
  exact Finset.card_image_of_injective _ (Finset.image_injective e.injective)

theorem hamiltonian_cycle_sum_reindex [CommSemiring R]
    (e : Equiv Jota Iota) (M : Matrix Iota Iota R) :
    hamiltonianCycleSum (M.submatrix e e) = hamiltonianCycleSum M := by
  let p := hamiltonianRelabelPermutationEquiv e
  have hWeight (f : Equiv.Perm Jota) :
      Finset.univ.prod (fun j : Jota => M (e (f j)) (e j)) =
        Finset.univ.prod (fun i : Iota => M (p f i) i) := by
    have h := Equiv.prod_comp e (fun i : Iota => M (p f i) i)
    have hPoint (j : Jota) : p f (e j) = e (f j) := by
      change e (f (e.symm (e j))) = e (f j)
      rw [e.symm_apply_apply]
    calc
      _ = Finset.univ.prod (fun j : Jota => M (p f (e j)) (e j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [hPoint]
      _ = _ := h
  unfold hamiltonianCycleSum
  calc
    _ = Finset.univ.sum (fun f : Equiv.Perm Jota =>
        if (hamiltonianPermutationOrbits (p f)).card = 1 then
          Finset.univ.prod (fun i : Iota => M (p f i) i) else 0) := by
      apply Finset.sum_congr rfl
      intro f hf
      have hCard : (hamiltonianPermutationOrbits (p f)).card =
          (hamiltonianPermutationOrbits f).card := hamiltonian_relabel_orbit_count e f
      rw [hCard]
      by_cases hCycle : (hamiltonianPermutationOrbits f).card = 1
      case pos => simpa only [hCycle, ite_true, Matrix.submatrix_apply] using hWeight f
      case neg => simp only [hCycle, ite_false]
    _ = _ := Equiv.sum_comp p (fun f : Equiv.Perm Iota =>
      if (hamiltonianPermutationOrbits f).card = 1 then
        Finset.univ.prod (fun i => M (f i) i) else 0)

end PrimeFactorOscillations
