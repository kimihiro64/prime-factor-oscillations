/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Matrix.Basic
import PrimeFactorOscillations.Helpers.HamiltonianGammaMoments

/-! # The exact permanent / rook / inverse-Gamma bridge

The rook sum is written over partial permutations, with the exact completion
multiplicity divided out. Every k-edge partial matching has (N-k)! completions.
The integral identity is proved directly from the finite expansion and actual
inverse-Gamma moments. No positivity or asymptotic hypothesis is used.

weightedPermutationSum is the permutation definition of the permanent. This
local definition avoids rebuilding the unavailable Permanent dependency.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [DecidableEq Iota] [Fintype Iota]

def weightedPermutationSum (M : Matrix Iota Iota Real) : Real :=
  Finset.sum Finset.univ (fun sigma : Equiv.Perm Iota =>
    Finset.prod Finset.univ (fun i => M (sigma i) i))

def hamiltonianRookPolynomial (B : Matrix Iota Iota Real) (s : Real) : Real :=
  Finset.sum Finset.univ (fun sigma : Equiv.Perm Iota =>
    Finset.sum (Finset.univ : Finset Iota).powerset (fun S =>
      (Finset.prod S (fun i => B (sigma i) i) /
        ((Fintype.card Iota - S.card).factorial : Real)) * s ^ S.card))

private theorem gamma_weighted_monomials {Alpha : Type*} (n : Nat)
    (S : Finset Alpha) (degree : Alpha -> Nat) (c : Alpha -> Real)
    (hDegree : forall i, Membership.mem S i -> degree i <= n) :
    gammaInverseAverage n
        (fun s => Finset.sum S (fun i => c i * s ^ degree i)) =
      Finset.sum S (fun i => c i *
        ((n : Real) ^ degree i * ((n - degree i).factorial : Real) /
          (n.factorial : Real))) := by
  have hFun :
      (fun t : Real => Real.exp (-t) * t ^ n *
        Finset.sum S (fun i => c i * ((n : Real) / t) ^ degree i)) =
      (fun t : Real => Finset.sum S
        (fun i => c i *
          (Real.exp (-t) * t ^ n * ((n : Real) / t) ^ degree i))) := by
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hTerm : forall i, Membership.mem S i ->
      MeasureTheory.Integrable
        (fun t : Real => c i *
          (Real.exp (-t) * t ^ n * ((n : Real) / t) ^ degree i)) gammaHalfLine := by
    intro i hi
    exact (gammaInversePower_integrable n (degree i) (hDegree i hi)).const_mul (c i)
  have hRaw := fun i hi => gammaInverseAverage_pow n (degree i) (hDegree i hi)
  unfold gammaInverseAverage at hRaw
  unfold gammaInverseAverage
  rw [hFun, MeasureTheory.integral_finsetSum S (fun i hi => hTerm i hi), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MeasureTheory.integral_const_mul]
  calc
    _ = c i * ((Inv.inv (n.factorial : Real)) *
        MeasureTheory.integral gammaHalfLine
          (fun t : Real => Real.exp (-t) * t ^ n * ((n : Real) / t) ^ degree i)) := by ring
    _ = _ := by rw [hRaw i hi]

private theorem gamma_rook_integrable (B : Matrix Iota Iota Real)
    (sigma : Equiv.Perm Iota) :
    MeasureTheory.Integrable
      (fun t : Real => Real.exp (-t) * t ^ Fintype.card Iota *
        Finset.sum (Finset.univ : Finset Iota).powerset (fun S =>
          (Finset.prod S (fun i => B (sigma i) i) /
            ((Fintype.card Iota - S.card).factorial : Real)) *
            ((Fintype.card Iota : Real) / t) ^ S.card)) gammaHalfLine := by
  have hFun :
      (fun t : Real => Real.exp (-t) * t ^ Fintype.card Iota *
        Finset.sum (Finset.univ : Finset Iota).powerset (fun S =>
          (Finset.prod S (fun i => B (sigma i) i) /
            ((Fintype.card Iota - S.card).factorial : Real)) *
            ((Fintype.card Iota : Real) / t) ^ S.card)) =
      (fun t : Real => Finset.sum (Finset.univ : Finset Iota).powerset (fun S =>
        (Finset.prod S (fun i => B (sigma i) i) /
          ((Fintype.card Iota - S.card).factorial : Real)) *
          (Real.exp (-t) * t ^ Fintype.card Iota *
            ((Fintype.card Iota : Real) / t) ^ S.card))) := by
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    ring
  rw [hFun]
  apply MeasureTheory.integrable_finset_sum
  intro S hS
  have hCard : S.card <= Fintype.card Iota := Finset.card_le_univ S
  exact (gammaInversePower_integrable (Fintype.card Iota) S.card hCard).const_mul _

theorem hamiltonianRookPolynomial_integrable (B : Matrix Iota Iota Real) :
    MeasureTheory.Integrable
      (fun t : Real => Real.exp (-t) * t ^ Fintype.card Iota *
        hamiltonianRookPolynomial B ((Fintype.card Iota : Real) / t)) gammaHalfLine := by
  have hFun :
      (fun t : Real => Real.exp (-t) * t ^ Fintype.card Iota *
        hamiltonianRookPolynomial B ((Fintype.card Iota : Real) / t)) =
      (fun t : Real => Finset.sum Finset.univ (fun sigma : Equiv.Perm Iota =>
        Real.exp (-t) * t ^ Fintype.card Iota *
          Finset.sum (Finset.univ : Finset Iota).powerset (fun S =>
            (Finset.prod S (fun i => B (sigma i) i) /
              ((Fintype.card Iota - S.card).factorial : Real)) *
              ((Fintype.card Iota : Real) / t) ^ S.card))) := by
    funext t
    unfold hamiltonianRookPolynomial
    rw [Finset.mul_sum]
  rw [hFun]
  exact MeasureTheory.integrable_finset_sum Finset.univ
    (fun sigma _ => gamma_rook_integrable B sigma)

private theorem rook_product_expansion (B : Matrix Iota Iota Real)
    (sigma : Equiv.Perm Iota) (y : Real) :
    Finset.prod Finset.univ (fun i => 1 + y * B (sigma i) i) =
      Finset.sum (Finset.univ : Finset Iota).powerset
        (fun S => y ^ S.card * Finset.prod S (fun i => B (sigma i) i)) := by
  calc
    _ = Finset.prod Finset.univ (fun i => y * B (sigma i) i + 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.prod_add]
      simp only [Finset.prod_mul_distrib, Finset.prod_const, one_pow, mul_one]

theorem hamiltonianRookPolynomial_gamma_exact (B : Matrix Iota Iota Real) :
    gammaInverseAverage (Fintype.card Iota) (hamiltonianRookPolynomial B) =
      weightedPermutationSum (fun i j => 1 + (Fintype.card Iota : Real) * B i j) /
        ((Fintype.card Iota).factorial : Real) := by
  have hFun :
      (fun t : Real => Real.exp (-t) * t ^ Fintype.card Iota *
        hamiltonianRookPolynomial B ((Fintype.card Iota : Real) / t)) =
      (fun t : Real => Finset.sum Finset.univ (fun sigma : Equiv.Perm Iota =>
        Real.exp (-t) * t ^ Fintype.card Iota *
          Finset.sum (Finset.univ : Finset Iota).powerset (fun S =>
            (Finset.prod S (fun i => B (sigma i) i) /
              ((Fintype.card Iota - S.card).factorial : Real)) *
              ((Fintype.card Iota : Real) / t) ^ S.card))) := by
    funext t
    unfold hamiltonianRookPolynomial
    rw [Finset.mul_sum]
  have hInner : forall sigma : Equiv.Perm Iota,
      gammaInverseAverage (Fintype.card Iota)
        (fun s => Finset.sum (Finset.univ : Finset Iota).powerset (fun S =>
          (Finset.prod S (fun i => B (sigma i) i) /
            ((Fintype.card Iota - S.card).factorial : Real)) * s ^ S.card)) =
        Finset.prod Finset.univ
          (fun i => 1 + (Fintype.card Iota : Real) * B (sigma i) i) /
          ((Fintype.card Iota).factorial : Real) := by
    intro sigma
    rw [gamma_weighted_monomials (Fintype.card Iota)
      (Finset.univ : Finset Iota).powerset Finset.card
      (fun S => Finset.prod S (fun i => B (sigma i) i) /
        ((Fintype.card Iota - S.card).factorial : Real))
      (fun S _ => Finset.card_le_univ S)]
    rw [rook_product_expansion B sigma, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro S hS
    have hFact : Not (((Fintype.card Iota - S.card).factorial : Real) = 0) := by
      exact_mod_cast Nat.factorial_ne_zero (Fintype.card Iota - S.card)
    field_simp
    <;> ring
  unfold gammaInverseAverage
  rw [hFun, MeasureTheory.integral_finsetSum Finset.univ
    (fun sigma _ => gamma_rook_integrable B sigma), Finset.mul_sum]
  change Finset.sum Finset.univ
      (fun sigma : Equiv.Perm Iota => gammaInverseAverage (Fintype.card Iota)
        (fun s => Finset.sum (Finset.univ : Finset Iota).powerset (fun S =>
          (Finset.prod S (fun i => B (sigma i) i) /
            ((Fintype.card Iota - S.card).factorial : Real)) * s ^ S.card))) = _
  simp_rw [hInner]
  rw [<- Finset.sum_div]
  rfl

theorem hamiltonianRookPolynomial_gamma_normalized (B : Matrix Iota Iota Real)
    (hN : 0 < Fintype.card Iota) :
    gammaInverseAverage (Fintype.card Iota) (hamiltonianRookPolynomial B) =
      (Fintype.card Iota : Real) ^ Fintype.card Iota /
        ((Fintype.card Iota).factorial : Real) *
        weightedPermutationSum (fun i j => 1 / (Fintype.card Iota : Real) + B i j) := by
  have hNonzero : Not ((Fintype.card Iota : Real) = 0) := by
    exact_mod_cast Nat.ne_of_gt hN
  have hEntry : forall i j, 1 + (Fintype.card Iota : Real) * B i j =
      (Fintype.card Iota : Real) * (1 / (Fintype.card Iota : Real) + B i j) := by
    intro i j
    field_simp
    <;> ring
  rw [hamiltonianRookPolynomial_gamma_exact]
  unfold weightedPermutationSum
  simp_rw [hEntry, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [<- Finset.mul_sum]
  ring

end PrimeFactorOscillations
