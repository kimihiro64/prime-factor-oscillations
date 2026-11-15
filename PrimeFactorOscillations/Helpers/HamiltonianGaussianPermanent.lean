/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianRookIdentification
import PrimeFactorOscillations.Helpers.HamiltonianPermanentLaplace

/-! # Exact bipartite Gaussian moments as permanents

The polynomial Stein identity retains every contraction. If contractions
within the left class vanish, the equal-size mixed moment satisfies the
full permanent Laplace recursion. No norm bound is used in this identity.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota J K : Type*} [Fintype Iota] [DecidableEq Iota]

theorem gaussianDirectionalDerivative_finset_product
    [DecidableEq J] (z a : Iota -> Complex) (S : Finset J)
    (p : J -> MvPolynomial Iota Complex) :
    gaussianDirectionalDerivative z a (Finset.prod S p) =
      Finset.sum S (fun j =>
        gaussianDirectionalDerivative z a (p j) *
          Finset.prod (S.erase j) p) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, gaussianDirectionalDerivative_one,
      Finset.sum_empty]
  | @insert j S hj ih =>
    rw [Finset.prod_insert hj, gaussianDirectionalDerivative_mul, ih,
      Finset.sum_insert hj]
    have hErase : (insert j S).erase j = S := Finset.erase_insert hj
    rw [hErase, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : Not (k = j) := by
      intro h
      rw [h] at hk
      exact hj hk
    have hInsert : (insert j S).erase k = insert j (S.erase k) :=
      Finset.erase_insert_of_ne (Ne.symm hkj)
    rw [hInsert, Finset.prod_insert (by
      intro h
      exact hj (Finset.mem_of_mem_erase h))]
    ring

theorem gaussianDirectionalDerivative_cross_zero
    [DecidableEq J] (z a : Iota -> Complex) (S : Finset J)
    (left : J -> Iota -> Complex)
    (hCov : forall j, Membership.mem S j ->
      gaussianLinearCovariance z a (left j) = 0) :
    gaussianDirectionalDerivative z a
        (Finset.prod S (fun j => gaussianLinearForm (left j))) = 0 := by
  rw [gaussianDirectionalDerivative_finset_product]
  apply Finset.sum_eq_zero
  intro j hj
  rw [gaussianDirectionalDerivative_linear, hCov j hj, map_zero, zero_mul]

theorem gaussianBipartiteMoment_step
    [DecidableEq J] [DecidableEq K]
    (z a : Iota -> Complex) (S : Finset J) (U : Finset K)
    (left : J -> Iota -> Complex) (right : K -> Iota -> Complex)
    (hCov : forall j, Membership.mem S j ->
      gaussianLinearCovariance z a (left j) = 0) :
    gaussianPolynomialState z
        (gaussianLinearForm a *
          (Finset.prod S (fun j => gaussianLinearForm (left j)) *
            Finset.prod U (fun k => gaussianLinearForm (right k)))) =
      Finset.sum U (fun k =>
        gaussianLinearCovariance z a (right k) *
          gaussianPolynomialState z
            (Finset.prod S (fun j => gaussianLinearForm (left j)) *
              Finset.prod (U.erase k) (fun l => gaussianLinearForm (right l)))) := by
  rw [gaussianLinearForm_stein, gaussianDirectionalDerivative_mul,
    gaussianDirectionalDerivative_cross_zero z a S left hCov,
    zero_mul, zero_add, gaussianDirectionalDerivative_finset_product,
    Finset.mul_sum, gaussianPolynomialState_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [gaussianDirectionalDerivative_linear]
  have hReorder :
      Finset.prod S (fun j => gaussianLinearForm (left j)) *
          (MvPolynomial.C (gaussianLinearCovariance z a (right k)) *
            Finset.prod (U.erase k) (fun l => gaussianLinearForm (right l))) =
        MvPolynomial.C (gaussianLinearCovariance z a (right k)) *
          (Finset.prod S (fun j => gaussianLinearForm (left j)) *
            Finset.prod (U.erase k) (fun l => gaussianLinearForm (right l))) := by
    ring
  rw [hReorder, gaussianPolynomialState_C_mul]

theorem fin_product_erase_swap {R : Type*} [CommMonoid R]
    {n : Nat} (f : Fin (n + 1) -> R) (j : Fin (n + 1)) :
    Finset.prod ((Finset.univ : Finset (Fin (n + 1))).erase j) f =
      Finset.prod Finset.univ
        (fun i : Fin n => f (Equiv.swap 0 j i.succ)) := by
  classical
  symm
  apply Finset.prod_bij (fun i _ => Equiv.swap 0 j i.succ)
  case hi =>
    intro i hi
    apply Finset.mem_erase.mpr
    refine And.intro ?_ (Finset.mem_univ _)
    intro h
    have hZero : i.succ = (0 : Fin (n + 1)) := by
      simpa using congrArg (Equiv.swap 0 j) h
    exact Fin.succ_ne_zero i hZero
  case i_inj =>
    intro a ha b hb h
    exact Fin.succ_injective _ ((Equiv.swap 0 j).injective h)
  case i_surj =>
    intro a ha
    have haj : Not (a = j) := (Finset.mem_erase.mp ha).1
    have hZero : Not (Equiv.swap 0 j a = (0 : Fin (n + 1))) := by
      intro h
      apply haj
      simpa using congrArg (Equiv.swap 0 j) h
    have hSucc : forall b : Fin (n + 1), Not (b = 0) ->
        exists i : Fin n, i.succ = b := by
      intro b
      exact Fin.cases (fun h => False.elim (h rfl))
        (fun i _ => Exists.intro i rfl) b
    cases hSucc _ hZero with
    | intro i hi =>
      refine Exists.intro i (Exists.intro (Finset.mem_univ _) ?_)
      simpa using congrArg (Equiv.swap 0 j) hi
  case h =>
    intro i hi
    rfl

theorem gaussianBipartiteMoment_permanent (z : Iota -> Complex) :
    forall (n : Nat) (left right : Fin n -> Iota -> Complex),
      (forall i j, gaussianLinearCovariance z (left i) (left j) = 0) ->
      gaussianPolynomialState z
          (Finset.prod Finset.univ (fun i => gaussianLinearForm (left i)) *
            Finset.prod Finset.univ (fun j => gaussianLinearForm (right j))) =
        finitePermutationSum
          (fun j i => gaussianLinearCovariance z (left i) (right j)) := by
  intro n
  induction n with
  | zero =>
    intro left right hCov
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      gaussianPolynomialState_one]
    exact (finitePermutationSum_fin_zero _).symm
  | succ n ih =>
    intro left right hCov
    let L := Finset.prod Finset.univ
      (fun i : Fin n => gaussianLinearForm (left i.succ))
    calc
      _ = gaussianPolynomialState z
          (gaussianLinearForm (left 0) *
            (L * Finset.prod Finset.univ
              (fun j => gaussianLinearForm (right j)))) := by
        congr 1
        rw [Fin.prod_univ_succ]
        dsimp only [L]
        ring
      _ = Finset.sum Finset.univ (fun j : Fin (n + 1) =>
          gaussianLinearCovariance z (left 0) (right j) *
            gaussianPolynomialState z
              (L * Finset.prod
                ((Finset.univ : Finset (Fin (n + 1))).erase j)
                (fun k => gaussianLinearForm (right k)))) :=
        gaussianBipartiteMoment_step z (left 0) Finset.univ Finset.univ
          (fun i : Fin n => left i.succ) right (fun i _ => hCov 0 i.succ)
      _ = Finset.sum Finset.univ (fun j : Fin (n + 1) =>
          gaussianLinearCovariance z (left 0) (right j) *
            finitePermutationSum (fun k i : Fin n =>
              gaussianLinearCovariance z (left i.succ)
                (right (Equiv.swap 0 j k.succ)))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [fin_product_erase_swap]
        rw [ih (fun i : Fin n => left i.succ)
          (fun k : Fin n => right (Equiv.swap 0 j k.succ))
          (fun i k => hCov i.succ k.succ)]
      _ = _ := (finitePermutationSum_laplace
        (fun j i => gaussianLinearCovariance z (left i) (right j))).symm

end PrimeFactorOscillations
