/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianPermanent
import PrimeFactorOscillations.Helpers.HamiltonianPermutationSubsets

/-! # Exact factorial completion of every Gaussian partial matching

The support-by-support identity is signed and contains every contraction.
The factorial weight is preserved by deletion of one selected left vertex
and its contracted right vertex. Summing all supports gives the rook law.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota J K : Type*} [Fintype Iota] [DecidableEq Iota]

theorem gaussianDirectionalDerivative_affine (z a b : Iota -> Complex) :
    gaussianDirectionalDerivative z a (1 + gaussianLinearForm b) =
      MvPolynomial.C (gaussianLinearCovariance z a b) := by
  have h : gaussianDirectionalDerivative z a (1 + gaussianLinearForm b) =
      gaussianDirectionalDerivative z a (gaussianLinearForm b) := by
    unfold gaussianDirectionalDerivative
    simp only [map_add, MvPolynomial.pderiv_one, zero_add]
  rw [h, gaussianDirectionalDerivative_linear]

theorem gaussianDirectionalDerivative_affine_zero [DecidableEq J]
    (z a : Iota -> Complex) (S : Finset J) (right : J -> Iota -> Complex)
    (hCov : forall j, gaussianLinearCovariance z a (right j) = 0) :
    gaussianDirectionalDerivative z a
        (Finset.prod S (fun j => 1 + gaussianLinearForm (right j))) = 0 := by
  rw [gaussianDirectionalDerivative_finset_product]
  apply Finset.sum_eq_zero
  intro j hj
  rw [gaussianDirectionalDerivative_affine, hCov j, map_zero, zero_mul]

theorem gaussianFiniteAffine_expectation [DecidableEq J]
    (z : Iota -> Complex) (S : Finset J) (right : J -> Iota -> Complex)
    (hCov : forall i j, gaussianLinearCovariance z (right i) (right j) = 0) :
    gaussianPolynomialState z
        (Finset.prod S (fun j => 1 + gaussianLinearForm (right j))) = 1 := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, gaussianPolynomialState_one]
  | @insert j S hj ih =>
    rw [Finset.prod_insert hj, add_mul, one_mul, gaussianPolynomialState_add,
      gaussianLinearForm_stein,
      gaussianDirectionalDerivative_affine_zero z (right j) S right (hCov j),
      gaussianPolynomialState_zero, add_zero, ih]

theorem gaussianBipartiteAffineMoment_step
    [DecidableEq J] [DecidableEq K]
    (z a : Iota -> Complex) (S : Finset J) (U : Finset K)
    (left : J -> Iota -> Complex) (right : K -> Iota -> Complex)
    (hCov : forall j, Membership.mem S j ->
      gaussianLinearCovariance z a (left j) = 0) :
    gaussianPolynomialState z
        (gaussianLinearForm a *
          (Finset.prod S (fun j => gaussianLinearForm (left j)) *
            Finset.prod U (fun k => 1 + gaussianLinearForm (right k)))) =
      Finset.sum U (fun k =>
        gaussianLinearCovariance z a (right k) *
          gaussianPolynomialState z
            (Finset.prod S (fun j => gaussianLinearForm (left j)) *
              Finset.prod (U.erase k) (fun l => 1 + gaussianLinearForm (right l)))) := by
  rw [gaussianLinearForm_stein, gaussianDirectionalDerivative_mul,
    gaussianDirectionalDerivative_cross_zero z a S left hCov,
    zero_mul, zero_add, gaussianDirectionalDerivative_finset_product,
    Finset.mul_sum, gaussianPolynomialState_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [gaussianDirectionalDerivative_affine]
  have hReorder :
      Finset.prod S (fun j => gaussianLinearForm (left j)) *
          (MvPolynomial.C (gaussianLinearCovariance z a (right k)) *
            Finset.prod (U.erase k) (fun l => 1 + gaussianLinearForm (right l))) =
        MvPolynomial.C (gaussianLinearCovariance z a (right k)) *
          (Finset.prod S (fun j => gaussianLinearForm (left j)) *
            Finset.prod (U.erase k) (fun l => 1 + gaussianLinearForm (right l))) := by
    ring
  rw [hReorder, gaussianPolynomialState_C_mul]

theorem gaussianPartialMatching_completion (z : Iota -> Complex) :
    forall (n : Nat) (left right : Fin n -> Iota -> Complex)
      (S : Finset (Fin n)),
      (forall i j, gaussianLinearCovariance z (left i) (left j) = 0) ->
      (forall i j, gaussianLinearCovariance z (right i) (right j) = 0) ->
      (((n - S.card).factorial : Nat) : Complex) *
          gaussianPolynomialState z
            (Finset.prod S (fun i => gaussianLinearForm (left i)) *
              Finset.prod Finset.univ (fun j => 1 + gaussianLinearForm (right j))) =
        Finset.sum Finset.univ (fun sigma : Equiv.Perm (Fin n) =>
          Finset.prod S (fun i => gaussianLinearCovariance z (left i) (right (sigma i)))) := by
  intro n
  induction n with
  | zero =>
    intro left right S hLeft hRight
    have hS : S = EmptyCollection.emptyCollection := by
      apply Finset.ext
      intro i
      exact Fin.elim0 i
    simp [hS, gaussianPolynomialState_one]
  | succ n ih =>
    intro left right S hLeft hRight
    by_cases hEmpty : S = EmptyCollection.emptyCollection
    case pos =>
      rw [hEmpty]
      simp only [Finset.prod_empty, Finset.card_empty, one_mul, Nat.sub_zero,
        gaussianFiniteAffine_expectation z Finset.univ right hRight,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Fintype.card_perm, Fintype.card_fin]
    case neg =>
      cases Finset.nonempty_iff_ne_empty.mpr hEmpty with
      | intro i hi =>
        let S' := finDeleteSupport S i
        have hCard : S'.card + 1 = S.card := finDeleteSupport_card_add_one S i hi
        have hIndex : n + 1 - S.card = n - S'.card := by omega
        have hMoment :
            gaussianPolynomialState z
                (Finset.prod S (fun k => gaussianLinearForm (left k)) *
                  Finset.prod Finset.univ (fun j => 1 + gaussianLinearForm (right j))) =
              Finset.sum Finset.univ (fun j : Fin (n + 1) =>
                gaussianLinearCovariance z (left i) (right j) *
                  gaussianPolynomialState z
                    (Finset.prod S' (fun k => gaussianLinearForm
                      (left (finDeleteEmbedding i k))) *
                    Finset.prod Finset.univ (fun k : Fin n =>
                      1 + gaussianLinearForm (right (finDeleteEmbedding j k))))) := by
          calc
            _ = gaussianPolynomialState z
                (gaussianLinearForm (left i) *
                  (Finset.prod (S.erase i) (fun k => gaussianLinearForm (left k)) *
                    Finset.prod Finset.univ
                      (fun j => 1 + gaussianLinearForm (right j)))) := by
              rw [<- Finset.mul_prod_erase S (fun k => gaussianLinearForm (left k)) hi]
              rw [mul_assoc]
            _ = Finset.sum Finset.univ (fun j : Fin (n + 1) =>
                gaussianLinearCovariance z (left i) (right j) *
                  gaussianPolynomialState z
                    (Finset.prod (S.erase i) (fun k => gaussianLinearForm (left k)) *
                      Finset.prod ((Finset.univ : Finset (Fin (n + 1))).erase j)
                        (fun k => 1 + gaussianLinearForm (right k)))) :=
              gaussianBipartiteAffineMoment_step z (left i) (S.erase i) Finset.univ
                left right (fun k _ => hLeft i k)
            _ = _ := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [finDeleteSupport_product, fin_product_erase_swap]
              rfl
        rw [hMoment, Finset.mul_sum]
        calc
          _ = Finset.sum Finset.univ (fun j : Fin (n + 1) =>
              gaussianLinearCovariance z (left i) (right j) *
                ((((n - S'.card).factorial : Nat) : Complex) *
                  gaussianPolynomialState z
                    (Finset.prod S' (fun k => gaussianLinearForm
                      (left (finDeleteEmbedding i k))) *
                    Finset.prod Finset.univ (fun k : Fin n =>
                      1 + gaussianLinearForm (right (finDeleteEmbedding j k)))))) := by
            rw [hIndex]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = Finset.sum Finset.univ (fun j : Fin (n + 1) =>
              gaussianLinearCovariance z (left i) (right j) *
                Finset.sum Finset.univ (fun sigma : Equiv.Perm (Fin n) =>
                  Finset.prod S' (fun k => gaussianLinearCovariance z
                    (left (finDeleteEmbedding i k))
                    (right (finDeleteEmbedding j (sigma k)))))) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [ih (fun k => left (finDeleteEmbedding i k))
              (fun k => right (finDeleteEmbedding j k)) S'
              (fun a b => hLeft _ _) (fun a b => hRight _ _)]
          _ = _ := (finitePermutationSubsetSum_delete
            (fun j k => gaussianLinearCovariance z (left k) (right j)) S i hi).symm

theorem gaussianAffineProduct_rook (z : Iota -> Complex) (n : Nat)
    (left right : Fin n -> Iota -> Complex)
    (hLeft : forall i j, gaussianLinearCovariance z (left i) (left j) = 0)
    (hRight : forall i j, gaussianLinearCovariance z (right i) (right j) = 0) :
    gaussianPolynomialState z
        (Finset.prod Finset.univ (fun i => 1 + gaussianLinearForm (left i)) *
          Finset.prod Finset.univ (fun j => 1 + gaussianLinearForm (right j))) =
      Finset.sum Finset.univ (fun sigma : Equiv.Perm (Fin n) =>
        Finset.sum (Finset.univ : Finset (Fin n)).powerset (fun S =>
          Finset.prod S (fun i => gaussianLinearCovariance z (left i) (right (sigma i))) /
            (((n - S.card).factorial : Nat) : Complex))) := by
  have hExpansion :
      Finset.prod Finset.univ (fun i => 1 + gaussianLinearForm (left i)) =
        Finset.sum (Finset.univ : Finset (Fin n)).powerset
          (fun S => Finset.prod S (fun i => gaussianLinearForm (left i))) := by
    calc
      _ = Finset.prod Finset.univ (fun i => gaussianLinearForm (left i) + 1) := by
        apply Finset.prod_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.prod_add]
        simp only [Finset.prod_const_one, mul_one]
  rw [hExpansion, Finset.sum_mul, gaussianPolynomialState_sum]
  calc
    _ = Finset.sum (Finset.univ : Finset (Fin n)).powerset (fun S =>
        Finset.sum Finset.univ (fun sigma : Equiv.Perm (Fin n) =>
          Finset.prod S (fun i => gaussianLinearCovariance z (left i) (right (sigma i))) /
            (((n - S.card).factorial : Nat) : Complex))) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hFact : Not ((((n - S.card).factorial : Nat) : Complex) = 0) := by
        exact_mod_cast Nat.factorial_ne_zero (n - S.card)
      rw [<- Finset.sum_div]
      apply (eq_div_iff hFact).mpr
      simpa only [mul_comm] using
        gaussianPartialMatching_completion z n left right S hLeft hRight
    _ = _ := Finset.sum_comm

end PrimeFactorOscillations
