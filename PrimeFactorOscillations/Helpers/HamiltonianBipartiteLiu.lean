/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteSupports
import PrimeFactorOscillations.Helpers.HamiltonianLiuIdentity

/-! # The full signed bipartite Liu packet

The actual cycle identity is specialized to both selected supports.
Every balanced rectangular minor, complementary permanent and sign is
retained. Unbalanced contributions vanish by their proved determinant
identity, rather than an estimate or a matching-support assumption.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota R : Type*} [Fintype Iota] [DecidableEq Iota] [CommRing R]

def hamiltonianBipartiteLiuPacket (T : Matrix Iota Iota R) : R := by
  classical
  exact -Finset.sum Finset.univ (fun U : Finset Iota =>
    (-1 : R) ^ U.card * (U.card : R) *
      Finset.sum (Finset.univ.powersetCard U.card) (fun S =>
        rectangularMinorDet T S U ^ 2 *
          rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) ^ 2))

theorem hamiltonianBipartiteLiu_term (T : Matrix Iota Iota R) (S U : Finset Iota) :
    (((S.disjSum U).card : R) * (-1 : R) ^ (S.disjSum U).card) *
        (principalMinorDet (bipartiteLift T) (S.disjSum U) *
          finitePermutationSum ((bipartiteLift T).submatrix
            (fun x : {x : Sum Iota Iota // Not (Membership.mem (S.disjSum U) x)} => x.val)
            (fun x : {x : Sum Iota Iota // Not (Membership.mem (S.disjSum U) x)} => x.val))) =
      if S.card = U.card then
        2 * ((-1 : R) ^ U.card * (U.card : R) *
          (rectangularMinorDet T S U ^ 2 *
            rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) ^ 2))
      else 0 := by
  classical
  rw [hamiltonianBipartite_principalMinor]
  by_cases hCard : S.card = U.card
  next =>
    simp only [if_pos hCard]
    rw [hamiltonianBipartite_complementaryPermanent T S U hCard,
      Finset.card_disjSum, hCard, Nat.cast_add]
    have hEven : (-1 : R) ^ (U.card + U.card) = 1 := by
      rw [pow_add, <- mul_pow]
      simp
    rw [hEven]
    ring
  next =>
    simp only [if_neg hCard, zero_mul, mul_zero]

theorem hamiltonianBipartiteLiuIdentity (T : Matrix Iota Iota R) :
    hamiltonianLiuSum (bipartiteLift T) = 2 * hamiltonianBipartiteLiuPacket T := by
  classical
  let W : Finset (Sum Iota Iota) -> R := fun V =>
    ((V.card : R) * (-1 : R) ^ V.card) *
      (principalMinorDet (bipartiteLift T) V *
        finitePermutationSum ((bipartiteLift T).submatrix
          (fun x : {x : Sum Iota Iota // Not (Membership.mem V x)} => x.val)
          (fun x : {x : Sum Iota Iota // Not (Membership.mem V x)} => x.val)))
  let F : Finset Iota -> R := fun U =>
    (-1 : R) ^ U.card * (U.card : R) *
      Finset.sum (Finset.univ.powersetCard U.card) (fun S =>
        rectangularMinorDet T S U ^ 2 *
          rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) ^ 2)
  let e : Equiv (Prod (Finset Iota) (Finset Iota)) (Finset (Sum Iota Iota)) :=
    Finset.sumEquiv.toEquiv.symm
  have hReindex : Finset.sum Finset.univ W =
      Finset.sum Finset.univ
        (fun p : Prod (Finset Iota) (Finset Iota) => W (p.1.disjSum p.2)) :=
    (Equiv.sum_comp e W).symm
  have hInner (U : Finset Iota) :
      Finset.sum Finset.univ (fun S : Finset Iota => W (S.disjSum U)) = 2 * F U := by
    have hFilter :
        (Finset.univ : Finset (Finset Iota)).filter (fun S => S.card = U.card) =
          Finset.univ.powersetCard U.card := by
      apply Finset.ext
      intro S
      simp [Finset.mem_powersetCard]
    calc
      _ = Finset.sum Finset.univ (fun S : Finset Iota =>
          if S.card = U.card then
            2 * ((-1 : R) ^ U.card * (U.card : R) *
              (rectangularMinorDet T S U ^ 2 *
                rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) ^ 2))
          else 0) := by
        apply Finset.sum_congr rfl
        intro S hS
        exact hamiltonianBipartiteLiu_term T S U
      _ = Finset.sum (Finset.univ.powersetCard U.card) (fun S =>
          2 * ((-1 : R) ^ U.card * (U.card : R) *
            (rectangularMinorDet T S U ^ 2 *
              rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) ^ 2))) := by
        rw [<- Finset.sum_filter, hFilter]
      _ = 2 * F U := by
        simp only [F, Finset.mul_sum]
  change -Finset.sum Finset.univ W = 2 * (-Finset.sum Finset.univ F)
  rw [hReindex, Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [hInner]
  rw [<- Finset.mul_sum, mul_neg]

theorem hamiltonianBipartiteCycleIdentity (T : Matrix Iota Iota Real) :
    (Fintype.card Iota : Real) * hamiltonianCycleSum (bipartiteLift T) =
      hamiltonianBipartiteLiuPacket T := by
  classical
  have h := hamiltonianLiuIdentity (bipartiteLift T)
  rw [hamiltonianBipartiteLiuIdentity, Fintype.card_sum, Nat.cast_add] at h
  nlinarith

end PrimeFactorOscillations
