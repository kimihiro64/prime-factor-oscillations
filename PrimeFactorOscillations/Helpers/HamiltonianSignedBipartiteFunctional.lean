/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteSupports
import PrimeFactorOscillations.Helpers.HamiltonianSignedMinorFunctional

/-! # Full weighted two-support readout of the signed functional

The support bijection retains independent row and column subsets.
Every unbalanced determinant is zero, every balanced sign and rank
is exact, and the empty support has its actual zero weight.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianSignedBipartiteFunctional (T : Matrix Iota Iota Real)
    (f : Finset (Sum Iota Iota) -> Real) : Real :=
  -Finset.univ.sum (fun U : Finset Iota =>
    (-1 : Real) ^ U.card * (U.card : Real) *
      (Finset.univ.powersetCard U.card).sum (fun S =>
        rectangularMinorDet T S U ^ 2 * f (S.disjSum U)))

theorem hamiltonian_signed_minor_bipartite (T : Matrix Iota Iota Real)
    (f : Finset (Sum Iota Iota) -> Real) :
    hamiltonianSignedMinorFunctional (bipartiteLift T) f =
      hamiltonianSignedBipartiteFunctional T f := by
  let W := fun V : Finset (Sum Iota Iota) =>
    -((V.card : Real) / 2) * principalMinorDet (bipartiteLift T) V * f V
  let F := fun U : Finset Iota =>
    (-1 : Real) ^ U.card * (U.card : Real) *
      (Finset.univ.powersetCard U.card).sum (fun S =>
        rectangularMinorDet T S U ^ 2 * f (S.disjSum U))
  let e : Equiv (Prod (Finset Iota) (Finset Iota)) (Finset (Sum Iota Iota)) :=
    Finset.sumEquiv.toEquiv.symm
  have hReindex : Finset.univ.sum W =
      Finset.univ.sum (fun p : Prod (Finset Iota) (Finset Iota) => W (p.1.disjSum p.2)) :=
    (Equiv.sum_comp e W).symm
  have hTerm (S U : Finset Iota) :
      W (S.disjSum U) =
        if S.card = U.card then
          -((-1 : Real) ^ U.card * (U.card : Real) *
            (rectangularMinorDet T S U ^ 2 * f (S.disjSum U))) else 0 := by
    dsimp only [W]
    rw [hamiltonianBipartite_principalMinor]
    by_cases h : S.card = U.card
    case pos =>
      rw [if_pos h, if_pos h, Finset.card_disjSum, h, Nat.cast_add]
      ring
    case neg => simp only [if_neg h, mul_zero, zero_mul]
  have hInner (U : Finset Iota) :
      Finset.univ.sum (fun S : Finset Iota => W (S.disjSum U)) = -F U := by
    have hFilter : (Finset.univ : Finset (Finset Iota)).filter
        (fun S => S.card = U.card) = Finset.univ.powersetCard U.card := by
      ext S
      simp [Finset.mem_powersetCard]
    calc
      _ = Finset.univ.sum (fun S : Finset Iota =>
          if S.card = U.card then
            -((-1 : Real) ^ U.card * (U.card : Real) *
              (rectangularMinorDet T S U ^ 2 * f (S.disjSum U))) else 0) :=
        Finset.sum_congr rfl (fun S _ => hTerm S U)
      _ = (Finset.univ.powersetCard U.card).sum (fun S =>
          -((-1 : Real) ^ U.card * (U.card : Real) *
            (rectangularMinorDet T S U ^ 2 * f (S.disjSum U)))) := by
        rw [<- Finset.sum_filter, hFilter]
      _ = -F U := by simp only [F, Finset.mul_sum, Finset.sum_neg_distrib]
  change Finset.univ.sum W = -Finset.univ.sum F
  rw [hReindex, Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [hInner]
  rw [Finset.sum_neg_distrib]

theorem hamiltonian_signed_minor_one_eq_centeredDet
    (T : Matrix Iota Iota Real) (q : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) :
    hamiltonianSignedMinorFunctional (bipartiteLift T) (fun _ => (1 : Real)) =
      Matrix.det ((1 : Matrix Iota Iota Real) -
        (centeredKernel T q).transpose * centeredKernel T q) := by
  rw [hamiltonian_signed_minor_bipartite]
  simpa only [hamiltonianSignedBipartiteFunctional, signedRectangularMinorMoment, mul_one] using
    signedRectangularMinorMoment_eq_centeredDet T q hq hRow hCol

end PrimeFactorOscillations
