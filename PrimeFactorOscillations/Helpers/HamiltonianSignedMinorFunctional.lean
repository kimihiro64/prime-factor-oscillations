/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPhysicalOccupancy

/-! # The actual finite signed minor functional

The ambient support is the full finite vertex set throughout.
Coordinate, rank and quadratic readouts retain every overlap and
both orders of each off-diagonal pair.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianSupportIndicator (S : Finset Iota) (i : Iota) : Real :=
  if Membership.mem S i then 1 else 0

def hamiltonianSignedMinorFunctional (M : Matrix Iota Iota Real) :
    Module.Dual Real (Finset Iota -> Real) where
  toFun f := Finset.univ.sum (fun S : Finset Iota =>
    -((S.card : Real) / 2) * principalMinorDet M S * f S)
  map_add' f g := by
    change Finset.univ.sum (fun S : Finset Iota =>
      -((S.card : Real) / 2) * principalMinorDet M S * (f S + g S)) = _
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    change Finset.univ.sum (fun S : Finset Iota =>
      -((S.card : Real) / 2) * principalMinorDet M S * (c * f S)) =
      c * Finset.univ.sum (fun S : Finset Iota =>
        -((S.card : Real) / 2) * principalMinorDet M S * f S)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    ring

theorem hamiltonian_support_indicator_square (S : Finset Iota) (i : Iota) :
    hamiltonianSupportIndicator S i * hamiltonianSupportIndicator S i =
      hamiltonianSupportIndicator S i := by
  by_cases h : Membership.mem S i <;> simp [hamiltonianSupportIndicator, h]

theorem hamiltonian_support_indicator_sum (S : Finset Iota) :
    Finset.univ.sum (fun i => hamiltonianSupportIndicator S i) = (S.card : Real) := by
  unfold hamiltonianSupportIndicator
  rw [<- Finset.sum_filter]
  have hFilter : Finset.univ.filter (fun i : Iota => Membership.mem S i) = S := by
    ext i
    simp
  rw [hFilter]
  simp

theorem hamiltonian_support_indicator_weighted_sum (S : Finset Iota) (v : Iota -> Real) :
    Finset.univ.sum (fun i => hamiltonianSupportIndicator S i * v i) = S.sum v := by
  simp only [hamiltonianSupportIndicator, ite_mul, one_mul, zero_mul]
  rw [<- Finset.sum_filter]
  have hFilter : Finset.univ.filter (fun i : Iota => Membership.mem S i) = S := by
    ext i
    simp
  rw [hFilter]

theorem hamiltonian_signed_minor_coordinate (M : Matrix Iota Iota Real) (i : Iota) :
    hamiltonianSignedMinorFunctional M (fun S => hamiltonianSupportIndicator S i) =
      hamiltonianCoordinateMinorMoment M i := by
  rw [hamiltonian_coordinate_minor_moment_sum]
  change Finset.univ.sum (fun S : Finset Iota =>
    -((S.card : Real) / 2) * principalMinorDet M S * hamiltonianSupportIndicator S i) = _
  apply Finset.sum_congr rfl
  intro S hS
  by_cases h : Membership.mem S i <;> simp [hamiltonianSupportIndicator, h]

theorem hamiltonian_signed_minor_coordinate_pair (M : Matrix Iota Iota Real) (i j : Iota) :
    hamiltonianSignedMinorFunctional M
      (fun S => hamiltonianSupportIndicator S i * hamiltonianSupportIndicator S j) =
        hamiltonianCoordinatePairMinorMoment M i j := by
  rw [hamiltonian_coordinate_pair_minor_moment_sum]
  change Finset.univ.sum (fun S : Finset Iota =>
    -((S.card : Real) / 2) * principalMinorDet M S *
      (hamiltonianSupportIndicator S i * hamiltonianSupportIndicator S j)) = _
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hi : Membership.mem S i <;> by_cases hj : Membership.mem S j <;>
    simp [hamiltonianSupportIndicator, hi, hj]

theorem hamiltonian_support_rank_pair_expansion (S : Finset Iota) :
    ((S.card : Real) / 2) * ((S.card : Real) / 2 - 1) =
      (1 / 4 : Real) *
        (Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota =>
          if j = i then 0 else hamiltonianSupportIndicator S i * hamiltonianSupportIndicator S j)) -
            Finset.univ.sum (fun i => hamiltonianSupportIndicator S i)) := by
  let u := hamiltonianSupportIndicator S
  have hCount : Finset.univ.sum u = (S.card : Real) := hamiltonian_support_indicator_sum S
  have hSquare (i : Iota) : u i * u i = u i := hamiltonian_support_indicator_square S i
  have hEach (i : Iota) : Finset.univ.sum (fun j : Iota =>
      if j = i then 0 else u i * u j) = u i * (S.card : Real) - u i := by
    have hPoint (j : Iota) :
        (if j = i then 0 else u i * u j) =
          u i * u j - (if j = i then u i else 0) := by
      by_cases h : j = i
      case pos =>
        subst j
        simp only [ite_true, hSquare, sub_self]
      case neg => simp only [if_neg h, sub_zero]
    calc
      _ = Finset.univ.sum (fun j : Iota => u i * u j - (if j = i then u i else 0)) :=
        Finset.sum_congr rfl (fun j _ => hPoint j)
      _ = u i * Finset.univ.sum u - u i := by
        rw [Finset.sum_sub_distrib, <- Finset.mul_sum]
        simp
      _ = _ := by rw [hCount]
  have hOff : Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota =>
      if j = i then 0 else u i * u j)) =
        (S.card : Real) ^ 2 - (S.card : Real) := by
    calc
      _ = Finset.univ.sum (fun i : Iota => u i * (S.card : Real) - u i) :=
        Finset.sum_congr rfl (fun i _ => hEach i)
      _ = Finset.univ.sum u * (S.card : Real) - Finset.univ.sum u := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = _ := by rw [hCount]; ring
  change ((S.card : Real) / 2) * ((S.card : Real) / 2 - 1) =
    (1 / 4 : Real) * (_ - Finset.univ.sum u)
  rw [hOff, hCount]
  ring

theorem hamiltonian_support_quadratic_pair_expansion
    (S : Finset Iota) (G : Matrix Iota Iota Real) :
    S.sum (fun i => S.sum (fun j => G i j)) =
      Finset.univ.sum (fun i : Iota => G i i * hamiltonianSupportIndicator S i) +
        Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota =>
          if j = i then 0 else G i j * hamiltonianSupportIndicator S i *
            hamiltonianSupportIndicator S j)) := by
  let u := hamiltonianSupportIndicator S
  have hSquare (i : Iota) : u i * u i = u i := hamiltonian_support_indicator_square S i
  have hInner (i : Iota) :
      Finset.univ.sum (fun j : Iota => G i j * u i * u j) =
        u i * S.sum (fun j => G i j) := by
    calc
      _ = u i * Finset.univ.sum (fun j : Iota => u j * G i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [hamiltonian_support_indicator_weighted_sum S]
  have hFull : Finset.univ.sum (fun i : Iota =>
      Finset.univ.sum (fun j : Iota => G i j * u i * u j)) =
        S.sum (fun i => S.sum (fun j => G i j)) := by
    calc
      _ = Finset.univ.sum (fun i : Iota => u i * S.sum (fun j => G i j)) :=
        Finset.sum_congr rfl (fun i _ => hInner i)
      _ = _ := hamiltonian_support_indicator_weighted_sum S _
  have hEach (i : Iota) :
      Finset.univ.sum (fun j : Iota => G i j * u i * u j) =
        G i i * u i + Finset.univ.sum (fun j : Iota =>
          if j = i then 0 else G i j * u i * u j) := by
    have hPoint (j : Iota) :
        G i j * u i * u j =
          (if j = i then G i i * u i else 0) +
            (if j = i then 0 else G i j * u i * u j) := by
      by_cases h : j = i
      case pos =>
        subst j
        simp only [ite_true, add_zero]
        rw [mul_assoc, hSquare]
      case neg => simp only [if_neg h, zero_add]
    calc
      _ = Finset.univ.sum (fun j : Iota =>
          (if j = i then G i i * u i else 0) +
            (if j = i then 0 else G i j * u i * u j)) :=
        Finset.sum_congr rfl (fun j _ => hPoint j)
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  calc
    _ = Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota => G i j * u i * u j)) :=
      hFull.symm
    _ = Finset.univ.sum (fun i : Iota =>
        G i i * u i + Finset.univ.sum (fun j : Iota =>
          if j = i then 0 else G i j * u i * u j)) :=
      Finset.sum_congr rfl (fun i _ => hEach i)
    _ = _ := Finset.sum_add_distrib


def hamiltonianSignedSupportCorrection (G : Matrix Iota Iota Real)
    (v : Iota -> Real) (q : Real) (S : Finset Iota) : Real :=
  ((S.card : Real) / 2) * ((S.card : Real) / 2 - 1) * q +
    S.sum (fun i => S.sum (fun j => G i j)) + 2 * S.sum v

theorem hamiltonian_signed_support_correction_expansion
    (G : Matrix Iota Iota Real) (v : Iota -> Real) (q : Real) (S : Finset Iota) :
    hamiltonianSignedSupportCorrection G v q S =
      (q / 4) *
        (Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota =>
          if j = i then 0 else hamiltonianSupportIndicator S i * hamiltonianSupportIndicator S j)) -
            Finset.univ.sum (fun i => hamiltonianSupportIndicator S i)) +
      Finset.univ.sum (fun i : Iota => G i i * hamiltonianSupportIndicator S i) +
      Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota =>
        if j = i then 0 else G i j * hamiltonianSupportIndicator S i *
          hamiltonianSupportIndicator S j)) +
      2 * Finset.univ.sum (fun i : Iota => v i * hamiltonianSupportIndicator S i) := by
  have hField : S.sum v =
      Finset.univ.sum (fun i : Iota => v i * hamiltonianSupportIndicator S i) := by
    rw [<- hamiltonian_support_indicator_weighted_sum S v]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold hamiltonianSignedSupportCorrection
  rw [hamiltonian_support_rank_pair_expansion, hamiltonian_support_quadratic_pair_expansion, hField]
  ring

theorem hamiltonian_signed_minor_correction_readout
    (M G : Matrix Iota Iota Real) (v : Iota -> Real) (q : Real) :
    hamiltonianSignedMinorFunctional M (hamiltonianSignedSupportCorrection G v q) =
      (q / 4) *
        (Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota =>
          if j = i then 0 else hamiltonianCoordinatePairMinorMoment M i j)) -
            Finset.univ.sum (fun i => hamiltonianCoordinateMinorMoment M i)) +
      Finset.univ.sum (fun i : Iota => G i i * hamiltonianCoordinateMinorMoment M i) +
      Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota =>
        if j = i then 0 else G i j * hamiltonianCoordinatePairMinorMoment M i j)) +
      2 * Finset.univ.sum (fun i : Iota => v i * hamiltonianCoordinateMinorMoment M i) := by
  let L := hamiltonianSignedMinorFunctional M
  let f := fun i : Iota => (fun S : Finset Iota => hamiltonianSupportIndicator S i)
  let pair := fun i j : Iota => (fun S : Finset Iota =>
    hamiltonianSupportIndicator S i * hamiltonianSupportIndicator S j)
  let singles := Finset.univ.sum f
  let pairs := Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota =>
    if j = i then (0 : Finset Iota -> Real) else pair i j))
  let diagonal := Finset.univ.sum (fun i : Iota => HSMul.hSMul (G i i) (f i))
  let offDiagonal := Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota =>
    if j = i then (0 : Finset Iota -> Real) else HSMul.hSMul (G i j) (pair i j)))
  let field := Finset.univ.sum (fun i : Iota => HSMul.hSMul (v i) (f i))
  have hFunction : hamiltonianSignedSupportCorrection G v q =
      HSMul.hSMul (q / 4) (pairs - singles) + diagonal + offDiagonal +
        HSMul.hSMul (2 : Real) field := by
    funext S
    have h := hamiltonian_signed_support_correction_expansion G v q S
    simpa only [pairs, singles, diagonal, offDiagonal, field, f, pair,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, Finset.sum_apply,
      ite_apply, smul_eq_mul, mul_assoc] using h
  have hSingle (i : Iota) : L (f i) = hamiltonianCoordinateMinorMoment M i :=
    hamiltonian_signed_minor_coordinate M i
  have hPair (i j : Iota) : L (pair i j) = hamiltonianCoordinatePairMinorMoment M i j :=
    hamiltonian_signed_minor_coordinate_pair M i j
  change L (hamiltonianSignedSupportCorrection G v q) = _
  rw [hFunction]
  simp only [map_add, map_sub, map_smul, pairs, singles, diagonal, offDiagonal,
    field, map_sum, apply_ite, map_zero, hSingle, hPair, smul_eq_mul]


end PrimeFactorOscillations
