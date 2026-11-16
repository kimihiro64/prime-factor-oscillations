/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianNormalizedScaling
import PrimeFactorOscillations.Helpers.HamiltonianWeightedBipartiteModes

/-! # Actual degree roots and native spectral input for stochastic scaling -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

def hamiltonianRowRoot (T : Matrix Iota Iota Real) (i : Iota) : Real :=
  Real.sqrt (hamiltonianCrossRowDegrees T i)

def hamiltonianColumnRoot (T : Matrix Iota Iota Real) (j : Iota) : Real :=
  Real.sqrt (hamiltonianCrossColumnDegrees T j)

def hamiltonianTotalDegree (T : Matrix Iota Iota Real) : Real :=
  Finset.univ.sum (hamiltonianCrossRowDegrees T)

theorem hamiltonian_total_degree_positive (T : Matrix Iota Iota Real)
    (hRow : forall i, 0 < hamiltonianCrossRowDegrees T i) :
    0 < hamiltonianTotalDegree T := by
  let i : Iota := Classical.choice inferInstance
  exact (hRow i).trans_le
    (Finset.single_le_sum (fun j _ => (hRow j).le) (Finset.mem_univ i))

theorem hamiltonian_degree_roots_equal_norms (T : Matrix Iota Iota Real)
    (hRow : forall i, 0 < hamiltonianCrossRowDegrees T i)
    (hCol : forall j, 0 < hamiltonianCrossColumnDegrees T j) :
    (Finset.univ.sum (fun i => hamiltonianRowRoot T i ^ 2) = hamiltonianTotalDegree T) /\
      (Finset.univ.sum (fun j => hamiltonianColumnRoot T j ^ 2) = hamiltonianTotalDegree T) := by
  constructor
  . change Finset.univ.sum (fun i => Real.sqrt (hamiltonianCrossRowDegrees T i) ^ 2) = _
    simp only [Real.sq_sqrt (hRow _).le]
    rfl
  . change Finset.univ.sum (fun j => Real.sqrt (hamiltonianCrossColumnDegrees T j) ^ 2) = _
    simp only [Real.sq_sqrt (hCol _).le]
    exact (hamiltonian_cross_degree_totals T).symm

theorem hamiltonian_actual_normalized_perron_left (T : Matrix Iota Iota Real)
    (hRow : forall i, 0 < hamiltonianCrossRowDegrees T i)
    (hCol : forall j, 0 < hamiltonianCrossColumnDegrees T j) (i : Iota) :
    Finset.univ.sum (fun j => hamiltonianActualDegreeNormalizedCross T i j *
      hamiltonianColumnRoot T j) = hamiltonianRowRoot T i := by
  have hr0 : Not (hamiltonianRowRoot T i = 0) :=
    ne_of_gt (Real.sqrt_pos.mpr (hRow i))
  have hEntry (j : Iota) :
      hamiltonianActualDegreeNormalizedCross T i j * hamiltonianColumnRoot T j =
        T i j / hamiltonianRowRoot T i := by
    have hc0 : Not (hamiltonianColumnRoot T j = 0) :=
      ne_of_gt (Real.sqrt_pos.mpr (hCol j))
    change (T i j / (hamiltonianRowRoot T i * hamiltonianColumnRoot T j)) *
      hamiltonianColumnRoot T j = T i j / hamiltonianRowRoot T i
    field_simp [hr0, hc0]
  simp_rw [hEntry]
  rw [<- Finset.sum_div]
  change hamiltonianCrossRowDegrees T i / hamiltonianRowRoot T i = hamiltonianRowRoot T i
  have hSquare : hamiltonianRowRoot T i ^ 2 = hamiltonianCrossRowDegrees T i :=
    Real.sq_sqrt (hRow i).le
  rw [<- hSquare]
  field_simp [hr0]
  <;> ring

theorem hamiltonian_actual_normalized_perron_right (T : Matrix Iota Iota Real)
    (hRow : forall i, 0 < hamiltonianCrossRowDegrees T i)
    (hCol : forall j, 0 < hamiltonianCrossColumnDegrees T j) (j : Iota) :
    Finset.univ.sum (fun i => hamiltonianActualDegreeNormalizedCross T i j *
      hamiltonianRowRoot T i) = hamiltonianColumnRoot T j := by
  have hc0 : Not (hamiltonianColumnRoot T j = 0) :=
    ne_of_gt (Real.sqrt_pos.mpr (hCol j))
  have hEntry (i : Iota) :
      hamiltonianActualDegreeNormalizedCross T i j * hamiltonianRowRoot T i =
        T i j / hamiltonianColumnRoot T j := by
    have hr0 : Not (hamiltonianRowRoot T i = 0) :=
      ne_of_gt (Real.sqrt_pos.mpr (hRow i))
    change (T i j / (hamiltonianRowRoot T i * hamiltonianColumnRoot T j)) *
      hamiltonianRowRoot T i = T i j / hamiltonianColumnRoot T j
    field_simp [hr0, hc0]
  simp_rw [hEntry]
  rw [<- Finset.sum_div]
  change hamiltonianCrossColumnDegrees T j / hamiltonianColumnRoot T j =
    hamiltonianColumnRoot T j
  have hSquare : hamiltonianColumnRoot T j ^ 2 = hamiltonianCrossColumnDegrees T j :=
    Real.sq_sqrt (hCol j).le
  rw [<- hSquare]
  field_simp [hc0]
  <;> ring

theorem hamiltonian_actual_normalized_mode_identity (T : Matrix Iota Iota Real)
    (q : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, 0 < hamiltonianCrossRowDegrees T i) :
    hamiltonianActualDegreeNormalizedMode T q =
      hamiltonianWeightedCrossMode (hamiltonianRowRoot T)
        (hamiltonianColumnRoot T) (hamiltonianTotalDegree T) := by
  have hn : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : Not (q = 0) := by intro h; rw [h, mul_zero] at hq; norm_num at hq
  have hR0 : Not (hamiltonianTotalDegree T = 0) :=
    ne_of_gt (hamiltonian_total_degree_positive T hRow)
  ext i j
  change (q * hamiltonianRowRoot T i * hamiltonianColumnRoot T j) /
    (q * hamiltonianTotalDegree T) =
      hamiltonianRowRoot T i * hamiltonianColumnRoot T j / hamiltonianTotalDegree T
  field_simp [hq0, hR0]
  <;> ring

theorem hamiltonian_actual_normalized_native_gap
    (T : Matrix Iota Iota Real) (q rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (hp : 0 <= rho)
    (hRow : forall i, 0 < hamiltonianCrossRowDegrees T i)
    (hCol : forall j, 0 < hamiltonianCrossColumnDegrees T j)
    (hSimplePlus : forall x : Sum Iota Iota -> Real,
      (forall i, (bipartiteLift (hamiltonianActualDegreeNormalizedCross T)).mulVec x i = x i) ->
      exists a : Real, forall i,
        x i = a * hamiltonianWeightedPlus (hamiltonianRowRoot T) (hamiltonianColumnRoot T) i)
    (hSimpleMinus : forall x : Sum Iota Iota -> Real,
      (forall i, (bipartiteLift (hamiltonianActualDegreeNormalizedCross T)).mulVec x i = -x i) ->
      exists a : Real, forall i,
        x i = a * hamiltonianWeightedMinus (hamiltonianRowRoot T) (hamiltonianColumnRoot T) i)
    (hSpectrum : forall k : Sum Iota Iota,
      Not ((bipartiteLift_hermitian (hamiltonianActualDegreeNormalizedCross T)).eigenvalues k = 1) ->
      Not ((bipartiteLift_hermitian (hamiltonianActualDegreeNormalizedCross T)).eigenvalues k =
        -(1 : Real)) ->
      abs ((bipartiteLift_hermitian (hamiltonianActualDegreeNormalizedCross T)).eigenvalues k) <= rho) :
    norm (hamiltonianActualDegreeNormalizedCross T -
      hamiltonianActualDegreeNormalizedMode T q) <= rho := by
  have hNorms := hamiltonian_degree_roots_equal_norms T hRow hCol
  rw [hamiltonian_actual_normalized_mode_identity T q hq hRow]
  exact hamiltonian_weighted_simple_spectral_gap
    (hamiltonianActualDegreeNormalizedCross T) (hamiltonianRowRoot T)
    (hamiltonianColumnRoot T) (hamiltonianTotalDegree T) rho
    (ne_of_gt (hamiltonian_total_degree_positive T hRow)) hp hNorms.1 hNorms.2
    (hamiltonian_actual_normalized_perron_left T hRow hCol)
    (hamiltonian_actual_normalized_perron_right T hRow hCol)
    hSimplePlus hSimpleMinus hSpectrum


structure HamiltonianNormalizedSpectralPacket (T : Matrix Iota Iota Real) (rho : Real) : Prop where
  plus_simple : forall x : Sum Iota Iota -> Real,
    (forall i, (bipartiteLift (hamiltonianActualDegreeNormalizedCross T)).mulVec x i = x i) ->
    exists a : Real, forall i,
      x i = a * hamiltonianWeightedPlus (hamiltonianRowRoot T) (hamiltonianColumnRoot T) i
  minus_simple : forall x : Sum Iota Iota -> Real,
    (forall i, (bipartiteLift (hamiltonianActualDegreeNormalizedCross T)).mulVec x i = -x i) ->
    exists a : Real, forall i,
      x i = a * hamiltonianWeightedMinus (hamiltonianRowRoot T) (hamiltonianColumnRoot T) i
  nontrivial : forall k : Sum Iota Iota,
    Not ((bipartiteLift_hermitian (hamiltonianActualDegreeNormalizedCross T)).eigenvalues k = 1) ->
    Not ((bipartiteLift_hermitian (hamiltonianActualDegreeNormalizedCross T)).eigenvalues k =
      -(1 : Real)) ->
    abs ((bipartiteLift_hermitian (hamiltonianActualDegreeNormalizedCross T)).eigenvalues k) <= rho

end PrimeFactorOscillations
