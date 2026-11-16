/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCycleScaling

/-! # Exact entropy and common cycle weight of the actual prime scaling -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimeCrossAdjacency (m : Nat) : Matrix (Fin m) (Fin m) Real :=
  fun i j => if Nat.Prime (2 * i.val + 2 * j.val + 3) then 1 else 0

def hamiltonianPrimeLeftScale (m : Nat) (z : Sum (Fin m) (Fin m) -> Real)
    (i : Fin m) : Real :=
  (1 + z (Sum.inl i)) * (Real.log (2 * m : Nat) / (2 * m : Nat))

def hamiltonianPrimeRightScale (m : Nat) (z : Sum (Fin m) (Fin m) -> Real)
    (j : Fin m) : Real := 1 + z (Sum.inr j)

theorem hamiltonian_prime_edge_scalar_positive (m : Nat) (hm : 1 <= m) :
    0 < Real.log (2 * m : Nat) / (2 * m : Nat) := by
  have hTwo : (1 : Real) < (2 * m : Nat) := by exact_mod_cast (by omega : 1 < 2 * m)
  exact div_pos (Real.log_pos hTwo) (by linarith only [hTwo])

theorem hamiltonian_prime_scaling_factors_positive (m : Nat) (hm : 1 <= m)
    (z : Sum (Fin m) (Fin m) -> Real) (hPos : forall i, 0 < 1 + z i) :
    And (forall i, 0 < hamiltonianPrimeLeftScale m z i)
      (forall j, 0 < hamiltonianPrimeRightScale m z j) := by
  constructor
  . intro i
    exact mul_pos (hPos _) (hamiltonian_prime_edge_scalar_positive m hm)
  . intro j
    exact hPos _

theorem hamiltonian_prime_scaled_cross_factorization (m : Nat)
    (z : Sum (Fin m) (Fin m) -> Real) :
    hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z =
      hamiltonianCrossScaled (hamiltonianPrimeCrossAdjacency m)
        (hamiltonianPrimeLeftScale m z) (hamiltonianPrimeRightScale m z) := by
  ext i j
  simp only [hamiltonianScaledCross, hamiltonian_prime_cross_formula,
    hamiltonianCrossScaled, hamiltonianPrimeCrossAdjacency,
    hamiltonianPrimeLeftScale, hamiltonianPrimeRightScale]
  split_ifs <;> ring

theorem hamiltonian_prime_entropy_log_potentials (m : Nat) (hm : 1 <= m)
    (z : Sum (Fin m) (Fin m) -> Real) (hPos : forall i, 0 < 1 + z i)
    (i j : Fin m)
    (hEntry : Not (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j = 0)) :
    Real.log (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) =
      Real.log (hamiltonianPrimeLeftScale m z i) +
        Real.log (hamiltonianPrimeRightScale m z j) := by
  have hFactors := hamiltonian_prime_scaling_factors_positive m hm z hPos
  rw [hamiltonian_prime_scaled_cross_factorization] at hEntry
  rw [hamiltonian_prime_scaled_cross_factorization]
  by_cases hp : Nat.Prime (2 * i.val + 2 * j.val + 3)
  . simp only [hamiltonianCrossScaled, hamiltonianPrimeCrossAdjacency, hp,
      ite_true, mul_one]
    exact Real.log_mul (ne_of_gt (hFactors.1 i)) (ne_of_gt (hFactors.2 j))
  . exfalso
    apply hEntry
    simp only [hamiltonianCrossScaled, hamiltonianPrimeCrossAdjacency, hp,
      ite_false, mul_zero, zero_mul]

theorem hamiltonian_prime_entropy_value (m : Nat) (hm : 1 <= m)
    (z : Sum (Fin m) (Fin m) -> Real) (hPos : forall i, 0 < 1 + z i)
    (hRows : forall i, Finset.univ.sum (fun j =>
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i =>
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1) :
    hamiltonianCrossEntropy (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z) =
      -Finset.univ.sum (fun i => Real.log (hamiltonianPrimeLeftScale m z i)) -
        Finset.univ.sum (fun j => Real.log (hamiltonianPrimeRightScale m z j)) :=
  hamiltonian_stochastic_entropy_value _ _ _ hRows hCols
    (hamiltonian_prime_entropy_log_potentials m hm z hPos)

theorem hamiltonian_prime_entropy_maximum (m : Nat) (hm : 1 <= m)
    (z : Sum (Fin m) (Fin m) -> Real) (hPos : forall i, 0 < 1 + z i)
    (hRows : forall i, Finset.univ.sum (fun j =>
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i =>
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1)
    (X : Matrix (Fin m) (Fin m) Real) (hX : forall i j, 0 <= X i j)
    (hXRows : forall i, Finset.univ.sum (fun j => X i j) = 1)
    (hXCols : forall j, Finset.univ.sum (fun i => X i j) = 1)
    (hXSupport : forall i j, Not (Nat.Prime (2 * i.val + 2 * j.val + 3)) -> X i j = 0) :
    hamiltonianCrossEntropy X <=
      hamiltonianCrossEntropy (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z) := by
  haveI : NeZero m := { out := by omega }
  have hFactors := hamiltonian_prime_scaling_factors_positive m hm z hPos
  have hSupport (i j : Fin m)
      (hZero : hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j = 0) :
      X i j = 0 := by
    apply hXSupport i j
    intro hp
    rw [hamiltonian_prime_scaled_cross_factorization] at hZero
    simp only [hamiltonianCrossScaled, hamiltonianPrimeCrossAdjacency, hp,
      ite_true, mul_one] at hZero
    exact (ne_of_gt (mul_pos (hFactors.1 i) (hFactors.2 j))) hZero
  exact hamiltonian_stochastic_entropy_maximum _ X _ _
    (hamiltonian_scaled_cross_nonnegative _ z hPos
      (hamiltonian_prime_cross_nonnegative m hm)) hX hRows hCols hXRows hXCols
    hSupport (hamiltonian_prime_entropy_log_potentials m hm z hPos)

theorem hamiltonian_prime_cycle_entropy_weight (m : Nat) (hm : 1 <= m)
    (z : Sum (Fin m) (Fin m) -> Real) (hPos : forall i, 0 < 1 + z i)
    (hRows : forall i, Finset.univ.sum (fun j =>
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i =>
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1) :
    hamiltonianCycleSum (bipartiteLift
      (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)) =
      Real.exp (-2 * hamiltonianCrossEntropy
        (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)) *
          hamiltonianCycleSum (bipartiteLift (hamiltonianPrimeCrossAdjacency m)) := by
  have hFactors := hamiltonian_prime_scaling_factors_positive m hm z hPos
  have hValue := hamiltonian_prime_entropy_value m hm z hPos hRows hCols
  have h := hamiltonian_cycle_sum_entropy_scaling (hamiltonianPrimeCrossAdjacency m)
    (hamiltonianPrimeLeftScale m z) (hamiltonianPrimeRightScale m z)
    (hamiltonianCrossEntropy (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z))
    hFactors.1 hFactors.2 hValue
  rwa [<- hamiltonian_prime_scaled_cross_factorization] at h

end PrimeFactorOscillations.LPF
