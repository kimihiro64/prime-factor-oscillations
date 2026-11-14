/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Basic.Real.Basic
import PrimeFactorOscillations.Helpers.HamiltonianStochasticParity

/-! # Centered stochastic energy with the full centering term

Nonnegative probability rows with maximum entry a*q have centered squared
energy at most (a-1)*q. Row and column versions and the total Frobenius bound
are derived for the actual kernel. These provide the row norms in the
resolvent-entry estimate used to bound the signed occupancy correction.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*}

theorem centeredProbabilityEnergy_eq (S : Finset Iota) (w : Iota -> Real) (q : Real)
    (hsum : Finset.sum S w = 1) (hq : (S.card : Real) * q = 1) :
    Finset.sum S (fun i => (w i - q) ^ 2) =
      Finset.sum S (fun i => w i ^ 2) - q := by
  have hExpand : Finset.sum S (fun i => (w i - q) ^ 2) =
      Finset.sum S (fun i => w i ^ 2) - 2 * q * Finset.sum S w +
        (S.card : Real) * q ^ 2 := by
    calc
      _ = Finset.sum S (fun i => w i ^ 2 - 2 * q * w i + q ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          <- Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hqSquare : (S.card : Real) * q ^ 2 = q := by
    calc
      _ = ((S.card : Real) * q) * q := by ring
      _ = q := by rw [hq, one_mul]
  rw [hExpand, hsum, hqSquare]
  ring

theorem centeredProbabilityEnergy_le (S : Finset Iota) (w : Iota -> Real) (q a : Real)
    (hsum : Finset.sum S w = 1) (hq : (S.card : Real) * q = 1)
    (hnonneg : forall i, Membership.mem S i -> 0 <= w i)
    (hupper : forall i, Membership.mem S i -> w i <= a * q) :
    Finset.sum S (fun i => (w i - q) ^ 2) <= (a - 1) * q := by
  have hSq : Finset.sum S (fun i => w i ^ 2) <= a * q := by
    calc
      _ <= Finset.sum S (fun i => (a * q) * w i) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [pow_two] using
          mul_le_mul_of_nonneg_right (hupper i hi) (hnonneg i hi)
      _ = a * q := by rw [<- Finset.mul_sum, hsum, mul_one]
  rw [centeredProbabilityEnergy_eq S w q hsum hq]
  calc
    _ <= a * q - q := sub_le_sub_right hSq q
    _ = (a - 1) * q := by ring

variable [Fintype Iota]

theorem stochastic_row_energy (T : Matrix Iota Iota Real) (q a : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hnonneg : forall i j, 0 <= T i j) (hupper : forall i j, T i j <= a * q)
    (i : Iota) :
    Finset.sum Finset.univ (fun j => (centeredKernel T q i j) ^ 2) <= (a - 1) * q := by
  have hqUniv : ((Finset.univ : Finset Iota).card : Real) * q = 1 := by
    simpa only [Finset.card_univ] using hq
  simpa only [centeredKernel, averagingKernel, Matrix.sub_apply] using
    (centeredProbabilityEnergy_le Finset.univ (fun j => T i j) q a (hrow i) hqUniv
      (fun j _ => hnonneg i j) (fun j _ => hupper i j))

theorem stochastic_column_energy (T : Matrix Iota Iota Real) (q a : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hcol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hnonneg : forall i j, 0 <= T i j) (hupper : forall i j, T i j <= a * q)
    (j : Iota) :
    Finset.sum Finset.univ (fun i => (centeredKernel T q i j) ^ 2) <= (a - 1) * q := by
  have hqUniv : ((Finset.univ : Finset Iota).card : Real) * q = 1 := by
    simpa only [Finset.card_univ] using hq
  simpa only [centeredKernel, averagingKernel, Matrix.sub_apply] using
    (centeredProbabilityEnergy_le Finset.univ (fun i => T i j) q a (hcol j) hqUniv
      (fun i _ => hnonneg i j) (fun i _ => hupper i j))

theorem stochastic_total_energy (T : Matrix Iota Iota Real) (q a : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hnonneg : forall i j, 0 <= T i j) (hupper : forall i j, T i j <= a * q) :
    Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
      (fun j => (centeredKernel T q i j) ^ 2)) <= a - 1 := by
  calc
    _ <= Finset.sum Finset.univ (fun _ : Iota => (a - 1) * q) := by
      apply Finset.sum_le_sum
      intro i hi
      exact stochastic_row_energy T q a hq hrow hnonneg hupper i
    _ = (a - 1) * ((Fintype.card Iota : Real) * q) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ = a - 1 := by rw [hq, mul_one]

end PrimeFactorOscillations
