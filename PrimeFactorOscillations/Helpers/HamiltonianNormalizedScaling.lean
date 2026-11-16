/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianNormalizedDegreeGap

/-! # Stochastic repair from the actual normalized degree mode

The average degree and weighted mode are computed from the same matrix.
All positive scaling, support, cap, and operator outputs share one witness.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

def hamiltonianCrossRowDegrees (T : Matrix Iota Iota Real) (i : Iota) : Real :=
  Finset.univ.sum (fun j => T i j)

def hamiltonianCrossColumnDegrees (T : Matrix Iota Iota Real) (j : Iota) : Real :=
  Finset.univ.sum (fun i => T i j)

def hamiltonianCrossMeanDegree (T : Matrix Iota Iota Real) (q : Real) : Real :=
  q * Finset.univ.sum (hamiltonianCrossRowDegrees T)

theorem hamiltonian_cross_degree_totals (T : Matrix Iota Iota Real) :
    Finset.univ.sum (hamiltonianCrossRowDegrees T) =
      Finset.univ.sum (hamiltonianCrossColumnDegrees T) := by
  exact Finset.sum_comm

theorem hamiltonian_uniform_degree_mean_error
    (r : Iota -> Real) (q eps : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (he : 0 <= eps)
    (hr : forall i, abs (r i - 1) <= eps) :
    abs (q * Finset.univ.sum r - 1) <= eps := by
  have hn : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hn]
  have hId : q * Finset.univ.sum r - 1 =
      q * Finset.univ.sum (fun i => r i - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    nlinarith only [hq]
  rw [hId, abs_mul, abs_of_nonneg hq0]
  have hSum := (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i => r i - 1)).trans
    (Finset.sum_le_sum (fun i _ => hr i))
  calc
    _ <= q * Finset.univ.sum (fun _ : Iota => eps) :=
      mul_le_mul_of_nonneg_left hSum hq0
    _ = eps := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc
        q * ((Fintype.card Iota : Real) * eps) =
            ((Fintype.card Iota : Real) * q) * eps := by ring
        _ = _ := by rw [hq, one_mul]

def hamiltonianActualDegreeNormalizedCross (T : Matrix Iota Iota Real) :
    Matrix Iota Iota Real :=
  hamiltonianDegreeNormalizedCross T (hamiltonianCrossRowDegrees T)
    (hamiltonianCrossColumnDegrees T)

def hamiltonianActualDegreeNormalizedMode (T : Matrix Iota Iota Real) (q : Real) :
    Matrix Iota Iota Real :=
  hamiltonianDegreeNormalizedMode (hamiltonianCrossRowDegrees T)
    (hamiltonianCrossColumnDegrees T) q (hamiltonianCrossMeanDegree T q)

theorem hamiltonian_actual_normalized_degree_gap
    (T : Matrix Iota Iota Real) (q eps rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (he0 : 0 <= eps) (he1 : eps <= 1 / 2) (hp0 : 0 <= rho) (hp1 : rho <= 1)
    (hRow : forall i, abs (hamiltonianCrossRowDegrees T i - 1) <= eps)
    (hCol : forall j, abs (hamiltonianCrossColumnDegrees T j - 1) <= eps)
    (hNorm : norm (hamiltonianActualDegreeNormalizedCross T -
      hamiltonianActualDegreeNormalizedMode T q) <= rho) :
    norm (centeredKernel T q) <= rho + 8 * eps := by
  exact hamiltonian_normalized_degree_centered_gap T
    (hamiltonianCrossRowDegrees T) (hamiltonianCrossColumnDegrees T)
    q (hamiltonianCrossMeanDegree T q) eps rho hq he0 he1 hp0 hp1 hRow hCol
    (hamiltonian_uniform_degree_mean_error (hamiltonianCrossRowDegrees T) q eps hq he0 hRow)
    hNorm

theorem hamiltonian_actual_stochastic_repair_from_normalized_gap
    (T : Matrix Iota Iota Real) (q a eps delta : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (he0 : 0 < eps) (he1 : eps <= 1 / 2)
    (hd0 : 0 < delta) (hd1 : delta < 1) (hMargin : 28 * eps <= delta)
    (hT : forall i j, 0 <= T i j)
    (hRow : forall i, abs (hamiltonianCrossRowDegrees T i - 1) <= eps)
    (hCol : forall j, abs (hamiltonianCrossColumnDegrees T j - 1) <= eps)
    (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (hamiltonianActualDegreeNormalizedCross T -
      hamiltonianActualDegreeNormalizedMode T q) <= 1 - delta)
    (hSmall : eps * hamiltonianDiffuseInverseBudget (a + 9 * eps) (1 - delta / 2) ^ 2 <=
      1 / 256) :
    let R := 4 * hamiltonianDiffuseInverseBudget (a + 9 * eps) (1 - delta / 2) * eps
    exists z : Sum Iota Iota -> Real,
      norm z <= R /\
      (forall i, 0 < 1 + z i) /\
      (forall i j, 0 <= hamiltonianScaledCross T z i j) /\
      (forall i, Finset.univ.sum (fun j => hamiltonianScaledCross T z i j) = 1) /\
      (forall j, Finset.univ.sum (fun i => hamiltonianScaledCross T z i j) = 1) /\
      (forall i j, hamiltonianScaledCross T z i j = 0 <-> T i j = 0) /\
      (forall i j, hamiltonianScaledCross T z i j <= (1 + R) ^ 2 * (a * q)) /\
      norm (hamiltonianScaledCross T z - T) <= (2 * R + R ^ 2) * (1 + eps) := by
  have hRaw := hamiltonian_actual_normalized_degree_gap T q eps (1 - delta)
    hq he0.le he1 (by linarith only [hd1]) (by linarith only [hd0]) hRow hCol hNorm
  have hAvail : norm (centeredKernel T q) <= (1 - delta / 2) - 6 * eps := by
    linarith only [hRaw, hMargin]
  exact hamiltonian_actual_diffuse_stochastic_repair T q a eps (1 - delta / 2)
    hq ha he0 he1 hT hRow hCol hUpper hAvail
    (by linarith only [hd1]) (by linarith only [hd0]) hSmall

end PrimeFactorOscillations
