/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAmplificationCoordinate

/-! # Sharp amplification for the actual centered singular spectrum

The convex chord coefficient controls every eigenvalue together.
The zero-norm case and the rational prime-density constant are explicit.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianSpectralKappa (rho : Real) : Real :=
  if rho = 0 then 2 else hamiltonianAmplificationCoordinate (rho ^ 2) / rho ^ 2

theorem hamiltonian_amplification_coordinate_nonnegative
    (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    0 <= hamiltonianAmplificationCoordinate x := by
  have hPlus : 0 <= Real.log (1 + x) := Real.log_nonneg (by linarith only [hx])
  have hMinusPos : 0 < 1 - x := sub_pos.mpr hx1
  have hMinus : Real.log (1 - x) <= 0 := by
    have h := Real.log_le_log hMinusPos (by linarith only [hx] : 1 - x <= 1)
    simpa only [Real.log_one] using h
  unfold hamiltonianAmplificationCoordinate
  linarith only [hPlus, hMinus]

theorem hamiltonian_spectral_kappa_nonnegative
    (rho : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1) :
    0 <= hamiltonianSpectralKappa rho := by
  unfold hamiltonianSpectralKappa
  split
  next h => norm_num
  next h =>
    have hR2 : rho ^ 2 < 1 := by nlinarith only [hRho0, hRho1]
    exact div_nonneg
      (hamiltonian_amplification_coordinate_nonnegative (rho ^ 2) (sq_nonneg rho) hR2)
      (sq_nonneg rho)

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_matrix_gram_amplification
    (B : Matrix Iota Iota Real) (rho : Real)
    (hRho0 : 0 <= rho) (hRho1 : rho < 1) (hNorm : norm B <= rho) :
    0 < Matrix.det ((1 : Matrix Iota Iota Real) + B.transpose * B) /
      Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B) /\
    Matrix.det ((1 : Matrix Iota Iota Real) + B.transpose * B) /
      Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B) <=
        Real.exp (hamiltonianSpectralKappa rho * Finset.univ.sum (realGramEigenvalues B)) := by
  let v := realGramEigenvalues B
  have hR2 : rho ^ 2 < 1 := by nlinarith only [hRho0, hRho1]
  have hNonneg (i : Iota) : 0 <= v i := realGramEigenvalues_nonnegative B i
  have hUpper (i : Iota) : v i <= rho ^ 2 :=
    realGramEigenvalues_le_norm_bound B rho hRho0 hNorm i
  have hOne (i : Iota) : v i < 1 := lt_of_le_of_lt (hUpper i) hR2
  have hPlus (i : Iota) : 0 < 1 + v i := by linarith only [hNonneg i]
  have hMinus (i : Iota) : 0 < 1 - v i := sub_pos.mpr (hOne i)
  have hDetPlus : Matrix.det ((1 : Matrix Iota Iota Real) + B.transpose * B) =
      Finset.univ.prod (fun i : Iota => 1 + v i) := by
    simpa only [neg_smul, sub_neg_eq_add, neg_mul, neg_neg, one_smul, one_mul,
      v, realGramEigenvalues] using!
      hermitian_det_one_sub_smul (B.transpose * B) (realGramHermitian B) (-1)
  have hDetMinus : Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B) =
      Finset.univ.prod (fun i : Iota => 1 - v i) := by
    simpa only [one_smul, one_mul, v, realGramEigenvalues] using!
      hermitian_det_one_sub_smul (B.transpose * B) (realGramHermitian B) 1
  have hRatio :
      Matrix.det ((1 : Matrix Iota Iota Real) + B.transpose * B) /
        Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B) =
      Finset.univ.prod (fun i : Iota => (1 + v i) / (1 - v i)) := by
    rw [hDetPlus, hDetMinus, Finset.prod_div_distrib]
  have hPoint (i : Iota) :
      (1 + v i) / (1 - v i) <= Real.exp (hamiltonianSpectralKappa rho * v i) := by
    by_cases hZero : rho = 0
    case pos =>
      have hUp : v i <= 0 := by simpa [hZero] using hUpper i
      have hV : v i = 0 := le_antisymm hUp (hNonneg i)
      simp only [hV, add_zero, sub_zero, div_one, mul_zero, Real.exp_zero, le_refl]
    case neg =>
      have hRhoPos : 0 < rho := by positivity
      have hChord := hamiltonian_amplification_coordinate_chord (rho ^ 2) (v i)
        (pow_pos hRhoPos 2) hR2 (hNonneg i) (hUpper i)
      have hKappa : hamiltonianSpectralKappa rho =
          hamiltonianAmplificationCoordinate (rho ^ 2) / rho ^ 2 := by
        simp only [hamiltonianSpectralKappa, if_neg hZero]
      rw [<- hKappa] at hChord
      have hLog : Real.log ((1 + v i) / (1 - v i)) =
          hamiltonianAmplificationCoordinate (v i) :=
        Real.log_div (ne_of_gt (hPlus i)) (ne_of_gt (hMinus i))
      have hExp := Real.exp_log (div_pos (hPlus i) (hMinus i))
      rw [hLog] at hExp
      calc
        _ = Real.exp (hamiltonianAmplificationCoordinate (v i)) := hExp.symm
        _ <= _ := Real.exp_le_exp.mpr hChord
  have hRatioNonneg (i : Iota) : 0 <= (1 + v i) / (1 - v i) :=
    le_of_lt (div_pos (hPlus i) (hMinus i))
  refine And.intro ?_ ?_
  next =>
    rw [hRatio]
    exact Finset.prod_pos (fun i _ => div_pos (hPlus i) (hMinus i))
  next =>
    rw [hRatio]
    calc
      _ <= Finset.univ.prod (fun i : Iota => Real.exp (hamiltonianSpectralKappa rho * v i)) := by
        gcongr with i hi
        all_goals first
          | exact fun i _ => hRatioNonneg i
          | exact fun i _ => hPoint i
          | exact hRatioNonneg _
          | exact hPoint _
      _ = _ := by rw [<- Real.exp_sum, <- Finset.mul_sum]

theorem hamiltonian_matrix_log_amplification
    (B : Matrix Iota Iota Real) (rho : Real)
    (hRho0 : 0 <= rho) (hRho1 : rho < 1) (hNorm : norm B <= rho) :
    Real.log (Matrix.det ((1 : Matrix Iota Iota Real) + B.transpose * B) /
      Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B)) <=
      hamiltonianSpectralKappa rho *
        Finset.univ.sum (fun i => Finset.univ.sum (fun j => B i j ^ 2)) := by
  have h := hamiltonian_matrix_gram_amplification B rho hRho0 hRho1 hNorm
  have hLog := Real.log_le_log h.1 h.2
  rw [Real.log_exp, realGramEigenvalues_sum_eq_energy] at hLog
  exact hLog

theorem stochastic_gram_amplification_upper
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hRho0 : 0 <= rho) (hRho1 : rho < 1)
    (hNorm : norm (centeredKernel T q) <= rho) :
    0 < hamiltonianGramAmplification T q /\
      hamiltonianGramAmplification T q <= Real.exp (hamiltonianSpectralKappa rho * (a - 1)) := by
  have h := hamiltonian_matrix_gram_amplification (centeredKernel T q) rho hRho0 hRho1 hNorm
  have hEnergy : Finset.univ.sum (realGramEigenvalues (centeredKernel T q)) <= a - 1 := by
    rw [realGramEigenvalues_sum_eq_energy]
    exact stochastic_total_energy T q a hq hRow hNonneg hUpper
  have hKappa := hamiltonian_spectral_kappa_nonnegative rho hRho0 hRho1
  exact And.intro h.1 (le_trans h.2 (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hEnergy hKappa)))

theorem hamiltonian_spectral_kappa_three_fifths :
    hamiltonianSpectralKappa (3 / 5 : Real) < 9 / 4 := by
  have hQuadratic := Real.quadratic_le_exp_of_nonneg
    (x := (81 / 100 : Real)) (by norm_num)
  have hExp : (17 / 8 : Real) < Real.exp (81 / 100 : Real) := by
    nlinarith only [hQuadratic]
  have hLog := Real.log_lt_log (by norm_num : (0 : Real) < 17 / 8) hExp
  rw [Real.log_exp] at hLog
  have hCoordinate : hamiltonianAmplificationCoordinate ((3 / 5 : Real) ^ 2) =
      Real.log (17 / 8 : Real) := by
    unfold hamiltonianAmplificationCoordinate
    have h := Real.log_div
      (by norm_num : Not ((1 + (3 / 5 : Real) ^ 2) = 0))
      (by norm_num : Not ((1 - (3 / 5 : Real) ^ 2) = 0))
    rw [<- h]
    congr 1
    norm_num
  have hKappa : hamiltonianSpectralKappa (3 / 5 : Real) =
      (25 / 9 : Real) * Real.log (17 / 8 : Real) := by
    unfold hamiltonianSpectralKappa
    rw [if_neg (by norm_num : Not ((3 / 5 : Real) = 0)), hCoordinate]
    norm_num
    <;> ring
  rw [hKappa]
  nlinarith only [hLog]


theorem hamiltonian_spectral_kappa_positive
    (rho : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1) :
    0 < hamiltonianSpectralKappa rho := by
  by_cases hZero : rho = 0
  case pos => simp only [hamiltonianSpectralKappa, hZero, if_pos rfl]; norm_num
  case neg =>
    have hRhoPos : 0 < rho := by positivity
    have hR2Pos : 0 < rho ^ 2 := pow_pos hRhoPos 2
    have hR2 : rho ^ 2 < 1 := by nlinarith only [hRho0, hRho1]
    have hPlus : 0 < Real.log (1 + rho ^ 2) := Real.log_pos (by linarith only [hR2Pos])
    have hMinus : Real.log (1 - rho ^ 2) <= 0 := by
      have h := Real.log_le_log (sub_pos.mpr hR2)
        (by nlinarith only [sq_nonneg rho] : 1 - rho ^ 2 <= 1)
      simpa only [Real.log_one] using h
    have hCoordinate : 0 < hamiltonianAmplificationCoordinate (rho ^ 2) := by
      unfold hamiltonianAmplificationCoordinate
      linarith only [hPlus, hMinus]
    simp only [hamiltonianSpectralKappa, if_neg hZero]
    exact div_pos hCoordinate hR2Pos

theorem stochastic_gram_amplification_power_bound
    (T : Matrix Iota Iota Real) (q a rho n b : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hRho0 : 0 <= rho) (hRho1 : rho < 1)
    (hNorm : norm (centeredKernel T q) <= rho)
    (hn : 0 < n) (hCap : a - 1 <= b * Real.log n) :
    hamiltonianGramAmplification T q <= n ^ (hamiltonianSpectralKappa rho * b) := by
  have hAmp := stochastic_gram_amplification_upper T q a rho hq hRow hNonneg hUpper
    hRho0 hRho1 hNorm
  have hKappa := hamiltonian_spectral_kappa_nonnegative rho hRho0 hRho1
  have hScaled := mul_le_mul_of_nonneg_left hCap hKappa
  rw [Real.rpow_def_of_pos hn]
  exact le_trans hAmp.2 (Real.exp_le_exp.mpr (by nlinarith only [hScaled]))

theorem stochastic_three_fifths_amplification_power
    (T : Matrix Iota Iota Real) (q a n : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= (3 / 5 : Real))
    (hn : 1 <= n) (hCap : a - 1 <= (3 / 5 : Real) * Real.log n) :
    hamiltonianGramAmplification T q <= n ^ (27 / 20 : Real) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hAmp := stochastic_gram_amplification_power_bound T q a (3 / 5) n (3 / 5)
    hq hRow hNonneg hUpper (by norm_num) (by norm_num) hNorm hn0 hCap
  have hExponent : hamiltonianSpectralKappa (3 / 5 : Real) * (3 / 5 : Real) <=
      (27 / 20 : Real) := by
    nlinarith only [hamiltonian_spectral_kappa_three_fifths]
  exact le_trans hAmp (Real.rpow_le_rpow_of_exponent_le hn hExponent)


theorem hamiltonian_gram_amplification_swap (B : Matrix Iota Iota Real) :
    Matrix.det ((1 : Matrix Iota Iota Real) + B.transpose * B) /
      Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B) =
    Matrix.det ((1 : Matrix Iota Iota Real) + B * B.transpose) /
      Matrix.det ((1 : Matrix Iota Iota Real) - B * B.transpose) := by
  have hPlus := Matrix.det_one_add_mul_comm B.transpose B
  have hMinus :
      Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B) =
      Matrix.det ((1 : Matrix Iota Iota Real) - B * B.transpose) := by
    simpa only [neg_mul, mul_neg, sub_eq_add_neg] using
      Matrix.det_one_add_mul_comm (-B.transpose) B
  rw [hPlus, hMinus]

end PrimeFactorOscillations
