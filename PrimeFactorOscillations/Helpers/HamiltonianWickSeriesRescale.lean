/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAnalyticCoefficientScale
import PrimeFactorOscillations.Helpers.HamiltonianLocalPermanentRemainder

/-! # Full signed Wick-series scaling and the actual physical window

Rescaling is a ring homomorphism. It is carried through every pairing,
support, composition and compensation coefficient before any remainder
estimate. No choice of eigenbasis for a rescaled matrix is required.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_rescale_C (c a : Complex) :
    PowerSeries.rescale c (PowerSeries.C a) = PowerSeries.C a := by
  ext k
  cases k <;> simp [PowerSeries.coeff_rescale, PowerSeries.coeff_C]

theorem wickTaylorSeries_comp_mul
    (f : Complex -> Complex) (hf : AnalyticAt Complex f 0) (c : Complex) :
    wickTaylorSeries (fun z => f (c * z)) = PowerSeries.rescale c (wickTaylorSeries f) := by
  ext k
  rw [wickTaylorSeries_coeff_comp_mul f hf c k, PowerSeries.coeff_rescale]

variable {Iota J : Type*}

theorem wickSeriesPairMoment_rescale
    (G : Matrix J J (PowerSeries Complex)) (c : Complex) (e : Nat) (xs : List J) :
    wickSeriesPairMoment (fun i j => PowerSeries.rescale c (G i j)) e xs =
      PowerSeries.rescale c (wickSeriesPairMoment G e xs) := by
  induction e generalizing xs with
  | zero =>
    cases xs <;> simp only [wickSeriesPairMoment, map_zero, map_one]
  | succ e ih =>
    cases xs with
    | nil => simp only [wickSeriesPairMoment, map_zero]
    | cons i xs =>
      simp only [wickSeriesPairMoment, map_sum, map_mul, ih]

theorem wickSeriesProfile_rescale
    (G : Matrix J J (PowerSeries Complex)) (c : Complex) (e : Nat)
    (d : Composition (2 * e)) (label : Fin d.length -> J) :
    wickSeriesProfile (fun i j => PowerSeries.rescale c (G i j)) e d label =
      PowerSeries.rescale c (wickSeriesProfile G e d label) := by
  simp only [wickSeriesProfile, map_mul, hamiltonian_rescale_C, wickSeriesPairMoment_rescale]

variable [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
theorem wickSeriesSupportProfile_rescale
    (G : Matrix J J (PowerSeries Complex)) (c : Complex) (e : Nat)
    (S : Finset J) (d : Composition (2 * e)) :
    wickSeriesSupportProfile (fun i j => PowerSeries.rescale c (G i j)) e S d =
      PowerSeries.rescale c (wickSeriesSupportProfile G e S d) := by
  unfold wickSeriesSupportProfile
  split_ifs
  case pos h => exact wickSeriesProfile_rescale G c e d _
  case neg h => exact (map_zero _).symm

theorem wickSeriesDiagramCoefficient_rescale
    (G : Matrix J J (PowerSeries Complex)) (c : Complex) (e v : Nat) :
    wickSeriesDiagramCoefficient (fun i j => PowerSeries.rescale c (G i j)) e v =
      PowerSeries.rescale c (wickSeriesDiagramCoefficient G e v) := by
  simp only [wickSeriesDiagramCoefficient, map_sum, wickSeriesSupportProfile_rescale]

theorem wickSeriesTruncatedDiagrams_rescale
    (G : Matrix J J (PowerSeries Complex)) (c : Complex) (H : Nat) :
    wickSeriesTruncatedDiagrams (fun i j => PowerSeries.rescale c (G i j)) H =
      PowerSeries.rescale c (wickSeriesTruncatedDiagrams G H) := by
  simp only [wickSeriesTruncatedDiagrams, map_sum, wickSeriesDiagramCoefficient_rescale]

theorem wickSeriesLowDiagrams_rescale
    (G : Matrix J J (PowerSeries Complex)) (c : Complex) :
    wickSeriesLowDiagrams (fun i j => PowerSeries.rescale c (G i j)) =
      PowerSeries.rescale c (wickSeriesLowDiagrams G) := by
  simp only [wickSeriesLowDiagrams, map_sum, wickSeriesDiagramCoefficient_rescale]

variable [Fintype Iota] [DecidableEq Iota]

theorem covarianceFormalSeries_real_smul
    (M : Matrix Iota Iota Real) (s : Real) :
    covarianceFormalSeries (HSMul.hSMul s M) =
      fun i j => PowerSeries.rescale (s : Complex) (covarianceFormalSeries M i j) := by
  funext i j
  ext k
  cases k with
  | zero =>
    simp only [covarianceFormalSeries_coeff_zero, PowerSeries.coeff_rescale, mul_zero]
  | succ k =>
    rw [covarianceFormalSeries_coeff_succ, PowerSeries.coeff_rescale,
      covarianceFormalSeries_coeff_succ, covarianceSeriesCoefficient_real_smul]
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]

theorem stochastic_compensated_scaled_taylor_covariance_series {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q rho s : Real) (H k : Nat)
    (hn : 0 < n) (hq : (n : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hk : k <= H) :
    PowerSeries.coeff k (wickTaylorSeries
      (fun z => hamiltonianCompensatedRook (centeredKernel T q) ((s : Complex) * z))) =
      PowerSeries.coeff k (wickSeriesTruncatedDiagrams
        (covarianceFormalSeries (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))) H) := by
  have hF : AnalyticAt Complex (hamiltonianCompensatedRook (centeredKernel T q)) 0 :=
    hamiltonianCompensatedRook_analyticOnNhd _ rho hNorm 0 (by simp)
  have h := stochastic_compensated_taylor_covariance_series T q rho H k
    hn hq hRow hCol hNorm hk
  change PowerSeries.coeff k
    (wickTaylorSeries (hamiltonianCompensatedRook (centeredKernel T q))) =
      PowerSeries.coeff k (wickSeriesTruncatedDiagrams
        (covarianceFormalSeries (bipartiteLift (centeredKernel T q))) H) at h
  rw [wickTaylorSeries_coeff_comp_mul _ hF (s : Complex) k, h,
    covarianceFormalSeries_real_smul]
  have hRes := wickSeriesTruncatedDiagrams_rescale
    (covarianceFormalSeries (bipartiteLift (centeredKernel T q))) (s : Complex) H
  calc
    _ = PowerSeries.coeff k (PowerSeries.rescale (s : Complex)
        (wickSeriesTruncatedDiagrams
          (covarianceFormalSeries (bipartiteLift (centeredKernel T q))) H)) :=
      (PowerSeries.coeff_rescale _ _ _).symm
    _ = _ := (congrArg (fun P : PowerSeries Complex => PowerSeries.coeff k P) hRes).symm

theorem stochastic_compensated_scaled_finiteSeriesValue {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q rho s : Real) (H : Nat)
    (hn : 0 < n) (hq : (n : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) :
    hamiltonianFiniteSeriesValue H (wickTaylorSeries
      (fun z => hamiltonianCompensatedRook (centeredKernel T q) ((s : Complex) * z))) =
      hamiltonianFiniteSeriesValue H (wickSeriesTruncatedDiagrams
        (covarianceFormalSeries (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))) H) := by
  unfold hamiltonianFiniteSeriesValue
  apply Finset.sum_congr rfl
  intro k hk
  exact stochastic_compensated_scaled_taylor_covariance_series T q rho s H k
    hn hq hRow hCol hNorm (by have h := Finset.mem_range.mp hk; omega)

end PrimeFactorOscillations
