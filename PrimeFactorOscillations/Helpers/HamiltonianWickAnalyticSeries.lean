/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedWickTaylor
import PrimeFactorOscillations.Helpers.HamiltonianWickSeriesCoefficients

/-! # Actual analytic Wick coefficients in the maintained power-series model

The full mixed Gaussian recursion is lifted by the actual Taylor
homomorphism. Every finite support/profile series is retained. The actual
stochastic compensated rook coefficients therefore agree with the complete
formal Wick sum at every finite cutoff. Only identically zero high-degree
coefficients are removed.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota J : Type*} [Fintype Iota] [DecidableEq Iota]

def gaussianCovarianceTaylorSeries (z : Complex -> Iota -> Complex)
    (row : J -> Iota -> Complex) : Matrix J J (PowerSeries Complex) :=
  fun i j => wickTaylorSeries
    (fun s => gaussianLinearCovariance (z s) (row i) (row j))

theorem gaussianLinearCovariance_analyticAt
    (z : Complex -> Iota -> Complex) (a b : Iota -> Complex) (s : Complex)
    (hz : forall j, AnalyticAt Complex (fun w => z w j) s) :
    AnalyticAt Complex (fun w => gaussianLinearCovariance (z w) a b) s := by
  unfold gaussianLinearCovariance
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact ((hz j).mul analyticAt_const).mul analyticAt_const

theorem gaussianLinearWickValue_analyticAt
    (z : Complex -> Iota -> Complex) (xs : List (Iota -> Complex)) (s : Complex)
    (hz : forall j, AnalyticAt Complex (fun w => z w j) s) :
    AnalyticAt Complex (fun w => gaussianLinearWickValue (z w) xs) s :=
  gaussianPolynomialState_analyticAt z s hz (gaussianLinearProduct xs)

theorem gaussianLinearWickValue_taylor_series
    (z : Complex -> Iota -> Complex) (row : J -> Iota -> Complex)
    (hz : forall j, AnalyticAt Complex (fun w => z w j) 0)
    (e : Nat) (xs : List J) (hLen : xs.length = 2 * e) :
    wickTaylorSeries (fun s => gaussianLinearWickValue (z s) (xs.map row)) =
      wickSeriesPairMoment (gaussianCovarianceTaylorSeries z row) e xs := by
  induction e generalizing xs with
  | zero =>
    cases xs with
    | nil =>
      simp only [List.map_nil, gaussianLinearWickValue_nil, wickSeriesPairMoment]
      simpa only [map_one] using wickTaylorSeries_const 1
    | cons i xs => simp only [List.length_cons] at hLen; omega
  | succ e ih =>
    cases xs with
    | nil => simp only [List.length_nil] at hLen; omega
    | cons i xs =>
      have hRec :
          (fun s : Complex => gaussianLinearWickValue (z s) ((i :: xs).map row)) =
          (fun s => Finset.sum (Finset.range xs.length) (fun k =>
            gaussianLinearCovariance (z s) (row i) (row (xs.getD k i)) *
              gaussianLinearWickValue (z s) ((xs.eraseIdx k).map row))) := by
        funext s
        rw [List.map_cons, gaussianLinearWickValue_cons, List.length_map]
        apply Finset.sum_congr rfl
        intro k hk
        rw [listMap_getD_lt row xs k i (fun _ => 0) (Finset.mem_range.mp hk),
          <- listMap_eraseIdx_eq row xs k]
      have hAnalytic (k : Nat) :
          AnalyticAt Complex (fun s =>
            gaussianLinearCovariance (z s) (row i) (row (xs.getD k i)) *
              gaussianLinearWickValue (z s) ((xs.eraseIdx k).map row)) 0 :=
        (gaussianLinearCovariance_analyticAt z _ _ 0 hz).mul
          (gaussianLinearWickValue_analyticAt z _ 0 hz)
      rw [hRec, wickTaylorSeries_finset_sum _ _ (fun k _ => hAnalytic k),
        wickSeriesPairMoment]
      apply Finset.sum_congr rfl
      intro k hk
      have hErase := List.length_eraseIdx_add_one (Finset.mem_range.mp hk)
      have hEraseLen : (xs.eraseIdx k).length = 2 * e := by
        simp only [List.length_cons] at hLen
        omega
      calc
        _ = wickTaylorSeries
              (fun s => gaussianLinearCovariance (z s) (row i) (row (xs.getD k i))) *
            wickTaylorSeries
              (fun s => gaussianLinearWickValue (z s) ((xs.eraseIdx k).map row)) :=
          wickTaylorSeries_mul _ _
            (gaussianLinearCovariance_analyticAt z _ _ 0 hz)
            (gaussianLinearWickValue_analyticAt z _ 0 hz)
        _ = _ := by
          rw [ih _ hEraseLen]
          rfl

theorem gaussianWickProfile_taylor_series
    (z : Complex -> Iota -> Complex) (row : J -> Iota -> Complex)
    (hz : forall j, AnalyticAt Complex (fun w => z w j) 0)
    (e : Nat) (d : Composition (2 * e)) (label : Fin d.length -> J) :
    wickTaylorSeries (fun s => gaussianWickProfile (z s) row d label) =
      wickSeriesProfile (gaussianCovarianceTaylorSeries z row) e d label := by
  unfold gaussianWickProfile wickSeriesProfile
  change wickTaylorSeries
      ((fun _ => Finset.prod Finset.univ (fun i => wickVertexCoefficient (d.blocksFun i))) *
        (fun s => gaussianLinearWickValue (z s) ((wickProfileList d label).map row))) = _
  rw [wickTaylorSeries_mul _ _ analyticAt_const
    (gaussianLinearWickValue_analyticAt z _ 0 hz), wickTaylorSeries_const,
    gaussianLinearWickValue_taylor_series z row hz e _ (wickProfileList_length d label)]

variable [Fintype J] [DecidableEq J]

theorem gaussianWickSupportProfile_taylor_series
    (z : Complex -> Iota -> Complex) (row : J -> Iota -> Complex)
    (hz : forall j, AnalyticAt Complex (fun w => z w j) 0)
    (e : Nat) (S : Finset J) (d : Composition (2 * e)) :
    wickTaylorSeries (fun s => gaussianWickSupportProfile (z s) row e S d) =
      wickSeriesSupportProfile (gaussianCovarianceTaylorSeries z row) e S d := by
  unfold gaussianWickSupportProfile wickSeriesSupportProfile
  by_cases hLen : d.length = S.card
  case pos =>
    simp only [dite_eq_left hLen]
    exact gaussianWickProfile_taylor_series z row hz e d _
  case neg =>
    simp only [dite_eq_right hLen]
    simpa only [map_zero] using wickTaylorSeries_const 0

theorem gaussianWickDiagramCoefficient_taylor_series
    (z : Complex -> Iota -> Complex) (row : J -> Iota -> Complex)
    (hz : forall j, AnalyticAt Complex (fun w => z w j) 0) (e v : Nat) :
    wickTaylorSeries (fun s => gaussianWickDiagramCoefficient (z s) row e v) =
      wickSeriesDiagramCoefficient (gaussianCovarianceTaylorSeries z row) e v := by
  unfold gaussianWickDiagramCoefficient wickSeriesDiagramCoefficient
  rw [wickTaylorSeries_finset_sum _ _
    (fun S _ => Finset.analyticAt_fun_sum _
      (fun d _ => gaussianWickSupportProfile_analyticAt z row 0 hz e S d))]
  apply Finset.sum_congr rfl
  intro S hS
  rw [wickTaylorSeries_finset_sum _ _
    (fun d _ => gaussianWickSupportProfile_analyticAt z row 0 hz e S d)]
  apply Finset.sum_congr rfl
  intro d hd
  exact gaussianWickSupportProfile_taylor_series z row hz e S d

theorem wickSeriesDiagramCoefficient_coeff_zero_of_lt
    (G : Matrix J J (PowerSeries Complex))
    (hZero : forall i j, PowerSeries.coeff 0 (G i j) = 0)
    (e v k : Nat) (hk : k < e) :
    PowerSeries.coeff k (wickSeriesDiagramCoefficient G e v) = 0 := by
  unfold wickSeriesDiagramCoefficient
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  unfold wickSeriesSupportProfile
  by_cases hLen : d.length = S.card
  case pos =>
    simp only [dite_eq_left hLen, wickSeriesProfile, PowerSeries.coeff_C_mul,
      wickSeriesPairMoment_coeff_zero_of_lt G hZero e k _ hk, mul_zero]
  case neg => simp only [dite_eq_right hLen, map_zero]

def realGaussianCovarianceTaylorSeries (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) : Matrix Iota Iota (PowerSeries Complex) :=
  gaussianCovarianceTaylorSeries
    (fun s j => s * realGaussianEigenVariances M hM j /
      (1 + s * realGaussianEigenVariances M hM j)) (realGaussianEigenRows M hM)

theorem realGaussianCovarianceTaylorSeries_coeff_zero
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (i j : Iota) :
    PowerSeries.coeff 0 (realGaussianCovarianceTaylorSeries M hM i j) = 0 := by
  simp [realGaussianCovarianceTaylorSeries, gaussianCovarianceTaylorSeries,
    wickTaylorSeries_coeff, iteratedDeriv_zero, gaussianLinearCovariance]

theorem stochastic_compensated_taylor_wick_series {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q rho : Real) (H k : Nat)
    (hn : 0 < n) (hq : (n : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hk : k <= H) :
    PowerSeries.coeff k (wickTaylorSeries
        (hamiltonianCompensatedRook (centeredKernel T q))) =
      PowerSeries.coeff k
        (Finset.sum (Finset.range (H + 1)) (fun e =>
          Finset.sum (Finset.range (e + 1)) (fun v =>
            wickSeriesDiagramCoefficient
              (realGaussianCovarianceTaylorSeries (bipartiteLift (centeredKernel T q))
                (bipartiteLift_hermitian (centeredKernel T q))) e v))) := by
  let M := bipartiteLift (centeredKernel T q)
  let hM := bipartiteLift_hermitian (centeredKernel T q)
  let z := fun s : Complex => fun j =>
    s * realGaussianEigenVariances M hM j / (1 + s * realGaussianEigenVariances M hM j)
  let G := realGaussianCovarianceTaylorSeries M hM
  have hz : forall j, AnalyticAt Complex (fun s => z s j) 0 := by
    intro j
    exact (analyticAt_id.mul analyticAt_const).div
      (analyticAt_const.add (analyticAt_id.mul analyticAt_const)) (by simp)
  have hReadout := stochastic_compensated_taylor_wick_readout T q rho k
    hn hq hRow hCol hNorm
  change PowerSeries.coeff k
      (wickTaylorSeries (hamiltonianCompensatedRook (centeredKernel T q))) =
    Finset.sum (Finset.range (k + 1)) (fun e =>
      Finset.sum (Finset.range (e + 1)) (fun v =>
        PowerSeries.coeff k
          (wickTaylorSeries (fun s => gaussianWickDiagramCoefficient (z s)
            (realGaussianEigenRows M hM) e v)))) at hReadout
  simp_rw [gaussianWickDiagramCoefficient_taylor_series z
    (realGaussianEigenRows M hM) hz] at hReadout
  rw [hReadout]
  simp only [map_sum]
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hk 1))
  intro e he hNot
  have hGe : k + 1 <= e :=
    Nat.le_of_not_gt (fun hLt => hNot (Finset.mem_range.mpr hLt))
  apply Finset.sum_eq_zero
  intro v hv
  exact wickSeriesDiagramCoefficient_coeff_zero_of_lt G
    (realGaussianCovarianceTaylorSeries_coeff_zero M hM) e v k (by omega)

end PrimeFactorOscillations
