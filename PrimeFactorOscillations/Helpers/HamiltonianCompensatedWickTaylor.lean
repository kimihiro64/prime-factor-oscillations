/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianAmplitudeReadout

/-! # Complete Taylor readout of the actual compensated rook function

Every actual deformation coefficient is a finite sum of the complete Wick
support/profile coefficients. High homogeneous degrees vanish to their true
deformation order; all odd degrees vanish exactly. No infinite Wick series
is integrated or evaluated at parameter one.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem gaussianPolynomialDegreeState_zero_of_bound (z : Iota -> Complex)
    (p : MvPolynomial Iota Complex) (j : Nat)
    (hj : gaussianPolynomialDegreeBound p < j) :
    gaussianPolynomialDegreeState z p j = 0 := by
  unfold gaussianPolynomialDegreeState
  apply Finset.sum_eq_zero
  intro d hd
  have hMember := (Finset.mem_filter.mp hd).1
  have hDegree := (Finset.mem_filter.mp hd).2
  have hLe := Finset.le_sup (f := gaussianStateDegree) hMember
  change gaussianStateDegree d <= gaussianPolynomialDegreeBound p at hLe
  omega

theorem gaussianPolynomialState_by_even_degree (z : Iota -> Complex)
    (p : MvPolynomial Iota Complex) :
    gaussianPolynomialState z p =
      Finset.sum (Finset.range (gaussianPolynomialDegreeBound p + 1))
        (fun e => gaussianPolynomialDegreeState z p (2 * e)) := by
  let D := gaussianPolynomialDegreeBound p
  let f := gaussianPolynomialDegreeState z p
  rw [gaussianPolynomialState_by_degree]
  change Finset.sum (Finset.range (D + 1)) f =
    Finset.sum (Finset.range (D + 1)) (fun e => f (2 * e))
  have hPadding : Finset.sum (Finset.range (D + 1)) f =
      Finset.sum (Finset.range (2 * (D + 1))) f := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hNot
    have hGe : D + 1 <= j :=
      Nat.le_of_not_gt (fun hLt => hNot (Finset.mem_range.mpr hLt))
    exact gaussianPolynomialDegreeState_zero_of_bound z p j (by omega)
  have hSubset :
      (Finset.range (D + 1)).image (fun e => 2 * e) <=
        Finset.range (2 * (D + 1)) := by
    intro j hj
    have hImage := Finset.mem_image.mp hj
    have hLt := Finset.mem_range.mp hImage.choose_spec.1
    rw [<- hImage.choose_spec.2]
    exact Finset.mem_range.mpr (by omega)
  have hDrop :
      Finset.sum ((Finset.range (D + 1)).image (fun e => 2 * e)) f =
        Finset.sum (Finset.range (2 * (D + 1))) f := by
    apply Finset.sum_subset hSubset
    intro j hj hNot
    have hLt := Finset.mem_range.mp hj
    by_cases hEven : j % 2 = 0
    case pos =>
      exfalso
      apply hNot
      apply Finset.mem_image.mpr
      exact Exists.intro (j / 2) (And.intro
        (Finset.mem_range.mpr (by omega)) (by omega))
    case neg =>
      have hRep : j = 2 * (j / 2) + 1 := by omega
      change gaussianPolynomialDegreeState z p j = 0
      rw [hRep]
      exact gaussianPolynomialDegreeState_odd z p (j / 2)
  calc
    _ = Finset.sum (Finset.range (2 * (D + 1))) f := hPadding
    _ = Finset.sum ((Finset.range (D + 1)).image (fun e => 2 * e)) f := hDrop.symm
    _ = _ := Finset.sum_image (fun e he e' he' h => by omega)

theorem gaussianPolynomialState_taylor_truncate
    (z : Complex -> Iota -> Complex)
    (hz : forall j, AnalyticAt Complex (fun w => z w j) 0)
    (p : MvPolynomial Iota Complex) (k : Nat) :
    PowerSeries.coeff k (wickTaylorSeries
        (fun w => gaussianPolynomialState (fun j => w * z w j) p)) =
      Finset.sum (Finset.range (k + 1)) (fun e =>
        PowerSeries.coeff k (wickTaylorSeries
          (fun w => gaussianPolynomialDegreeState (fun j => w * z w j) p (2 * e)))) := by
  let D := gaussianPolynomialDegreeBound p
  let f := fun e (w : Complex) =>
    gaussianPolynomialDegreeState (fun j => w * z w j) p (2 * e)
  have hf : forall e, AnalyticAt Complex (f e) 0 := by
    intro e
    exact gaussianPolynomialDegreeState_analyticAt (fun w j => w * z w j)
      0 (fun j => analyticAt_id.mul (hz j)) p (2 * e)
  have hFull :
      (fun w : Complex => gaussianPolynomialState (fun j => w * z w j) p) =
      (fun w => Finset.sum (Finset.range (D + 1)) (fun e => f e w)) := by
    funext w
    exact gaussianPolynomialState_by_even_degree (fun j => w * z w j) p
  rw [hFull, wickTaylorSeries_finset_sum _ _ (fun e _ => hf e), map_sum]
  change Finset.sum (Finset.range (D + 1))
      (fun e => PowerSeries.coeff k (wickTaylorSeries (f e))) =
    Finset.sum (Finset.range (k + 1))
      (fun e => PowerSeries.coeff k (wickTaylorSeries (f e)))
  by_cases h : k <= D
  case pos =>
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right h 1))
    intro e he hNot
    have hGe : k + 1 <= e :=
      Nat.le_of_not_gt (fun hLt => hNot (Finset.mem_range.mpr hLt))
    have hDerivative := gaussianPolynomialDegreeState_high_derivative_zero z hz p e k
      (by omega)
    simp only [f, wickTaylorSeries_coeff, hDerivative, mul_zero]
  case neg =>
    have hLe : D <= k := by omega
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hLe 1))
    intro e he hNot
    have hGe : D + 1 <= e :=
      Nat.le_of_not_gt (fun hLt => hNot (Finset.mem_range.mpr hLt))
    have hZero : f e = (fun _ => 0) := by
      funext w
      exact gaussianPolynomialDegreeState_zero_of_bound (fun j => w * z w j) p
        (2 * e) (by omega)
    rw [hZero, wickTaylorSeries_const]
    simp

theorem gaussianWickSupportProfile_analyticAt {J : Type*} [Fintype J] [DecidableEq J]
    (z : Complex -> Iota -> Complex) (row : J -> Iota -> Complex) (s : Complex)
    (hz : forall j, AnalyticAt Complex (fun w => z w j) s)
    (e : Nat) (S : Finset J) (d : Composition (2 * e)) :
    AnalyticAt Complex (fun w => gaussianWickSupportProfile (z w) row e S d) s := by
  unfold gaussianWickSupportProfile
  by_cases hLen : d.length = S.card
  case pos =>
    simp only [dite_eq_left hLen]
    unfold gaussianWickProfile gaussianLinearWickValue
    exact analyticAt_const.mul (gaussianPolynomialState_analyticAt z s hz _)
  case neg =>
    simp only [dite_eq_right hLen]
    exact analyticAt_const

theorem gaussianWickDiagramCoefficient_analyticAt {J : Type*} [Fintype J] [DecidableEq J]
    (z : Complex -> Iota -> Complex) (row : J -> Iota -> Complex) (s : Complex)
    (hz : forall j, AnalyticAt Complex (fun w => z w j) s) (e v : Nat) :
    AnalyticAt Complex (fun w => gaussianWickDiagramCoefficient (z w) row e v) s := by
  unfold gaussianWickDiagramCoefficient
  apply Finset.analyticAt_fun_sum
  intro S hS
  apply Finset.analyticAt_fun_sum
  intro d hd
  exact gaussianWickSupportProfile_analyticAt z row s hz e S d

theorem stochastic_compensated_taylor_wick_readout {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q rho : Real) (k : Nat)
    (hn : 0 < n) (hq : (n : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) :
    PowerSeries.coeff k (wickTaylorSeries
        (hamiltonianCompensatedRook (centeredKernel T q))) =
      Finset.sum (Finset.range (k + 1)) (fun e =>
        Finset.sum (Finset.range (e + 1)) (fun v =>
          PowerSeries.coeff k (wickTaylorSeries (fun s =>
            gaussianWickDiagramCoefficient
              (fun j => s *
                realGaussianEigenVariances (bipartiteLift (centeredKernel T q))
                  (bipartiteLift_hermitian (centeredKernel T q)) j /
                (1 + s *
                  realGaussianEigenVariances (bipartiteLift (centeredKernel T q))
                    (bipartiteLift_hermitian (centeredKernel T q)) j))
              (realGaussianEigenRows (bipartiteLift (centeredKernel T q))
                (bipartiteLift_hermitian (centeredKernel T q))) e v)))) := by
  letI : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 hn)
  let B := centeredKernel T q
  let M := bipartiteLift B
  let hM := bipartiteLift_hermitian B
  let H := k + 1
  let p := wickFiniteGaussianJetPolynomial M hM H
  let gamma := fun s : Complex => fun j =>
    s * realGaussianEigenVariances M hM j /
      (1 + s * realGaussianEigenVariances M hM j)
  let zeta := fun s : Complex => fun j =>
    realGaussianEigenVariances M hM j /
      (1 + s * realGaussianEigenVariances M hM j)
  have hzeta : forall j, AnalyticAt Complex (fun s => zeta s j) 0 := by
    intro j
    exact analyticAt_const.div
      (analyticAt_const.add (analyticAt_id.mul analyticAt_const)) (by simp)
  have hgamma : forall j, AnalyticAt Complex (fun s => gamma s j) 0 := by
    intro j
    exact (analyticAt_id.mul analyticAt_const).div
      (analyticAt_const.add (analyticAt_id.mul analyticAt_const)) (by simp)
  have hCov (s : Complex) : (fun j => s * zeta s j) = gamma s := by
    funext j
    dsimp only [gamma, zeta]
    ring
  have hTruncate := gaussianPolynomialState_taylor_truncate zeta hzeta p k
  simp_rw [hCov] at hTruncate
  have hMatch := stochastic_compensated_finiteJet_taylor_match T q rho H k
    hn hq hRow hCol hNorm (Nat.lt_succ_self k)
  change PowerSeries.coeff k
      (wickTaylorSeries (hamiltonianCompensatedRook B)) =
    PowerSeries.coeff k (wickTaylorSeries (fun s => gaussianPolynomialState (gamma s) p))
      at hMatch
  rw [hMatch, hTruncate]
  have hBalance := centered_bipartite_column_sum_zero T q
    (by simpa only [Fintype.card_fin] using hq) hRow hCol
  apply Finset.sum_congr rfl
  intro e he
  have heH : e < H := Finset.mem_range.mp he
  have hLow :
      (fun s : Complex => gaussianPolynomialDegreeState (gamma s) p (2 * e)) =
      (fun s => Finset.sum (Finset.range (e + 1)) (fun v =>
        gaussianWickDiagramCoefficient (gamma s) (realGaussianEigenRows M hM) e v)) := by
    funext s
    exact realGaussianQuotient_finiteJet_degree_readout M hM s hBalance H e heH
  rw [hLow, wickTaylorSeries_finset_sum _ _
    (fun v _ => gaussianWickDiagramCoefficient_analyticAt gamma
      (realGaussianEigenRows M hM) 0 hgamma e v), map_sum]

end PrimeFactorOscillations
