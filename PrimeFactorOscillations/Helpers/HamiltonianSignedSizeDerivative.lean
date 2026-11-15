/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import PrimeFactorOscillations.Helpers.HamiltonianSignedBipartiteFunctional
import PrimeFactorOscillations.Helpers.HamiltonianSignedOccupancyBounds

/-! # Exact analytic size moments of the full signed minor wave

Every row and column support is retained. The analytic second derivative
is the actual signed rank-factorial moment and the parity factor supplies
the complete two-term determinant derivative. No derivative identity or
zero exclusion is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianSignedRankWave (T : Matrix Iota Iota Real) (t : Real) : Real :=
  -Finset.univ.sum (fun U : Finset Iota =>
    (-1 : Real) ^ U.card * (U.card : Real) *
      (Finset.univ.powersetCard U.card).sum (fun S =>
        rectangularMinorDet T S U ^ 2) * t ^ U.card)

theorem gramDeterminantPolynomial_eval (T : Matrix Iota Iota Real) (t : Real) :
    Polynomial.eval t (gramDeterminantPolynomial T) =
      Matrix.det ((1 : Matrix Iota Iota Real) -
        HSMul.hSMul t (T.transpose * T)) := by
  unfold gramDeterminantPolynomial
  change (Polynomial.evalRingHom t) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;>
    simp [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.smul_apply, smul_eq_mul, Polynomial.eval_finsetSum, h]

theorem gramDeterminantPolynomial_transpose (T : Matrix Iota Iota Real) :
    gramDeterminantPolynomial T = gramDeterminantPolynomial T.transpose := by
  rw [gramDeterminantPolynomial_as_minors,
    gramDeterminantPolynomial_as_minors]
  simpa only [Matrix.neg_mul, Matrix.mul_neg, Matrix.transpose_transpose] using
    principalMinorPolynomial_mul_comm (-T.transpose) T

theorem hamiltonian_signed_rank_wave_polynomial
    (T : Matrix Iota Iota Real) (t : Real) :
    hamiltonianSignedRankWave T t =
      Polynomial.eval t (-polynomialEuler (gramDeterminantPolynomial T)) := by
  rw [Polynomial.eval_neg, gramEuler_eval]
  unfold hamiltonianSignedRankWave
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [gramPrincipalMinor_eq_rectangularSquares]
  ring

theorem hamiltonian_polynomial_monomial_second_one (k : Nat) (a : Real) :
    Polynomial.eval 1 (Polynomial.monomial k a).derivative.derivative =
      (k : Real) * ((k : Real) - 1) * a := by
  cases k with
  | zero => simp
  | succ k =>
      cases k with
      | zero => simp
      | succ k =>
          simp only [Polynomial.derivative_monomial, Nat.add_sub_cancel,
            Polynomial.eval_monomial, one_pow, mul_one, Nat.cast_add,
            Nat.cast_one]
          ring

theorem hamiltonian_signed_rank_wave_second_sum (T : Matrix Iota Iota Real) :
    deriv (deriv (hamiltonianSignedRankWave T)) 1 =
      -Finset.univ.sum (fun U : Finset Iota =>
        (-1 : Real) ^ U.card * (U.card : Real) *
          (Finset.univ.powersetCard U.card).sum (fun S =>
            rectangularMinorDet T S U ^ 2) *
              ((U.card : Real) * ((U.card : Real) - 1))) := by
  let p := -polynomialEuler (gramDeterminantPolynomial T)
  have hWave : hamiltonianSignedRankWave T = fun t => Polynomial.eval t p :=
    funext (hamiltonian_signed_rank_wave_polynomial T)
  have hFirst : deriv (hamiltonianSignedRankWave T) =
      fun t => Polynomial.eval t p.derivative := by
    rw [hWave]
    exact funext (fun t => p.deriv)
  rw [hFirst, Polynomial.deriv]
  dsimp only [p]
  rw [gramDeterminantPolynomial_as_minors, principalMinorGeneratingPolynomial_eq,
    polynomialEuler_sum]
  simp only [Polynomial.derivative_neg, Polynomial.derivative_sum,
    Polynomial.eval_neg, Polynomial.eval_finsetSum]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [polynomialEuler_monomial, hamiltonian_polynomial_monomial_second_one]
  simp only [principalMinorDet, Matrix.submatrix_neg, Pi.neg_apply,
    Matrix.det_neg, Fintype.card_coe]
  rw [<- gramPrincipalMinor_eq_rectangularSquares T U]
  unfold principalMinorDet
  ring

theorem hamiltonian_signed_rank_second_derivative
    (T : Matrix Iota Iota Real) (q : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) :
    deriv (deriv (hamiltonianSignedRankWave T)) 1 =
      4 * deriv (fun t : Real => Matrix.det
        ((1 : Matrix Iota Iota Real) - HSMul.hSMul t
          ((centeredKernel T q).transpose * centeredKernel T q))) 1 +
      3 * deriv (deriv (fun t : Real => Matrix.det
        ((1 : Matrix Iota Iota Real) - HSMul.hSMul t
          ((centeredKernel T q).transpose * centeredKernel T q)))) 1 := by
  let p := -polynomialEuler (gramDeterminantPolynomial T)
  let d := gramDeterminantPolynomial (centeredKernel T q)
  have hWave : hamiltonianSignedRankWave T = fun t => Polynomial.eval t p :=
    funext (hamiltonian_signed_rank_wave_polynomial T)
  have hFirst : deriv (hamiltonianSignedRankWave T) =
      fun t => Polynomial.eval t p.derivative := by
    rw [hWave]
    exact funext (fun t => p.deriv)
  have hDet : (fun t : Real => Matrix.det
      ((1 : Matrix Iota Iota Real) - HSMul.hSMul t
        ((centeredKernel T q).transpose * centeredKernel T q))) =
      fun t => Polynomial.eval t d :=
    funext (fun t => (gramDeterminantPolynomial_eval (centeredKernel T q) t).symm)
  have hDeriv : deriv (fun t => Polynomial.eval t d) =
      fun t => Polynomial.eval t d.derivative :=
    funext (fun t => d.deriv)
  rw [hFirst, Polynomial.deriv, hDet, hDeriv]
  simp only [Polynomial.deriv]
  exact signedGram_secondSizeMoment T q hq hRow hCol

theorem hamiltonian_signed_rank_second_derivative_transpose
    (T : Matrix Iota Iota Real) (q : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) :
    deriv (deriv (hamiltonianSignedRankWave T)) 1 =
      4 * deriv (fun t : Real => Matrix.det
        ((1 : Matrix Iota Iota Real) - HSMul.hSMul t
          (centeredKernel T q * (centeredKernel T q).transpose))) 1 +
      3 * deriv (deriv (fun t : Real => Matrix.det
        ((1 : Matrix Iota Iota Real) - HSMul.hSMul t
          (centeredKernel T q * (centeredKernel T q).transpose)))) 1 := by
  have hFun : (fun t : Real => Matrix.det
      ((1 : Matrix Iota Iota Real) - HSMul.hSMul t
        ((centeredKernel T q).transpose * centeredKernel T q))) =
      (fun t : Real => Matrix.det
        ((1 : Matrix Iota Iota Real) - HSMul.hSMul t
          (centeredKernel T q * (centeredKernel T q).transpose))) := by
    funext t
    rw [<- gramDeterminantPolynomial_eval, gramDeterminantPolynomial_transpose,
      gramDeterminantPolynomial_eval, Matrix.transpose_transpose]
  have h := hamiltonian_signed_rank_second_derivative T q hq hRow hCol
  rw [hFun] at h
  exact h

theorem hamiltonian_signed_size_second_derivative
    (T : Matrix Iota Iota Real) :
    hamiltonianSignedMinorFunctional (bipartiteLift T)
      (fun V => ((V.card : Real) / 2) * ((V.card : Real) / 2 - 1)) =
        deriv (deriv (hamiltonianSignedRankWave T)) 1 := by
  rw [hamiltonian_signed_minor_bipartite, hamiltonian_signed_rank_wave_second_sum]
  unfold hamiltonianSignedBipartiteFunctional
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  have hInner :
      (Finset.univ.powersetCard U.card).sum (fun S =>
        rectangularMinorDet T S U ^ 2 *
          (((S.disjSum U).card : Real) / 2 *
            (((S.disjSum U).card : Real) / 2 - 1))) =
      (Finset.univ.powersetCard U.card).sum (fun S =>
        rectangularMinorDet T S U ^ 2) *
          ((U.card : Real) * ((U.card : Real) - 1)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S hS
    have hCard : S.card = U.card := (Finset.mem_powersetCard.mp hS).2
    rw [Finset.card_disjSum, hCard, Nat.cast_add]
    ring
  rw [hInner]
  ring


theorem hamiltonian_signed_rank_coordinate_readout (M : Matrix Iota Iota Real) :
    hamiltonianSignedMinorFunctional M
      (fun S => ((S.card : Real) / 2) * ((S.card : Real) / 2 - 1)) =
      (1 / 4 : Real) *
        (Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota =>
          if j = i then 0 else hamiltonianCoordinatePairMinorMoment M i j)) -
            Finset.univ.sum (fun i => hamiltonianCoordinateMinorMoment M i)) := by
  have h := hamiltonian_signed_minor_correction_readout M 0 0 1
  have hFunction :
      hamiltonianSignedSupportCorrection (0 : Matrix Iota Iota Real)
        (0 : Iota -> Real) 1 =
      fun S => ((S.card : Real) / 2) * ((S.card : Real) / 2 - 1) := by
    funext S
    simp [hamiltonianSignedSupportCorrection]
  rw [hFunction] at h
  simpa using h

theorem hamiltonian_signed_rank_coordinate_bound
    (M : Matrix Iota Iota Real) (q p d : Real)
    (hq : 0 <= q) (hp : 1 <= p)
    (hNq : (Fintype.card Iota : Real) * q = 2)
    (hSingle : forall i,
      abs (hamiltonianCoordinateMinorMoment M i) <= 5 * abs d * p * q)
    (hPair : forall i j, Not (i = j) ->
      abs (hamiltonianCoordinatePairMinorMoment M i j) <=
        50 * abs d * p ^ 2 * q ^ 2) :
    abs (hamiltonianSignedMinorFunctional M
      (fun S => ((S.card : Real) / 2) * ((S.card : Real) / 2 - 1))) <=
        53 * abs d * p ^ 2 := by
  let m : Real := Fintype.card Iota
  let singles := Finset.univ.sum (fun i : Iota => hamiltonianCoordinateMinorMoment M i)
  let pairs := Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota =>
    if j = i then 0 else hamiltonianCoordinatePairMinorMoment M i j))
  have hp0 : 0 <= p := le_trans (by norm_num) hp
  have hd : 0 <= abs d := abs_nonneg d
  have hSum (f : Iota -> Real) (c : Real) (h : forall i, abs (f i) <= c) :
      abs (Finset.univ.sum f) <= m * c := by
    calc
      _ <= Finset.univ.sum (fun i => abs (f i)) := Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.univ.sum (fun _ : Iota => c) := Finset.sum_le_sum (fun i _ => h i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m]
  have hMq : m * q = 2 := hNq
  have hSingles : abs singles <= 10 * abs d * p := by
    calc
      _ <= m * (5 * abs d * p * q) := hSum _ _ hSingle
      _ = 5 * abs d * p * (m * q) := by ring
      _ = _ := by rw [hMq]; ring
  have hPairs : abs pairs <= 200 * abs d * p ^ 2 := by
    have hTerm (i j : Iota) : abs (if j = i then 0 else
        hamiltonianCoordinatePairMinorMoment M i j) <=
          50 * abs d * p ^ 2 * q ^ 2 := by
      by_cases h : j = i
      case pos =>
        simp only [if_pos h, abs_zero]
        positivity
      case neg =>
        simp only [if_neg h]
        exact hPair i j (Ne.symm h)
    calc
      _ <= m * (m * (50 * abs d * p ^ 2 * q ^ 2)) :=
        hSum _ _ (fun i => hSum _ _ (hTerm i))
      _ = 50 * abs d * p ^ 2 * (m * q) ^ 2 := by ring
      _ = _ := by rw [hMq]; ring
  have hp12 : p <= p ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hp hp0
    nlinarith only [h]
  have hScaled := mul_le_mul_of_nonneg_left hp12 hd
  have hNonneg : 0 <= abs d * p ^ 2 := mul_nonneg hd (sq_nonneg p)
  have hReadout := hamiltonian_signed_rank_coordinate_readout M
  change hamiltonianSignedMinorFunctional M
      (fun S => ((S.card : Real) / 2) * ((S.card : Real) / 2 - 1)) =
    (1 / 4 : Real) * (pairs - singles) at hReadout
  rw [hReadout, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 1 / 4)]
  have hTriangle := abs_sub pairs singles
  nlinarith only [hTriangle, hSingles, hPairs, hScaled, hNonneg]

variable [Nonempty Iota]

theorem stochastic_signed_size_second_derivative_bound
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    abs (deriv (deriv (hamiltonianSignedRankWave T)) 1) <=
      53 * abs (Matrix.det ((1 : Matrix Iota Iota Real) -
        (centeredKernel T q).transpose * centeredKernel T q)) *
          (a / (1 - rho)) ^ 2 := by
  let g := 1 - rho
  let p := a / g
  let d := Matrix.det ((1 : Matrix Iota Iota Real) -
    (centeredKernel T q).transpose * centeredKernel T q)
  have hg : 0 < g := sub_pos.mpr hRho
  have hDen : Not (g = 0) := ne_of_gt hg
  have hgSq : 0 < g ^ 2 := sq_pos_of_pos hg
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hg1 : g <= 1 := by dsimp only [g]; linarith only [hRho0]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hp0 : 0 <= p := div_nonneg ha0 (le_of_lt hg)
  have hpClear : g * p = a := by dsimp only [p]; field_simp
  have hp : 1 <= p := by nlinarith only [hpClear, hg1, hp0, ha]
  have hSquare : g ^ 2 * p ^ 2 = a ^ 2 := by rw [<- mul_pow, hpClear]
  have hCard : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hCard]
  have hFull : (Fintype.card (Sum Iota Iota) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hSingle (i : Sum Iota Iota) :
      abs (hamiltonianCoordinateMinorMoment (bipartiteLift T) i) <=
        5 * abs d * p * q := by
    apply le_of_mul_le_mul_left _ hg
    calc
      _ <= 5 * abs d * a * q :=
        stochastic_signed_coordinate_occupancy_bound T q a rho hq ha
          hRow hCol hNonneg hUpper hNorm hRho i
      _ = g * (5 * abs d * p * q) := by rw [<- hpClear]; ring
  have hPair (i j : Sum Iota Iota) (hIJ : Not (i = j)) :
      abs (hamiltonianCoordinatePairMinorMoment (bipartiteLift T) i j) <=
        50 * abs d * p ^ 2 * q ^ 2 := by
    apply le_of_mul_le_mul_left _ hgSq
    calc
      _ <= 50 * abs d * a ^ 2 * q ^ 2 :=
        stochastic_signed_coordinate_pair_occupancy_bound T q a rho hq ha
          hRow hCol hNonneg hUpper hNorm hRho i j hIJ
      _ = g ^ 2 * (50 * abs d * p ^ 2 * q ^ 2) := by rw [<- hSquare]; ring
  rw [<- hamiltonian_signed_size_second_derivative]
  exact hamiltonian_signed_rank_coordinate_bound (bipartiteLift T) q p d
    hq0 hp hFull hSingle hPair

end PrimeFactorOscillations
