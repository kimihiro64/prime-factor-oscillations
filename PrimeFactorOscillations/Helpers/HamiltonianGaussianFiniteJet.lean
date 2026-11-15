/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedGaussianIntegral
import PrimeFactorOscillations.Helpers.HamiltonianWickTailSummation

/-! # Finite Gaussian jets with the full zero-sum compensation

Odd moments vanish exactly. The complete pointwise truncation error keeps
the affine product until its linear sum has cancelled. Its Gaussian
dominating density is explicit and preserves all quadratic overlaps.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem gaussianLinearWickValue_odd (z : Iota -> Complex)
    (xs : List (Iota -> Complex)) (hOdd : xs.length % 2 = 1) :
    gaussianLinearWickValue z xs = 0 := by
  have hAll : forall n : Nat, forall ys : List (Iota -> Complex),
      ys.length = n -> n % 2 = 1 -> gaussianLinearWickValue z ys = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro ys hLen hParity
      cases ys with
      | nil =>
        simp only [List.length_nil] at hLen
        omega
      | cons a ys =>
        rw [gaussianLinearWickValue_cons]
        apply Finset.sum_eq_zero
        intro k hk
        have hkLt := Finset.mem_range.mp hk
        have hErase := List.length_eraseIdx_add_one hkLt
        have hSmall : (ys.eraseIdx k).length < n := by
          simp only [List.length_cons] at hLen
          omega
        have hParityErase : (ys.eraseIdx k).length % 2 = 1 := by
          simp only [List.length_cons] at hLen
          omega
        rw [ih (ys.eraseIdx k).length hSmall (ys.eraseIdx k) rfl hParityErase, mul_zero]
  exact hAll xs.length xs rfl hOdd

omit [DecidableEq Iota] in
theorem gaussianLinearCovariance_scale_variance
    (z a b : Iota -> Complex) (c : Complex) :
    gaussianLinearCovariance (fun i => c * z i) a b =
      c * gaussianLinearCovariance z a b := by
  unfold gaussianLinearCovariance
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem gaussianLinearWickValue_scale_variance
    (z : Iota -> Complex) (c : Complex) (e : Nat)
    (xs : List (Iota -> Complex)) (hLen : xs.length = 2 * e) :
    gaussianLinearWickValue (fun i => c * z i) xs =
      c ^ e * gaussianLinearWickValue z xs := by
  induction e generalizing xs with
  | zero =>
    cases xs with
    | nil => simp only [gaussianLinearWickValue_nil, pow_zero, one_mul]
    | cons a ys => simp only [List.length_cons] at hLen; omega
  | succ e ih =>
    cases xs with
    | nil => simp only [List.length_nil] at hLen; omega
    | cons a ys =>
      rw [gaussianLinearWickValue_cons, gaussianLinearWickValue_cons, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkLt := Finset.mem_range.mp hk
      have hErase := List.length_eraseIdx_add_one hkLt
      have hEraseLen : (ys.eraseIdx k).length = 2 * e := by
        simp only [List.length_cons] at hLen
        omega
      rw [gaussianLinearCovariance_scale_variance, ih _ hEraseLen, pow_succ]
      ring

def wickFiniteGaussianJet (Y : Iota -> Complex) (H : Nat) : Complex :=
  Finset.prod Finset.univ (fun i => 1 + Y i) *
    Finset.sum (Finset.range H) (fun j =>
      (Finset.sum Finset.univ (fun i => Y i ^ 2) / 2) ^ j / (j.factorial : Complex))

omit [DecidableEq Iota] in
theorem wick_bilinear_square_norm_bound (Y : Iota -> Complex) :
    norm (Finset.sum Finset.univ (fun i => Y i ^ 2) / 2) <=
      collectiveSquareMass Y / 2 := by
  have hTwo : norm (2 : Complex) = (2 : Real) := by norm_num
  rw [norm_div, hTwo]
  have h := norm_sum_le Finset.univ (fun i => Y i ^ 2)
  simp only [norm_pow] at h
  exact div_le_div_of_nonneg_right h (by norm_num)

theorem wickFiniteGaussianJet_remainder_bound [Nonempty Iota]
    (Y : Iota -> Complex) (H : Nat) (hZero : Finset.sum Finset.univ Y = 0) :
    norm (Finset.prod Finset.univ (fun i => wickVertexFunction (Y i)) -
      wickFiniteGaussianJet Y H) <=
        (collectiveSquareMass Y / 2) ^ H * Real.exp (collectiveSquareMass Y) := by
  let W : Real := collectiveSquareMass Y
  let Q : Complex := Finset.sum Finset.univ (fun i => Y i ^ 2) / 2
  have hW : 0 <= W := collectiveSquareMass_nonnegative Y
  have hQ : norm Q <= W / 2 := wick_bilinear_square_norm_bound Y
  have hProduct : norm (Finset.prod Finset.univ (fun i => 1 + Y i)) <=
      Real.exp (W / 2) := by
    rw [norm_prod]
    simpa only [one_mul, norm_one, one_pow] using
      collective_zero_sum_exponential_bound Y (1 : Complex) hZero
  have hTaylor := Complex.norm_exp_sub_sum_le_norm_mul_exp Q H
  have hPower := wick_nonnegative_power_le (norm Q) (W / 2)
    (norm_nonneg Q) hQ H
  have hError : norm (Complex.exp Q -
      Finset.sum (Finset.range H) (fun j => Q ^ j / (j.factorial : Complex))) <=
        (W / 2) ^ H * Real.exp (W / 2) := by
    exact le_trans hTaylor (mul_le_mul hPower (Real.exp_le_exp.mpr hQ)
      (Real.exp_pos _).le (pow_nonneg (by positivity : 0 <= W / 2) H))
  rw [wickVertexFunction_product_zero_sum Y hZero]
  unfold wickFiniteGaussianJet
  rw [<- mul_sub, norm_mul]
  change norm (Finset.prod Finset.univ (fun i => 1 + Y i)) *
      norm (Complex.exp Q - Finset.sum (Finset.range H)
        (fun j => Q ^ j / (j.factorial : Complex))) <= _
  calc
    _ <= Real.exp (W / 2) * ((W / 2) ^ H * Real.exp (W / 2)) :=
      mul_le_mul hProduct hError (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      have hExp : Real.exp (W / 2) * Real.exp (W / 2) = Real.exp W := by
        rw [<- Real.exp_add]
        congr 1
        ring
      change _ = (W / 2) ^ H * Real.exp W
      rw [mul_left_comm, hExp]

theorem wickFiniteGaussianJet_density_bound [Nonempty Iota]
    (Y : Iota -> Complex) (H : Nat) (S C t : Real)
    (hZero : Finset.sum Finset.univ Y = 0)
    (hS : 0 <= S) (hC : 0 <= C) (ht : 0 <= t)
    (hSmall : C * t <= 1 / 8)
    (hMass : collectiveSquareMass Y <= C * t * S) :
    Real.exp (-S / 2) *
        norm (Finset.prod Finset.univ (fun i => wickVertexFunction (Y i)) -
          wickFiniteGaussianJet Y H) <=
      t ^ H * (C / 2) ^ H * S ^ H * Real.exp (-(3 / 8 : Real) * S) := by
  let W : Real := collectiveSquareMass Y
  have hW : 0 <= W := collectiveSquareMass_nonnegative Y
  have hSmallS := mul_le_mul_of_nonneg_right hSmall hS
  have hExp : W - S / 2 <= -(3 / 8 : Real) * S := by
    change W <= C * t * S at hMass
    nlinarith only [hSmallS, hMass]
  have hPow : (W / 2) ^ H <= (C * t * S / 2) ^ H :=
    wick_nonnegative_power_le _ _ (by positivity)
      (div_le_div_of_nonneg_right hMass (by norm_num)) H
  calc
    _ <= Real.exp (-S / 2) * ((W / 2) ^ H * Real.exp W) :=
      mul_le_mul_of_nonneg_left (wickFiniteGaussianJet_remainder_bound Y H hZero)
        (Real.exp_pos _).le
    _ = (W / 2) ^ H * Real.exp (W - S / 2) := by
      have hExpId : Real.exp (-S / 2) * Real.exp W = Real.exp (W - S / 2) := by
        rw [<- Real.exp_add]
        congr 1
        ring
      calc
        _ = (W / 2) ^ H * (Real.exp (-S / 2) * Real.exp W) := by ring
        _ = _ := by rw [hExpId]
    _ <= (C * t * S / 2) ^ H * Real.exp (-(3 / 8 : Real) * S) :=
      mul_le_mul hPow (Real.exp_le_exp.mpr hExp)
        (Real.exp_pos _).le (pow_nonneg (by positivity) H)
    _ = _ := by
      have hAlgebra : C * t * S / 2 = t * (C / 2) * S := by ring
      rw [hAlgebra, mul_pow, mul_pow]

theorem realGaussianWeightedVector_square_mass (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (w : Iota -> Complex) (x : Iota -> Real) :
    collectiveSquareMass (realGaussianWeightedVector M hM w x) =
      Finset.sum Finset.univ (fun j => norm (w j) ^ 2 * x j ^ 2) := by
  unfold collectiveSquareMass realGaussianWeightedVector
  rw [realOrthogonal_complex_energy (realGaussianEigenMatrix M hM)
    (realGaussianEigenMatrix_orthogonal M hM)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem realGaussianWeightedVector_square_mass_bound (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (w : Iota -> Complex) (x : Iota -> Real) (C : Real)
    (hWeights : forall j, norm (w j) ^ 2 <= C) :
    collectiveSquareMass (realGaussianWeightedVector M hM w x) <=
      C * Finset.sum Finset.univ (fun j => x j ^ 2) := by
  rw [realGaussianWeightedVector_square_mass, Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hWeights j) (sq_nonneg _))

theorem realGaussianQuotientWeights_small_norm (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (rho t : Real)
    (hNorm : norm M <= rho) (ht : 0 <= t) (hSmall : t * rho <= 1 / 2)
    (j : Iota) :
    norm (realGaussianQuotientWeights M hM (t : Complex) j) ^ 2 <= 2 * rho * t := by
  have hRho : 0 <= rho := le_trans (norm_nonneg M) hNorm
  have hEigen : abs (hM.eigenvalues j) <= rho :=
    le_trans (realGaussianEigenvalue_abs_le_norm M hM j) hNorm
  have hLower := mul_le_mul_of_nonneg_left (abs_le.mp hEigen).1 ht
  have hDenHalf : 1 / 2 <= 1 + t * hM.eigenvalues j := by
    nlinarith only [hLower, hSmall]
  have hDen : 0 < 1 + t * hM.eigenvalues j := lt_of_lt_of_le (by norm_num) hDenHalf
  have hCast : 1 + (t : Complex) * (hM.eigenvalues j : Complex) =
      ((1 + t * hM.eigenvalues j : Real) : Complex) := by
    push_cast
    rfl
  have hNum : t * abs (hM.eigenvalues j) <= t * rho :=
    mul_le_mul_of_nonneg_left hEigen ht
  have hCo : 0 <= 2 * rho * t := by positivity
  have hDenProd : t * rho <= (2 * rho * t) * (1 + t * hM.eigenvalues j) := by
    have h := mul_le_mul_of_nonneg_left hDenHalf hCo
    nlinarith only [h]
  have hDivision : t * abs (hM.eigenvalues j) / (1 + t * hM.eigenvalues j) <=
      2 * rho * t := by
    by_contra hNot
    have hStrict := mul_lt_mul_of_pos_right (lt_of_not_ge hNot) hDen
    have hId : (t * abs (hM.eigenvalues j) / (1 + t * hM.eigenvalues j)) *
        (1 + t * hM.eigenvalues j) = t * abs (hM.eigenvalues j) := by
      field_simp [ne_of_gt hDen]
    rw [hId] at hStrict
    linarith only [hStrict, hNum, hDenProd]
  rw [<- norm_pow, realGaussianQuotientWeights_sq]
  have hFormula : norm ((t : Complex) * (hM.eigenvalues j : Complex) /
      (1 + (t : Complex) * (hM.eigenvalues j : Complex))) =
        t * abs (hM.eigenvalues j) / (1 + t * hM.eigenvalues j) := by
    rw [norm_div, norm_mul, hCast]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht,
      abs_of_nonneg hDen.le]
  rw [hFormula]
  exact hDivision

theorem realGaussianQuotientFiniteJet_density_bound [Nonempty Iota]
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (rho t : Real)
    (H : Nat) (x : Iota -> Real)
    (hNorm : norm M <= rho) (ht : 0 <= t) (hSmall : t * rho <= 1 / 16)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0) :
    Real.exp (-Finset.sum Finset.univ (fun j => x j ^ 2) / 2) *
      norm (Finset.prod Finset.univ (fun i => wickVertexFunction
          (realGaussianWeightedVector M hM (realGaussianQuotientWeights M hM (t : Complex)) x i)) -
        wickFiniteGaussianJet
          (realGaussianWeightedVector M hM (realGaussianQuotientWeights M hM (t : Complex)) x) H) <=
      t ^ H * rho ^ H * (Finset.sum Finset.univ (fun j => x j ^ 2)) ^ H *
        Real.exp (-(3 / 8 : Real) * Finset.sum Finset.univ (fun j => x j ^ 2)) := by
  have hRho : 0 <= rho := le_trans (norm_nonneg M) hNorm
  have hS : 0 <= Finset.sum Finset.univ (fun j => x j ^ 2) :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hWeights : forall j,
      norm (realGaussianQuotientWeights M hM (t : Complex) j) ^ 2 <= 2 * rho * t := by
    intro j
    exact realGaussianQuotientWeights_small_norm M hM rho t hNorm ht (by linarith) j
  have hMass := realGaussianWeightedVector_square_mass_bound M hM
    (realGaussianQuotientWeights M hM (t : Complex)) x (2 * rho * t) hWeights
  have h := wickFiniteGaussianJet_density_bound
    (realGaussianWeightedVector M hM (realGaussianQuotientWeights M hM (t : Complex)) x)
    H (Finset.sum Finset.univ (fun j => x j ^ 2)) (2 * rho) t
    (realGaussianQuotientVector_zero_sum M hM (t : Complex) hCol x)
    hS (by positivity) ht (by nlinarith only [hSmall]) hMass
  have hFactor : 2 * rho / 2 = rho := by ring
  simpa only [hFactor] using h

end PrimeFactorOscillations
