/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianStateRealization
import PrimeFactorOscillations.Helpers.HamiltonianMatrixSpectralAverage

/-! # Actual spectral Gaussian realization of a real symmetric matrix

The covariance and zero-sum vector condition are derived from the actual
orthogonal eigenbasis. Indefinite eigenvalues are retained through complex
square roots. No positive-semidefinite or covariance-size assumption is made.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

private theorem realGaussian_star_eq_transpose (U : Matrix Iota Iota Real) :
    star U = U.transpose := by
  ext i j
  rfl

def realGaussianEigenMatrix (M : Matrix Iota Iota Real) (hM : M.IsHermitian) :
    Matrix Iota Iota Real :=
  hM.eigenvectorUnitary

def realGaussianEigenVariances (M : Matrix Iota Iota Real) (hM : M.IsHermitian) :
    Iota -> Complex :=
  fun i => (hM.eigenvalues i : Complex)

def realGaussianEigenRows (M : Matrix Iota Iota Real) (hM : M.IsHermitian)
    (i : Iota) : Iota -> Complex :=
  fun j => (realGaussianEigenMatrix M hM i j : Complex)

theorem realGaussianEigenMatrix_orthogonal (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) :
    (realGaussianEigenMatrix M hM).transpose * realGaussianEigenMatrix M hM = 1 := by
  have hUnit :
      star (hM.eigenvectorUnitary : Matrix Iota Iota Real) *
        (hM.eigenvectorUnitary : Matrix Iota Iota Real) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_star_mul_self hM.eigenvectorUnitary
  simpa only [realGaussianEigenMatrix, realGaussian_star_eq_transpose] using hUnit

theorem realGaussianEigenMatrix_decomposition (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) :
    M = realGaussianEigenMatrix M hM * Matrix.diagonal hM.eigenvalues *
      (realGaussianEigenMatrix M hM).transpose := by
  have hSpectral :
      M = Unitary.conjStarAlgAut Real (Matrix Iota Iota Real) hM.eigenvectorUnitary
        (Matrix.diagonal hM.eigenvalues) := by
    simpa using hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hSpectral
  change M = realGaussianEigenMatrix M hM * Matrix.diagonal hM.eigenvalues *
    star (realGaussianEigenMatrix M hM) at hSpectral
  rw [realGaussian_star_eq_transpose] at hSpectral
  exact hSpectral

theorem realGaussianEigenCovariance (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (i k : Iota) :
    gaussianLinearCovariance (realGaussianEigenVariances M hM)
        (realGaussianEigenRows M hM i) (realGaussianEigenRows M hM k) =
      (M i k : Complex) := by
  let U := realGaussianEigenMatrix M hM
  have hSpec := realGaussianEigenMatrix_decomposition M hM
  have hEntry := congrArg (fun A : Matrix Iota Iota Real => A i k) hSpec
  rw [Matrix.mul_apply] at hEntry
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply] at hEntry
  have hReal : Finset.sum Finset.univ (fun j =>
      hM.eigenvalues j * U i j * U k j) = M i k := by
    rw [hEntry]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [U]
    ring
  unfold gaussianLinearCovariance realGaussianEigenVariances realGaussianEigenRows
  exact_mod_cast hReal

theorem realGaussianEigenCovariance_scaled (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (t : Complex) (i k : Iota) :
    gaussianLinearCovariance (fun j => t * realGaussianEigenVariances M hM j)
        (realGaussianEigenRows M hM i) (realGaussianEigenRows M hM k) =
      t * (M i k : Complex) := by
  calc
    _ = t * gaussianLinearCovariance (realGaussianEigenVariances M hM)
        (realGaussianEigenRows M hM i) (realGaussianEigenRows M hM k) := by
      unfold gaussianLinearCovariance
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [realGaussianEigenCovariance]

theorem realGaussianEigenColumn_balance (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0) (k : Iota) :
    hM.eigenvalues k *
      Finset.sum Finset.univ (fun i => realGaussianEigenMatrix M hM i k) = 0 := by
  let U := realGaussianEigenMatrix M hM
  have hUnit := realGaussianEigenMatrix_orthogonal M hM
  have hMU : M * U = U * Matrix.diagonal hM.eigenvalues := by
    calc
      M * U = (U * Matrix.diagonal hM.eigenvalues * U.transpose) * U :=
        congrArg (fun A : Matrix Iota Iota Real => A * U)
          (realGaussianEigenMatrix_decomposition M hM)
      _ = U * Matrix.diagonal hM.eigenvalues := by
        rw [Matrix.mul_assoc, hUnit, Matrix.mul_one]
  have hZero : Finset.sum Finset.univ (fun i => (M * U) i k) = 0 := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    rw [<- Finset.sum_mul, hCol j, zero_mul]
  rw [hMU] at hZero
  simp only [Matrix.mul_diagonal] at hZero
  rw [<- Finset.sum_mul] at hZero
  exact (mul_comm _ _).trans hZero

def realGaussianVector (M : Matrix Iota Iota Real) (hM : M.IsHermitian)
    (x : Iota -> Real) : Iota -> Complex :=
  fun i => Finset.sum Finset.univ (fun j =>
    (realGaussianEigenMatrix M hM i j : Complex) *
      complexGaussianSquareRoot (realGaussianEigenVariances M hM j) * (x j : Complex))

theorem realGaussianVector_zero_sum (M : Matrix Iota Iota Real) (hM : M.IsHermitian)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (x : Iota -> Real) :
    Finset.sum Finset.univ (realGaussianVector M hM x) = 0 := by
  have hScalar : forall j,
      Finset.sum Finset.univ (fun i => (realGaussianEigenMatrix M hM i j : Complex)) *
        complexGaussianSquareRoot (realGaussianEigenVariances M hM j) = 0 := by
    intro j
    have hBalance : (hM.eigenvalues j : Complex) *
        Finset.sum Finset.univ (fun i => (realGaussianEigenMatrix M hM i j : Complex)) = 0 := by
      exact_mod_cast realGaussianEigenColumn_balance M hM hCol j
    have hSquare :
        (Finset.sum Finset.univ (fun i => (realGaussianEigenMatrix M hM i j : Complex)) *
          complexGaussianSquareRoot (realGaussianEigenVariances M hM j)) ^ 2 = 0 := by
      rw [mul_pow, complexGaussianSquareRoot_sq]
      unfold realGaussianEigenVariances
      calc
        _ = ((hM.eigenvalues j : Complex) *
          Finset.sum Finset.univ (fun i => (realGaussianEigenMatrix M hM i j : Complex))) *
            Finset.sum Finset.univ (fun i => (realGaussianEigenMatrix M hM i j : Complex)) := by ring
        _ = 0 := by rw [hBalance, zero_mul]
    rw [pow_two] at hSquare
    exact (mul_eq_zero.mp hSquare).elim id id
  unfold realGaussianVector
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  rw [<- Finset.sum_mul, <- Finset.sum_mul, hScalar j, zero_mul]

theorem realGaussianWickIntegral_norm_bound (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (c : Real) (hc : 0 <= c)
    (hEntry : forall i j, abs (M i j) <= c) (e : Nat) (xs : List Iota)
    (hLen : xs.length = 2 * e) :
    norm (MeasureTheory.integral gaussianTensorMeasure
        (standardGaussianPolynomialKernel (realGaussianEigenVariances M hM)
          (gaussianLinearProduct (xs.map (realGaussianEigenRows M hM)))) /
        gaussianTensorTiltNormalizer (fun _ : Iota => 0)) <=
      (wickPairCount e : Real) * c ^ e := by
  apply standardGaussianLinearWickIntegral_norm_bound _ c hc e _
    (by simpa only [List.length_map] using hLen)
  intro a ha b hb
  cases List.mem_map.mp ha with
  | intro i hi =>
    cases hi with
    | intro hi hAi =>
      cases List.mem_map.mp hb with
      | intro k hk =>
        cases hk with
        | intro hk hBk =>
          rw [<- hAi, <- hBk, realGaussianEigenCovariance]
          simpa only [Complex.norm_real, Real.norm_eq_abs] using hEntry i k

theorem bipartiteLift_hermitian (B : Matrix Iota Iota Real) :
    (bipartiteLift B).IsHermitian := by
  change (bipartiteLift B).conjTranspose = bipartiteLift B
  ext i j
  cases i <;> cases j <;>
    simp [bipartiteLift, Matrix.fromBlocks, Matrix.conjTranspose_apply,
      Matrix.transpose_apply]

theorem centered_bipartite_column_sum_zero (T : Matrix Iota Iota Real) (q : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (j : Sum Iota Iota) :
    Finset.sum Finset.univ (fun i => bipartiteLift (centeredKernel T q) i j) = 0 := by
  have hRowB : forall i, Finset.sum Finset.univ (fun j => centeredKernel T q i j) = 0 := by
    intro i
    simp only [centeredKernel, averagingKernel, Matrix.sub_apply]
    rw [Finset.sum_sub_distrib, hRow i, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hq, sub_self]
  have hColB : forall j, Finset.sum Finset.univ (fun i => centeredKernel T q i j) = 0 := by
    intro j
    simp only [centeredKernel, averagingKernel, Matrix.sub_apply]
    rw [Finset.sum_sub_distrib, hCol j, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hq, sub_self]
  cases j with
  | inl j =>
    simpa [Fintype.sum_sum_type, bipartiteLift, Matrix.fromBlocks,
      Matrix.transpose_apply] using hRowB j
  | inr j =>
    simpa [Fintype.sum_sum_type, bipartiteLift, Matrix.fromBlocks,
      Matrix.transpose_apply] using hColB j

theorem stochasticGaussianVector_zero_sum (T : Matrix Iota Iota Real) (q : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (x : Sum Iota Iota -> Real) :
    Finset.sum Finset.univ
      (realGaussianVector (bipartiteLift (centeredKernel T q))
        (bipartiteLift_hermitian (centeredKernel T q)) x) = 0 :=
  realGaussianVector_zero_sum _ _ (centered_bipartite_column_sum_zero T q hq hRow hCol) x

theorem realOrthogonal_square_energy (U : Matrix Iota Iota Real)
    (hOrth : U.transpose * U = 1) (f : Iota -> Real) :
    Finset.sum Finset.univ (fun i => (U.mulVec f i) ^ 2) =
      Finset.sum Finset.univ (fun i => f i ^ 2) := by
  have hAdj : Matrix.vecMul (U.mulVec f) U = f := by
    calc
      Matrix.vecMul (U.mulVec f) U = U.transpose.mulVec (U.mulVec f) := by
        ext j
        simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (U.transpose * U).mulVec f := Matrix.mulVec_mulVec f U.transpose U
      _ = f := by rw [hOrth, Matrix.one_mulVec]
  have hDot := Matrix.dotProduct_mulVec (U.mulVec f) U f
  rw [hAdj] at hDot
  simpa only [dotProduct, <- pow_two] using hDot

theorem realOrthogonal_complex_energy (U : Matrix Iota Iota Real)
    (hOrth : U.transpose * U = 1) (z : Iota -> Complex) :
    Finset.sum Finset.univ
        (fun i => norm (Finset.sum Finset.univ (fun j => (U i j : Complex) * z j)) ^ 2) =
      Finset.sum Finset.univ (fun j => norm (z j) ^ 2) := by
  have hRe : forall i,
      (Finset.sum Finset.univ (fun j => (U i j : Complex) * z j)).re =
        U.mulVec (fun j => (z j).re) i := by
    intro i
    change Complex.reCLM (Finset.sum Finset.univ
      (fun j => (U i j : Complex) * z j)) = _
    rw [map_sum]
    change Finset.sum Finset.univ (fun j => ((U i j : Complex) * z j).re) = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Matrix.mulVec, dotProduct]
  have hIm : forall i,
      (Finset.sum Finset.univ (fun j => (U i j : Complex) * z j)).im =
        U.mulVec (fun j => (z j).im) i := by
    intro i
    change Complex.imCLM (Finset.sum Finset.univ
      (fun j => (U i j : Complex) * z j)) = _
    rw [map_sum]
    change Finset.sum Finset.univ (fun j => ((U i j : Complex) * z j).im) = _
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Matrix.mulVec, dotProduct]
  have hNorm : forall u : Complex, norm u ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    intro u
    rw [<- Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  calc
    _ = Finset.sum Finset.univ (fun i =>
        (U.mulVec (fun j => (z j).re) i) ^ 2 +
          (U.mulVec (fun j => (z j).im) i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hNorm, hRe i, hIm i]
    _ = Finset.sum Finset.univ (fun i => (U.mulVec (fun j => (z j).re) i) ^ 2) +
        Finset.sum Finset.univ (fun i => (U.mulVec (fun j => (z j).im) i) ^ 2) :=
      Finset.sum_add_distrib
    _ = Finset.sum Finset.univ (fun j => (z j).re ^ 2) +
        Finset.sum Finset.univ (fun j => (z j).im ^ 2) := by
      rw [realOrthogonal_square_energy U hOrth, realOrthogonal_square_energy U hOrth]
    _ = _ := by
      rw [<- Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      exact (hNorm (z j)).symm

theorem realGaussianVector_energy (M : Matrix Iota Iota Real) (hM : M.IsHermitian)
    (x : Iota -> Real) :
    Finset.sum Finset.univ (fun i => norm (realGaussianVector M hM x i) ^ 2) =
      Finset.sum Finset.univ (fun j => abs (hM.eigenvalues j) * x j ^ 2) := by
  let U := realGaussianEigenMatrix M hM
  have hVec : realGaussianVector M hM x = fun i =>
      Finset.sum Finset.univ (fun j => (U i j : Complex) *
        (complexGaussianSquareRoot (realGaussianEigenVariances M hM j) * (x j : Complex))) := by
    funext i
    unfold realGaussianVector
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [U]
    ring
  rw [hVec, realOrthogonal_complex_energy U (realGaussianEigenMatrix_orthogonal M hM)]
  apply Finset.sum_congr rfl
  intro j hj
  have hRoot : norm (complexGaussianSquareRoot (realGaussianEigenVariances M hM j)) ^ 2 =
      abs (hM.eigenvalues j) := by
    rw [<- norm_pow, complexGaussianSquareRoot_sq]
    simp only [realGaussianEigenVariances, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_mul, mul_pow, hRoot]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

end PrimeFactorOscillations
