/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFiniteFactorGramBound
import PrimeFactorOscillations.Helpers.HamiltonianPrimeRealMatrix
import PrimeFactorOscillations.Helpers.HamiltonianSchurBudget

/-! # Real finite factors from complex Fourier frames without an ambient loss -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota : Type*} [Fintype Iota] [DecidableEq Iota]
variable [Fintype Jota] [DecidableEq Jota]

def hamiltonianRealPartVector (z : EuclideanSpace Complex Iota) :
    EuclideanSpace Real Iota := WithLp.toLp 2 (fun i => (z.ofLp i).re)

def hamiltonianRealPartMatrix (M : Matrix Iota Jota Complex) : Matrix Iota Jota Real :=
  fun i j => (M i j).re

theorem hamiltonian_complex_real_sum (S : Finset Jota) (f : Jota -> Complex) :
    (S.sum f).re = S.sum (fun j => (f j).re) :=
  map_sum Complex.reCLM f S

theorem hamiltonian_real_part_vector_norm_le (z : EuclideanSpace Complex Iota) :
    norm (hamiltonianRealPartVector z) <= norm z := by
  have hSquare : norm (hamiltonianRealPartVector z) ^ 2 <= norm z ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i hi
    change norm (z.ofLp i).re ^ 2 <= norm (z.ofLp i) ^ 2
    have h := Complex.abs_re_le_norm (z.ofLp i)
    rw [Real.norm_eq_abs]
    have hSq := mul_le_mul h h (abs_nonneg _) (norm_nonneg _)
    nlinarith only [hSq]
  nlinarith only [hSquare, norm_nonneg (hamiltonianRealPartVector z), norm_nonneg z]

theorem hamiltonian_real_part_matrix_norm_le (M : Matrix Iota Iota Complex) :
    norm (hamiltonianRealPartMatrix M) <= norm M := by
  let opR := (@Matrix.toEuclideanCLM Real Iota _ _ _) (hamiltonianRealPartMatrix M)
  let opC := (@Matrix.toEuclideanCLM Complex Iota _ _ _) M
  have hImage (x : EuclideanSpace Real Iota) :
      hamiltonianRealPartVector (opC (LPF.hamiltonianComplexVector x)) = opR x := by
    ext i
    change (Finset.univ.sum (fun j => M i j * (x.ofLp j : Complex))).re =
      Finset.univ.sum (fun j => (M i j).re * x.ofLp j)
    simp only [hamiltonian_complex_real_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  have hOp : norm opR <= norm opC := by
    apply ContinuousLinearMap.opNorm_le_bound opR (norm_nonneg _)
    intro x
    calc
      _ = norm (hamiltonianRealPartVector (opC (LPF.hamiltonianComplexVector x))) :=
        congrArg norm (hImage x).symm
      _ <= norm (opC (LPF.hamiltonianComplexVector x)) :=
        hamiltonian_real_part_vector_norm_le _
      _ <= norm opC * norm (LPF.hamiltonianComplexVector x) :=
        ContinuousLinearMap.le_opNorm opC _
      _ = norm opC * norm x := by rw [LPF.hamiltonian_complex_vector_norm]
  rwa [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_toEuclideanCLM] at hOp

theorem hamiltonian_real_part_matrix_sub
    (A B : Matrix Iota Jota Complex) :
    hamiltonianRealPartMatrix (A - B) =
      hamiltonianRealPartMatrix A - hamiltonianRealPartMatrix B := by
  ext i j
  exact Complex.sub_re _ _

theorem hamiltonian_rectangular_normalized_entry_norm_bound
    {K : Type*} [RCLike K] (M : Matrix Iota Jota K) (s : Real)
    (hs : 0 <= s) (hEntries : forall i j, norm (M i j) <= s)
    (hScale : (Fintype.card Iota : Real) * s ^ 2 <= 1) :
    norm M <= (Fintype.card Jota : Real) + 1 := by
  have hEntry (i j : Jota) : norm ((M.conjTranspose * M) i j) <= 1 := by
    calc
      _ <= Finset.univ.sum (fun a : Iota => norm (star (M a i) * M a j)) :=
        norm_sum_le _ _
      _ = Finset.univ.sum (fun a : Iota => norm (M a i) * norm (M a j)) := by
        simp only [norm_mul, norm_star]
      _ <= Finset.univ.sum (fun _ : Iota => s * s) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul
          (hEntries a i) (hEntries a j) (norm_nonneg _) hs)
      _ = (Fintype.card Iota : Real) * s ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pow_two]
      _ <= 1 := hScale
  have hGram : norm (M.conjTranspose * M) <= (Fintype.card Jota : Real) := by
    apply hamiltonian_l2_row_column_budget _ _ (Nat.cast_nonneg _)
    all_goals
      intro i
      calc
        _ <= Finset.univ.sum (fun _ : Jota => (1 : Real)) :=
          Finset.sum_le_sum (fun j _ => hEntry _ _)
        _ = _ := by simp
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hGram
  have hk : 0 <= (Fintype.card Jota : Real) := Nat.cast_nonneg _
  nlinarith only [hGram, hk, norm_nonneg M, sq_nonneg (Fintype.card Jota : Real)]

def hamiltonianRealFactorLeft (A : Matrix Iota Jota Complex) :
    Matrix Iota (Sum Jota Jota) Real :=
  fun i s => Sum.elim (fun j => (A i j).re) (fun j => -(A i j).im) s

def hamiltonianRealFactorRight (B : Matrix Jota Iota Complex) :
    Matrix (Sum Jota Jota) Iota Real :=
  fun s i => Sum.elim (fun j => (B j i).re) (fun j => (B j i).im) s

theorem hamiltonian_real_factor_product
    (A : Matrix Iota Jota Complex) (B : Matrix Jota Iota Complex) :
    hamiltonianRealPartMatrix (A * B) =
      hamiltonianRealFactorLeft A * hamiltonianRealFactorRight B := by
  ext i j
  change (Finset.univ.sum (fun a => A i a * B a j)).re =
    Finset.univ.sum (fun a : Sum Jota Jota =>
      hamiltonianRealFactorLeft A i a * hamiltonianRealFactorRight B a j)
  rw [hamiltonian_complex_real_sum, Fintype.sum_sum_type]
  simp only [Complex.mul_re, hamiltonianRealFactorLeft, hamiltonianRealFactorRight,
    Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    sub_eq_add_neg, Finset.sum_add_distrib]

theorem hamiltonian_real_factor_norm_bounds
    (A : Matrix Iota Jota Complex) (B : Matrix Jota Iota Complex) (s : Real)
    (hs : 0 <= s)
    (hA : forall i j, norm (A i j) <= s) (hB : forall j i, norm (B j i) <= s)
    (hScale : (Fintype.card Iota : Real) * s ^ 2 <= 1) :
    norm (hamiltonianRealFactorLeft A) <=
        (Fintype.card (Sum Jota Jota) : Real) + 1 /\
      norm (hamiltonianRealFactorRight B) <=
        (Fintype.card (Sum Jota Jota) : Real) + 1 := by
  have hLeft (i : Iota) (j : Sum Jota Jota) :
      norm (hamiltonianRealFactorLeft A i j) <= s := by
    cases j with
    | inl j =>
      change norm (A i j).re <= s
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (hA i j)
    | inr j =>
      change norm (-(A i j).im) <= s
      rw [norm_neg, Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans (hA i j)
  have hRight (i : Iota) (j : Sum Jota Jota) :
      norm ((hamiltonianRealFactorRight B).transpose i j) <= s := by
    cases j with
    | inl j =>
      change norm (B j i).re <= s
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (hB j i)
    | inr j =>
      change norm (B j i).im <= s
      rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans (hB j i)
  refine And.intro (hamiltonian_rectangular_normalized_entry_norm_bound _ s hs hLeft hScale) ?_
  rw [<- hamiltonian_real_transpose_norm]
  exact hamiltonian_rectangular_normalized_entry_norm_bound _ s hs hRight hScale

end PrimeFactorOscillations
