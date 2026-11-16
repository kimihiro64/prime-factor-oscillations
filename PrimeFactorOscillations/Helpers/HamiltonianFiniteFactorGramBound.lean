/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFiniteFactorDeterminant

/-! # Dimension-independent entry bounds for all four Gram update blocks -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota Kappa : Type*}
variable [Fintype Iota] [Fintype Jota] [Fintype Kappa]
variable [DecidableEq Iota] [DecidableEq Jota] [DecidableEq Kappa]

theorem hamiltonian_rectangular_product_norm_bound
    (A : Matrix Iota Jota Real) (B : Matrix Jota Kappa Real)
    (a b : Real) (ha : 0 <= a) (hA : norm A <= a) (hB : norm B <= b) :
    norm (A * B) <= a * b :=
  (Matrix.l2_opNorm_mul A B).trans
    (mul_le_mul hA hB (norm_nonneg B) ha)

theorem hamiltonian_real_transpose_norm (A : Matrix Iota Jota Real) :
    norm A.transpose = norm A := by
  have he : A.conjTranspose = A.transpose := by ext i j; rfl
  rw [<- he, Matrix.l2_opNorm_conjTranspose]

theorem hamiltonian_gram_update_entry_bound
    (R A : Matrix Iota Iota Real) (U : Matrix Iota Jota Real)
    (V : Matrix Jota Iota Real) (alpha L : Real)
    (hAlpha : 0 <= alpha) (hL : 0 <= L)
    (hR : norm R <= 1) (hA : norm A <= alpha)
    (hU : norm U <= L) (hV : norm V <= L)
    (s t : Sum Jota Jota) :
    abs ((hamiltonianGramUpdateRight R U V * A *
      hamiltonianGramUpdateLeft R U V) s t) <= alpha * (L ^ 2 + L ^ 4) := by
  have hRt : norm R.transpose <= 1 := by
    rw [hamiltonian_real_transpose_norm]
    exact hR
  have hUt : norm U.transpose <= L := by
    rw [hamiltonian_real_transpose_norm]
    exact hU
  have hVt : norm V.transpose <= L := by
    rw [hamiltonian_real_transpose_norm]
    exact hV
  have hRU : norm (R.transpose * U) <= L := by
    simpa only [one_mul] using
      hamiltonian_rectangular_product_norm_bound R.transpose U 1 L (by norm_num) hRt hU
  have hUR : norm (U.transpose * R) <= L := by
    simpa only [mul_one] using
      hamiltonian_rectangular_product_norm_bound U.transpose R L 1 hL hUt hR
  have hUU : norm (U.transpose * U) <= L ^ 2 := by
    simpa only [pow_two] using
      hamiltonian_rectangular_product_norm_bound U.transpose U L L hL hUt hU
  have hUUV : norm (U.transpose * U * V) <= L ^ 3 := by
    have h := hamiltonian_rectangular_product_norm_bound
      (U.transpose * U) V (L ^ 2) L (sq_nonneg L) hUU hV
    simpa only [pow_succ] using h
  have hW : norm (U.transpose * R + U.transpose * U * V) <= L + L ^ 3 :=
    (norm_add_le _ _).trans (add_le_add hUR hUUV)
  have hVLarge : norm V <= L + L ^ 3 :=
    hV.trans (le_add_of_nonneg_right (pow_nonneg hL 3))
  have hLL : 0 <= L + L ^ 3 := add_nonneg hL (pow_nonneg hL 3)
  have hBlock (W : Matrix Jota Iota Real) (Z : Matrix Iota Jota Real)
      (hWN : norm W <= L + L ^ 3) (hZN : norm Z <= L) (i j : Jota) :
      abs ((W * A * Z) i j) <= alpha * (L ^ 2 + L ^ 4) := by
    have hWA : norm (W * A) <= (L + L ^ 3) * alpha :=
      hamiltonian_rectangular_product_norm_bound W A (L + L ^ 3) alpha hLL hWN hA
    have hN : norm (W * A * Z) <= alpha * (L ^ 2 + L ^ 4) := by
      calc
        _ <= ((L + L ^ 3) * alpha) * L :=
          hamiltonian_rectangular_product_norm_bound (W * A) Z
            ((L + L ^ 3) * alpha) L (mul_nonneg hLL hAlpha) hWA hZN
        _ = _ := by ring
    have hE : abs ((W * A * Z) i j) <= norm (W * A * Z) := by
      simpa only [Real.norm_eq_abs] using l2_matrix_entry_le_norm (W * A * Z) i j
    exact hE.trans hN
  cases s with
  | inl i =>
    cases t with
    | inl j =>
      change abs ((V * A * (R.transpose * U)) i j) <= _
      exact hBlock V (R.transpose * U) hVLarge hRU i j
    | inr j =>
      change abs ((V * A * V.transpose) i j) <= _
      exact hBlock V V.transpose hVLarge hVt i j
  | inr i =>
    cases t with
    | inl j =>
      change abs (((U.transpose * R + U.transpose * U * V) * A *
        (R.transpose * U)) i j) <= _
      exact hBlock _ _ hW hRU i j
    | inr j =>
      change abs (((U.transpose * R + U.transpose * U * V) * A * V.transpose) i j) <= _
      exact hBlock _ _ hW hVt i j

theorem hamiltonian_gram_determinant_update_bound
    (B R M A : Matrix Iota Iota Real) (U : Matrix Iota Jota Real)
    (V : Matrix Jota Iota Real) (alpha L : Real)
    (hB : B = R + U * V) (hInv : M * A = 1)
    (hAlpha : 0 <= alpha) (hL : 0 <= L)
    (hR : norm R <= 1) (hA : norm A <= alpha)
    (hU : norm U <= L) (hV : norm V <= L) :
    abs (Matrix.det (M + (B.transpose * B - R.transpose * R)) / Matrix.det M) <=
      ((Fintype.card (Sum Jota Jota)).factorial : Real) *
        (1 + alpha * (L ^ 2 + L ^ 4)) ^ Fintype.card (Sum Jota Jota) := by
  rw [hamiltonian_gram_update_factorization B R U V hB,
    hamiltonian_determinant_right_inverse_update M A _ _ hInv]
  exact hamiltonian_det_one_add_entry_bound _ _
    (hamiltonian_gram_update_entry_bound R A U V alpha L
      hAlpha hL hR hA hU hV)

end PrimeFactorOscillations
