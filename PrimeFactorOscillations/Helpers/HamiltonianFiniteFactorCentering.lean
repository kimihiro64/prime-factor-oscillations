/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianInjectiveMatrixRestriction

/-! # The negative mean mode remains in the bounded finite factorization -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota Kappa : Type*}
variable [Fintype Iota] [DecidableEq Iota]
variable [Fintype Jota] [DecidableEq Jota]
variable [Fintype Kappa] [DecidableEq Kappa]

def hamiltonianFactorJoinLeft (U : Matrix Iota Jota Real) (X : Matrix Iota Kappa Real) :
    Matrix Iota (Sum Jota Kappa) Real :=
  fun i s => Sum.elim (fun j => U i j) (fun j => X i j) s

def hamiltonianFactorJoinRight (V : Matrix Jota Iota Real) (Y : Matrix Kappa Iota Real) :
    Matrix (Sum Jota Kappa) Iota Real :=
  fun s i => Sum.elim (fun j => V j i) (fun j => Y j i) s

theorem hamiltonian_factor_join_product
    (U : Matrix Iota Jota Real) (X : Matrix Iota Kappa Real)
    (V : Matrix Jota Iota Real) (Y : Matrix Kappa Iota Real) :
    hamiltonianFactorJoinLeft U X * hamiltonianFactorJoinRight V Y = U * V + X * Y := by
  ext i j
  change (Finset.univ.sum (fun s : Sum Jota Kappa =>
    hamiltonianFactorJoinLeft U X i s * hamiltonianFactorJoinRight V Y s j)) = _
  rw [Fintype.sum_sum_type]
  rfl

theorem hamiltonian_factor_join_left_norm
    (U : Matrix Iota Jota Real) (X : Matrix Iota Kappa Real) :
    norm (hamiltonianFactorJoinLeft U X) <= norm U + norm X := by
  let f : Jota -> Sum Jota Kappa := Sum.inl
  let g : Kappa -> Sum Jota Kappa := Sum.inr
  have hf : Function.Injective f := fun i j h => Sum.inl.inj h
  have hg : Function.Injective g := fun i j h => Sum.inr.inj h
  have hIdentity : hamiltonianFactorJoinLeft U X =
      U * hamiltonianRowSelector f + X * hamiltonianRowSelector g := by
    ext i s
    cases s <;>
      simp [hamiltonianFactorJoinLeft, Matrix.mul_apply, hamiltonianRowSelector,
        f, g, mul_ite]
  have hU : norm (U * hamiltonianRowSelector f) <= norm U := by
    calc
      _ <= norm U * norm (hamiltonianRowSelector f) := Matrix.l2_opNorm_mul _ _
      _ <= norm U * 1 := mul_le_mul_of_nonneg_left
        (hamiltonian_row_selector_norm f hf) (norm_nonneg U)
      _ = _ := mul_one _
  have hX : norm (X * hamiltonianRowSelector g) <= norm X := by
    calc
      _ <= norm X * norm (hamiltonianRowSelector g) := Matrix.l2_opNorm_mul _ _
      _ <= norm X * 1 := mul_le_mul_of_nonneg_left
        (hamiltonian_row_selector_norm g hg) (norm_nonneg X)
      _ = _ := mul_one _
  rw [hIdentity]
  exact (norm_add_le _ _).trans (add_le_add hU hX)

theorem hamiltonian_factor_join_right_norm
    (V : Matrix Jota Iota Real) (Y : Matrix Kappa Iota Real) :
    norm (hamiltonianFactorJoinRight V Y) <= norm V + norm Y := by
  have hIdentity : (hamiltonianFactorJoinRight V Y).transpose =
      hamiltonianFactorJoinLeft V.transpose Y.transpose := by
    ext i s
    cases s <;> rfl
  rw [<- hamiltonian_real_transpose_norm (hamiltonianFactorJoinRight V Y), hIdentity]
  have h := hamiltonian_factor_join_left_norm V.transpose Y.transpose
  simpa only [hamiltonian_real_transpose_norm] using h

theorem hamiltonian_finite_factor_centering
    (U : Matrix Iota Jota Real) (V : Matrix Jota Iota Real) (q c L : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (hq0 : 0 <= q)
    (hc : 0 <= c) (hc2 : c <= 2) (hL : 0 <= L)
    (hU : norm U <= L) (hV : norm V <= L) :
    exists A : Matrix Iota (Sum Jota PUnit) Real,
      exists B : Matrix (Sum Jota PUnit) Iota Real,
        SMul.smul c (U * V) - averagingKernel q = A * B /\
          norm A <= 2 * L + 2 /\ norm B <= 2 * L + 2 := by
  let X : Matrix Iota PUnit Real := fun _ _ => Real.sqrt q
  let Y : Matrix PUnit Iota Real := fun _ _ => -Real.sqrt q
  have hScale : (Fintype.card Iota : Real) * (Real.sqrt q) ^ 2 <= 1 := by
    rw [Real.sq_sqrt hq0, hq]
  have hX : norm X <= 2 := by
    have h := hamiltonian_rectangular_normalized_entry_norm_bound X (Real.sqrt q)
      (Real.sqrt_nonneg q) (by intro i j; exact le_of_eq (Real.norm_of_nonneg (Real.sqrt_nonneg q)))
      hScale
    norm_num only [Fintype.card_punit, Nat.cast_one] at h
    exact h
  have hY : norm Y <= 2 := by
    have h := hamiltonian_rectangular_normalized_entry_norm_bound Y.transpose (Real.sqrt q)
      (Real.sqrt_nonneg q) (by
        intro i j
        change norm (-Real.sqrt q) <= Real.sqrt q
        rw [norm_neg, Real.norm_of_nonneg (Real.sqrt_nonneg q)])
      hScale
    rw [hamiltonian_real_transpose_norm] at h
    norm_num only [Fintype.card_punit, Nat.cast_one] at h
    exact h
  have hXY : X * Y = -averagingKernel q := by
    ext i j
    change (Finset.univ.sum (fun _ : PUnit => Real.sqrt q * (-Real.sqrt q))) = -q
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_punit, one_smul]
    nlinarith only [Real.sq_sqrt hq0]
  let W : Matrix Iota Jota Real := SMul.smul c U
  have hW : norm W <= 2 * L := by
    calc
      _ = c * norm U := by
        have he : norm W = norm c * norm U := norm_smul c U
        rw [he, Real.norm_of_nonneg hc]
      _ <= 2 * L := mul_le_mul hc2 hU (norm_nonneg U) (by norm_num)
  refine Exists.intro (hamiltonianFactorJoinLeft W X)
    (Exists.intro (hamiltonianFactorJoinRight V Y) (And.intro ?_ (And.intro ?_ ?_)))
  next =>
    rw [hamiltonian_factor_join_product, hXY]
    have he : W * V = SMul.smul c (U * V) := by
      ext i j
      change Finset.univ.sum (fun a => (c * U i a) * V a j) =
        c * Finset.univ.sum (fun a => U i a * V a j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    rw [he]
    abel
  next =>
    exact (hamiltonian_factor_join_left_norm W X).trans (add_le_add hW hX)
  next =>
    have h := (hamiltonian_factor_join_right_norm V Y).trans (add_le_add hV hY)
    linarith only [h, hL]

end PrimeFactorOscillations
