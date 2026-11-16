/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianHankelFourierBound

/-! # Exact full Fourier determinant products

The two complete character frames cancel the entire grid normalization.
Every signed frequency remains in the resulting finite product.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations.LPF

variable {n : Nat} [NeZero n]

theorem hamiltonian_cyclic_inverse_one (t : ZMod n) :
    lpfCyclicInverse (fun _ : ZMod n => (1 : Complex)) t =
      if t = 0 then 1 else 0 := by
  have hN : Not ((n : Complex) = 0) := by exact_mod_cast NeZero.ne n
  have hPhase (x : ZMod n) :
      ZMod.stdAddChar (t * (-x)) =
        ZMod.stdAddChar (x * (0 : ZMod n)) *
          (starRingEnd Complex) (ZMod.stdAddChar (x * t)) := by
    rw [mul_zero, AddChar.map_zero_eq_one, one_mul,
      show t * (-x) = -(x * t) by ring, AddChar.map_neg_eq_conj]
  unfold lpfCyclicInverse
  simp only [zpow_neg_one, one_mul]
  simp_rw [hPhase]
  rw [AddChar.sum_crossPhase (ZMod.stdAddChar (N := n)) (ZMod.isPrimitive_stdAddChar n)]
  by_cases h : t = 0
  case pos => simp [h, ZMod.card, hN]
  case neg =>
    have hZero : Not ((0 : ZMod n) = t) := Ne.symm h
    simp [h, hZero]

theorem hamiltonian_fourier_difference_identity :
    hamiltonianFourierHankel (fun _ : ZMod n => (1 : Complex))
      (fun x : ZMod n => x) (fun y : ZMod n => -y) =
        (1 : Matrix (ZMod n) (ZMod n) Complex) := by
  ext x y
  simp only [hamiltonianFourierHankel, hamiltonian_cyclic_inverse_one,
    <- sub_eq_add_neg, sub_eq_zero, Matrix.one_apply]

theorem hamiltonian_fourier_difference_determinant (F : ZMod n -> Complex) :
    Matrix.det (hamiltonianFourierHankel F
      (fun x : ZMod n => x) (fun y : ZMod n => -y)) =
        Finset.univ.prod F := by
  let W := hamiltonianFourierFrame (fun x : ZMod n => -x)
  have hN : Not ((n : Complex) = 0) := by exact_mod_cast NeZero.ne n
  have hGram : Matrix.det W * Matrix.det W.conjTranspose = (n : Complex) ^ n := by
    rw [<- Matrix.det_mul]
    change Matrix.det (hamiltonianFourierFrame (fun x : ZMod n => -x) *
      (hamiltonianFourierFrame (fun x : ZMod n => -x)).conjTranspose) = _
    rw [hamiltonian_fourier_frame_gram (fun x : ZMod n => -x) neg_injective]
    simp only [Matrix.det_smul, Matrix.det_one, ZMod.card, mul_one]
  rw [hamiltonian_fourier_hankel_factorization, Matrix.det_smul,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, ZMod.card]
  change (Inv.inv (n : Complex)) ^ n *
    ((Matrix.det W * Finset.univ.prod F) * Matrix.det W.conjTranspose) = _
  calc
    _ = (Inv.inv (n : Complex)) ^ n *
        (Matrix.det W * Matrix.det W.conjTranspose) * Finset.univ.prod F := by ring
    _ = _ := by rw [hGram, <- mul_pow]; field_simp <;> simp


theorem hamiltonian_fourier_hankel_scalar (c : Complex) (F : ZMod n -> Complex) :
    hamiltonianFourierHankel (fun k => c * F k)
      (fun x : ZMod n => x) (fun y : ZMod n => -y) =
        HSMul.hSMul c (hamiltonianFourierHankel F
          (fun x : ZMod n => x) (fun y : ZMod n => -y)) := by
  ext x y
  simp only [hamiltonianFourierHankel, lpfCyclicInverse, Matrix.smul_apply,
    smul_eq_mul, <- Finset.mul_sum, mul_assoc]
  ring

end PrimeFactorOscillations.LPF
