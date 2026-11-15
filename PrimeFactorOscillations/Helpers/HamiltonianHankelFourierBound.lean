/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import PrimeFactorOscillations.Helpers.LPFCyclicFourier

/-! # Lossless Fourier-to-Hankel operator transfer

Two independent injective input samplings are retained. The full frequency
error, including its phases and principal compensation, is the symbol.
The operator bound has no auxiliary-grid or input-dimension loss.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

variable {Iota Jota : Type*}
variable [Fintype Iota] [DecidableEq Iota]
variable [Fintype Jota] [DecidableEq Jota]
variable {N : Nat} [NeZero N]

def hamiltonianFourierFrame (freq : Iota -> ZMod N) :
    Matrix Iota (ZMod N) Complex :=
  fun i x => ZMod.stdAddChar (x * freq i)

def hamiltonianFourierHankel (F : ZMod N -> Complex)
    (freq : Iota -> ZMod N) (freq' : Jota -> ZMod N) :
    Matrix Iota Jota Complex :=
  fun i j => lpfCyclicInverse F (freq i + freq' j)

theorem hamiltonian_fourier_frame_gram (freq : Iota -> ZMod N)
    (hFreq : Function.Injective freq) :
    hamiltonianFourierFrame freq *
        (hamiltonianFourierFrame freq).conjTranspose =
      HSMul.hSMul (N : Complex) (1 : Matrix Iota Iota Complex) := by
  ext i j
  change Finset.univ.sum (fun x : ZMod N =>
    ZMod.stdAddChar (x * freq i) *
      (starRingEnd Complex) (ZMod.stdAddChar (x * freq j))) = _
  rw [AddChar.sum_crossPhase (ZMod.stdAddChar (N := N))
    (ZMod.isPrimitive_stdAddChar N)]
  simp only [hFreq.eq_iff, ZMod.card, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem hamiltonian_fourier_frame_norm_square [Nonempty Iota]
    (freq : Iota -> ZMod N) (hFreq : Function.Injective freq) :
    norm (hamiltonianFourierFrame freq) *
      norm (hamiltonianFourierFrame freq) = (N : Real) := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self
    (hamiltonianFourierFrame freq).conjTranspose
  rw [Matrix.conjTranspose_conjTranspose,
    hamiltonian_fourier_frame_gram freq hFreq] at h
  simpa only [norm_smul, Complex.norm_natCast, norm_one, mul_one,
    Matrix.l2_opNorm_conjTranspose] using h.symm

theorem hamiltonian_fourier_hankel_factorization
    (F : ZMod N -> Complex) (freq : Iota -> ZMod N)
    (freq' : Jota -> ZMod N) :
    hamiltonianFourierHankel F freq freq' =
      HSMul.hSMul (Inv.inv (N : Complex))
        ((hamiltonianFourierFrame (fun i => -freq i) * Matrix.diagonal F) *
          (hamiltonianFourierFrame freq').conjTranspose) := by
  ext i j
  unfold hamiltonianFourierHankel lpfCyclicInverse
  rw [zpow_neg_one]
  rw [Matrix.mul_assoc]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    hamiltonianFourierFrame]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hArg : (freq i + freq' j) * (-x) =
      x * (-freq i) - x * freq' j := by ring
  have hPhase : ZMod.stdAddChar ((freq i + freq' j) * (-x)) =
      ZMod.stdAddChar (x * (-freq i)) *
        (starRingEnd Complex) (ZMod.stdAddChar (x * freq' j)) := by
    rw [hArg, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
  rw [hPhase]
  simp only [starRingEnd_apply]
  ring

theorem hamiltonian_fourier_hankel_sub
    (F G : ZMod N -> Complex) (freq : Iota -> ZMod N)
    (freq' : Jota -> ZMod N) :
    hamiltonianFourierHankel (fun x => F x - G x) freq freq' =
      hamiltonianFourierHankel F freq freq' -
        hamiltonianFourierHankel G freq freq' := by
  ext i j
  simp only [hamiltonianFourierHankel, lpfCyclicInverse, Matrix.sub_apply,
    sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem hamiltonian_fourier_hankel_norm_bound
    [Nonempty Iota] [Nonempty Jota]
    (F : ZMod N -> Complex) (freq : Iota -> ZMod N)
    (freq' : Jota -> ZMod N)
    (hFreq : Function.Injective freq) (hFreq' : Function.Injective freq')
    (E : Real) (hE : 0 <= E) (hBound : forall x, norm (F x) <= E) :
    norm (hamiltonianFourierHankel F freq freq') <= E := by
  let A := hamiltonianFourierFrame (fun i => -freq i)
  let B := hamiltonianFourierFrame freq'
  have hNeg : Function.Injective (fun i => -freq i) := neg_injective.comp hFreq
  have hA := hamiltonian_fourier_frame_norm_square (fun i => -freq i) hNeg
  have hB := hamiltonian_fourier_frame_norm_square freq' hFreq'
  change norm A * norm A = (N : Real) at hA
  change norm B * norm B = (N : Real) at hB
  have hNormEq : norm A = norm B := by
    nlinarith only [hA, hB, norm_nonneg A, norm_nonneg B]
  have hProduct : norm A * norm B = (N : Real) := by
    rw [hNormEq]
    exact hB
  have hDiag : norm (Matrix.diagonal F) <= E := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hE).mpr hBound
  have hFirst := Matrix.l2_opNorm_mul A (Matrix.diagonal F)
  have hSecond := Matrix.l2_opNorm_mul (A * Matrix.diagonal F) B.conjTranspose
  rw [Matrix.l2_opNorm_conjTranspose] at hSecond
  have hAll : norm ((A * Matrix.diagonal F) * B.conjTranspose) <=
      (norm A * E) * norm B := by
    calc
      _ <= norm (A * Matrix.diagonal F) * norm B := hSecond
      _ <= (norm A * norm (Matrix.diagonal F)) * norm B :=
        mul_le_mul_of_nonneg_right hFirst (norm_nonneg B)
      _ <= _ := by gcongr
  have hN : (0 : Real) < (N : Real) := by exact_mod_cast (NeZero.pos N)
  rw [hamiltonian_fourier_hankel_factorization, norm_smul, norm_inv,
    Complex.norm_natCast]
  change Inv.inv (N : Real) * norm ((A * Matrix.diagonal F) * B.conjTranspose) <= E
  calc
    _ <= Inv.inv (N : Real) * ((norm A * E) * norm B) :=
      mul_le_mul_of_nonneg_left hAll (by positivity)
    _ = E := by
      rw [show (norm A * E) * norm B = E * (norm A * norm B) by ring, hProduct]
      field_simp

theorem hamiltonian_fourier_hankel_difference_bound
    [Nonempty Iota] [Nonempty Jota]
    (F G : ZMod N -> Complex) (freq : Iota -> ZMod N)
    (freq' : Jota -> ZMod N)
    (hFreq : Function.Injective freq) (hFreq' : Function.Injective freq')
    (E : Real) (hE : 0 <= E) (hBound : forall x, norm (F x - G x) <= E) :
    norm (hamiltonianFourierHankel F freq freq' -
      hamiltonianFourierHankel G freq freq') <= E := by
  rw [<- hamiltonian_fourier_hankel_sub]
  exact hamiltonian_fourier_hankel_norm_bound (fun x => F x - G x)
    freq freq' hFreq hFreq' E hE hBound

end PrimeFactorOscillations.LPF
