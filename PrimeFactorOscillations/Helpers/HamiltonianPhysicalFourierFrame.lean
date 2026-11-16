/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianReferencePhysicalCutoff
import PrimeFactorOscillations.Helpers.HamiltonianRetainedOperatorBounds

/-! # The physical rational sampling frame

A complex entry budget is applied only to the centered Gram error.
The actual character frame retains every phase and both input samplings.
Its squared norm is controlled by n plus the complete Gram error.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_complex_l2_entry_budget (M : Matrix Iota Iota Complex)
    (c : Real) (hc : 0 <= c) (hEntry : forall i j, norm (M i j) <= c) :
    norm M <= (Fintype.card Iota : Real) * c := by
  let m : Real := Fintype.card Iota
  let op := (@Matrix.toEuclideanCLM Complex Iota _ _ _) M
  have hm : 0 <= m := Nat.cast_nonneg _
  have hRow (i : Iota) :
      Finset.univ.sum (fun j => norm (M i j) ^ 2) <= m * c ^ 2 := by
    calc
      _ <= Finset.univ.sum (fun _ : Iota => c ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        have h := mul_le_mul (hEntry i j) (hEntry i j) (norm_nonneg _) hc
        simpa only [pow_two] using h
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m]
  have hOp : norm op <= m * c := by
    apply ContinuousLinearMap.opNorm_le_bound op (mul_nonneg hm hc)
    intro x
    let y := op x
    have hEach (i : Iota) : norm (y.ofLp i) ^ 2 <= (m * c ^ 2) * norm x ^ 2 := by
      let S := Finset.univ.sum (fun j => norm (M i j) * norm (x.ofLp j))
      have hSum : norm (y.ofLp i) <= S := by
        change norm (Finset.univ.sum (fun j => M i j * x.ofLp j)) <= _
        exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul, S])
      have hS : 0 <= S := Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      have hSquare := mul_le_mul hSum hSum (norm_nonneg _) hS
      have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j => norm (M i j)) (fun j => norm (x.ofLp j))
      have hNorm : Finset.univ.sum (fun j => norm (x.ofLp j) ^ 2) = norm x ^ 2 :=
        (EuclideanSpace.norm_sq_eq x).symm
      rw [hNorm] at hCS
      have hFirst : norm (y.ofLp i) ^ 2 <=
          (Finset.univ.sum (fun j => norm (M i j) ^ 2)) * norm x ^ 2 := by
        nlinarith only [hSquare, hCS]
      exact hFirst.trans (mul_le_mul_of_nonneg_right (hRow i) (sq_nonneg (norm x)))
    have hSquare : norm y ^ 2 <= (m * c * norm x) ^ 2 := by
      calc
        _ = Finset.univ.sum (fun i => norm (y.ofLp i) ^ 2) := EuclideanSpace.norm_sq_eq y
        _ <= Finset.univ.sum (fun _ : Iota => (m * c ^ 2) * norm x ^ 2) :=
          Finset.sum_le_sum (fun i _ => hEach i)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m]; ring
    have hPositive : 0 <= m * c * norm x := mul_nonneg (mul_nonneg hm hc) (norm_nonneg x)
    nlinarith only [hSquare, hPositive, norm_nonneg y]
  rwa [Matrix.l2_opNorm_toEuclideanCLM] at hOp

def hamiltonianPhysicalFourierFrame (n R : Nat) [NeZero R]
    (freq : Iota -> ZMod R) : Matrix (Fin n) Iota Complex :=
  fun i u => ZMod.stdAddChar (freq u * ((i.val + 1 : Nat) : ZMod R))

theorem hamiltonian_physical_frame_gram {R : Nat} [NeZero R]
    (n : Nat) (freq : Iota -> ZMod R) (u v : Iota) :
    ((hamiltonianPhysicalFourierFrame n R freq).conjTranspose *
      hamiltonianPhysicalFourierFrame n R freq) u v =
        lpfIntervalFrequencyKernel R 0 n (freq v - freq u) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hamiltonianPhysicalFourierFrame]
  rw [Fin.sum_univ_eq_sum_range (fun i : Nat =>
    star (ZMod.stdAddChar (freq u * ((i + 1 : Nat) : ZMod R))) *
      ZMod.stdAddChar (freq v * ((i + 1 : Nat) : ZMod R)))]
  unfold lpfIntervalFrequencyKernel
  apply Finset.sum_congr rfl
  intro i hi
  have hPhase : ZMod.stdAddChar
      ((freq v - freq u) * ((0 + 1 + i : Nat) : ZMod R)) =
      (starRingEnd Complex) (ZMod.stdAddChar (freq u * ((i + 1 : Nat) : ZMod R))) *
        ZMod.stdAddChar (freq v * ((i + 1 : Nat) : ZMod R)) := by
    have hArg : (freq v - freq u) * ((0 + 1 + i : Nat) : ZMod R) =
        -(freq u * ((i + 1 : Nat) : ZMod R)) +
          freq v * ((i + 1 : Nat) : ZMod R) := by push_cast; ring
    rw [hArg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
  exact hPhase.symm

theorem hamiltonian_physical_frame_norm_square {R : Nat} [NeZero R]
    (n : Nat) (freq : Iota -> ZMod R) (B : Real) (hB : 0 <= B)
    (hOff : forall u v, Not (u = v) ->
      norm (lpfIntervalFrequencyKernel R 0 n (freq v - freq u)) <= B) :
    norm (hamiltonianPhysicalFourierFrame n R freq) *
        norm (hamiltonianPhysicalFourierFrame n R freq) <=
      (n : Real) + (Fintype.card Iota : Real) * B := by
  let F := hamiltonianPhysicalFourierFrame n R freq
  let G := F.conjTranspose * F - HSMul.hSMul (n : Complex) (1 : Matrix Iota Iota Complex)
  have hEntry : forall u v, norm (G u v) <= B := by
    intro u v
    change norm (((hamiltonianPhysicalFourierFrame n R freq).conjTranspose *
      hamiltonianPhysicalFourierFrame n R freq) u v -
      (n : Complex) * (1 : Matrix Iota Iota Complex) u v) <= B
    rw [hamiltonian_physical_frame_gram]
    by_cases h : u = v
    . subst v
      simpa only [sub_self, lpfIntervalFrequencyKernel, zero_mul,
        AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one, Matrix.one_apply_eq, sub_self, norm_zero] using hB
    . rw [Matrix.one_apply_ne h, mul_zero, sub_zero]
      exact hOff u v h
  have hGram := hamiltonian_complex_l2_entry_budget G B hB hEntry
  have hIdentity : norm (1 : Matrix Iota Iota Complex) <= 1 := by
    rw [<- Matrix.l2_opNorm_toEuclideanCLM]
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    rw [map_one]
    change norm x <= 1 * norm x
    rw [one_mul]
  have hDiagonal : norm (HSMul.hSMul (n : Complex) (1 : Matrix Iota Iota Complex)) <=
      (n : Real) := by
    rw [norm_smul, Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left hIdentity (Nat.cast_nonneg n)).trans_eq (mul_one _)
  have hFull : norm (F.conjTranspose * F) <=
      (n : Real) + (Fintype.card Iota : Real) * B := by
    have hDecomp : F.conjTranspose * F =
        G + HSMul.hSMul (n : Complex) (1 : Matrix Iota Iota Complex) := by dsimp [G]; abel
    rw [hDecomp]
    exact (norm_add_le _ _).trans (by linarith only [hGram, hDiagonal])
  rwa [Matrix.l2_opNorm_conjTranspose_mul_self] at hFull

end PrimeFactorOscillations.LPF
