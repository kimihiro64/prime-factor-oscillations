/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianLinearScalingSupport

/-! # Complete signed scaling trace comparison before numeric substitution

The ambient linear trace is retained. Only the Schur correction,
quadratic scaling, rank centering and exact support difference are
estimated. The zero diagonal cancels the identity contribution.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_scaling_trace_budget
    (A G P C : Matrix Iota Iota Real) (D : Finset Iota)
    (z : forall _i : (Compl.compl D : Finset Iota), Real)
    (J : Matrix (Compl.compl D : Finset Iota) (Compl.compl D : Finset Iota) Real)
    (q qNew c b v eJ eE : Real)
    (hc : 0 <= c) (hb : 0 <= b) (hv : 0 <= v) (heJ : 0 <= eJ) (heE : 0 <= eE)
    (hA : A = 1 - G) (hCenter : Matrix.trace (A * C) = 0)
    (hG : forall i j, abs (G i j) <= c)
    (hPDiag : forall i, P i i = 0) (hCDiag : forall i, C i i = 0)
    (hC : forall i j, abs (C i j) <= 1)
    (hNonneg : forall i j, 0 <= P i j)
    (hRow : forall i, Finset.sum Finset.univ (fun j => P i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => P i j) = 1)
    (hP : forall i j, abs (P i j) <= v)
    (hZ : forall i, abs (z i) <= b)
    (hJ : forall i j : (Compl.compl D : Finset Iota),
      abs (J i j - A i.val j.val) <= eJ)
    (hE : forall i j : (Compl.compl D : Finset Iota),
      abs (hamiltonianScalingPerturbation
        (P.submatrix (fun i => i.val) (fun i => i.val))
        (C.submatrix (fun i => i.val) (fun i => i.val)) z q qNew i j) <= eE) :
    let R : Finset Iota := Compl.compl D
    let PR := P.submatrix (fun i : R => i.val) (fun i : R => i.val)
    let CR := C.submatrix (fun i : R => i.val) (fun i : R => i.val)
    let E := hamiltonianScalingPerturbation PR CR z q qNew
    let x := hamiltonianZeroExtend D z
    let X := Matrix.diagonal x * P + P * Matrix.diagonal x
    abs (Matrix.trace (J * E) - Matrix.trace (A * X)) <=
      (R.card : Real) ^ 2 * eJ * eE +
      (R.card : Real) ^ 2 * c * b ^ 2 * v +
      abs (q - qNew) * (2 * (D.card : Real) * (Fintype.card Iota : Real) * c) +
      2 * (D.card : Real) * c * b := by
  let R : Finset Iota := Compl.compl D
  let AR := A.submatrix (fun i : R => i.val) (fun i : R => i.val)
  let GR := G.submatrix (fun i : R => i.val) (fun i : R => i.val)
  let PR := P.submatrix (fun i : R => i.val) (fun i : R => i.val)
  let CR := C.submatrix (fun i : R => i.val) (fun i : R => i.val)
  let E := hamiltonianScalingPerturbation PR CR z q qNew
  let x := hamiltonianZeroExtend D z
  let X := Matrix.diagonal x * P + P * Matrix.diagonal x
  let XR := Matrix.diagonal z * PR + PR * Matrix.diagonal z
  let Q := Matrix.diagonal z * PR * Matrix.diagonal z
  let u := Matrix.trace ((J - AR) * E)
  let w := Matrix.trace (GR * Q)
  let s := (q - qNew) * Matrix.trace (GR * CR)
  let m := Matrix.trace (G * X) - Matrix.trace (GR * XR)
  have hAR : AR = 1 - GR := by
    change A.submatrix (fun i : R => i.val) (fun i : R => i.val) = 1 - GR
    rw [hA]
    apply Matrix.ext
    intro i j
    change (1 : Matrix Iota Iota Real) i.val j.val - G i.val j.val =
      (1 : Matrix R R Real) i j - G i.val j.val
    simp only [Matrix.one_apply, Subtype.ext_iff]
  have hPDiagR (i : R) : PR i i = 0 := hPDiag i.val
  have hCDiagR (i : R) : CR i i = 0 := hCDiag i.val
  have hEDiag (i : R) : E i i = 0 := by
    dsimp only [E]
    rw [hamiltonianScalingPerturbation_entry, hPDiagR, hCDiagR]
    ring
  have hXDiag (i : Iota) : X i i = 0 := by
    simp only [X, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      hPDiag, mul_zero, zero_mul, add_zero]
  have hTraceAX : Matrix.trace (A * X) = -Matrix.trace (G * X) := by
    rw [hA]
    exact hamiltonian_trace_one_sub_zero_diagonal G X hXDiag
  have hTraceARE : Matrix.trace (AR * E) = -Matrix.trace (GR * E) := by
    rw [hAR]
    exact hamiltonian_trace_one_sub_zero_diagonal GR E hEDiag
  have hMatrixSplit : J * E = (J - AR) * E + AR * E := by rw [sub_mul, sub_add_cancel]
  have hTraceSplit : Matrix.trace (J * E) = u + Matrix.trace (AR * E) := by
    rw [hMatrixSplit, Matrix.trace_add]
  have hEDecomp : E = XR + Q + HSMul.hSMul (q - qNew) CR :=
    hamiltonianScalingPerturbation_decomposition PR CR z q qNew
  have hScaledTrace : Matrix.trace (GR * HSMul.hSMul (q - qNew) CR) =
      (q - qNew) * Matrix.trace (GR * CR) := by
    rw [Matrix.mul_smul]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  have hTraceE : Matrix.trace (GR * E) =
      Matrix.trace (GR * XR) + Matrix.trace (GR * Q) +
        (q - qNew) * Matrix.trace (GR * CR) := by
    rw [hEDecomp, mul_add, mul_add, Matrix.trace_add, Matrix.trace_add, hScaledTrace]
  have hIdentity : Matrix.trace (J * E) - Matrix.trace (A * X) = u - w - s + m := by
    rw [hTraceSplit, hTraceARE, hTraceAX, hTraceE]
    dsimp only [w, s, m]
    ring
  have hSchur : abs u <= (R.card : Real) ^ 2 * eJ * eE := by
    have h := hamiltonian_trace_product_entry_bound (J - AR) E eJ eE heJ heE
      (fun i j => hJ i j) (fun i j => hE i j)
    simpa only [Fintype.card_coe] using h
  have hQEntry (i j : R) : abs (Q i j) <= b ^ 2 * v := by
    have hFirst := mul_le_mul (hZ i) (hP i.val j.val) (abs_nonneg _) hb
    have hSecond := mul_le_mul hFirst (hZ j) (abs_nonneg _) (mul_nonneg hb hv)
    calc
      _ = (abs (z i) * abs (PR i j)) * abs (z j) := by
        simp only [Q, Matrix.diagonal_mul, Matrix.mul_diagonal, abs_mul]
      _ <= (b * v) * b := hSecond
      _ = _ := by ring
  have hQuadratic : abs w <= (R.card : Real) ^ 2 * c * b ^ 2 * v := by
    have h := hamiltonian_trace_product_entry_bound GR Q c (b ^ 2 * v)
      hc (by positivity) (fun i j => hG i.val j.val) hQEntry
    simp only [Fintype.card_coe] at h
    change abs w <= (R.card : Real) ^ 2 * c * (b ^ 2 * v) at h
    nlinarith only [h]
  have hTraceGC : Matrix.trace (G * C) = 0 := by
    have h := hamiltonian_trace_one_sub_zero_diagonal G C hCDiag
    rw [<- hA, hCenter] at h
    linarith only [h]
  have hPair (i j : Iota) : abs (G i j * C j i) <= c := by
    rw [abs_mul]
    have h := mul_le_mul (hG i j) (hC j i) (abs_nonneg _) hc
    simpa only [mul_one] using h
  have hCenterBound : abs (Matrix.trace (GR * CR)) <=
      2 * (D.card : Real) * (Fintype.card Iota : Real) * c := by
    have h := hamiltonian_trace_removed_pair_bound G C D c hc hPair
    rw [hTraceGC, zero_sub, abs_neg] at h
    exact h
  have hCenterTerm : abs s <= abs (q - qNew) *
      (2 * (D.card : Real) * (Fintype.card Iota : Real) * c) := by
    dsimp only [s]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hCenterBound (abs_nonneg _)
  have hRemoved : abs m <= 2 * (D.card : Real) * c * b :=
    hamiltonian_linear_scaling_removed_trace_bound G P D z c b hc hb
      hG hNonneg hRow hCol hZ
  have hOne : abs (u - w - s + m) <= abs (u - w - s) + abs m := abs_add_le _ _
  have hTwo : abs (u - w - s) <= abs (u - w) + abs s := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (u - w) (-s)
  have hThree : abs (u - w) <= abs u + abs w := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le u (-w)
  change abs (Matrix.trace (J * E) - Matrix.trace (A * X)) <= _
  rw [hIdentity]
  linarith only [hOne, hTwo, hThree, hSchur, hQuadratic, hCenterTerm, hRemoved]

end PrimeFactorOscillations
