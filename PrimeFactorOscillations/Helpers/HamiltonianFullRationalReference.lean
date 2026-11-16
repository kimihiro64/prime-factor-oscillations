/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeOperatorFourier
import PrimeFactorOscillations.Helpers.LPFCyclicKernel
import PrimeFactorOscillations.Helpers.LPFGridReference

/-! # The complete untruncated rational reference

All reduced rational centers and their signed Mobius coefficients remain
in the actual Fourier symbol. Its inverse is exactly the physical
Ramanujan model on the sampled integer domain. No arc extension is needed.
The coefficient mass is used only for explicitly off-resonant leakage.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianRationalCenter (R Q : Nat) (u : lpfRationalCenters Q) : ZMod R :=
  lpfRationalGridPoint R (u.1.val + 1) (u.2 : ZMod (u.1.val + 1)).val 0

def hamiltonianRationalMain (R : Nat) [NeZero R] (Q : Nat) (t : ZMod R) : Complex :=
  Finset.univ.sum (fun u : lpfRationalCenters Q =>
    lpfRationalCoefficient (u.1.val + 1) *
      ZMod.stdAddChar ((-hamiltonianRationalCenter R Q u) * t))

def hamiltonianFullRationalReference (R : Nat) [NeZero R]
    (Q s L : Nat) (x : ZMod R) : Complex :=
  Finset.univ.sum (fun u : lpfRationalCenters Q =>
    lpfRationalCoefficient (u.1.val + 1) *
      lpfIntervalFrequencyKernel R s L (x - hamiltonianRationalCenter R Q u))

theorem hamiltonian_rational_coefficient_mass (Q : Nat) :
    Finset.univ.sum (fun u : lpfRationalCenters Q =>
      norm (lpfRationalCoefficient (u.1.val + 1))) <= (Q : Real) := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ZMod.card_units_eq_totient]
  have hTerm (q : Fin Q) :
      ((q.val + 1).totient : Real) *
        norm (lpfRationalCoefficient (q.val + 1)) <= 1 := by
    have hPhi : (0 : Real) < ((q.val + 1).totient : Real) := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.succ_pos q.val))
    have h := mul_le_mul_of_nonneg_left
      (norm_lpfRationalCoefficient_le (q.val + 1) (Nat.succ_pos _)) hPhi.le
    calc
      _ <= ((q.val + 1).totient : Real) *
          (1 / ((q.val + 1).totient : Real)) := h
      _ = 1 := by field_simp
  calc
    _ <= Finset.univ.sum (fun _ : Fin Q => (1 : Real)) :=
      Finset.sum_le_sum (fun q _ => hTerm q)
    _ = _ := by simp

theorem hamiltonian_full_reference_transform {R : Nat} [NeZero R]
    (Q s L : Nat) (x : ZMod R) :
    hamiltonianFullRationalReference R Q s L x =
      lpfFiniteTransform (Finset.range L)
        (fun i => ((s + 1 + i : Nat) : ZMod R))
        (fun i => hamiltonianRationalMain R Q ((s + 1 + i : Nat) : ZMod R)) x := by
  unfold hamiltonianFullRationalReference lpfIntervalFrequencyKernel
    lpfFiniteTransform hamiltonianRationalMain
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u hu
  have hArg :
      (x - hamiltonianRationalCenter R Q u) * ((s + 1 + i : Nat) : ZMod R) =
      (-hamiltonianRationalCenter R Q u) * ((s + 1 + i : Nat) : ZMod R) +
        x * ((s + 1 + i : Nat) : ZMod R) := by ring
  rw [hArg, AddChar.map_add_eq_mul]
  ring

theorem hamiltonian_full_reference_inverse {R : Nat} [NeZero R]
    (Q M t : Nat) (ht1 : 1 <= t) (htM : t <= M) (hMR : M < R) :
    lpfCyclicInverse (hamiltonianFullRationalReference R Q 0 M) (t : ZMod R) =
      hamiltonianRationalMain R Q (t : ZMod R) := by
  have hTransform : hamiltonianFullRationalReference R Q 0 M =
      lpfFiniteTransform (Finset.range M)
        (fun i => ((0 + 1 + i : Nat) : ZMod R))
        (fun i => hamiltonianRationalMain R Q ((0 + 1 + i : Nat) : ZMod R)) :=
    funext (hamiltonian_full_reference_transform Q 0 M)
  rw [hTransform, hamiltonian_cyclic_inverse_finite, Finset.sum_eq_single (t - 1)]
  . simp only [Nat.zero_add, Nat.add_comm 1, Nat.sub_add_cancel ht1, ite_true]
  . intro b hb hbt
    have hbM := Finset.mem_range.mp hb
    have hbR : 0 + 1 + b < R := by omega
    have htR : t < R := htM.trans_lt hMR
    have hCast : Not (((0 + 1 + b : Nat) : ZMod R) = (t : ZMod R)) := by
      intro h
      have hVal := congrArg (fun z : ZMod R => z.val) h
      rw [ZMod.val_natCast_of_lt hbR, ZMod.val_natCast_of_lt htR] at hVal
      apply hbt
      omega
    rw [if_neg hCast]
  . intro hNot
    exact False.elim (hNot (Finset.mem_range.mpr (by omega)))

def hamiltonianRationalSumMatrix (n R : Nat) [NeZero R] (Q : Nat) :
    Matrix (Fin n) (Fin n) Complex :=
  fun i j => hamiltonianRationalMain R Q
    (((i.val + 1) + (j.val + 1) : Nat) : ZMod R) / (n : Complex)

theorem hamiltonian_rational_sum_matrix_fourier
    {n R : Nat} [NeZero R] (Q M : Nat)
    (hSize : 2 * n <= M) (hMR : M < R) :
    hamiltonianRationalSumMatrix n R Q =
      HSMul.hSMul (Inv.inv (n : Complex))
        (hamiltonianFourierHankel (hamiltonianFullRationalReference R Q 0 M)
          (fun i : Fin n => ((i.val + 1 : Nat) : ZMod R))
          (fun j : Fin n => ((j.val + 1 : Nat) : ZMod R))) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  have ht1 : 1 <= (i.val + 1) + (j.val + 1) := by omega
  have htM : (i.val + 1) + (j.val + 1) <= M := by omega
  have h := hamiltonian_full_reference_inverse Q M ((i.val + 1) + (j.val + 1))
    ht1 htM hMR
  change hamiltonianRationalMain R Q
      (((i.val + 1) + (j.val + 1) : Nat) : ZMod R) / (n : Complex) =
    Inv.inv (n : Complex) *
      lpfCyclicInverse (hamiltonianFullRationalReference R Q 0 M)
        (((i.val + 1 : Nat) : ZMod R) + ((j.val + 1 : Nat) : ZMod R))
  rw [<- Nat.cast_add, h]
  ring

theorem hamiltonian_full_reference_operator_error
    {n R : Nat} [NeZero n] [NeZero R] (Q M : Nat)
    (hSize : 2 * n <= M) (hMR : M < R) (E : Real) (hE : 0 <= E)
    (hError : forall x, norm (lpfGridIntervalWeight R 0 M x -
      hamiltonianFullRationalReference R Q 0 M x) <= E) :
    norm (hamiltonianMangoldtSumMatrix n - hamiltonianRationalSumMatrix n R Q) <=
      E / (n : Real) := by
  rw [hamiltonian_rational_sum_matrix_fourier Q M hSize hMR]
  exact hamiltonian_mangoldt_operator_error M hSize hMR
    (hamiltonianFullRationalReference R Q 0 M) E hE hError

theorem hamiltonian_interval_kernel_outside {R : Nat} [NeZero R]
    (s L W : Nat) (hW : 1 <= W) (x : ZMod R)
    (hx : Not (Membership.mem (lpfIntervalOffsetGrid R W) x)) :
    norm (lpfIntervalFrequencyKernel R s L x) <= (R : Real) / (2 * (W : Real)) := by
  choose k hk hEq using lpfIntervalFrequency_tail_cover W x hx
  have hK := Finset.mem_Ioc.mp hk
  have hkPos : 0 < k := by omega
  have hHalf : 2 * k <= R := by omega
  have hPositive : norm (lpfIntervalFrequencyKernel R s L (k : ZMod R)) <=
      (R : Real) / (2 * (W : Real)) := by
    have h := norm_lpfGridIntervalKernel_le_inverse_frequency (N := R) s L k hkPos hHalf
    have hSame : lpfIntervalFrequencyKernel R s L (k : ZMod R) =
        lpfGridIntervalKernel R s L (k : Int) := by
      simp only [lpfIntervalFrequencyKernel, lpfGridIntervalKernel, Int.cast_natCast]
    rw [hSame]
    calc
      _ <= (R : Real) / (2 * (k : Real)) := h
      _ <= _ := by gcongr; exact_mod_cast hK.1.le
  cases hEq with
  | inl hEq => rw [hEq]; exact hPositive
  | inr hEq =>
      rw [hEq, lpfIntervalFrequencyKernel_norm_neg]
      exact hPositive

theorem hamiltonian_full_reference_far_bound {R : Nat} [NeZero R]
    (Q s L W : Nat) (hW : 1 <= W) (x : ZMod R)
    (hFar : forall u : lpfRationalCenters Q,
      Not (Membership.mem (lpfIntervalOffsetGrid R W)
        (x - hamiltonianRationalCenter R Q u))) :
    norm (hamiltonianFullRationalReference R Q s L x) <=
      (Q : Real) * ((R : Real) / (2 * (W : Real))) := by
  have hC : 0 <= (R : Real) / (2 * (W : Real)) := by positivity
  unfold hamiltonianFullRationalReference
  calc
    _ <= Finset.univ.sum (fun u : lpfRationalCenters Q =>
        norm (lpfRationalCoefficient (u.1.val + 1) *
          lpfIntervalFrequencyKernel R s L (x - hamiltonianRationalCenter R Q u))) :=
      norm_sum_le _ _
    _ <= Finset.univ.sum (fun u : lpfRationalCenters Q =>
        norm (lpfRationalCoefficient (u.1.val + 1)) *
          ((R : Real) / (2 * (W : Real)))) := by
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (hamiltonian_interval_kernel_outside s L W hW
          (x - hamiltonianRationalCenter R Q u) (hFar u)) (norm_nonneg _)
    _ = (Finset.univ.sum (fun u : lpfRationalCenters Q =>
        norm (lpfRationalCoefficient (u.1.val + 1)))) *
          ((R : Real) / (2 * (W : Real))) := (Finset.sum_mul _ _ _).symm
    _ <= _ := mul_le_mul_of_nonneg_right (hamiltonian_rational_coefficient_mass Q) hC

end PrimeFactorOscillations.LPF
