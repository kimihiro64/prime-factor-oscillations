/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianHankelFourierBound
import PrimeFactorOscillations.Helpers.LPFGridPhase

/-! # Exact Fourier transfer for the actual integer prime-sum operator

The sampled variables are the two vertices i+1 and j+1. The Mangoldt
prefix cutoff M covers every output i+j+2, and the independent auxiliary
period R exceeds M. No prime powers or diagonal terms are removed here.
A bound for the full symbol difference gives the actual normalized
operator bound with factor 1/n and no auxiliary-period cost.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_cyclic_inverse_finite {Iota : Type*} {R : Nat} [NeZero R]
    (U : Finset Iota) (freq : Iota -> ZMod R) (w : Iota -> Complex)
    (t : ZMod R) :
    lpfCyclicInverse (lpfFiniteTransform U freq w) t =
      U.sum (fun i => if freq i = t then w i else 0) := by
  have h := lpfCyclicInverse_finite_product U ({() } : Finset Unit)
    freq (fun _ => (0 : ZMod R)) w (fun _ => (1 : Complex)) t
  unfold lpfFiniteTransform
  simpa [lpfFiniteTransform] using h

theorem hamiltonian_prime_prefix_inverse {R : Nat} [NeZero R]
    (M t : Nat) (ht1 : 1 <= t) (htM : t <= M) (hMR : M < R) :
    lpfCyclicInverse (fun x => lpfGridIntervalWeight R 0 M x) (t : ZMod R) =
      (ArithmeticFunction.vonMangoldt t : Complex) := by
  have hTransform : (fun x => lpfGridIntervalWeight R 0 M x) =
      lpfFiniteTransform (lpfGridIntervalInputs 0 M)
        (fun n => (n : ZMod R))
        (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) :=
    funext (fun x => lpfGridIntervalWeight_eq_transform 0 M x)
  rw [hTransform, hamiltonian_cyclic_inverse_finite]
  have hMem : Membership.mem (lpfGridIntervalInputs 0 M) t := by
    unfold lpfGridIntervalInputs
    apply Finset.mem_image.mpr
    refine Exists.intro (t - 1) (And.intro ?_ ?_)
    . exact Finset.mem_range.mpr (by omega)
    . omega
  rw [Finset.sum_eq_single t]
  . simp
  . intro b hb hbt
    have hbM := lpfGridIntervalInputs_le 0 M b hb
    simp only [Nat.zero_add] at hbM
    have hbR : b < R := hbM.trans_lt hMR
    have htR : t < R := htM.trans_lt hMR
    have hCast : Not ((b : ZMod R) = (t : ZMod R)) := by
      intro h
      apply hbt
      have hVal := congrArg (fun z : ZMod R => z.val) h
      simpa only [ZMod.val_natCast_of_lt hbR, ZMod.val_natCast_of_lt htR] using hVal
    rw [if_neg hCast]
  . intro hNot
    exact False.elim (hNot hMem)

def hamiltonianMangoldtSumMatrix (n : Nat) : Matrix (Fin n) (Fin n) Complex :=
  fun i j => (ArithmeticFunction.vonMangoldt ((i.val + 1) + (j.val + 1)) : Complex) /
    (n : Complex)

theorem hamiltonian_prime_input_injective {n R : Nat} (hnR : n < R) :
    Function.Injective (fun i : Fin n => ((i.val + 1 : Nat) : ZMod R)) := by
  intro i j h
  apply Fin.ext
  have hi : i.val + 1 < R := by have hI := i.isLt; omega
  have hj : j.val + 1 < R := by have hJ := j.isLt; omega
  have hVal := congrArg (fun z : ZMod R => z.val) h
  rw [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at hVal
  omega

theorem hamiltonian_mangoldt_sum_matrix_fourier
    {n R : Nat} [NeZero R] (M : Nat) (hSize : 2 * n <= M) (hMR : M < R) :
    hamiltonianMangoldtSumMatrix n =
      HSMul.hSMul (Inv.inv (n : Complex))
        (hamiltonianFourierHankel (fun x => lpfGridIntervalWeight R 0 M x)
          (fun i : Fin n => ((i.val + 1 : Nat) : ZMod R))
          (fun j : Fin n => ((j.val + 1 : Nat) : ZMod R))) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  have ht1 : 1 <= (i.val + 1) + (j.val + 1) := by omega
  have htM : (i.val + 1) + (j.val + 1) <= M := by omega
  have h := hamiltonian_prime_prefix_inverse M ((i.val + 1) + (j.val + 1))
    ht1 htM hMR
  change (ArithmeticFunction.vonMangoldt ((i.val + 1) + (j.val + 1)) : Complex) /
    (n : Complex) = Inv.inv (n : Complex) *
      lpfCyclicInverse (fun x => lpfGridIntervalWeight R 0 M x)
        (((i.val + 1 : Nat) : ZMod R) + ((j.val + 1 : Nat) : ZMod R))
  rw [<- Nat.cast_add, h]
  ring

theorem hamiltonian_mangoldt_operator_error
    {n R : Nat} [NeZero n] [NeZero R]
    (M : Nat) (hSize : 2 * n <= M) (hMR : M < R)
    (G : ZMod R -> Complex) (E : Real) (hE : 0 <= E)
    (hError : forall x, norm (lpfGridIntervalWeight R 0 M x - G x) <= E) :
    norm (hamiltonianMangoldtSumMatrix n -
      HSMul.hSMul (Inv.inv (n : Complex))
        (hamiltonianFourierHankel G
          (fun i : Fin n => ((i.val + 1 : Nat) : ZMod R))
          (fun j : Fin n => ((j.val + 1 : Nat) : ZMod R)))) <= E / (n : Real) := by
  have hnR : n < R := by omega
  have hN : (0 : Real) < (n : Real) := by exact_mod_cast (NeZero.pos n)
  have hNorm := hamiltonian_fourier_hankel_difference_bound
    (fun x => lpfGridIntervalWeight R 0 M x) G
    (fun i : Fin n => ((i.val + 1 : Nat) : ZMod R))
    (fun j : Fin n => ((j.val + 1 : Nat) : ZMod R))
    (hamiltonian_prime_input_injective hnR)
    (hamiltonian_prime_input_injective hnR) E hE hError
  rw [hamiltonian_mangoldt_sum_matrix_fourier M hSize hMR,
    <- smul_sub, norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ <= Inv.inv (n : Real) * E :=
      mul_le_mul_of_nonneg_left hNorm (by positivity)
    _ = E / (n : Real) := by ring

end PrimeFactorOscillations.LPF
