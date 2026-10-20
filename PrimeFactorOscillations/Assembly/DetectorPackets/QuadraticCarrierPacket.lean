/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import PrimeFactorOscillations.Assembly.DetectorPackets.CarrierIndexedAdmission

/-!
# QuadraticCarrierPacket

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# An actual quadratic character packet for the uniform carrier

The quadratic character is the zero-extended integer Jacobi symbol.
Square rows give the full unmodified cofactor sum when coprimality holds.
The probability observations are constructed, not assumed. No saving for
the signed cross packet is asserted.
-/


noncomputable section
namespace PrimeFactorOscillations.QuadraticCarrierPacket

def kernel (u n : Nat) : Complex := (jacobiSym (u : Int) n : Complex)

theorem kernel_norm_le_one (u n : Nat) : norm (kernel u n) <= 1 := by
  rcases jacobiSym.trichotomy (u : Int) n with h0 | h1 | hm
  . simp [kernel, h0]
  . simp [kernel, h1]
  . simp [kernel, hm]

theorem kernel_square (r n : Nat) (h : (r : Int).gcd n = 1) :
    kernel (r ^ 2) n = 1 := by
  have hJ : jacobiSym ((r ^ 2 : Nat) : Int) n = 1 := by
    simpa only [Nat.cast_pow] using jacobiSym.sq_one' h
  simp only [kernel, hJ, Int.cast_one]

theorem square_row_amplitude (s : Finset Nat) (a : Nat -> Complex)
    (r : Nat) (h : forall n, Membership.mem s n -> (r : Int).gcd n = 1) :
    s.sum (fun n => a n * kernel (r ^ 2) n) = s.sum a := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [kernel_square r n (h n hn), mul_one]

def cofactor (eta W : Nat -> Complex) (n : Nat) : Complex :=
  (ArithmeticFunction.moebius n : Complex) * eta n * W n

theorem cofactor_norm_le_one (eta W : Nat -> Complex)
    (heta : forall n, norm (eta n) <= 1)
    (hW : forall n, norm (W n) <= 1) (n : Nat) :
    norm (cofactor eta W n) <= 1 := by
  have hmu : norm (ArithmeticFunction.moebius n : Complex) <= 1 := by
    rcases ArithmeticFunction.moebius_eq_or n with h0 | h1 | hm
    . simp [h0]
    . simp [h1]
    . simp [hm]
  unfold cofactor
  rw [norm_mul, norm_mul]
  calc
    _ <= (1 : Real) * 1 * 1 :=
      mul_le_mul
        (mul_le_mul hmu (heta n) (norm_nonneg _) zero_le_one)
        (hW n) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem cofactor_norm_le_nat (eta W : Nat -> Complex)
    (heta : forall n, norm (eta n) <= 1)
    (hW : forall n, norm (W n) <= 1) (n : Nat) :
    norm (cofactor eta W n) <= (n : Real) := by
  by_cases hn : n = 0
  . subst n
    simp [cofactor]
  . exact (cofactor_norm_le_one eta W heta hW n).trans
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

theorem cofactor_zero_of_not_squarefree (eta W : Nat -> Complex) (n : Nat)
    (hn : Not (Squarefree n)) : cofactor eta W n = 0 := by
  simp only [cofactor, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn,
    Int.cast_zero, zero_mul]

theorem exists_uniform_quadratic_probability_packet :
    exists n0 : Nat, exists C : Real, 100 <= n0 /\ 0 < C /\
      forall (eta W : Nat -> Complex)
        (heta : forall n, norm (eta n) <= 1)
        (hW : forall n, norm (W n) <= 1)
        (rows s : Finset Nat) (P : Nat -> Complex)
        (D Y Crows Ccols Camp : Real),
      0 < D -> 0 <= Y -> 0 <= Crows -> 0 <= Ccols -> 0 <= Camp ->
      (forall n, Membership.mem s n -> n0 <= n) ->
      (forall n, Membership.mem s n -> D <= (n : Real)) ->
      (s.card : Real) <= Ccols * D ->
      (rows.card : Real) <= Crows * D ^ 4 ->
      (forall r, Membership.mem rows r -> norm (P r) <= Camp * Y) ->
      exists f : Nat -> Complex,
        (forall n, Membership.mem s n ->
          exists O : UniformCarrier.CoefficientObservation 4 n (cofactor eta W n)
            (cofactor_norm_le_nat eta W heta hW n), f n = O.value) /\
        (forall n, Membership.mem s n ->
          norm (f n - cofactor eta W n) <= C / D ^ 3) /\
        UniformCarrier.AmplifiedMoment.energy rows s f kernel P <=
          2 * UniformCarrier.AmplifiedMoment.energy rows s (cofactor eta W) kernel P +
            2 * Crows * Ccols ^ 2 * Camp ^ 2 * C ^ 2 * Y ^ 2 := by
  choose n0 C hn0 hC hData using
    UniformCarrier.IndexedAdmission.exists_uniform_indexed_amplified_observations
  refine Exists.intro n0 (Exists.intro C (And.intro hn0 (And.intro hC ?_)))
  intro eta W heta hW rows s P D Y Crows Ccols Camp
    hD hY hRows hCols hAmp hLarge hLower hS hT hP
  have hKernel : forall r, Membership.mem rows r ->
      forall n, Membership.mem s n -> norm (kernel r n) <= 1 :=
    fun r _ n _ => kernel_norm_le_one r n
  exact hData Nat Nat rows s id (cofactor eta W)
    (cofactor_norm_le_nat eta W heta hW) kernel P D Y Crows Ccols Camp
    hD hY hRows hCols hAmp hLarge hLower hS hT hKernel hP

end PrimeFactorOscillations.QuadraticCarrierPacket

