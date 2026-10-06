/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import PrimeFactorOscillations.Helpers.LcmDivisorArithmetic

/-!
# Real logarithm of the zeta Euler product

This supplies the convergent prime-log identity needed by the actual
generalized-divisor comparison.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations

theorem lcmPrimeEulerFactor_pos (k : Real) (hk : 0 < k) (p : Nat.Primes) :
    0 < 1 - (p : Real) ^ (-k) := by
  have hp : (1 : Real) < p := by exact_mod_cast p.property.one_lt
  have hPower := Real.rpow_lt_rpow_of_exponent_lt hp (show -k < 0 by linarith)
  simp only [Real.rpow_zero] at hPower
  linarith

theorem lcmPrimeLog_complex_cast (k : Real) (hk : 0 < k) (p : Nat.Primes) :
    ((-Real.log (1 - (p : Real) ^ (-k)) : Real) : Complex) =
      -Complex.log (1 - (p : Complex) ^ (-(k : Complex))) := by
  have hPow : (((p : Real) ^ (-k) : Real) : Complex) =
      (p : Complex) ^ (-(k : Complex)) := by
    rw [Complex.ofReal_cpow (by exact_mod_cast p.property.pos.le)]
    simp only [Complex.ofReal_neg, Complex.ofReal_natCast]
  rw [Complex.ofReal_neg, Complex.ofReal_log (lcmPrimeEulerFactor_pos k hk p).le,
    Complex.ofReal_sub, Complex.ofReal_one, hPow]

theorem lcm_logZeta_eq_primeSum (k : Real) (hk : 1 < k) :
    Real.log (riemannZeta (k : Complex)).re =
      tsum (fun p : Nat.Primes => -Real.log (1 - (p : Real) ^ (-k))) := by
  have hComplex := riemannZeta_eulerProduct_exp_log (s := (k : Complex))
    (by simpa using hk)
  have hSum :
      tsum (fun p : Nat.Primes => -Complex.log (1 - (p : Complex) ^ (-(k : Complex)))) =
        ((tsum (fun p : Nat.Primes => -Real.log (1 - (p : Real) ^ (-k))) : Real) : Complex) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr (fun p => (lcmPrimeLog_complex_cast k (by linarith) p).symm)
  rw [<- hComplex, hSum, Complex.exp_ofReal_re, Real.log_exp]

theorem lcmPrimeLog_summable (k : Real) (hk : 1 < k) :
    Summable (fun p : Nat.Primes => -Real.log (1 - (p : Real) ^ (-k))) := by
  have hs : 1 < (k : Complex).re := by simpa using hk
  have hc : Summable (fun p : Nat.Primes =>
      -Complex.log (1 - (p : Complex) ^ (-(k : Complex)))) := by
    have hi : Function.Injective (fun p : Nat.Primes => p.val) := by
      intro p q hpq
      exact Subtype.ext hpq
    have h := (summable_riemannZetaSummand hs).of_norm.clog_one_sub.neg.comp_injective hi
    simpa only [Function.comp_def, riemannZetaSummandHom,
      MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk] using h
  have hr := hc.hasSum.map Complex.reAddGroupHom Complex.continuous_re
  apply hr.summable.congr
  intro p
  exact congrArg Complex.re (lcmPrimeLog_complex_cast k (by linarith) p).symm

def lcmFiniteZetaTail (k : Real) (S : Finset Nat.Primes) : Real :=
  tsum (fun p : {p : Nat.Primes // Not (Membership.mem S p)} =>
    -Real.log (1 - ((p.val : Nat.Primes) : Real) ^ (-k)))

theorem lcm_logZeta_eq_prefix_add_tail (k : Real) (hk : 1 < k)
    (S : Finset Nat.Primes) :
    Real.log (riemannZeta (k : Complex)).re =
      S.sum (fun p => -Real.log (1 - (p : Real) ^ (-k))) +
        lcmFiniteZetaTail k S := by
  rw [lcm_logZeta_eq_primeSum k hk]
  exact ((lcmPrimeLog_summable k hk).sum_add_tsum_subtype_compl S).symm

theorem lcmPrimeLog_nonneg (k : Real) (hk : 0 < k) (p : Nat.Primes) :
    0 <= -Real.log (1 - (p : Real) ^ (-k)) := by
  apply neg_nonneg.mpr
  apply Real.log_nonpos (lcmPrimeEulerFactor_pos k hk p).le
  have hPow : 0 <= (p : Real) ^ (-k) := Real.rpow_nonneg (by positivity) _
  linarith

theorem lcmFiniteZetaTail_nonneg (k : Real) (hk : 0 < k) (S : Finset Nat.Primes) :
    0 <= lcmFiniteZetaTail k S :=
  tsum_nonneg (fun p => lcmPrimeLog_nonneg k hk p.val)

theorem lcmPrimeLog_antitone (k K : Real) (hk : 0 < k) (hLe : k <= K)
    (p : Nat.Primes) :
    -Real.log (1 - (p : Real) ^ (-K)) <= -Real.log (1 - (p : Real) ^ (-k)) := by
  have hPow := Real.rpow_le_rpow_of_exponent_le
    (show (1 : Real) <= p by exact_mod_cast p.property.one_lt.le)
    (show -K <= -k by linarith)
  exact neg_le_neg (Real.log_le_log (lcmPrimeEulerFactor_pos k hk p) (by linarith))

theorem lcmFiniteZetaTail_antitone (k K : Real) (hk : 1 < k) (hLe : k <= K)
    (S : Finset Nat.Primes) :
    lcmFiniteZetaTail K S <= lcmFiniteZetaTail k S := by
  have hK : 1 < K := hk.trans_le hLe
  exact Summable.tsum_le_tsum (fun p => lcmPrimeLog_antitone k K (by linarith) hLe p.val)
    ((lcmPrimeLog_summable K hK).subtype _)
    ((lcmPrimeLog_summable k hk).subtype _)

end PrimeFactorOscillations
