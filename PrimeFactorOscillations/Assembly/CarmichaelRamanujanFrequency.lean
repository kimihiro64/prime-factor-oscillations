/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelEisensteinPrimeMean

/-!
# General-frequency prime-power Gauss transport

The actual conductor Fourier lift is applied before any estimate. Principal
characters retain their nonunit frequency contribution; it cannot be replaced
by the inverse value of a primitive character. These exact identities are
inputs to the full signed source row, not a complete bound for that row.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelRamanujanFrequency

open scoped Classical
open OAI.ActualEisensteinCubic
open OAI.SevenEighths.ProbePrimePower

/-- Every divisible frequency lifts with its exact ideal norm, for every residue character. -/
theorem prime_power_frequency_lift
    (p : O) (hp : Not (p = 0))
    (chi : MulChar (HasQuotient.Quotient O (Ideal.span {p})) Complex)
    (n : Nat) (k : O) :
    primePowerGauss p hp chi n (p ^ n * k) =
      (Ideal.absNorm (Ideal.span {p ^ n}) : Complex) *
        primeGauss p hp chi k := by
  have h := OAI.CubicEisenstein.conductorFourier_lift
    p (p ^ n) hp (pow_ne_zero n hp) chi k
  simpa only [primePowerGauss, primeGauss, tsum_fintype] using h

/-- Level zero is the actual finite residue-field Gauss sum. -/
theorem prime_power_zero_eq_prime
    (p : O) (hp : Not (p = 0))
    (chi : MulChar (HasQuotient.Quotient O (Ideal.span {p})) Complex)
    (k : O) :
    primePowerGauss p hp chi 0 k = primeGauss p hp chi k := by
  simpa using prime_power_frequency_lift p hp chi 0 k

/-- The principal base Gauss sum retains both the divisible and nondivisible frequencies. -/
theorem principal_prime_gauss_general
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal] (H : O) :
    primeGauss p hp.ne_zero 1 H =
      (if Dvd.dvd p H then (Ideal.absNorm (Ideal.span {p}) : Complex) else 0) - 1 := by
  have hpsi := OAI.PrimitiveTrace.eisTraceModChar_breveE_ne_one
    (Ideal.span {p}) p rfl hp.ne_zero
  change Not (OAI.CubicEisenstein.quotientTrace p hp.ne_zero = 1) at hpsi
  by_cases hdiv : Dvd.dvd p H
  . rw [ite_eq_left hdiv]
    have hH0 : Ideal.Quotient.mk (Ideal.span {p}) H = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
    have hp0 : Ideal.Quotient.mk (Ideal.span {p}) p = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl p))
    calc
      primeGauss p hp.ne_zero 1 H = primeGauss p hp.ne_zero 1 p := by
        simp only [primeGauss, hH0, hp0]
      _ = primePowerGauss p hp.ne_zero 1 0 (p ^ 1) := by
        simpa only [pow_one] using (prime_power_zero_eq_prime p hp.ne_zero 1 p).symm
      _ = _ := by
        simpa using primePowerGauss_at_pow_principal p hp hpsi 0 1
  . rw [ite_eq_right hdiv, zero_sub]
    have hH0 : Not (Ideal.Quotient.mk (Ideal.span {p}) H = 0) := by
      intro hz
      exact hdiv (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
    have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {p}) H) :=
      isUnit_iff_ne_zero.mpr hH0
    have hshift : Not ((OAI.CubicEisenstein.quotientTrace p hp.ne_zero).mulShift
        (Ideal.Quotient.mk (Ideal.span {p}) H) = 1) := by
      intro h
      exact hpsi ((AddChar.mulShift_unit_eq_one_iff
        (OAI.CubicEisenstein.quotientTrace p hp.ne_zero) hunit).mp h)
    simpa only [primeGauss, gaussSum, AddChar.mulShift_apply, tsum_fintype]
      using (gaussSum_one_left hshift)

/-- The full principal prime-power row is the difference of two adjacent divisibility masks. -/
theorem principal_prime_power_ramanujan
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal] (n : Nat) (H : O) :
    primePowerGauss p hp.ne_zero 1 n H =
      (Ideal.absNorm (Ideal.span {p ^ n}) : Complex) *
        ((if Dvd.dvd (p ^ (n + 1)) H then
          (Ideal.absNorm (Ideal.span {p}) : Complex) else 0) -
          (if Dvd.dvd (p ^ n) H then 1 else 0)) := by
  by_cases hdiv : Dvd.dvd (p ^ n) H
  . choose k hk using hdiv
    have hlow : Dvd.dvd (p ^ n) H := Exists.intro k hk
    have hiff : Dvd.dvd p k <-> Dvd.dvd (p ^ (n + 1)) H := by
      constructor
      . intro h
        cases h with
        | intro a ha =>
          refine Exists.intro a ?_
          rw [hk, ha, pow_succ]
          ring
      . intro h
        cases h with
        | intro a ha =>
          refine Exists.intro a ?_
          have hmul : p ^ n * (k - p * a) = 0 := by
            calc
              p ^ n * (k - p * a) = p ^ n * k - p ^ (n + 1) * a := by
                rw [mul_sub, pow_succ]
                ring
              _ = 0 := by rw [<- hk, <- ha, sub_self]
          exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (pow_ne_zero n hp.ne_zero))
    calc
      primePowerGauss p hp.ne_zero 1 n H =
          (Ideal.absNorm (Ideal.span {p ^ n}) : Complex) *
            primeGauss p hp.ne_zero 1 k := by
        rw [hk, prime_power_frequency_lift]
      _ = _ := by
        rw [principal_prime_gauss_general p hp k, ite_eq_left hlow]
        by_cases hpk : Dvd.dvd p k
        . rw [ite_eq_left hpk, ite_eq_left (hiff.mp hpk)]
        . have hhigh : Not (Dvd.dvd (p ^ (n + 1)) H) :=
            fun h => hpk (hiff.mpr h)
          rw [ite_eq_right hpk, ite_eq_right hhigh]
  . have hhigh : Not (Dvd.dvd (p ^ (n + 1)) H) := by
      intro h
      have hd : Dvd.dvd (p ^ n) (p ^ (n + 1)) :=
        Exists.intro p (pow_succ p n)
      exact hdiv (dvd_trans hd h)
    rw [primePowerGauss_zero_off_support p hp.ne_zero 1 n H hdiv,
      ite_eq_right hhigh, ite_eq_right hdiv, sub_self, mul_zero]

/-- Both Ramanujan terms remain coupled through every summable complex frequency weight. -/
theorem ramanujan_weighted_tsum
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal] (n : Nat)
    (f : O -> Complex) (hf : Summable f) :
    tsum (fun H : O => primePowerGauss p hp.ne_zero 1 n H * f H) =
      (Ideal.absNorm (Ideal.span {p ^ n}) : Complex) *
        ((Ideal.absNorm (Ideal.span {p}) : Complex) *
          tsum (Set.indicator (fun H : O => Dvd.dvd (p ^ (n + 1)) H) f) -
          tsum (Set.indicator (fun H : O => Dvd.dvd (p ^ n) H) f)) := by
  have hhigh := hf.indicator (fun H : O => Dvd.dvd (p ^ (n + 1)) H)
  have hlow := hf.indicator (fun H : O => Dvd.dvd (p ^ n) H)
  have hpoint (H : O) :
      primePowerGauss p hp.ne_zero 1 n H * f H =
        (Ideal.absNorm (Ideal.span {p ^ n}) : Complex) *
          ((Ideal.absNorm (Ideal.span {p}) : Complex) *
            Set.indicator (fun a : O => Dvd.dvd (p ^ (n + 1)) a) f H -
            Set.indicator (fun a : O => Dvd.dvd (p ^ n) a) f H) := by
    rw [principal_prime_power_ramanujan p hp n H]
    have hhighval :
        Set.indicator (fun a : O => Dvd.dvd (p ^ (n + 1)) a) f H =
          if Dvd.dvd (p ^ (n + 1)) H then f H else 0 := by
      by_cases hh : Dvd.dvd (p ^ (n + 1)) H
      . rw [Set.indicator_of_mem
          (s := fun a : O => Dvd.dvd (p ^ (n + 1)) a) (a := H) hh f,
          ite_eq_left hh]
      . rw [Set.indicator_of_notMem
          (s := fun a : O => Dvd.dvd (p ^ (n + 1)) a) (a := H) hh f,
          ite_eq_right hh]
    have hlowval :
        Set.indicator (fun a : O => Dvd.dvd (p ^ n) a) f H =
          if Dvd.dvd (p ^ n) H then f H else 0 := by
      by_cases hl : Dvd.dvd (p ^ n) H
      . rw [Set.indicator_of_mem
          (s := fun a : O => Dvd.dvd (p ^ n) a) (a := H) hl f,
          ite_eq_left hl]
      . rw [Set.indicator_of_notMem
          (s := fun a : O => Dvd.dvd (p ^ n) a) (a := H) hl f,
          ite_eq_right hl]
    rw [hhighval, hlowval]
    by_cases hh : Dvd.dvd (p ^ (n + 1)) H
    . by_cases hl : Dvd.dvd (p ^ n) H
      . simp only [ite_eq_left hh, ite_eq_left hl] <;> ring
      . simp only [ite_eq_left hh, ite_eq_right hl] <;> ring
    . by_cases hl : Dvd.dvd (p ^ n) H
      . simp only [ite_eq_right hh, ite_eq_left hl] <;> ring
      . simp only [ite_eq_right hh, ite_eq_right hl] <;> ring
  simp_rw [hpoint]
  rw [tsum_mul_left, Summable.tsum_sub
    (hhigh.mul_left (Ideal.absNorm (Ideal.span {p}) : Complex)) hlow,
    tsum_mul_left]

end PrimeFactorOscillations.CarmichaelRamanujanFrequency
