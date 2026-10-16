/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.UniformCarrierComplex

/-!
# Uniform Carrier Observation

Actual localized carrier observations and their single-prime scaled coefficient estimates.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.UniformCarrier

structure Observation (alpha : Real) (P : Nat) (g : Nat.Primes -> Complex)
    (hg : forall p, norm (g p) <= 1) where
  up : Real
  um : Real
  vp : Real
  vm : Real
  re_pos : (positiveLaw (fun p => (g p).re) (real_bounds g hg)).densityRatio (2 * P)
    (carrierRank alpha P) = carrierReference alpha P up
  re_neg : (negativeLaw (fun p => (g p).re) (real_bounds g hg)).densityRatio (2 * P)
    (carrierRank alpha P) = carrierReference alpha P um
  im_pos : (positiveLaw (fun p => (g p).im) (imag_bounds g hg)).densityRatio (2 * P)
    (carrierRank alpha P) = carrierReference alpha P vp
  im_neg : (negativeLaw (fun p => (g p).im) (imag_bounds g hg)).densityRatio (2 * P)
    (carrierRank alpha P) = carrierReference alpha P vm
  up_band : abs (up - baseline.arithmeticClock (2 * P)) <= 1 / 2
  um_band : abs (um - baseline.arithmeticClock (2 * P)) <= 1 / 2
  vp_band : abs (vp - baseline.arithmeticClock (2 * P)) <= 1 / 2
  vm_band : abs (vm - baseline.arithmeticClock (2 * P)) <= 1 / 2

def Observation.value {alpha : Real} {P : Nat} {g : Nat.Primes -> Complex}
    {hg : forall p, norm (g p) <= 1} (O : Observation alpha P g hg) : Complex :=
  Complex.mk (O.up - O.um) (O.vp - O.vm)

theorem exists_observation (alpha : Real) (ha : 0 < alpha) :
    exists P0 : Nat, exists C : Real, 1 <= P0 /\ 0 < C /\
      forall P : Nat, P0 <= P ->
      forall T : Finset Nat.Primes, T <= primeProfilePrefixSet (2 * P) ->
      (forall p, Membership.mem T p -> P < (p : Nat)) -> T.card <= P / 100 ->
      forall g : Nat.Primes -> Complex, forall hg : (forall p, norm (g p) <= 1),
      (forall p, Not (Membership.mem T p) -> g p = 0) ->
      exists O : Observation alpha P g hg,
        norm (O.value - weightedSum T g) <= C * (T.card : Real) / (P : Real) ^ 2 := by
  choose P0 C hP0 hC hCarrier using exists_complex_carrier alpha ha
  refine Exists.intro P0 (Exists.intro C (And.intro hP0 (And.intro hC ?_)))
  intro P hP T hT hprime hcard g hg hSupport
  choose UP UM VP VM hRP hRM hIP hIM hE using hCarrier P hP T hT hprime hcard g hg hSupport
  exact Exists.intro (@Observation.mk alpha P g hg UP UM VP VM hRP hRM hIP hIM
    hE.2.1 hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2) hE.1

def singletonMark (P : Nat) (p : Nat.Primes) (z : Complex) (q : Nat.Primes) : Complex :=
  if q = p then Complex.ofReal (((p : Nat) : Real) / (2 * (P : Real))) * z else 0

theorem singletonMark_bound (P : Nat) (p : Nat.Primes)
    (hp : (p : Nat) <= 2 * P) (z : Complex) (hz : norm z <= 1) :
    forall q, norm (singletonMark P p z q) <= 1 := by
  have hP : 1 <= P := by
    have hTwo := p.property.two_le
    omega
  have hPpos : (0 : Real) < P := by exact_mod_cast Nat.zero_lt_one.trans_le hP
  have hpR : ((p : Nat) : Real) <= 2 * (P : Real) := by exact_mod_cast hp
  have hl0 : 0 <= ((p : Nat) : Real) / (2 * (P : Real)) := by positivity
  have hl1 : ((p : Nat) : Real) / (2 * (P : Real)) <= 1 :=
    (div_le_one (mul_pos (by norm_num) hPpos)).mpr hpR
  intro q
  by_cases he : q = p
  . simp only [singletonMark, if_pos he, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hl0]
    calc
      _ <= (1 : Real) * 1 := mul_le_mul hl1 hz (norm_nonneg _) zero_le_one
      _ = 1 := by norm_num
  . simp only [singletonMark, if_neg he, norm_zero, zero_le_one]

theorem singletonMark_weightedSum (P : Nat) (hP : 1 <= P) (p : Nat.Primes) (z : Complex) :
    weightedSum {p} (singletonMark P p z) = z / ((2 * (P : Real) : Real) : Complex) := by
  rw [weightedSum_eq, Finset.sum_singleton]
  simp only [singletonMark, if_pos rfl]
  have hpC : Not (((p : Nat) : Complex) = 0) := by exact_mod_cast p.property.ne_zero
  have hPC : Not ((P : Complex) = 0) := by exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_one.trans_le hP)
  push_cast
  field_simp [hpC, hPC]

theorem exists_singleton_observation (alpha : Real) (ha : 0 < alpha) :
    exists P0 : Nat, exists C : Real, 100 <= P0 /\ 0 < C /\
      forall P : Nat, P0 <= P -> forall p : Nat.Primes,
      P < (p : Nat) -> forall hp : ((p : Nat) <= 2 * P),
      forall z : Complex, forall hz : (norm z <= 1),
      exists O : Observation alpha P (singletonMark P p z)
          (singletonMark_bound P p hp z hz),
        norm (((2 * (P : Real) : Real) : Complex) * O.value - z) <= C / (P : Real) := by
  choose Pbase C hPbase hC hObs using exists_observation alpha ha
  let P0 := max 100 Pbase
  refine Exists.intro P0 (Exists.intro (2 * C)
    (And.intro (le_max_left _ _) (And.intro (by positivity) ?_)))
  intro P hP p hpLo hpHi z hz
  have hP1 : 1 <= P := by have h100 := (le_max_left _ _).trans hP; omega
  have hPbase' : Pbase <= P := (le_max_right _ _).trans hP
  have hT : ({p} : Finset Nat.Primes) <= primeProfilePrefixSet (2 * P) := by
    intro q hq
    have heq := Finset.mem_singleton.mp hq
    subst q
    exact (mem_primeProfilePrefixSet p (2 * P)).mpr hpHi
  have hPrime : forall q, Membership.mem ({p} : Finset Nat.Primes) q -> P < (q : Nat) := by
    intro q hq
    simpa only [Finset.mem_singleton.mp hq] using hpLo
  have hCard : ({p} : Finset Nat.Primes).card <= P / 100 := by
    have h100 := (le_max_left _ _).trans hP
    simp only [Finset.card_singleton]
    omega
  have hSupport : forall q, Not (Membership.mem ({p} : Finset Nat.Primes) q) ->
      singletonMark P p z q = 0 := by
    intro q hq
    have he : Not (q = p) := by simpa only [Finset.mem_singleton] using hq
    simp only [singletonMark, if_neg he]
  choose O hO using hObs P hPbase' {p} hT hPrime hCard (singletonMark P p z)
    (singletonMark_bound P p hpHi z hz) hSupport
  have hE : norm (O.value - z / (((2 * (P : Real) : Real) : Complex))) <= C / (P : Real) ^ 2 := by
    simpa only [singletonMark_weightedSum P hP1 p z, Finset.card_singleton, Nat.cast_one, mul_one] using hO
  have hPpos : (0 : Real) < P := by exact_mod_cast Nat.zero_lt_one.trans_le hP1
  have hScale : 0 < 2 * (P : Real) := mul_pos (by norm_num) hPpos
  have hScaleC : Not ((((2 * (P : Real) : Real) : Complex)) = 0) := by exact_mod_cast hScale.ne'
  have hid : (((2 * (P : Real) : Real) : Complex)) * O.value - z =
      (((2 * (P : Real) : Real) : Complex)) * (O.value - z / (((2 * (P : Real) : Real) : Complex))) := by
    field_simp [hScaleC]
  refine Exists.intro O ?_
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hScale]
  calc
    _ <= (2 * (P : Real)) * (C / (P : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hE hScale.le
    _ = (2 * C) / (P : Real) := by field_simp <;> ring

end PrimeFactorOscillations.UniformCarrier
