/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Data.Nat.Prime.Nth
import PrimeFactorOscillations.Helpers.QuadraticProfileRH

/-!
# RH readout after a bounded reindexing of prime values

Moving a prime value by at most H changes its reciprocal predecessor odds
by at most H(H+1) times the square of the original odds. The existing
unconditional quadratic-law comparison therefore applies to every such
fixed reindexing, including the distance-six swaps used by short quadruplets.
No recurrence or existence of a constellation is asserted here.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

/-- An explicit quadratic perturbation bound for reciprocals of displaced positive denominators. -/
theorem reciprocal_displacement_quadratic_bound (x y H : Real)
    (hx : 1 <= x) (hy : 1 <= y) (hH : 0 <= H) (hxy : abs (x - y) <= H) :
    abs (1 / y - 1 / x) <= H * (H + 1) * (1 / x) ^ 2 := by
  have hxpos : 0 < x := by linarith only [hx]
  have hypos : 0 < y := by linarith only [hy]
  have hrel : x <= (H + 1) * y := by
    have hdiff : x - y <= H := (le_abs_self (x - y)).trans hxy
    nlinarith only [hdiff, hy, hH]
  have hid : 1 / y - 1 / x = (x - y) / (x * y) := by
    field_simp
  have habs : abs (1 / y - 1 / x) * (x * y) = abs (x - y) := by
    rw [hid, abs_div, abs_of_pos (mul_pos hxpos hypos)]
    field_simp
  have hprod : abs (1 / y - 1 / x) * (x * y) <= H := by
    rw [habs]
    exact hxy
  have hscale := mul_le_mul_of_nonneg_right hprod (by linarith : 0 <= H + 1)
  have hcomp := mul_le_mul_of_nonneg_left hrel
    (mul_nonneg (abs_nonneg (1 / y - 1 / x)) hxpos.le)
  have hfinal : abs (1 / y - 1 / x) * x ^ 2 <= H * (H + 1) := by
    nlinarith only [hscale, hcomp]
  have hcancel : (H * (H + 1) * (1 / x) ^ 2) * x ^ 2 = H * (H + 1) := by
    field_simp
  by_contra hn
  have hgt := lt_of_not_ge hn
  have hbad := mul_lt_mul_of_pos_right hgt (sq_pos_of_pos hxpos)
  rw [hcancel] at hbad
  exact (not_lt_of_ge hfinal) hbad

/-- Prime-value displacement supplies the exact quadratic-law hypothesis at every prime, including two. -/
theorem primeProfileWeight_displacement_bound (p q : Nat) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (H : Real) (hH : 0 <= H)
    (hdispl : abs ((q : Real) - (p : Real)) <= H) :
    abs (primeProfileWeight q - primeProfileWeight p) <=
      H * (H + 1) * (primeProfileWeight p) ^ 2 := by
  have hp1 : 1 <= p - 1 := by have h := hp.two_le; omega
  have hq1 : 1 <= q - 1 := by have h := hq.two_le; omega
  have hx : (1 : Real) <= ((p - 1 : Nat) : Real) := by exact_mod_cast hp1
  have hy : (1 : Real) <= ((q - 1 : Nat) : Real) := by exact_mod_cast hq1
  have hpc : ((p - 1 : Nat) : Real) = (p : Real) - 1 := by
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  have hqc : ((q - 1 : Nat) : Real) = (q : Real) - 1 := by
    rw [Nat.cast_sub hq.one_le, Nat.cast_one]
  have hd : abs (((p - 1 : Nat) : Real) - ((q - 1 : Nat) : Real)) <= H := by
    rw [hpc, hqc]
    have heq : (p : Real) - 1 - ((q : Real) - 1) = -((q : Real) - (p : Real)) := by ring
    rw [heq, abs_neg]
    exact hdispl
  exact reciprocal_displacement_quadratic_bound _ _ H hx hy hH hd

/-- The actual local odds obtained from a bounded map of prime values form a qualifying law. -/
def boundedPrimeReindexingLaw (f : Nat.Primes -> Nat)
    (hf : forall p, Nat.Prime (f p)) (H : Real) (hH : 0 <= H)
    (hdispl : forall p : Nat.Primes, abs ((f p : Real) - (p : Nat)) <= H) :
    QuadraticPrimeLaw where
  weight p := primeProfileWeight (f p)
  nu := 1
  error := H * (H + 1)
  nu_pos := by norm_num
  error_nonneg := mul_nonneg hH (by linarith)
  weight_nonneg p := by unfold primeProfileWeight; positivity
  quadratic_error p := by
    simpa only [one_mul] using
      primeProfileWeight_displacement_bound (p : Nat) (f p) p.property (hf p) H hH (hdispl p)

/-- A fixed bounded reindexing retains the unconditional moving-coefficient RH equivalence. -/
theorem bounded_prime_reindexing_rh_iff (f : Nat.Primes -> Nat)
    (hf : forall p, Nat.Prime (f p)) (H : Real) (hH : 0 <= H)
    (hdispl : forall p : Nat.Primes, abs ((f p : Real) - (p : Nat)) <= H)
    (alpha : Real) (ha : 0 < alpha) :
    let law := boundedPrimeReindexingLaw f hf H hH hdispl
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * law.referenceClock N)
      law.densityRatio N r < law.referenceRatio r (law.referenceClock N)) Filter.atTop := by
  exact QuadraticPrimeLaw.riemannHypothesis_iff_eventually_densityRatio_lt_reference
    (boundedPrimeReindexingLaw f hf H hH hdispl) alpha ha

/-- Convert a coordinate permutation to its actual prime value at a prime-labelled coordinate. -/
def permutedPrimeValue (e : Equiv.Perm Nat) (p : Nat.Primes) : Nat :=
  PrimeFactorUnimodality.primeAt (e (Nat.count Nat.Prime (p : Nat)))

theorem permutedPrimeValue_prime (e : Equiv.Perm Nat) (p : Nat.Primes) :
    Nat.Prime (permutedPrimeValue e p) :=
  PrimeFactorUnimodality.prime_primeAt _

/-- The prime label is exactly recovered before applying any coordinate permutation. -/
theorem primeAt_count_prime (p : Nat.Primes) :
    PrimeFactorUnimodality.primeAt (Nat.count Nat.Prime (p : Nat)) = (p : Nat) := by
  exact Nat.nth_count p.property

/-- A uniform prime-value displacement on the coordinate enumeration verifies every law coordinate. -/
theorem permutedPrimeValue_displacement (e : Equiv.Perm Nat) (H : Real)
    (he : forall i : Nat,
      abs ((PrimeFactorUnimodality.primeAt (e i) : Real) -
        (PrimeFactorUnimodality.primeAt i : Real)) <= H) :
    forall p : Nat.Primes, abs ((permutedPrimeValue e p : Real) - (p : Nat)) <= H := by
  intro p
  have h := he (Nat.count Nat.Prime (p : Nat))
  rw [primeAt_count_prime p] at h
  exact h

end PrimeFactorOscillations
