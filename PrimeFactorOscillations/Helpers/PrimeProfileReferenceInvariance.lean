/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import PrimeFactorOscillations.Helpers.PrimeProfileBoundedReindexing
import PrimeFactorOscillations.Helpers.QuadraticProfilePositive

/-!
# Exact reference invariance under involutive prime reindexing

The difference of two convergent logarithmic profiles is a summable signed
coboundary. Reindexing by its involution negates the full sum, so the sum
vanishes. The entire profiles and all reference coefficients then coincide.
No divergent positive logarithmic series is rearranged.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Filter
open scoped Topology

namespace PrimeFactorOscillations

namespace QuadraticPrimeLaw

/-- Pair the complete summable logarithmic difference under the same involution. -/
theorem logProfile_eq_of_involutive_weights (a b : QuadraticPrimeLaw)
    (e : Equiv.Perm Nat.Primes) (he : Function.Involutive e)
    (hnu : a.nu = b.nu) (hw : forall p, a.weight p = b.weight (e p))
    (t : Real) (ht : 0 <= t) :
    a.logProfile t = b.logProfile t := by
  let g : Nat.Primes -> Real := fun p => a.logFactor t p - b.logFactor t p
  have ha := a.summable_logFactor t ht
  have hb := b.summable_logFactor t ht
  have hg : Summable g := ha.sub hb
  have hpair : forall p, g (e p) = -g p := by
    intro p
    dsimp only [g, logFactor]
    rw [hw (e p), hw p, he p, hnu]
    ring
  have hcomp : (fun p => g (e p)) = fun p => -g p := funext hpair
  have hsum := e.tsum_eq g
  rw [hcomp, tsum_neg] at hsum
  have hzero : tsum g = 0 := by linarith only [hsum]
  have hdiff : tsum g = a.logProfile t - b.logProfile t := by
    exact ha.tsum_sub hb
  linarith only [hzero, hdiff]

/-- Equality on nonnegative real probes identifies the complete entire reference profile. -/
theorem complexProfile_eq_of_involutive_weights (a b : QuadraticPrimeLaw)
    (e : Equiv.Perm Nat.Primes) (he : Function.Involutive e)
    (hnu : a.nu = b.nu) (hw : forall p, a.weight p = b.weight (e p)) :
    a.complexProfile = b.complexProfile := by
  have hreal : forall t : Real, 0 <= t ->
      a.complexProfile (t : Complex) = b.complexProfile (t : Complex) := by
    intro t ht
    rw [a.complexProfile_ofReal_eq_exp t ht, b.complexProfile_ofReal_eq_exp t ht,
      logProfile_eq_of_involutive_weights a b e he hnu hw t ht]
  have ha : AnalyticOnNhd Complex a.complexProfile Set.univ := by
    intro z _
    exact a.differentiable_complexProfile.analyticAt z
  have hb : AnalyticOnNhd Complex b.complexProfile Set.univ := by
    intro z _
    exact b.differentiable_complexProfile.analyticAt z
  have hclosure : Membership.mem
      (closure ({z : Complex | a.complexProfile z = b.complexProfile z} \
        ({0} : Set Complex))) (0 : Complex) := by
    apply Metric.mem_closure_iff.mpr
    intro eps heps
    let t : Real := eps / 2
    have ht : 0 < t := by dsimp only [t]; linarith only [heps]
    refine Exists.intro (t : Complex) (And.intro ?_ ?_)
    . constructor
      . exact hreal t ht.le
      . intro hz
        have hzero : (t : Complex) = 0 := Set.mem_singleton_iff.mp hz
        have htzero : t = 0 := Complex.ofReal_eq_zero.mp hzero
        linarith only [ht, htzero]
    . rw [dist_comm, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      dsimp only [t]
      linarith only [heps]
  have hsame := ha.eqOn_of_preconnected_of_mem_closure hb isPreconnected_univ
    (Set.mem_univ (0 : Complex)) hclosure
  exact funext (fun z => hsame (Set.mem_univ z))

/-- The entire reference equality retains every coefficient, including degree zero. -/
theorem realCoefficient_eq_of_involutive_weights (a b : QuadraticPrimeLaw)
    (e : Equiv.Perm Nat.Primes) (he : Function.Involutive e)
    (hnu : a.nu = b.nu) (hw : forall p, a.weight p = b.weight (e p)) (j : Nat) :
    a.realCoefficient j = b.realCoefficient j := by
  unfold realCoefficient
  rw [complexProfile_eq_of_involutive_weights a b e he hnu hw]

/-- Reference ratios agree algebraically at every rank and real clock argument. -/
theorem referenceRatio_eq_of_involutive_weights (a b : QuadraticPrimeLaw)
    (e : Equiv.Perm Nat.Primes) (he : Function.Involutive e)
    (hnu : a.nu = b.nu) (hw : forall p, a.weight p = b.weight (e p))
    (r : Nat) (u : Real) :
    a.referenceRatio r u = b.referenceRatio r u := by
  have hcoeff : a.realCoefficient = b.realCoefficient := by
    funext j
    exact realCoefficient_eq_of_involutive_weights a b e he hnu hw j
  unfold referenceRatio
  rw [hcoeff]

end QuadraticPrimeLaw

/-- One fixed canonical reciprocal-odds law, independent of every constellation support. -/
def canonicalPrimeOddsLaw : QuadraticPrimeLaw where
  weight p := primeProfileWeight (p : Nat)
  nu := 1
  error := 0
  nu_pos := by norm_num
  error_nonneg := le_rfl
  weight_nonneg p := by unfold primeProfileWeight; positivity
  quadratic_error p := by simp only [one_mul, sub_self, abs_zero, zero_mul, le_refl]

/-- The zero-based prime index is recovered from its actual prime value. -/
theorem count_primeAt (i : Nat) :
    Nat.count Nat.Prime (PrimeFactorUnimodality.primeAt i) = i := by
  exact PrimeFactorUnimodality.primeAt_strictMono.injective
    (primeAt_count_prime (Subtype.mk _ (PrimeFactorUnimodality.prime_primeAt i)))

/-- Exact coordinate conversion between natural prime indices and prime-labelled values. -/
def primeCoordinateEquiv : Equiv Nat Nat.Primes where
  toFun i := Subtype.mk (PrimeFactorUnimodality.primeAt i)
    (PrimeFactorUnimodality.prime_primeAt i)
  invFun p := Nat.count Nat.Prime (p : Nat)
  left_inv := count_primeAt
  right_inv p := Subtype.ext (primeAt_count_prime p)

/-- The actual prime permutation induced by a permutation of enumeration coordinates. -/
def primeValuePermutation (e : Equiv.Perm Nat) : Equiv.Perm Nat.Primes :=
  primeCoordinateEquiv.symm.trans (e.trans primeCoordinateEquiv)

/-- Involutions remain involutions under the exact prime-coordinate conversion. -/
theorem primeValuePermutation_involutive (e : Equiv.Perm Nat)
    (he : Function.Involutive e) : Function.Involutive (primeValuePermutation e) := by
  intro p
  apply Subtype.ext
  change PrimeFactorUnimodality.primeAt
    (e (Nat.count Nat.Prime
      (PrimeFactorUnimodality.primeAt (e (Nat.count Nat.Prime (p : Nat)))))) = (p : Nat)
  rw [count_primeAt, he, primeAt_count_prime p]

end PrimeFactorOscillations
