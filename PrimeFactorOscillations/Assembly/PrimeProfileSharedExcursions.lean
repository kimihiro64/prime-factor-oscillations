/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.PrimeProfileUniformConstellationRH
import PrimeFactorOscillations.Helpers.PrimeProfileExcursionClock

/-!
# Shared false-RH excursions for all bounded prime permutations

The lower prefix sandwich retains the signed Nicolas signal. A positive
excursion exceeding the full clock correction pushes every bounded
permutation above one canonical reference at the same cutoff.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Robin1984

/-- The lower canonical prefix has the required moving-rank denominator eventually. -/
theorem eventually_canonical_lower_prefix_pos
    (H : Nat) (alpha : Real) (ha : 0 < alpha) :
    Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
      0 < r /\ 0 < canonicalPrimeOddsLaw.prefixEsymm (N - H) r /\
      0 < Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient r
        (canonicalPrimeOddsLaw.referenceClock N)) atTop := by
  choose D hD hDomain using
    canonicalPrimeOddsLaw.exists_eventually_prefixProfile_moving_floor_sign
      alpha ha canonicalPrimeOddsLaw.arithmeticClock
      (fun M => canonicalPrimeOddsLaw.referenceClock (M + H))
      (tendsto_canonical_shifted_referenceClock_atTop H)
      (tendsto_canonical_shifted_clock_difference_zero H)
  choose M0 hM0 using eventually_atTop.mp hDomain
  apply eventually_atTop.mpr
  refine Exists.intro (M0 + H) ?_
  intro N hN
  have hHN : H <= N := by omega
  have hDmn := hM0 (N - H) (by omega)
  rw [Nat.sub_add_cancel hHN] at hDmn
  refine And.intro hDmn.1 (And.intro ?_ hDmn.2.2.1)
  rw [<- canonicalPrimeOddsLaw.prefix_factorialConvolution_eq_esymm]
  exact hDmn.2.1

/-- An explicit signed threshold forces all bounded permutations above the reference. -/
theorem exists_eventually_uniform_bounded_permutation_positive_response
    (H : Nat) (alpha : Real) (ha : 0 < alpha) :
    exists K : Real, 0 <= K /\ Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
      0 < r /\
      0 < Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient r
        (canonicalPrimeOddsLaw.referenceClock N) /\
      forall (sigma : Equiv.Perm Nat.Primes)
        (hdispl : forall p : Nat.Primes,
          abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (H : Real)),
        0 < (boundedPrimePermutationLaw sigma H hdispl).prefixEsymm N r /\
        (K / (N : Real) < nicolasLogMertensOscillation (N : Real) ->
          canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N) <
            (boundedPrimePermutationLaw sigma H hdispl).densityRatio N r)) atTop := by
  choose C hC hSign using
    canonicalPrimeOddsLaw.exists_eventually_prefixProfile_moving_floor_sign
      alpha ha canonicalPrimeOddsLaw.arithmeticClock
      (fun M => canonicalPrimeOddsLaw.referenceClock (M - H))
      (tendsto_canonical_past_referenceClock_atTop H)
      (tendsto_canonical_past_clock_difference_zero H)
  have hshift : Tendsto (fun N : Nat => N + H) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact (eventually_ge_atTop b).mono (fun N hN => hN.trans (Nat.le_add_right N H))
  refine Exists.intro (C + H + 1) (And.intro (by positivity) ?_)
  filter_upwards [hshift.eventually hSign, eventually_canonical_lower_prefix_pos H alpha ha,
      tendsto_primeProfile_theta_atTop.eventually_gt_atTop (1 : Real),
      eventually_ge_atTop (max 1 H)] with N hS hLower hTheta hN
  rw [Nat.add_sub_cancel] at hS
  have hOne : 1 <= N := (le_max_left 1 H).trans hN
  have hHN : H <= N := (le_max_right 1 H).trans hN
  have hn : (0 : Real) < N := by exact_mod_cast hOne
  refine And.intro hLower.1 (And.intro hLower.2.2 ?_)
  intro sigma hdispl
  have hSandwich := bounded_prime_permutation_ratio_sandwich sigma H N hHN hdispl
    (Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)) (by omega) hLower.2.1
  refine And.intro hSandwich.1 ?_
  intro hF
  have hInc := canonical_arithmeticClock_increment_bounds N H hOne
  have hClock := canonicalPrimeOddsLaw.clock_difference_eq_nicolas N hTheta
  change canonicalPrimeOddsLaw.referenceClock N - canonicalPrimeOddsLaw.arithmeticClock N =
    1 * nicolasLogMertensOscillation (N : Real) at hClock
  rw [one_mul] at hClock
  have hCcmp : C / ((N + H : Nat) : Real) <= C / (N : Real) := by
    apply div_le_div_of_nonneg_left hC hn
    exact_mod_cast Nat.le_add_right N H
  have hInv : (0 : Real) < 1 / (N : Real) := one_div_pos.mpr hn
  have hCancel : (C + (H : Real) + 1) / (N : Real) - H / N =
      C / N + 1 / N := by ring
  have hSub : (C + (H : Real) + 1) / (N : Real) - H / N <
      nicolasLogMertensOscillation (N : Real) -
        (canonicalPrimeOddsLaw.arithmeticClock (N + H) -
          canonicalPrimeOddsLaw.arithmeticClock N) := by
    linarith only [hF, hInc.2]
  rw [hCancel] at hSub
  have hMargin : C / ((N + H : Nat) : Real) <
      canonicalPrimeOddsLaw.referenceClock N -
        canonicalPrimeOddsLaw.arithmeticClock (N + H) := by
    linarith only [hSub, hClock, hCcmp, hInv]
  have hAbove := hS.2.2.2.1 hMargin
  change canonicalPrimeOddsLaw.referenceRatio
      (Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N))
      (canonicalPrimeOddsLaw.referenceClock N) < _ at hAbove
  rw [<- canonicalPrimeOddsLaw.densityRatio_eq_factorialConvolution] at hAbove
  exact hAbove.trans_le hSandwich.2.2.1

/-- False RH creates arbitrarily late common positive excursions for every bounded permutation. -/
theorem unbounded_shared_bounded_permutation_excursions_of_not_RH
    (H : Nat) (alpha : Real) (ha : 0 < alpha) (hNotRH : Not RiemannHypothesis) :
    forall N0 : Nat, exists N : Nat, N0 <= N /\
      let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
      0 < r /\
      0 < Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient r
        (canonicalPrimeOddsLaw.referenceClock N) /\
      forall (sigma : Equiv.Perm Nat.Primes)
        (hdispl : forall p : Nat.Primes,
          abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (H : Real)),
        0 < (boundedPrimePermutationLaw sigma H hdispl).prefixEsymm N r /\
        canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N) <
          (boundedPrimePermutationLaw sigma H hdispl).densityRatio N r := by
  choose K hK hResponse using
    exists_eventually_uniform_bounded_permutation_positive_response H alpha ha
  choose M0 hM0 using eventually_atTop.mp hResponse
  intro N0
  choose N hN hPeak using nicolasLog_scaled_unbounded_of_not_RH hNotRH K
    (max N0 (max M0 1))
  have hN0 : N0 <= N := (le_max_left _ _).trans hN
  have hNM : M0 <= N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hOne : 1 <= N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hn : (0 : Real) < N := by exact_mod_cast hOne
  have hF : K / (N : Real) < nicolasLogMertensOscillation (N : Real) := by
    by_contra h
    have hUpper := mul_le_mul_of_nonneg_left (le_of_not_gt h) hn.le
    have hCancel : (N : Real) * (K / N) = K := by field_simp
    rw [hCancel] at hUpper
    linarith only [hPeak, hUpper]
  have h := hM0 N hNM
  refine Exists.intro N (And.intro hN0 (And.intro h.1 (And.intro h.2.1 ?_)))
  intro sigma hdispl
  exact And.intro (h.2.2 sigma hdispl).1 ((h.2.2 sigma hdispl).2 hF)

/-- A single bounded permutation's eventual canonical upper sign implies RH. -/
theorem riemannHypothesis_of_bounded_permutation_canonical_sign
    (sigma : Equiv.Perm Nat.Primes) (H : Nat)
    (hdispl : forall p : Nat.Primes,
      abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (H : Real))
    (alpha : Real) (ha : 0 < alpha)
    (hEvent : Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
      (boundedPrimePermutationLaw sigma H hdispl).densityRatio N r <=
        canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N))
      atTop) : RiemannHypothesis := by
  by_contra hNotRH
  choose N0 hN0 using eventually_atTop.mp hEvent
  choose N hN hAbove using
    unbounded_shared_bounded_permutation_excursions_of_not_RH H alpha ha hNotRH N0
  exact (not_lt_of_ge (hN0 N hN)) (hAbove.2.2 sigma hdispl).2

/-- Every individual bounded prime permutation has the canonical RH criterion. -/
theorem riemannHypothesis_iff_bounded_permutation_canonical_sign
    (sigma : Equiv.Perm Nat.Primes) (H : Nat)
    (hdispl : forall p : Nat.Primes,
      abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (H : Real))
    (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
      (boundedPrimePermutationLaw sigma H hdispl).densityRatio N r <
        canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N))
      atTop := by
  constructor
  . intro hRH
    exact (eventually_uniform_bounded_prime_permutation_sign_of_RH H alpha ha hRH).mono
      (fun N hN => (hN.2.2 sigma hdispl).2)
  . intro hEvent
    exact riemannHypothesis_of_bounded_permutation_canonical_sign sigma H hdispl alpha ha
      (hEvent.mono (fun N hN => hN.le))

end PrimeFactorOscillations
