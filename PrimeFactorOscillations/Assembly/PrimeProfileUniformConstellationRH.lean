/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.PrimeProfilePrefixSandwich
import PrimeFactorOscillations.Assembly.PrimeProfileQuadrupletCanonicalRH
import PrimeFactorOscillations.Helpers.PrimeProfileClockShift

/-!
# A uniform RH criterion over bounded prime permutations

The finite ratio sandwich retains every crossing coordinate. The canonical
clock comparison absorbs its positive H/M correction with the RH margin.
The eventual cutoff is independent of the permitted prime permutation.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Robin1984

/-- RH controls a smaller canonical prefix at the larger prefix's reference clock. -/
theorem eventually_shifted_canonical_ratio_lt_reference_of_RH
    (H : Nat) (alpha : Real) (ha : 0 < alpha) (hRH : RiemannHypothesis) :
    Filter.Eventually (fun M : Nat =>
      let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock (M + H))
      0 < r /\
      0 < canonicalPrimeOddsLaw.prefixEsymm M r /\
      0 < Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient r
        (canonicalPrimeOddsLaw.referenceClock (M + H)) /\
      canonicalPrimeOddsLaw.densityRatio M r <
        canonicalPrimeOddsLaw.referenceRatio r
          (canonicalPrimeOddsLaw.referenceClock (M + H))) atTop := by
  choose C hC hSign using
    canonicalPrimeOddsLaw.exists_eventually_prefixProfile_moving_floor_sign
      alpha ha canonicalPrimeOddsLaw.arithmeticClock
      (fun M => canonicalPrimeOddsLaw.referenceClock (M + H))
      (tendsto_canonical_shifted_referenceClock_atTop H)
      (tendsto_canonical_shifted_clock_difference_zero H)
  have hshift : Tendsto (fun M : Nat => M + H) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact (eventually_ge_atTop b).mono (fun M hM => hM.trans (Nat.le_add_right M H))
  have hNeg := hshift.eventually
    (eventually_nicolasLog_nat_lt_neg_div_of_RH hRH (2 * (C + H + 1)))
  have hTheta := hshift.eventually
    (tendsto_primeProfile_theta_atTop.eventually_gt_atTop (1 : Real))
  filter_upwards [hSign, hNeg, hTheta, eventually_ge_atTop (max 1 H)]
    with M hS hN hT hM
  have hOne : 1 <= M := (le_max_left 1 H).trans hM
  have hHM : H <= M := (le_max_right 1 H).trans hM
  have hMp : (0 : Real) < M := by exact_mod_cast hOne
  have hNp : (0 : Real) < (M + H : Nat) := by exact_mod_cast (show 0 < M + H by omega)
  have hSpos : 0 < C + (H : Real) + 1 := by positivity
  have hcmp : -(2 * (C + (H : Real) + 1)) / ((M + H : Nat) : Real) <=
      -(C + (H : Real) + 1) / (M : Real) := by
    have hHM' : (H : Real) <= (M : Real) := by exact_mod_cast hHM
    have hden : ((M + H : Nat) : Real) <= 2 * (M : Real) := by
      push_cast
      linarith only [hHM']
    have hq := div_le_div_of_nonneg_left hSpos.le hNp hden
    have htwo := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : Real) <= 2)
    have hcancel : 2 * ((C + (H : Real) + 1) / (2 * (M : Real))) =
        (C + (H : Real) + 1) / (M : Real) := by ring
    rw [hcancel] at htwo
    have hneg := neg_le_neg htwo
    simpa only [neg_div, mul_div_assoc, neg_mul] using hneg
  have hInc := canonical_arithmeticClock_increment_bounds M H hOne
  have hClock := canonicalPrimeOddsLaw.clock_difference_eq_nicolas (M + H) hT
  change canonicalPrimeOddsLaw.referenceClock (M + H) -
    canonicalPrimeOddsLaw.arithmeticClock (M + H) =
      1 * nicolasLogMertensOscillation ((M + H : Nat) : Real) at hClock
  rw [one_mul] at hClock
  have hMargin : canonicalPrimeOddsLaw.referenceClock (M + H) -
      canonicalPrimeOddsLaw.arithmeticClock M < -C / (M : Real) := by
    have hF := hN.trans_le hcmp
    have hAdd := add_lt_add_of_lt_of_le hF hInc.2
    have hInv : (0 : Real) < 1 / (M : Real) := one_div_pos.mpr hMp
    have hCancel : -(C + (H : Real) + 1) / (M : Real) + H / M =
        -C / M - 1 / M := by ring
    rw [hCancel] at hAdd
    linarith only [hClock, hAdd, hInv]
  dsimp only at hS
  refine And.intro hS.1 (And.intro ?_ (And.intro hS.2.2.1 ?_))
  . rw [<- canonicalPrimeOddsLaw.prefix_factorialConvolution_eq_esymm]
    exact hS.2.1
  . rw [canonicalPrimeOddsLaw.densityRatio_eq_factorialConvolution]
    exact hS.2.2.2.2 hMargin

/-- One eventual cutoff controls all prime permutations of displacement at most H. -/
theorem eventually_uniform_bounded_prime_permutation_sign_of_RH
    (H : Nat) (alpha : Real) (ha : 0 < alpha) (hRH : RiemannHypothesis) :
    Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
      0 < r /\
      0 < Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient r
        (canonicalPrimeOddsLaw.referenceClock N) /\
      forall (sigma : Equiv.Perm Nat.Primes)
        (hdispl : forall p : Nat.Primes,
          abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (H : Real)),
        0 < (boundedPrimePermutationLaw sigma H hdispl).prefixEsymm N r /\
        (boundedPrimePermutationLaw sigma H hdispl).densityRatio N r <
          canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N))
      atTop := by
  choose M0 hM0 using eventually_atTop.mp
    (eventually_shifted_canonical_ratio_lt_reference_of_RH H alpha ha hRH)
  apply eventually_atTop.mpr
  refine Exists.intro (M0 + H) ?_
  intro N hN
  have hHN : H <= N := by omega
  have hM : M0 <= N - H := by omega
  have hAdd : N - H + H = N := Nat.sub_add_cancel hHN
  have hBase := hM0 (N - H) hM
  rw [hAdd] at hBase
  refine And.intro hBase.1 (And.intro hBase.2.2.1 ?_)
  intro sigma hdispl
  have hSandwich := bounded_prime_permutation_ratio_sandwich sigma H N hHN
    hdispl (Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N))
    (by omega) hBase.2.1
  exact And.intro hSandwich.1 (hSandwich.2.2.2.trans_lt hBase.2.2.2)

/-- The uniform bounded-permutation sign condition is equivalent to RH, even for H = 0. -/
theorem riemannHypothesis_iff_uniform_bounded_prime_permutation_sign
    (H : Nat) (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <->
      Filter.Eventually (fun N : Nat =>
        let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
        forall (sigma : Equiv.Perm Nat.Primes)
          (hdispl : forall p : Nat.Primes,
            abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (H : Real)),
          (boundedPrimePermutationLaw sigma H hdispl).densityRatio N r <
            canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N))
        atTop := by
  constructor
  . intro hRH
    exact (eventually_uniform_bounded_prime_permutation_sign_of_RH H alpha ha hRH).mono
      (fun N hN sigma hdispl => (hN.2.2 sigma hdispl).2)
  . intro hEvent
    apply canonicalPrimeOddsLaw.riemannHypothesis_of_eventually_densityRatio_le_reference
      alpha ha
    filter_upwards [hEvent] with N hN
    have hId : forall p : Nat.Primes,
        abs ((((Equiv.refl Nat.Primes) p : Nat) : Real) - ((p : Nat) : Real)) <=
          (H : Real) := by
      intro p
      simp
    have h := hN (Equiv.refl Nat.Primes) hId
    change canonicalPrimeOddsLaw.densityRatio N
      (Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)) < _ at h
    exact h.le

namespace PrimeProfileRigidity

/-- One RH cutoff works for every admissible distance-six constellation support. -/
theorem eventually_uniform_quadruplet_sign_of_RH
    (alpha : Real) (ha : 0 < alpha) (hRH : RiemannHypothesis) :
    Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
      forall (B : Set Nat)
        (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)))
        (hgap : forall n, Membership.mem B n ->
          PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6),
        0 < (quadrupletSwapPrimeLaw B hB hgap).prefixEsymm N r /\
        (quadrupletSwapPrimeLaw B hB hgap).densityRatio N r <
          canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N))
      atTop := by
  filter_upwards [eventually_uniform_bounded_prime_permutation_sign_of_RH 6 alpha ha hRH]
    with N hN
  dsimp only
  intro B hB hgap
  let sigma := primeValuePermutation (Finset.twoStepSwapPerm B hB)
  have hdispl : forall p : Nat.Primes,
      abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (6 : Real) := by
    intro p
    have h := twoStepSwap_prime_value_displacement B hB hgap (Nat.count Nat.Prime (p : Nat))
    change abs ((PrimeFactorUnimodality.primeAt
        (Finset.twoStepSwapPerm B hB (Nat.count Nat.Prime (p : Nat))) : Real) -
      ((p : Nat) : Real)) <= 6
    simpa only [primeAt_count_prime p] using h
  have h := hN.2.2 sigma hdispl
  change 0 < (quadrupletSwapPrimeLaw B hB hgap).prefixEsymm N _ /\
    (quadrupletSwapPrimeLaw B hB hgap).densityRatio N _ <
      canonicalPrimeOddsLaw.referenceRatio _ (canonicalPrimeOddsLaw.referenceClock N) at h
  exact h

/-- Uniformity over constellation supports is itself an RH equivalent. -/
theorem riemannHypothesis_iff_uniform_quadruplet_sign
    (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <->
      Filter.Eventually (fun N : Nat =>
        let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
        forall (B : Set Nat)
          (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)))
          (hgap : forall n, Membership.mem B n ->
            PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6),
          (quadrupletSwapPrimeLaw B hB hgap).densityRatio N r <
            canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N))
        atTop := by
  constructor
  . intro hRH
    exact (eventually_uniform_quadruplet_sign_of_RH alpha ha hRH).mono
      (fun N hN B hB hgap => (hN B hB hgap).2)
  . intro hEvent
    let B : Set Nat := fun _ => False
    have hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)) := by
      intro n hn
      exact False.elim hn
    have hgap : forall n, Membership.mem B n ->
        PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6 := by
      intro n hn
      exact False.elim hn
    exact (quadruplet_swap_rh_iff_canonical B hB hgap alpha ha).mpr
      (hEvent.mono (fun N hN => hN B hB hgap))

end PrimeProfileRigidity

end PrimeFactorOscillations
