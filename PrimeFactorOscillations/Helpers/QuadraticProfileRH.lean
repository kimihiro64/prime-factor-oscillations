/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.FamilyNicolasTransfer
import PrimeFactorOscillations.Helpers.QuadraticProfileGenerating
import PrimeFactorOscillations.Helpers.QuadraticProfileMovingClockSign

/-!
# RH and actual moving-rank ratios in every qualifying law

The elementary symmetric coefficients are the actual finite local odds.
Every positive fixed rank parameter is allowed. No prime-gap premise occurs.
Forced-prime rank shifts belong to the arithmetic density interpretation.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

open Filter Robin1984

theorem exists_eventually_densityRatio_reference_sign (law : QuadraticPrimeLaw)
    (alpha : Real) (ha : 0 < alpha) :
    exists C : Real, 0 <= C /\ Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * law.referenceClock N)
      1 < Chebyshev.theta (N : Real) /\ 0 < r /\
        0 < law.prefixEsymm N r /\
        0 < Nat.factorialConvolution law.realCoefficient r (law.referenceClock N) /\
        (C / (N : Real) < law.nu * nicolasLogMertensOscillation (N : Real) ->
          law.referenceRatio r (law.referenceClock N) < law.densityRatio N r) /\
        (law.nu * nicolasLogMertensOscillation (N : Real) < -C / (N : Real) ->
          law.densityRatio N r < law.referenceRatio r (law.referenceClock N))) atTop := by
  choose C hC hEvent using law.exists_eventually_prefixProfile_moving_floor_sign
    alpha ha law.arithmeticClock law.referenceClock law.tendsto_referenceClock_atTop
    law.tendsto_clock_difference_zero
  refine Exists.intro C (And.intro hC ?_)
  filter_upwards [hEvent, tendsto_primeProfile_theta_atTop.eventually_gt_atTop (1 : Real)]
    with N hN hTheta
  dsimp only at hN
  rw [law.clock_difference_eq_nicolas N hTheta] at hN
  let r := Nat.floor (alpha * law.referenceClock N)
  have hFinite : 0 < law.prefixEsymm N r := by
    rw [<- law.prefix_factorialConvolution_eq_esymm N r]
    exact hN.2.1
  refine And.intro hTheta (And.intro hN.1
    (And.intro hFinite (And.intro hN.2.2.1 (And.intro ?_ ?_))))
  . intro hF
    rw [law.densityRatio_eq_factorialConvolution]
    exact hN.2.2.2.1 hF
  . intro hF
    rw [law.densityRatio_eq_factorialConvolution]
    exact hN.2.2.2.2 hF

theorem eventually_densityRatio_lt_reference_of_RH (law : QuadraticPrimeLaw)
    (alpha : Real) (ha : 0 < alpha) (hRH : RiemannHypothesis) :
    Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * law.referenceClock N)
      law.densityRatio N r < law.referenceRatio r (law.referenceClock N)) atTop := by
  choose C hC hSign using law.exists_eventually_densityRatio_reference_sign alpha ha
  have hNeg := eventually_nicolasLog_nat_lt_neg_div_of_RH hRH ((C + 1) / law.nu)
  filter_upwards [hSign, hNeg, eventually_ge_atTop (1 : Nat)] with N hS hN hOne
  have hn : (0 : Real) < N := by exact_mod_cast hOne
  have hScaled := mul_lt_mul_of_pos_left hN law.nu_pos
  have hCancel : law.nu * (-((C + 1) / law.nu) / (N : Real)) =
      -C / N - 1 / N := by
    field_simp [law.nu_pos.ne', hn.ne']
    <;> ring
  rw [hCancel] at hScaled
  have hInv : (0 : Real) < 1 / N := one_div_pos.mpr hn
  exact hS.2.2.2.2.2 (by linarith only [hScaled, hInv])

theorem riemannHypothesis_of_eventually_densityRatio_le_reference
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha)
    (hEvent : Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * law.referenceClock N)
      law.densityRatio N r <= law.referenceRatio r (law.referenceClock N)) atTop) :
    RiemannHypothesis := by
  by_contra hNotRH
  choose C hC hSign using law.exists_eventually_densityRatio_reference_sign alpha ha
  have hAll := (hSign.and hEvent).and (eventually_ge_atTop (1 : Nat))
  choose N0 hN0 using eventually_atTop.mp hAll
  choose N hN hPeak using nicolasLog_scaled_unbounded_of_not_RH
    hNotRH ((C + 1) / law.nu) N0
  have hDomain := hN0 N hN
  have hn : (0 : Real) < N := by exact_mod_cast hDomain.2
  have hScaled := mul_lt_mul_of_pos_left hPeak law.nu_pos
  have hCancel : law.nu * ((C + 1) / law.nu) = C + 1 := by field_simp [law.nu_pos.ne']
  rw [hCancel] at hScaled
  have hMargin : C / (N : Real) < law.nu * nicolasLogMertensOscillation (N : Real) := by
    by_contra h
    have hUpper := mul_le_mul_of_nonneg_left (le_of_not_gt h) hn.le
    have hCancelN : (N : Real) * (C / N) = C := by field_simp
    rw [hCancelN] at hUpper
    nlinarith only [hScaled, hUpper]
  have hAbove := hDomain.1.1.2.2.2.2.1 hMargin
  exact (not_lt_of_ge hDomain.1.2) hAbove

theorem riemannHypothesis_iff_eventually_densityRatio_lt_reference
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * law.referenceClock N)
      law.densityRatio N r < law.referenceRatio r (law.referenceClock N)) atTop := by
  constructor
  . exact law.eventually_densityRatio_lt_reference_of_RH alpha ha
  . intro h
    apply law.riemannHypothesis_of_eventually_densityRatio_le_reference alpha ha
    exact h.mono (fun _ hx => hx.le)

theorem riemannHypothesis_iff_eventually_densityRatio_le_reference
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * law.referenceClock N)
      law.densityRatio N r <= law.referenceRatio r (law.referenceClock N)) atTop := by
  constructor
  . intro hRH
    exact (law.eventually_densityRatio_lt_reference_of_RH alpha ha hRH).mono (fun _ hx => hx.le)
  . exact law.riemannHypothesis_of_eventually_densityRatio_le_reference alpha ha

end PrimeFactorOscillations.QuadraticPrimeLaw
