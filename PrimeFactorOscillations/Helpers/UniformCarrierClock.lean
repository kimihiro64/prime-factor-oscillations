/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.SumPrimeReciprocals
import PrimeFactorOscillations.Helpers.UniformCarrierSparse

/-!
# Uniform Carrier Clock

Divergence of the common baseline clock and eventual admissibility of every fixed positive rank parameter.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.UniformCarrier

open Filter

def baseline : PrimeClockLaw :=
  BoundedAmplitudeDetector.law (fun _ => (1 / 2 : Real))
    (fun _ => by norm_num) (fun _ => by norm_num)

theorem baseline_scale : baseline.scale = 1 := rfl
theorem baseline_error : baseline.error = 0 := rfl

theorem baseline_compensator (p : Nat.Primes) :
    baseline.compensator p = 1 / (2 * ((p : Nat) : Real) - 1) := by
  have hp : (1 : Real) < (p : Nat) := by exact_mod_cast p.property.one_lt
  change (1 / 2 : Real) / (((p : Nat) : Real) - 1 / 2) = _
  field_simp <;> ring

theorem prime_reciprocal_le_twice_baseline (p : Nat.Primes) :
    (1 : Real) / (p : Nat) <= 2 * baseline.compensator p := by
  have hp : (1 : Real) < (p : Nat) := by exact_mod_cast p.property.one_lt
  have hn : 0 < (2 * ((p : Nat) : Real) - 1) := by linarith
  rw [baseline_compensator]
  have h := one_div_le_one_div_of_le hn (by linarith : 2 * ((p : Nat) : Real) - 1 <= 2 * (p : Nat))
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0 : Real) <= 2)
  convert hm using 1 <;> field_simp <;> ring

theorem baseline_clock_monotone : Monotone baseline.arithmeticClock := by
  intro N M hNM
  apply Finset.sum_le_sum_of_subset_of_nonneg (monotone_primeProfilePrefixSet hNM)
  intro p hp hpN
  exact baseline.compensator_nonneg p

theorem baseline_clock_tendsto : Tendsto baseline.arithmeticClock atTop atTop := by
  have hUnbounded : forall B : Real, exists N : Nat, B <= baseline.arithmeticClock N := by
    intro B
    by_contra hnot
    push_neg at hnot
    have hsum : Summable baseline.compensator := by
      apply summable_of_sum_le baseline.compensator_nonneg
      intro T
      let N := T.sup (fun p => (p : Nat))
      have hT : T <= primeProfilePrefixSet N := by
        intro p hp
        apply (mem_primeProfilePrefixSet p N).mpr
        exact Finset.le_sup hp
      have hle : T.sum baseline.compensator <= baseline.arithmeticClock N := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hT
        intro p hp hpT
        exact baseline.compensator_nonneg p
      exact hle.trans (hnot N).le
    have hinv : Summable (fun p : Nat.Primes => (1 / (p : Nat) : Real)) :=
      (hsum.mul_left 2).of_nonneg_of_le
        (fun p => by positivity) prime_reciprocal_le_twice_baseline
    exact Nat.Primes.not_summable_one_div hinv
  apply tendsto_atTop.mpr
  intro B
  choose N hN using hUnbounded B
  exact eventually_atTop.mpr (Exists.intro N (fun M hNM =>
    hN.trans (baseline_clock_monotone hNM)))

theorem eventual_carrier_rank (alpha : Real) (ha : 0 < alpha)
    (r0 N0 P0 : Nat) :
    exists P1 : Nat, forall P : Nat, P1 <= P ->
      P0 <= P /\ N0 <= 2 * P /\ 3 <= baseline.arithmeticClock (2 * P) /\
      r0 <= Nat.floor (alpha * baseline.arithmeticClock (2 * P)) /\
      alpha / 4 <=
        (Nat.floor (alpha * baseline.arithmeticClock (2 * P)) : Real) /
          (baseline.arithmeticClock (2 * P) + 1) /\
      (Nat.floor (alpha * baseline.arithmeticClock (2 * P)) : Real) /
          (baseline.arithmeticClock (2 * P) - 1) <= 4 * alpha := by
  let T := max 4 (((r0 : Real) + 4) / alpha)
  have hevent := (tendsto_atTop.mp baseline_clock_tendsto) T
  choose NN hNN using eventually_atTop.mp hevent
  refine Exists.intro (max P0 (max N0 NN)) ?_
  intro P hP
  have hP0 : P0 <= P := (le_max_left _ _).trans hP
  have hPN : N0 <= P := (le_max_left _ _).trans ((le_max_right _ _).trans hP)
  have hPNN : NN <= P := (le_max_right _ _).trans ((le_max_right _ _).trans hP)
  have hN : N0 <= 2 * P := by omega
  have hNN' : NN <= 2 * P := by omega
  let B := baseline.arithmeticClock (2 * P)
  let r := Nat.floor (alpha * B)
  have hBT : T <= B := hNN (2 * P) hNN'
  have hB4 : (4 : Real) <= B := (le_max_left _ _).trans hBT
  have hscaled : ((r0 : Real) + 4) / alpha <= B := (le_max_right _ _).trans hBT
  have hm := mul_le_mul_of_nonneg_right hscaled ha.le
  have hc : (((r0 : Real) + 4) / alpha) * alpha = (r0 : Real) + 4 := by field_simp
  rw [hc] at hm
  have hab : 0 <= alpha * B := mul_nonneg ha.le (by linarith)
  have hrUpper : (r : Real) <= alpha * B := Nat.floor_le hab
  have hrLower : alpha * B - 1 <= (r : Real) := by
    have h := Nat.lt_floor_add_one (alpha * B)
    change alpha * B < (r : Real) + 1 at h
    linarith
  have hr0 : r0 <= r := by
    have h : (r0 : Real) <= r := by linarith only [hm, hrLower]
    exact_mod_cast h
  have hBp : 0 < B + 1 := by linarith only [hB4]
  have hBm : 0 < B - 1 := by linarith only [hB4]
  have hprod : 4 * alpha <= alpha * B := by
    nlinarith only [mul_nonneg ha.le (sub_nonneg.mpr hB4)]
  have hl : alpha / 4 * (B + 1) <= (r : Real) := by
    have hn : (0 : Real) <= r0 := Nat.cast_nonneg r0
    have hba : 4 <= alpha * B := by linarith only [hm, hn]
    nlinarith only [hrLower, hba, hprod]
  have hu : (r : Real) <= 4 * alpha * (B - 1) := by
    nlinarith only [hrUpper, hprod, hab]
  refine And.intro hP0 (And.intro hN (And.intro (by linarith only [hB4])
    (And.intro hr0 (And.intro ?_ ?_))))
  . calc
      alpha / 4 = (alpha / 4 * (B + 1)) / (B + 1) := by field_simp
      _ <= (r : Real) / (B + 1) := div_le_div_of_nonneg_right hl hBp.le
  . calc
      (r : Real) / (B - 1) <= (4 * alpha * (B - 1)) / (B - 1) :=
        div_le_div_of_nonneg_right hu hBm.le
      _ = 4 * alpha := by field_simp

end PrimeFactorOscillations.UniformCarrier
