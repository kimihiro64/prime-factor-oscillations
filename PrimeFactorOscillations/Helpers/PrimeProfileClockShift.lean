/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileReferenceInvariance

/-!
# Explicit clock corrections for bounded prime-prefix shifts

The canonical clock increment is the complete sum over the added primes.
Its nonnegative correction is at most H/M, including H = 0.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter

/-- Moving a canonical prefix through H integers costs at most H/M in its clock. -/
theorem canonical_arithmeticClock_increment_bounds (M H : Nat) (hM : 1 <= M) :
    0 <= canonicalPrimeOddsLaw.arithmeticClock (M + H) -
      canonicalPrimeOddsLaw.arithmeticClock M /\
    canonicalPrimeOddsLaw.arithmeticClock (M + H) -
      canonicalPrimeOddsLaw.arithmeticClock M <= (H : Real) / (M : Real) := by
  classical
  let S := primeProfilePrefixSet (M + H) \ primeProfilePrefixSet M
  let f := fun p : Nat.Primes => Real.log (1 + primeProfileWeight (p : Nat))
  have hsub := monotone_primeProfilePrefixSet (Nat.le_add_right M H)
  have hdiff : canonicalPrimeOddsLaw.arithmeticClock (M + H) -
      canonicalPrimeOddsLaw.arithmeticClock M = S.sum f := by
    have hs := Finset.sum_sdiff (f := f) hsub
    simp only [QuadraticPrimeLaw.arithmeticClock, canonicalPrimeOddsLaw, one_mul]
    change _ = S.sum f
    linarith
  have hMp : (0 : Real) < (M : Real) := by exact_mod_cast hM
  have hterm : forall p, Membership.mem S p -> 0 <= f p /\ f p <= 1 / (M : Real) := by
    intro p hp
    have hps := Finset.mem_sdiff.mp hp
    have hpM : M < (p : Nat) := by
      by_contra h
      exact hps.2 ((mem_primeProfilePrefixSet p M).mpr (by omega))
    have hmden : (M : Real) <= (((p : Nat) - 1 : Nat) : Real) := by
      exact_mod_cast (show M <= (p : Nat) - 1 by omega)
    have hw := primeProfileWeight_nonneg (p : Nat)
    have hwM : primeProfileWeight (p : Nat) <= 1 / (M : Real) :=
      one_div_le_one_div_of_le hMp hmden
    have hlog := (Real.sub_log_one_add_bounds (primeProfileWeight (p : Nat)) hw).1
    exact And.intro (Real.log_nonneg (by linarith)) (by dsimp [f]; linarith)
  let e : Function.Embedding Nat.Primes Nat :=
    Function.Embedding.mk (fun p => (p : Nat)) Nat.Primes.coe_nat_injective
  have hcard : S.card <= H := by
    have hinc : S.map e <= Finset.Ioc M (M + H) := by
      intro x hx
      have hh := Finset.mem_map.mp hx
      let p := hh.choose
      have hp := hh.choose_spec.1
      have heq := hh.choose_spec.2
      have hps := Finset.mem_sdiff.mp hp
      have hlo : M < (p : Nat) := by
        by_contra h
        exact hps.2 ((mem_primeProfilePrefixSet p M).mpr (by omega))
      have hhi := (mem_primeProfilePrefixSet p (M + H)).mp hps.1
      change (p : Nat) = x at heq
      exact Finset.mem_Ioc.mpr (by simpa only [heq] using And.intro hlo hhi)
    calc
      S.card = (S.map e).card := (Finset.card_map e).symm
      _ <= (Finset.Ioc M (M + H)).card := Finset.card_le_card hinc
      _ = H := by rw [Nat.card_Ioc]; omega
  rw [hdiff]
  refine And.intro (Finset.sum_nonneg (fun p hp => (hterm p hp).1)) ?_
  calc
    S.sum f <= S.sum (fun _ => 1 / (M : Real)) :=
      Finset.sum_le_sum (fun p hp => (hterm p hp).2)
    _ = (S.card : Real) * (1 / (M : Real)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ <= (H : Real) * (1 / (M : Real)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = (H : Real) / (M : Real) := by ring

/-- A fixed finite displacement has a vanishing canonical clock correction. -/
theorem tendsto_canonical_arithmeticClock_increment_zero (H : Nat) :
    Tendsto (fun M => canonicalPrimeOddsLaw.arithmeticClock (M + H) -
      canonicalPrimeOddsLaw.arithmeticClock M) atTop (nhds 0) := by
  have hb := (eventually_ge_atTop 1).mono
    (fun M hM => canonical_arithmeticClock_increment_bounds M H hM)
  exact squeeze_zero' (hb.mono (fun _ h => h.1)) (hb.mono (fun _ h => h.2))
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)

/-- The reference clock remains divergent after a fixed forward shift. -/
theorem tendsto_canonical_shifted_referenceClock_atTop (H : Nat) :
    Tendsto (fun M => canonicalPrimeOddsLaw.referenceClock (M + H)) atTop atTop := by
  have hshift : Tendsto (fun M : Nat => M + H) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact (eventually_ge_atTop b).mono (fun M hM => hM.trans (Nat.le_add_right M H))
  exact canonicalPrimeOddsLaw.tendsto_referenceClock_atTop.comp hshift

/-- The arithmetic clock may be compared with the shifted canonical reference. -/
theorem tendsto_canonical_shifted_clock_difference_zero (H : Nat) :
    Tendsto (fun M => canonicalPrimeOddsLaw.arithmeticClock M -
      canonicalPrimeOddsLaw.referenceClock (M + H)) atTop (nhds 0) := by
  have hshift : Tendsto (fun M : Nat => M + H) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact (eventually_ge_atTop b).mono (fun M hM => hM.trans (Nat.le_add_right M H))
  have h := (canonicalPrimeOddsLaw.tendsto_clock_difference_zero.comp hshift).sub
    (tendsto_canonical_arithmeticClock_increment_zero H)
  have hsame : (fun M : Nat =>
      (canonicalPrimeOddsLaw.arithmeticClock (M + H) -
        canonicalPrimeOddsLaw.referenceClock (M + H)) -
      (canonicalPrimeOddsLaw.arithmeticClock (M + H) -
        canonicalPrimeOddsLaw.arithmeticClock M)) =
      (fun M => canonicalPrimeOddsLaw.arithmeticClock M -
        canonicalPrimeOddsLaw.referenceClock (M + H)) := by
    funext M
    ring
  simpa only [Function.comp_def, hsame, sub_zero] using h

end PrimeFactorOscillations
