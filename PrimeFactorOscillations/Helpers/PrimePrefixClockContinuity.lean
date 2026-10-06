/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasQuantitativeClock
import PrimeFactorOscillations.Helpers.PrimeProfileSpatialThreshold

/-!
# Finite increments of the prime-product clock

All omitted integers are retained in the upper comparison for the exact
prime-prefix sum. Quantitative PNT then bounds physical clock increments
by eight times the integer interval length times its endpoint logarithm.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter

def primePrefixLogSum (N : Nat) : Real :=
  (primeProfilePrefixSet N).sum (fun p => Real.log (1 + primeProfileWeight (p : Nat)))

theorem primePrefixLogSum_increment_bounds (N M : Nat) (hN : 1 <= N) (hNM : N <= M) :
    0 <= primePrefixLogSum M - primePrefixLogSum N /\
      primePrefixLogSum M - primePrefixLogSum N <=
        ((M : Real) - (N : Real)) / (N : Real) := by
  classical
  let S := primeProfilePrefixSet M \ primeProfilePrefixSet N
  let g : Nat.Primes -> Real := fun p => Real.log (1 + primeProfileWeight (p : Nat))
  have hn : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hId : primePrefixLogSum M - primePrefixLogSum N = S.sum g := by
    have h := Finset.sum_sdiff (f := g) (monotone_primeProfilePrefixSet hNM)
    dsimp [primePrefixLogSum, S, g] at *
    linarith
  have hRange (p : Nat.Primes) (hp : Membership.mem S p) :
      N < (p : Nat) /\ (p : Nat) <= M := by
    have hs := Finset.mem_sdiff.mp hp
    refine And.intro ?_ ((mem_primeProfilePrefixSet p M).mp hs.1)
    exact Nat.lt_of_not_ge (fun h => hs.2 ((mem_primeProfilePrefixSet p N).mpr h))
  have hTerm (p : Nat.Primes) (hp : Membership.mem S p) : g p <= 1 / (N : Real) := by
    have ha := primeProfileWeight_nonneg (p : Nat)
    have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + primeProfileWeight (p : Nat))
    have hw : primeProfileWeight (p : Nat) <= 1 / (N : Real) := by
      dsimp [primeProfileWeight]
      exact one_div_le_one_div_of_le hn
        (by exact_mod_cast (show N <= (p : Nat) - 1 by have h := (hRange p hp).1; omega))
    dsimp only [g]
    linarith
  rw [hId]
  refine And.intro (Finset.sum_nonneg (fun p hp =>
    Real.log_nonneg (by have h := primeProfileWeight_nonneg (p : Nat); linarith))) ?_
  calc
    _ <= (Finset.Ioc N M).sum (fun _ => 1 / (N : Real)) := by
      have hTarget : S.image (fun p : Nat.Primes => (p : Nat)) <= Finset.Ioc N M := by
        intro n hn
        choose p hp using Finset.mem_image.mp hn
        rw [<- hp.2]
        exact Finset.mem_Ioc.mpr (hRange p hp.1)
      exact Finset.sum_le_sum_of_injOn (fun p : Nat.Primes => (p : Nat))
        Nat.Primes.coe_nat_injective.injOn hTarget
        hTerm (fun _ _ _ => by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      rw [Nat.cast_sub hNM]
      ring

private theorem exp_sub_le_right_derivative (u v : Real) :
    Real.exp u - Real.exp v <= Real.exp u * (u - v) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (v - u)) (Real.exp_nonneg u)
  rw [<- Real.exp_add, show u + (v - u) = v by ring] at h
  nlinarith

theorem primeProductClock_increment_le_log_clocks (N M : Nat) (hN : 1 <= N) (hNM : N <= M) :
    0 <= nicolasPrimeProductClock (M : Real) - nicolasPrimeProductClock (N : Real) /\
      nicolasPrimeProductClock (M : Real) - nicolasPrimeProductClock (N : Real) <=
        nicolasPrimeProductClock (M : Real) * Real.log (nicolasPrimeProductClock (M : Real)) *
          (((M : Real) - (N : Real)) / (N : Real)) := by
  let B := primePrefixLogSum
  let gamma := Real.eulerMascheroniConstant
  have hId (j : Nat) : nicolasPrimeProductClock (j : Real) = Real.exp (Real.exp (B j - gamma)) :=
    nicolasPrimeProductClock_nat_eq_prefix_clock j
  have hB := primePrefixLogSum_increment_bounds N M hN hNM
  have hMono : nicolasPrimeProductClock (N : Real) <= nicolasPrimeProductClock (M : Real) := by
    rw [hId N, hId M]
    exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by dsimp [B]; linarith [hB.1]))
  refine And.intro (sub_nonneg.mpr hMono) ?_
  have hOuter := exp_sub_le_right_derivative (Real.exp (B M - gamma)) (Real.exp (B N - gamma))
  have hInner := exp_sub_le_right_derivative (B M - gamma) (B N - gamma)
  have hUpper : nicolasPrimeProductClock (M : Real) - nicolasPrimeProductClock (N : Real) <=
      nicolasPrimeProductClock (M : Real) * Real.log (nicolasPrimeProductClock (M : Real)) *
        (B M - B N) := by
    rw [hId N, hId M, Real.log_exp]
    have hm := mul_le_mul_of_nonneg_left hInner (Real.exp_nonneg (Real.exp (B M - gamma)))
    nlinarith [hOuter]
  have hPos : 0 <= nicolasPrimeProductClock (M : Real) *
      Real.log (nicolasPrimeProductClock (M : Real)) := by
    rw [hId M, Real.log_exp]
    positivity
  exact hUpper.trans (mul_le_mul_of_nonneg_left hB.2 hPos)

theorem eventually_primeProductClock_increment_bound :
    exists N0 : Nat, 2 <= N0 /\ forall N M : Nat, N0 <= N -> N <= M -> M <= 2 * N ->
      0 <= nicolasPrimeProductClock (M : Real) - nicolasPrimeProductClock (N : Real) /\
      nicolasPrimeProductClock (M : Real) - nicolasPrimeProductClock (N : Real) <=
        8 * ((M : Real) - (N : Real)) * Real.log (M : Real) := by
  have hC := (tendsto_nicolasPrimeProductClock_div_self.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : Nat => (N : Real)) atTop atTop)).eventually_lt_const
      (by norm_num : (1 : Real) < 2)
  choose N1 hN1 using hC.exists_forall_of_atTop
  refine Exists.intro (max N1 2) (And.intro (le_max_right _ _) ?_)
  intro N M hN hNM hMN
  have hn2 : 2 <= N := (le_max_right _ _).trans hN
  have hm2 : 2 <= M := hn2.trans hNM
  have hn0 : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hm0 : (0 : Real) < M := by exact_mod_cast (show 0 < M by omega)
  have hl : 0 < Real.log (M : Real) := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hCM := hN1 M (((le_max_left _ _).trans hN).trans hNM)
  change nicolasPrimeProductClock (M : Real) / (M : Real) < 2 at hCM
  have hCUpper : nicolasPrimeProductClock (M : Real) <= 2 * (M : Real) := by
    have h := mul_lt_mul_of_pos_right hCM hm0
    have hid : nicolasPrimeProductClock (M : Real) / (M : Real) * M =
        nicolasPrimeProductClock (M : Real) := by field_simp
    rw [hid] at h
    exact h.le
  have hCPos : 0 < nicolasPrimeProductClock (M : Real) := Real.exp_pos _
  have hLogPos : 0 < Real.log (nicolasPrimeProductClock (M : Real)) := by
    rw [nicolasPrimeProductClock_nat_eq_prefix_clock, Real.log_exp]
    positivity
  have hLogUpper : Real.log (nicolasPrimeProductClock (M : Real)) <= 2 * Real.log (M : Real) := by
    have h := Real.log_le_log hCPos hCUpper
    rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hm0.ne'] at h
    have h2 := Real.log_le_log (by norm_num : (0 : Real) < 2)
      (show (2 : Real) <= M by exact_mod_cast hm2)
    linarith
  have hDiff := primeProductClock_increment_le_log_clocks N M (by omega) hNM
  refine And.intro hDiff.1 ?_
  have hDelta : 0 <= (M : Real) - (N : Real) := sub_nonneg.mpr (by exact_mod_cast hNM)
  have hMNR : (M : Real) <= 2 * (N : Real) := by exact_mod_cast hMN
  have hCoeff := mul_le_mul hCUpper hLogUpper hLogPos.le (by positivity)
  calc
    _ <= nicolasPrimeProductClock (M : Real) * Real.log (nicolasPrimeProductClock (M : Real)) *
        (((M : Real) - (N : Real)) / (N : Real)) := hDiff.2
    _ <= ((2 * (M : Real)) * (2 * Real.log (M : Real))) *
        (((M : Real) - (N : Real)) / (N : Real)) :=
      mul_le_mul_of_nonneg_right hCoeff (div_nonneg hDelta hn0.le)
    _ = (4 * ((M : Real) - (N : Real)) * Real.log (M : Real)) * ((M : Real) / (N : Real)) := by ring
    _ <= (4 * ((M : Real) - (N : Real)) * Real.log (M : Real)) * 2 :=
      mul_le_mul_of_nonneg_left (by
        have h := div_le_div_of_nonneg_right hMNR hn0.le
        have hid : (2 * (N : Real)) / (N : Real) = 2 := by field_simp
        rwa [hid] at h) (by positivity)
    _ = _ := by ring

end PrimeFactorOscillations
