/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.ConditionalLocation.LastAscentSandwich
import PrimeFactorOscillations.Helpers.PrimePrefixClockStability

/-!
# A square-root-scale clock error envelope

The local-coverage sandwich and exact clock increments give a vanishing
normalized error with explicit constants.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter
open PrimeFactorUnimodality

private theorem gapCoverageLength_le_eighth (x : Real) (hx : 64 <= x)
    (hl : 1 <= Real.log x) : gapCoverageLength x <= x / 8 := by
  have hs := Real.sqrt_nonneg x
  have hsq := Real.sq_sqrt (show 0 <= x by linarith)
  have hs8 : 8 <= Real.sqrt x := by nlinarith
  have hsx : Real.sqrt x <= x / 8 := by nlinarith
  exact (div_le_self hs (by nlinarith : 1 <= (Real.log x) ^ (2 : Nat))).trans hsx

/-- A deterministic error envelope on the actual square-root scale. -/
theorem exists_last_ascent_clock_error_envelope :
    exists N0 : Nat, 2 <= N0 /\ forall P V : Nat,
      N0 <= P - 1 -> 64 <= V -> P <= V ->
      4 <= Real.log (V : Real) ->
      (V : Real) - 2 * gapCoverageLength V <= P ->
      forall T M : Real, 0 <= M ->
      abs (T - nicolasPrimeProductClock (V - 1 : Nat)) <= M * Real.log (V - 1 : Nat) ->
      abs ((T - nicolasPrimeProductClock (P - 1 : Nat)) / Real.sqrt P) <=
        2 * M * Real.log V / Real.sqrt V + 32 / Real.log V := by
  choose N0 hN0 hIncrement using eventually_primeProductClock_increment_bound
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro P V hPN hV hPV hl hclose T M hM hT
  have hP3 : 3 <= P := by omega
  have hP0 : (0 : Real) < P := by exact_mod_cast (show 0 < P by omega)
  have hV0 : (0 : Real) < V := by exact_mod_cast (show 0 < V by omega)
  have hVR : (64 : Real) <= V := by exact_mod_cast hV
  have hsmall := gapCoverageLength_le_eighth (V : Real) hVR (by linarith)
  have hPbig : 3 * (V : Real) / 4 <= P := by linarith
  have hPVReal : (P : Real) <= V := by exact_mod_cast hPV
  have hVcast : ((V - 1 : Nat) : Real) = (V : Real) - 1 := by
    rw [Nat.cast_sub (show 1 <= V by omega), Nat.cast_one]
  have hPcast : ((P - 1 : Nat) : Real) = (P : Real) - 1 := by
    rw [Nat.cast_sub (show 1 <= P by omega), Nat.cast_one]
  have hDouble : V - 1 <= 2 * (P - 1) := by
    have hReal : ((V - 1 : Nat) : Real) <= 2 * ((P - 1 : Nat) : Real) := by
      rw [hVcast, hPcast]
      linarith
    exact_mod_cast hReal
  have hInc := hIncrement (P - 1) (V - 1) hPN (Nat.sub_le_sub_right hPV 1) hDouble
  have hLog : 0 < Real.log (V : Real) := by linarith
  have hLogN : Real.log (V - 1 : Nat) <= Real.log V := by
    apply Real.log_le_log
    . rw [hVcast]; linarith
    . rw [hVcast]; linarith
  have hDistance : 0 <= (V : Real) - P := sub_nonneg.mpr hPVReal
  have hGapBound : nicolasPrimeProductClock (V - 1 : Nat) -
      nicolasPrimeProductClock (P - 1 : Nat) <= 16 * Real.sqrt V / Real.log V := by
    calc
      _ <= 8 * (((V - 1 : Nat) : Real) - ((P - 1 : Nat) : Real)) *
          Real.log (V - 1 : Nat) := hInc.2
      _ = 8 * ((V : Real) - P) * Real.log (V - 1 : Nat) := by rw [hVcast, hPcast]; ring
      _ <= 8 * ((V : Real) - P) * Real.log V :=
        mul_le_mul_of_nonneg_left hLogN (by positivity)
      _ <= 8 * (2 * gapCoverageLength V) * Real.log V :=
        mul_le_mul_of_nonneg_right (by linarith : 8 * ((V : Real) - P) <= 8 * (2 * gapCoverageLength V)) hLog.le
      _ = _ := by dsimp [gapCoverageLength]; field_simp; ring
  have hAll : abs (T - nicolasPrimeProductClock (P - 1 : Nat)) <=
      M * Real.log V + 16 * Real.sqrt V / Real.log V := by
    have htriangle := abs_add_le (T - nicolasPrimeProductClock (V - 1 : Nat))
      (nicolasPrimeProductClock (V - 1 : Nat) - nicolasPrimeProductClock (P - 1 : Nat))
    rw [sub_add_sub_cancel, abs_of_nonneg hInc.1] at htriangle
    have hT' := hT.trans (mul_le_mul_of_nonneg_left hLogN hM)
    linarith
  have hrootP : 0 < Real.sqrt (P : Real) := Real.sqrt_pos.mpr hP0
  have hrootV : 0 < Real.sqrt (V : Real) := Real.sqrt_pos.mpr hV0
  have hrootCompare : Real.sqrt V / 2 <= Real.sqrt P := by
    nlinarith [Real.sq_sqrt hP0.le, Real.sq_sqrt hV0.le]
  rw [abs_div, abs_of_pos hrootP]
  calc
    _ <= (M * Real.log V + 16 * Real.sqrt V / Real.log V) / Real.sqrt P :=
      div_le_div_of_nonneg_right hAll hrootP.le
    _ <= (M * Real.log V + 16 * Real.sqrt V / Real.log V) / (Real.sqrt V / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hrootCompare
    _ = _ := by field_simp; ring

end PrimeFactorOscillations
