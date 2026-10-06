/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ConsecutiveRootProbability
import PrimeFactorOscillations.Helpers.PrimeAddedRootBudget
import PrimeFactorOscillations.Helpers.QuadraticPrimeCriterion

/-!
# Exact signed profile for a growing consecutive-root family

Identifies the full logarithmic error of the actual polynomial-plus-prime
local law with the Nicolas signal minus its explicit prime tail. When the
polynomial degree equals the cutoff, the normalized error tends to -1
unconditionally. This growing-degree sign does not assert an RH criterion.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter Robin1984

theorem consecutiveRootLaw_logFactor_tail (d : Nat) (hd : 1 <= d)
    (p : Nat.Primes) (hpd : d < (p : Nat)) :
    (consecutiveRootLaw d hd).logFactor 1 p =
      -Real.log (1 + ((d : Real) - 1) * (primeProfileWeight (p : Nat)) ^ 2) := by
  let P : Real := (p : Nat)
  let w : Real := primeProfileWeight (p : Nat)
  have hpR : 1 < P := by dsimp [P]; exact_mod_cast p.property.one_lt
  have hp0 : 0 < P := by linarith
  have hdR : (1 : Real) <= d := by exact_mod_cast hd
  have hEta : consecutiveRootProbability d (p : Nat) =
      (P - (d : Real)) / (P * (P - 1)) := by
    rw [consecutiveRootProbability_formula d (p : Nat) p.property, Nat.min_eq_left hpd.le]
  have hEtaLt : consecutiveRootProbability d (p : Nat) < 1 := by
    apply (consecutiveRootProbability_bounds d hd (p : Nat) p.property).2.trans_lt
    exact (div_lt_one hp0).mpr hpR
  have hEtaDen : 0 < 1 - (P - (d : Real)) / (P * (P - 1)) := by
    rw [<- hEta]
    linarith
  have hw : w = 1 / (P - 1) := by
    dsimp [w, primeProfileWeight, P]
    rw [Nat.cast_sub p.property.one_lt.le, Nat.cast_one]
  have ht : 0 < 1 + ((d : Real) - 1) * w ^ 2 := by positivity
  have hb : 0 < 1 + w := by
    have h := primeProfileWeight_nonneg (p : Nat)
    change 0 <= w at h
    linarith
  have hDen : 0 < P * (P - 1) - (P - (d : Real)) := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hpR)]
  have hDen' : Not (-(P * 2) + P ^ 2 + (d : Real) = 0) := by
    intro hz
    nlinarith only [hDen, hz]
  have hid : 1 + (consecutiveRootLaw d hd).weight p =
      (1 + w) / (1 + ((d : Real) - 1) * w ^ 2) := by
    rw [consecutiveRootLaw_weight, hEta, hw]
    rw [hw] at ht
    field_simp [hEtaDen.ne', hDen.ne', (sub_pos.mpr hpR).ne', hp0.ne', ht.ne']
    ring_nf
    have hInv : (-(P * 2) + P ^ 2 + (d : Real)) *
        Inv.inv (-(P * 2) + P ^ 2 + (d : Real)) = 1 := by
      simpa only [div_eq_mul_inv] using div_self hDen'
    have hMul := congrArg (fun t : Real => P * (P - 1) * t) hInv
    nlinarith only [hMul]
  unfold QuadraticPrimeLaw.logFactor
  rw [consecutiveRootLaw_nu]
  simp only [mul_one, one_mul]
  change Real.log (1 + (consecutiveRootLaw d hd).weight p) - Real.log (1 + w) = _
  rw [hid, Real.log_div hb.ne' ht.ne']
  ring

theorem consecutiveRootLaw_logError_exact (d : Nat) (hd : 1 <= d)
    (N : Nat) (hdN : d <= N) (hTheta : 1 < Chebyshev.theta (N : Real)) :
    (consecutiveRootLaw d hd).logError N 1 =
      nicolasLogMertensOscillation (N : Real) - primeAddedRootTail N ((d : Real) - 1) := by
  classical
  let law := consecutiveRootLaw d hd
  have hSum := @Summable.sum_add_tsum_subtype_compl Real Nat.Primes
    _ _ _ _ _ (law.logFactor 1) (law.summable_logFactor 1 (by norm_num))
    (primeProfilePrefixSet N)
  have hPredicate :
      (fun p : Nat.Primes => Not (Membership.mem (primeProfilePrefixSet N) p)) =
      (fun p : Nat.Primes => N < (p : Nat)) := by
    funext p
    apply propext
    exact (not_congr (mem_primeProfilePrefixSet p N)).trans not_le
  rw [hPredicate] at hSum
  have hRest : law.logProfile 1 - (primeProfilePrefixSet N).sum (law.logFactor 1) =
      tsum (fun p : {p : Nat.Primes // N < (p : Nat)} => law.logFactor 1 p.val) := by
    dsimp only [QuadraticPrimeLaw.logProfile]
    linarith only [hSum]
  have hTail : tsum (fun p : {p : Nat.Primes // N < (p : Nat)} => law.logFactor 1 p.val) =
      -primeAddedRootTail N ((d : Real) - 1) := by
    calc
      _ = tsum (fun p : {p : Nat.Primes // N < (p : Nat)} =>
          -Real.log (1 + ((d : Real) - 1) * (primeProfileWeight (p.val : Nat)) ^ 2)) := by
        apply tsum_congr
        intro p
        exact consecutiveRootLaw_logFactor_tail d hd p.val (lt_of_le_of_lt hdN p.property)
      _ = _ := by rw [tsum_neg]; rfl
  change law.logError N 1 = _
  rw [law.logError_eq_signal_add_tail N 1 hTheta, hRest, hTail]
  dsimp only [law]
  rw [consecutiveRootLaw_nu]
  ring

def consecutiveRootDiagonalLogError (N : Nat) : Real :=
  if hN : 1 <= N then (consecutiveRootLaw N hN).logError N 1 else 0

theorem tendsto_consecutiveRootDiagonalLogError_scaled :
    Tendsto (fun N : Nat => consecutiveRootDiagonalLogError N * Real.log N)
      atTop (nhds (-1)) := by
  apply tendsto_primeAddedRootSignedError_scaled.congr'
  filter_upwards [eventually_ge_atTop (1 : Nat),
    tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1] with N hN hTheta
  rw [consecutiveRootDiagonalLogError, dite_eq_left hN,
    consecutiveRootLaw_logError_exact N hN N le_rfl hTheta]
  rfl

theorem eventually_consecutiveRootDiagonalLogError_neg :
    Filter.Eventually (fun N : Nat => consecutiveRootDiagonalLogError N < 0) atTop := by
  filter_upwards [eventually_primeAddedRootSignedError_neg,
    eventually_ge_atTop (1 : Nat), tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1]
      with N hNeg hN hTheta
  rw [consecutiveRootDiagonalLogError, dite_eq_left hN,
    consecutiveRootLaw_logError_exact N hN N le_rfl hTheta]
  exact hNeg

end PrimeFactorOscillations
