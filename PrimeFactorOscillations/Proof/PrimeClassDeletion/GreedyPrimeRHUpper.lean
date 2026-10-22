/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasLogDegreeLocalization
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeRealCutoffs

/-!
# The RH theta estimate controls the actual greedy deletion count

The entire initial range is retained in one fixed nonnegative theta
constant. The native record bound controls all later prime errors.
No theta estimate is assumed beyond the maintained RH provider.
-/

set_option autoImplicit false
set_option Elab.async false

open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem primeClassPrefix_count_mul_log_two_le_theta (P : Set Nat) (X : Nat) :
    ((primeClassPrefix P X).card : Real) * Real.log 2 <= primeClassTheta P X := by
  classical
  unfold primeClassTheta
  calc
    _ = (primeClassPrefix P X).sum (fun _ => Real.log (2 : Real)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ <= _ := by
      apply Finset.sum_le_sum
      intro p hp
      have hPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
      exact Real.log_le_log (by norm_num) (Nat.cast_le.mpr hPrime.two_le)

theorem greedyDeletedPrimeClass_RH_count_mass_bound (hRH : RiemannHypothesis) :
    Exists fun A : Real => And (0 <= A) (Exists fun C : Real => And (0 < C)
      (forall X : Nat, 2 <= X ->
        ((primeClassPrefix greedyDeletedPrimeClass X).card : Real) * Real.log 2 <=
          A + C * Real.sqrt (X : Real) * (Real.log (X : Real)) ^ 2 +
            Real.log (X : Real))) := by
  choose C hC hTheta using
    PrimeFactorOscillations.exists_nicolasThetaError_le_sqrt_log_sq hRH
  let T : Real := max 4 (2 * Real.exp 1)
  let A : Real := Chebyshev.theta T
  have hA : 0 <= A := Chebyshev.theta_nonneg T
  have hRecord (X : Nat) :
      greedyPrimeRegulator X <=
        A + C * Real.sqrt (X : Real) * (Real.log (X : Real)) ^ 2 := by
    apply (greedyPrimeRegulator_le_iff X _).mpr
    refine And.intro (by positivity) ?_
    intro p hp hpX
    rw [primeClassTheta_univ_eq_chebyshev]
    have hp0 : (0 : Real) <= (p : Real) := Nat.cast_nonneg p
    have hpPos : (0 : Real) < (p : Real) := Nat.cast_pos.mpr hp.pos
    have hpTwo : (2 : Real) <= (p : Real) := Nat.cast_le.mpr hp.two_le
    have hpXReal : (p : Real) <= (X : Real) := Nat.cast_le.mpr hpX
    by_cases hSmall : (p : Real) < T
    case pos =>
      have hMono := Chebyshev.theta_mono hSmall.le
      have hRest : 0 <= C * Real.sqrt (X : Real) * (Real.log (X : Real)) ^ 2 := by
        positivity
      change Chebyshev.theta (p : Real) - (p : Real) <=
        Chebyshev.theta T + C * Real.sqrt (X : Real) * (Real.log (X : Real)) ^ 2
      linarith only [hMono, hp0, hRest]
    case neg =>
      have hT : T <= (p : Real) := le_of_not_gt hSmall
      have hFour : (4 : Real) <= (p : Real) :=
        (le_max_left 4 (2 * Real.exp 1)).trans hT
      have hExp : 2 * Real.exp 1 <= (p : Real) :=
        (le_max_right 4 (2 * Real.exp 1)).trans hT
      have hLog : 1 <= Real.log ((p : Real) / 2) := by
        have h := Real.log_le_log (Real.exp_pos 1)
          (show Real.exp 1 <= (p : Real) / 2 by linarith only [hExp])
        simpa only [Real.log_exp] using h
      have hErr := (le_abs_self _).trans (hTheta (p : Real) hFour hLog)
      have hLogP : 0 <= Real.log (p : Real) :=
        Real.log_nonneg (by linarith only [hpTwo])
      have hLogPX : Real.log (p : Real) <= Real.log (X : Real) :=
        Real.log_le_log hpPos hpXReal
      have hLogSq : (Real.log (p : Real)) ^ 2 <= (Real.log (X : Real)) ^ 2 := by
        have hProduct := mul_nonneg (sub_nonneg.mpr hLogPX)
          (show 0 <= Real.log (X : Real) + Real.log (p : Real) by linarith only [hLogP, hLogPX])
        nlinarith only [hProduct]
      have hProduct := mul_le_mul (Real.sqrt_le_sqrt hpXReal) hLogSq
        (sq_nonneg (Real.log (p : Real))) (Real.sqrt_nonneg (X : Real))
      have hScaled := mul_le_mul_of_nonneg_left hProduct hC.le
      linarith only [hErr, hScaled, hA]
  refine Exists.intro A (And.intro hA (Exists.intro C (And.intro hC ?_)))
  intro X hX
  have hMass := (greedyDeletedPrimeClass_record_bounds X hX).2
  have hCount := primeClassPrefix_count_mul_log_two_le_theta greedyDeletedPrimeClass X
  have hReg := hRecord X
  linarith only [hCount, hMass, hReg]

end PrimeFactorOscillations.PrimeClassDeletion
