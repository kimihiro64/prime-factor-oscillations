/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFStateWeights
import PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Ring.FiberCovariance

/-!
# One complete residue-projected lower bound for actual LPF states

The state weights remain exact. The positive residue projection and the joint
centered loss use the same finite interval and residue map. No energy estimate
or positive supply hypothesis is silently assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def oddInterval (M : Nat) : Finset Nat :=
  (Finset.Icc 1 (4 * M - 1)).filter (fun n => n % 2 = 1)

noncomputable def frontierIndicator (M n : Nat) : Real :=
  if M < Nat.largestPrimeFactor n then 1 else 0

noncomputable def residueProjection (S : Finset Nat) (M Q : Nat) : Real :=
  Finset.sum ((oddInterval M).image (fun n => n % Q)) (fun a =>
    Finset.fiberMean (oddInterval M) (fun n => n % Q)
      (fun n => (pairWeight S n : Real)) a *
      Finset.sum ((oddInterval M).filter (fun n => n % Q = a))
        (frontierIndicator M))

noncomputable def pairResidueEnergy (S : Finset Nat) (M Q : Nat) : Real :=
  Finset.sum (oddInterval M) (fun n =>
    ((pairWeight S n : Real) -
      Finset.fiberMean (oddInterval M) (fun m => m % Q)
        (fun m => (pairWeight S m : Real)) (n % Q)) ^ 2)

noncomputable def frontierResidueEnergy (M Q : Nat) : Real :=
  Finset.sum (oddInterval M) (fun n =>
    (frontierIndicator M n -
      Finset.fiberMean (oddInterval M) (fun m => m % Q)
        (frontierIndicator M) (n % Q)) ^ 2)

theorem pairResidueEnergy_nonneg (S : Finset Nat) (M Q : Nat) :
    0 <= pairResidueEnergy S M Q := Finset.sum_nonneg (fun n hn => sq_nonneg _)

theorem frontierResidueEnergy_nonneg (M Q : Nat) :
    0 <= frontierResidueEnergy M Q := Finset.sum_nonneg (fun n hn => sq_nonneg _)

theorem residue_projection_lower_bound (S : Finset Nat) (M Q : Nat)
    (hBound : forall p, Membership.mem S p -> p <= M) :
    residueProjection S M Q -
      Real.sqrt (pairResidueEnergy S M Q * frontierResidueEnergy M Q) <=
      (frontierCount S M : Real) := by
  have h := Finset.fiber_projection_sub_covariance_le_sum_mul
    (oddInterval M) (fun n => n % Q)
    (fun n => (pairWeight S n : Real)) (frontierIndicator M)
  have hCount : (frontierCount S M : Real) =
      Finset.sum ((Finset.Icc 1 (4 * M - 1)).filter (fun n => M < Nat.largestPrimeFactor n))
        (fun n => (pairWeight S n : Real)) := by
    exact_mod_cast frontierCount_eq_sum_pairWeight S M hBound
  have hSum : Finset.sum (oddInterval M)
      (fun n => (pairWeight S n : Real) * frontierIndicator M n) =
      (frontierCount S M : Real) := by
    rw [hCount]
    unfold oddInterval
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hOdd : n % 2 = 1
    next => simp [hOdd, frontierIndicator, mul_ite]
    next =>
      have hEven : n = 2 * (n / 2) := by omega
      have hWeight : pairWeight S n = 0 := by
        rw [hEven]
        exact pairWeight_even S (n / 2)
      simp [hOdd, hWeight]
  rw [hSum] at h
  exact h

theorem not_closed_of_residue_projection_surplus (S : Finset Nat) (M Q : Nat)
    (hBound : forall p, Membership.mem S p -> p <= M)
    (hSurplus : Real.sqrt (pairResidueEnergy S M Q * frontierResidueEnergy M Q) <
      residueProjection S M Q) : Not (step S = S) := by
  have hLower := residue_projection_lower_bound S M Q hBound
  have hPos : (0 : Real) < (frontierCount S M : Real) := by linarith
  have hNat : 0 < frontierCount S M := by exact_mod_cast hPos
  exact not_closed_of_frontierCount_pos S M hBound hNat

end PrimeFactorOscillations.LPF
