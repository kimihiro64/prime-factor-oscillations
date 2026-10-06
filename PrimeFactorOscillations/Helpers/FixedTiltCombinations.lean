/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasTiltedCriterion

/-!
# Finite fixed-tilt combinations retain the same arithmetic signal

A finite weighted combination of tilted logarithms has leading term
(sum a_i*z_i)*F and a uniform inverse-cutoff remainder. If that coefficient
vanishes, the combination is bounded by C/N. This statement keeps a fixed
finite support and does not apply to growing or unrestricted tilt families.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Robin1984

theorem exists_fixed_tilt_combination_error
    {I : Type*} (s : Finset I) (a z : I -> Real)
    (hz : forall i, Membership.mem s i -> 0 <= z i) :
    exists C : Real, 0 <= C /\ forall N : Nat, 1 <= N ->
      1 < Chebyshev.theta (N : Real) ->
      abs (s.sum (fun i => a i * nicolasTiltedLog (z i) (N : Real)) -
        (s.sum (fun i => a i * z i)) * nicolasLogMertensOscillation (N : Real)) <= C / N := by
  classical
  let B := s.sum z
  have hB : 0 <= B := Finset.sum_nonneg hz
  choose K hK hError using exists_nicolasTiltedLog_nat_error B hB
  let C := (s.sum (fun i => abs (a i))) * K
  have hC : 0 <= C := mul_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hK
  refine Exists.intro C (And.intro hC ?_)
  intro N hN hTheta
  have hBound : forall i, Membership.mem s i ->
      abs (a i * (nicolasTiltedLog (z i) (N : Real) -
        z i * nicolasLogMertensOscillation (N : Real))) <= abs (a i) * (K / N) := by
    intro i hi
    have hzi : z i <= B := Finset.single_le_sum hz hi
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hError N hN hTheta (z i) (hz i hi) hzi) (abs_nonneg _)
  have hEq :
      s.sum (fun i => a i * (nicolasTiltedLog (z i) (N : Real) -
        z i * nicolasLogMertensOscillation (N : Real))) =
      s.sum (fun i => a i * nicolasTiltedLog (z i) (N : Real)) -
        (s.sum (fun i => a i * z i)) * nicolasLogMertensOscillation (N : Real) := by
    calc
      _ = s.sum (fun i => a i * nicolasTiltedLog (z i) (N : Real) -
        (a i * z i) * nicolasLogMertensOscillation (N : Real)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_mul]
  rw [<- hEq]
  calc
    _ <= s.sum (fun i => abs (a i * (nicolasTiltedLog (z i) (N : Real) -
        z i * nicolasLogMertensOscillation (N : Real)))) := Finset.abs_sum_le_sum_abs _ _
    _ <= s.sum (fun i => abs (a i) * (K / N)) := Finset.sum_le_sum hBound
    _ = C / N := by rw [<- Finset.sum_mul]; dsimp [C]; ring

theorem exists_fixed_tilt_combination_bound_of_signal_cancelled
    {I : Type*} (s : Finset I) (a z : I -> Real)
    (hz : forall i, Membership.mem s i -> 0 <= z i)
    (hcancel : s.sum (fun i => a i * z i) = 0) :
    exists C : Real, 0 <= C /\ forall N : Nat, 1 <= N ->
      1 < Chebyshev.theta (N : Real) ->
      abs (s.sum (fun i => a i * nicolasTiltedLog (z i) (N : Real))) <= C / N := by
  choose C hC hBound using exists_fixed_tilt_combination_error s a z hz
  refine Exists.intro C (And.intro hC ?_)
  intro N hN hTheta
  simpa only [hcancel, zero_mul, sub_zero] using hBound N hN hTheta

end PrimeFactorOscillations
