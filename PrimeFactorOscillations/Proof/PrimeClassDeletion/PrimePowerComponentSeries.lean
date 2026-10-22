/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentBudget

/-!
# Full supported series for prime-power component sampling

The complete l1 series, including all supported positive integers, is
summable and satisfies the exact finite-prime Euler budget.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

def primePowerSupportedOn (s : Finset Nat) (a : Nat) : Prop :=
  And (0 < a) (forall p : Nat,
    Membership.mem a.factorization.support p -> Membership.mem s p)

noncomputable def supportedPrimePowerWeight
    (s : Finset Nat) (sigma : Real) (a : Nat) : Real := by
  classical
  exact if primePowerSupportedOn s a then (a : Real) ^ (-sigma) else 0

noncomputable def supportedPrimePowerComponentError
    (s : Finset Nat) (N a : Nat) : Real := by
  classical
  exact if primePowerSupportedOn s a then
    abs (((primePowerComponentFiber s N a).card : Real) / (N : Real) -
      finitePrimeComponentSurvival s / (a : Real)) else 0

private theorem supported_weight_subsum
    (s t : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (sigma : Real) (hs : 0 < sigma) :
    t.sum (supportedPrimePowerWeight s sigma) <=
      s.prod (fun p => 1 / (1 - (p : Real) ^ (-sigma))) := by
  classical
  let u := t.filter (primePowerSupportedOn s)
  have hpositive (a : Nat) (ha : Membership.mem u a) : 0 < a :=
    (Finset.mem_filter.mp ha).2.1
  have hsupport (a : Nat) (ha : Membership.mem u a) :
      forall p : Nat, Membership.mem a.factorization.support p -> Membership.mem s p :=
    (Finset.mem_filter.mp ha).2.2
  have hsum : t.sum (supportedPrimePowerWeight s sigma) =
      u.sum (fun a => (a : Real) ^ (-sigma)) := by
    simp only [u, Finset.sum_filter]
    rfl
  rw [hsum]
  exact supported_primePower_finite_sum_le_euler s u hprime hpositive hsupport sigma hs

theorem supportedPrimePowerWeight_summable
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (sigma : Real) (hs : 0 < sigma) :
    Summable (supportedPrimePowerWeight s sigma) := by
  apply summable_of_sum_le
  case hf =>
    intro a
    unfold supportedPrimePowerWeight
    split_ifs
    case pos => exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    case neg => exact le_refl 0
  case h => exact fun t => supported_weight_subsum s t hprime sigma hs

theorem supportedPrimePowerWeight_tsum_le_euler
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (sigma : Real) (hs : 0 < sigma) :
    tsum (supportedPrimePowerWeight s sigma) <=
      s.prod (fun p => 1 / (1 - (p : Real) ^ (-sigma))) := by
  apply Real.tsum_le_of_sum_le
  case hf =>
    intro a
    unfold supportedPrimePowerWeight
    split_ifs
    case pos => exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    case neg => exact le_refl 0
  case h => exact fun t => supported_weight_subsum s t hprime sigma hs

private theorem supported_component_error_subsum
    (s t : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (N : Nat) (hN : 0 < N) (sigma : Real) (hs0 : 0 < sigma) (hs1 : sigma <= 1) :
    t.sum (supportedPrimePowerComponentError s N) <=
      (N : Real) ^ (sigma - 1) *
        s.prod (fun p => (1 + (p : Real) ^ (-sigma)) /
          (1 - (p : Real) ^ (-sigma))) := by
  classical
  let u := t.filter (primePowerSupportedOn s)
  have hpositive (a : Nat) (ha : Membership.mem u a) : 0 < a :=
    (Finset.mem_filter.mp ha).2.1
  have hsupport (a : Nat) (ha : Membership.mem u a) :
      forall p : Nat, Membership.mem a.factorization.support p -> Membership.mem s p :=
    (Finset.mem_filter.mp ha).2.2
  have hsum : t.sum (supportedPrimePowerComponentError s N) =
      u.sum (fun a => abs
        (((primePowerComponentFiber s N a).card : Real) / (N : Real) -
          finitePrimeComponentSurvival s / (a : Real))) := by
    simp only [u, Finset.sum_filter]
    rfl
  rw [hsum]
  exact primePowerComponentFiber_finite_l1_error_le
    s u hprime hpositive hsupport N hN sigma hs0 hs1

theorem supportedPrimePowerComponentError_summable
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (N : Nat) (hN : 0 < N) (sigma : Real) (hs0 : 0 < sigma) (hs1 : sigma <= 1) :
    Summable (supportedPrimePowerComponentError s N) := by
  apply summable_of_sum_le
  case hf =>
    intro a
    unfold supportedPrimePowerComponentError
    split_ifs
    case pos => exact abs_nonneg _
    case neg => exact le_refl 0
  case h => exact fun t =>
    supported_component_error_subsum s t hprime N hN sigma hs0 hs1

theorem supportedPrimePowerComponentError_tsum_le_euler
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (N : Nat) (hN : 0 < N) (sigma : Real) (hs0 : 0 < sigma) (hs1 : sigma <= 1) :
    tsum (supportedPrimePowerComponentError s N) <=
      (N : Real) ^ (sigma - 1) *
        s.prod (fun p => (1 + (p : Real) ^ (-sigma)) /
          (1 - (p : Real) ^ (-sigma))) := by
  apply Real.tsum_le_of_sum_le
  case hf =>
    intro a
    unfold supportedPrimePowerComponentError
    split_ifs
    case pos => exact abs_nonneg _
    case neg => exact le_refl 0
  case h => exact fun t =>
    supported_component_error_subsum s t hprime N hN sigma hs0 hs1

end PrimeFactorOscillations.PrimeClassSampling
