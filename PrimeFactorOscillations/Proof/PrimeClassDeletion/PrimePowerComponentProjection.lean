/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.ComponentEmpiricalStatistics

/-!
# Exact consistency of finite-prime component laws

Component projections compose. Their empirical laws agree exactly, and
the complete finite l1 estimates pass this identity to the reference laws.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

theorem finitePrimePowerComponent_subprojection
    (s t : Finset Nat)
    (hprime : forall p : Nat, Membership.mem t p -> Nat.Prime p)
    (hst : forall p : Nat, Membership.mem s p -> Membership.mem t p) (m : Nat) :
    finitePrimePowerComponent s (finitePrimePowerComponent t m) =
      finitePrimePowerComponent s m := by
  classical
  have hf : (m.factorization.filter (fun p => Membership.mem t p)).filter
      (fun p => Membership.mem s p) =
        m.factorization.filter (fun p => Membership.mem s p) := by
    apply Finsupp.ext
    intro p
    simp only [Finsupp.filter_apply]
    by_cases hp : Membership.mem s p
    case pos => simp only [ite_eq_left hp, ite_eq_left (hst p hp)]
    case neg => simp only [ite_eq_right hp]
  change ((finitePrimePowerComponent t m).factorization.filter
    (fun p => Membership.mem s p)).prod (fun p k => p ^ k) =
      (m.factorization.filter (fun p => Membership.mem s p)).prod (fun p k => p ^ k)
  rw [finitePrimePowerComponent_factorization t hprime m, hf]

theorem literalPrimePowerComponentProbability_subprojection
    (s t : Finset Nat)
    (hprime : forall p : Nat, Membership.mem t p -> Nat.Prime p)
    (hst : forall p : Nat, Membership.mem s p -> Membership.mem t p) (N b : Nat) :
    componentStatisticMass (finitePrimePowerComponent s)
      (literalPrimePowerComponentProbability t N) b =
        literalPrimePowerComponentProbability s N b := by
  classical
  have heq : literalPrimePowerComponentProbability t N =
      (fun a => (Finset.Icc 1 N).sum (fun m =>
        if finitePrimePowerComponent t m = a then 1 / (N : Real) else 0)) :=
    funext (literalPrimePowerComponentProbability_eq_empirical t N)
  rw [heq, componentStatisticMass_empirical,
    literalPrimePowerComponentProbability_eq_empirical s N b]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hb : finitePrimePowerComponent s m = b
  case pos =>
    simp only [finitePrimePowerComponent_subprojection s t hprime hst m, ite_eq_left hb]
  case neg =>
    simp only [finitePrimePowerComponent_subprojection s t hprime hst m, ite_eq_right hb]

private theorem finite_pushed_probability_tendsto {B : Type*}
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (f : Nat -> B) (b : B) :
    Tendsto (fun N : Nat => componentStatisticMass f
      (literalPrimePowerComponentProbability s N) b) atTop
        (nhds (componentStatisticMass f (finitePrimePowerReference s) b)) := by
  classical
  let C := s.prod (fun p => (1 + (p : Real) ^ (-(1 / 2 : Real))) /
    (1 - (p : Real) ^ (-(1 / 2 : Real))))
  have hp := (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : Real))).comp
    (tendsto_natCast_atTop_atTop (R := Real))
  have hlimit : Tendsto (fun N : Nat => (N : Real) ^ (-(1 / 2 : Real)) * C)
      atTop (nhds 0) := by
    simpa only [Function.comp_apply, zero_mul] using hp.mul_const C
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have he : Filter.Eventually
      (fun N : Nat => (N : Real) ^ (-(1 / 2 : Real)) * C < epsilon) atTop :=
    (tendsto_order.mp hlimit).2 epsilon hepsilon
  filter_upwards [eventually_ge_atTop 1, he] with N hN hsmall
  have hNpos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hsample := literalPrimePowerComponentProbability_hasSum_one s hprime N hNpos
  have href := finitePrimePowerReference_hasSum_one s hprime
  have herror := literalPrimePowerComponentProbability_full_l1_error
    s hprime N hNpos (1 / 2) (by norm_num) (by norm_num)
  have hcontract := componentStatisticMass_l1_contraction f
    (literalPrimePowerComponentProbability s N) (finitePrimePowerReference s)
    hsample.summable href.summable herror.1
  have hpoint : abs (componentStatisticMass f
      (literalPrimePowerComponentProbability s N) b -
        componentStatisticMass f (finitePrimePowerReference s) b) <=
      tsum (fun a => abs (literalPrimePowerComponentProbability s N a -
        finitePrimePowerReference s a)) := by
    calc
      _ = ({b} : Finset B).sum (fun c => abs (componentStatisticMass f
          (literalPrimePowerComponentProbability s N) c -
            componentStatisticMass f (finitePrimePowerReference s) c)) := by
        rw [Finset.sum_singleton]
      _ <= tsum (fun c => abs (componentStatisticMass f
          (literalPrimePowerComponentProbability s N) c -
            componentStatisticMass f (finitePrimePowerReference s) c)) :=
        Summable.sum_le_tsum {b} (fun c _hc => abs_nonneg _) hcontract.1
      _ <= _ := hcontract.2
  have hhalf : (1 / 2 : Real) - 1 = -(1 / 2 : Real) := by norm_num
  have hbound : abs (componentStatisticMass f
      (literalPrimePowerComponentProbability s N) b -
        componentStatisticMass f (finitePrimePowerReference s) b) <=
      (N : Real) ^ (-(1 / 2 : Real)) * C := by
    exact hpoint.trans (by simpa only [hhalf, C] using herror.2)
  rw [Real.dist_eq]
  exact hbound.trans_lt hsmall

theorem finitePrimePowerReference_subprojection
    (s t : Finset Nat)
    (hprime : forall p : Nat, Membership.mem t p -> Nat.Prime p)
    (hst : forall p : Nat, Membership.mem s p -> Membership.mem t p) (b : Nat) :
    componentStatisticMass (finitePrimePowerComponent s) (finitePrimePowerReference t) b =
      finitePrimePowerReference s b := by
  have hs : forall p : Nat, Membership.mem s p -> Nat.Prime p :=
    fun p hp => hprime p (hst p hp)
  have hlarge := finite_pushed_probability_tendsto t hprime
    (finitePrimePowerComponent s) b
  have hsmall : Tendsto (fun N : Nat => literalPrimePowerComponentProbability s N b)
      atTop (nhds (finitePrimePowerReference s b)) := by
    simpa only [componentStatisticMass_id] using
      finite_pushed_probability_tendsto s hs (fun a : Nat => a) b
  have heq : (fun N : Nat => componentStatisticMass (finitePrimePowerComponent s)
      (literalPrimePowerComponentProbability t N) b) =
        (fun N : Nat => literalPrimePowerComponentProbability s N b) :=
    funext (fun N => literalPrimePowerComponentProbability_subprojection s t hprime hst N b)
  rw [heq] at hlarge
  exact tendsto_nhds_unique hlarge hsmall

end PrimeFactorOscillations.PrimeClassSampling
