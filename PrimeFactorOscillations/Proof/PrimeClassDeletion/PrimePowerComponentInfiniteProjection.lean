/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentProjection

/-!
# Every finite-prime marginal of the infinite component law

The full reciprocal supported series dominates every finite reference law.
Dominated convergence of each statistic fiber passes exact finite-prime
projective consistency to the infinite normalized reference.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

theorem finitePrimeComponentSurvival_le_one
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) :
    finitePrimeComponentSurvival s <= 1 := by
  classical
  unfold finitePrimeComponentSurvival
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hs : forall q : Nat, Membership.mem s q -> Nat.Prime q :=
        fun q hq => hprime q (Finset.mem_insert_of_mem hq)
      have hnonneg : 0 <= s.prod (fun q => 1 - 1 / (q : Real)) :=
        (finitePrimeComponentSurvival_pos s hs).le
      rw [Finset.prod_insert hp]
      have hfactor : 1 - 1 / (p : Real) <= 1 :=
        sub_le_self 1 (div_nonneg zero_le_one (Nat.cast_nonneg p))
      exact (mul_le_mul_of_nonneg_right hfactor hnonneg).trans
        (by simpa only [one_mul] using ih hs)

theorem finitePrimePowerReference_prefix_le_classWeight
    (P : Set Nat) (Y a : Nat) :
    finitePrimePowerReference (primeClassPrefix P Y) a <= classPrimePowerWeight P 1 a := by
  classical
  by_cases ha : primePowerSupportedOn (primeClassPrefix P Y) a
  case pos =>
    have hc : classPrimePowerSupported P a :=
      And.intro ha.1 (fun p hp => (Finset.mem_filter.mp (ha.2 p hp)).2.2)
    rw [finitePrimePowerReference, ite_eq_left ha,
      classPrimePowerWeight, ite_eq_left hc, Real.rpow_neg_one]
    simpa only [one_div] using
      div_le_div_of_nonneg_right
        (finitePrimeComponentSurvival_le_one (primeClassPrefix P Y)
          (primeClassPrefix_prime P Y)) (Nat.cast_nonneg a)
  case neg =>
    rw [finitePrimePowerReference, ite_eq_right ha]
    exact classPrimePowerWeight_nonneg P 1 a

theorem componentStatisticMass_finitePrefixReference_tendsto {B : Type*}
    (f : Nat -> B) (P : Set Nat)
    (hsum : Summable (classPowerWeight P 1)) (b : B) :
    Tendsto (fun Y : Nat =>
      componentStatisticMass f (finitePrimePowerReference (primeClassPrefix P Y)) b)
      atTop (nhds (componentStatisticMass f (classPrimePowerReference P) b)) := by
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun a : {a : Nat // f a = b} => classPrimePowerWeight P 1 a.val)
    ((classPrimePowerWeight_summable P 1 zero_lt_one hsum).subtype (fun a => f a = b)) ?_ ?_
  . intro a
    exact finitePrimePowerReference_prefix_tendsto P hsum a.val
  . apply Filter.Eventually.of_forall
    intro Y a
    have hn := finitePrimePowerReference_nonneg (primeClassPrefix P Y)
      (primeClassPrefix_prime P Y) a.val
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact finitePrimePowerReference_prefix_le_classWeight P Y a.val

theorem primeClassPrefix_eventually_contains
    (P : Set Nat) (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (hP : forall p : Nat, Membership.mem s p -> Membership.mem P p) :
    Filter.Eventually (fun Y : Nat => forall p : Nat,
      Membership.mem s p -> Membership.mem (primeClassPrefix P Y) p) atTop := by
  classical
  filter_upwards [eventually_ge_atTop (s.sup id)] with Y hY
  intro p hp
  have hbound : p <= s.sup id := Finset.le_sup (f := id) hp
  exact Finset.mem_filter.mpr (And.intro
    (Finset.mem_Icc.mpr (And.intro (hprime p hp).two_le (hbound.trans hY)))
    (And.intro (hprime p hp) (hP p hp)))

theorem classPrimePowerReference_subprojection
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1)) (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (hP : forall p : Nat, Membership.mem s p -> Membership.mem P p) (b : Nat) :
    componentStatisticMass (finitePrimePowerComponent s) (classPrimePowerReference P) b =
      finitePrimePowerReference s b := by
  have hlimit := componentStatisticMass_finitePrefixReference_tendsto
    (finitePrimePowerComponent s) P hsum b
  have he : Filter.Eventually (fun Y : Nat =>
      componentStatisticMass (finitePrimePowerComponent s)
        (finitePrimePowerReference (primeClassPrefix P Y)) b =
          finitePrimePowerReference s b) atTop := by
    filter_upwards [primeClassPrefix_eventually_contains P s hprime hP] with Y hY
    exact finitePrimePowerReference_subprojection s (primeClassPrefix P Y)
      (primeClassPrefix_prime P Y) hY b
  have hconst : Tendsto (fun Y : Nat =>
      componentStatisticMass (finitePrimePowerComponent s)
        (finitePrimePowerReference (primeClassPrefix P Y)) b)
      atTop (nhds (finitePrimePowerReference s b)) :=
    tendsto_const_nhds.congr' (he.mono (fun _Y h => h.symm))
  exact tendsto_nhds_unique hlimit hconst

end PrimeFactorOscillations.PrimeClassSampling
