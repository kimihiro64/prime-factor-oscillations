/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentSeries

/-!
# Literal integer components and the exact divisor fibers

Restricting the prime factorization defines the actual finite-prime
component. Its atoms agree with the signed counting fibers on their full
supported domain.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

def finitePrimePowerComponent (s : Finset Nat) (m : Nat) : Nat :=
  (m.factorization.filter (fun p => Membership.mem s p)).prod (fun p k => p ^ k)

theorem finitePrimePowerComponent_pos
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) (m : Nat) :
    0 < finitePrimePowerComponent s m := by
  unfold finitePrimePowerComponent Finsupp.prod
  apply Finset.prod_pos
  intro p hp
  have hpS : Membership.mem s p := by
    rw [Finsupp.support_filter] at hp
    exact (Finset.mem_filter.mp hp).2
  exact pow_pos (hprime p hpS).pos _

theorem finitePrimePowerComponent_factorization
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) (m : Nat) :
    (finitePrimePowerComponent s m).factorization =
      m.factorization.filter (fun p => Membership.mem s p) := by
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  rw [Finsupp.support_filter] at hp
  exact hprime p (Finset.mem_filter.mp hp).2

theorem finitePrimePowerComponent_supported
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) (m : Nat) :
    primePowerSupportedOn s (finitePrimePowerComponent s m) := by
  refine And.intro (finitePrimePowerComponent_pos s hprime m) ?_
  intro p hp
  rw [finitePrimePowerComponent_factorization s hprime m, Finsupp.support_filter] at hp
  exact (Finset.mem_filter.mp hp).2

theorem finitePrimePowerComponent_fiber_conditions
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (m : Nat) (hm : 0 < m) :
    And (Dvd.dvd (finitePrimePowerComponent s m) m)
      ((s.filter (fun p => Dvd.dvd p (m / finitePrimePowerComponent s m))).card = 0) := by
  classical
  let a := finitePrimePowerComponent s m
  have ha : 0 < a := finitePrimePowerComponent_pos s hprime m
  have hf : a.factorization =
      m.factorization.filter (fun p => Membership.mem s p) :=
    finitePrimePowerComponent_factorization s hprime m
  have hd : Dvd.dvd a m := by
    apply (Nat.factorization_le_iff_dvd (Nat.ne_of_gt ha) (Nat.ne_of_gt hm)).mp
    rw [hf]
    intro p
    rw [Finsupp.filter_apply]
    split_ifs
    case pos => exact le_rfl
    case neg => exact Nat.zero_le _
  refine And.intro hd ?_
  have hq : 0 < m / a := Nat.div_pos (Nat.le_of_dvd hm hd) ha
  have hnot (p : Nat) (hp : Membership.mem s p) : Not (Dvd.dvd p (m / a)) := by
    intro hpq
    have hval : (m / a).factorization p = 0 := by
      rw [Nat.factorization_div hd, Finsupp.tsub_apply, hf, Finsupp.filter_apply,
        ite_eq_left hp, Nat.sub_self]
    have hpos := (hprime p hp).factorization_pos_of_dvd (Nat.ne_of_gt hq) hpq
    rw [hval] at hpos
    exact Nat.not_lt_zero _ hpos
  apply Finset.card_eq_zero.mpr
  apply Finset.ext
  intro p
  constructor
  case mp =>
    intro hp
    have hdata := Finset.mem_filter.mp hp
    exact False.elim (hnot p hdata.1 hdata.2)
  case mpr =>
    intro hp
    simp at hp

theorem finitePrimePowerComponent_eq_of_fiber
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (m a : Nat) (hm : 0 < m) (ha : primePowerSupportedOn s a)
    (hd : Dvd.dvd a m)
    (hfree : (s.filter (fun p => Dvd.dvd p (m / a))).card = 0) :
    finitePrimePowerComponent s m = a := by
  classical
  have hq : 0 < m / a := Nat.div_pos (Nat.le_of_dvd hm hd) ha.1
  have hnot (p : Nat) (hp : Membership.mem s p) : Not (Dvd.dvd p (m / a)) := by
    intro hpq
    have hmem : Membership.mem (s.filter (fun p => Dvd.dvd p (m / a))) p :=
      Finset.mem_filter.mpr (And.intro hp hpq)
    have hempty := Finset.card_eq_zero.mp hfree
    rw [hempty] at hmem
    simp at hmem
  apply Nat.factorization_inj
    (Nat.ne_of_gt (finitePrimePowerComponent_pos s hprime m)) (Nat.ne_of_gt ha.1)
  apply Finsupp.ext
  intro p
  rw [finitePrimePowerComponent_factorization s hprime m, Finsupp.filter_apply]
  by_cases hp : Membership.mem s p
  case pos =>
    rw [ite_eq_left hp]
    have hzero : (m / a).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (hnot p hp)
    have hmul := congrArg (fun f : Finsupp Nat Nat => f p)
      (Nat.factorization_mul (Nat.ne_of_gt ha.1) (Nat.ne_of_gt hq))
    rw [Nat.mul_div_cancel' hd] at hmul
    simpa only [Finsupp.add_apply, hzero, add_zero] using hmul
  case neg =>
    rw [ite_eq_right hp]
    symm
    by_contra hval
    exact hp (ha.2 p (Finsupp.mem_support_iff.mpr hval))

theorem primePowerComponentFiber_eq_actual_fiber
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (N a : Nat) (ha : primePowerSupportedOn s a) :
    primePowerComponentFiber s N a =
      (Finset.Icc 1 N).filter (fun m => finitePrimePowerComponent s m = a) := by
  classical
  apply Finset.ext
  intro m
  simp only [primePowerComponentFiber, Finset.mem_filter]
  constructor
  case mp =>
    intro hm
    refine And.intro hm.1 ?_
    exact finitePrimePowerComponent_eq_of_fiber s hprime m a
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm.1).1)
      ha hm.2.1 hm.2.2
  case mpr =>
    intro hm
    refine And.intro hm.1 ?_
    have hconditions := finitePrimePowerComponent_fiber_conditions s hprime m
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm.1).1)
    simpa only [hm.2] using hconditions

end PrimeFactorOscillations.PrimeClassSampling
