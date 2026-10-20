/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Ring

/-!
# DepletedMobius

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.DepletedMobius

def SupportedOn (h n : Nat) : Prop :=
  Not (n = 0) /\ forall p : Nat, Nat.Prime p -> Dvd.dvd p n -> Dvd.dvd p h

theorem supported_one (h : Nat) : SupportedOn h 1 := by
  refine And.intro Nat.one_ne_zero ?_
  intro p hp hd
  exact False.elim (hp.ne_one (Nat.dvd_one.mp hd))

theorem supported_mul (h m n : Nat) :
    SupportedOn h (m * n) <-> SupportedOn h m /\ SupportedOn h n := by
  constructor
  . intro hs
    have hm : Not (m = 0) := by
      intro hz
      exact hs.1 (by simp [hz])
    have hn : Not (n = 0) := by
      intro hz
      exact hs.1 (by simp [hz])
    exact And.intro
      (And.intro hm (fun p hp hd => hs.2 p hp (dvd_mul_of_dvd_left hd n)))
      (And.intro hn (fun p hp hd => hs.2 p hp (dvd_mul_of_dvd_right hd m)))
  . intro hs
    refine And.intro (mul_ne_zero hs.1.1 hs.2.1) ?_
    intro p hp hd
    rcases hp.dvd_mul.mp hd with hm | hn
    . exact hs.1.2 p hp hm
    . exact hs.2.2 p hp hn

theorem supported_prime_power (h : Nat) {p k : Nat} (hp : Nat.Prime p) :
    SupportedOn h (p ^ k) <-> k = 0 \/ Dvd.dvd p h := by
  constructor
  . intro hs
    by_cases hk : k = 0
    . exact Or.inl hk
    . exact Or.inr (hs.2 p hp (dvd_pow_self p hk))
  . intro hs
    rcases hs with hk | hph
    . simpa only [hk, pow_zero] using supported_one h
    . refine And.intro (pow_ne_zero k hp.ne_zero) ?_
      intro q hq hd
      rcases (Nat.dvd_prime hp).mp (hq.dvd_of_dvd_pow hd) with hq1 | hqp
      . exact False.elim (hq.ne_one hq1)
      . simpa only [hqp] using hph

def smoothIndicator (h : Nat) : ArithmeticFunction Int where
  toFun n := if SupportedOn h n then 1 else 0
  map_zero' := by simp [SupportedOn]

def maskedMobius (h : Nat) : ArithmeticFunction Int where
  toFun n := if n.Coprime h then ArithmeticFunction.moebius n else 0
  map_zero' := by simp

theorem smoothIndicator_multiplicative (h : Nat) :
    (smoothIndicator h).IsMultiplicative := by
  constructor
  . simp [smoothIndicator, supported_one]
  . intro m n _
    by_cases hm : SupportedOn h m
    <;> by_cases hn : SupportedOn h n
    <;> simp [smoothIndicator, supported_mul, hm, hn]

theorem maskedMobius_multiplicative (h : Nat) :
    (maskedMobius h).IsMultiplicative := by
  constructor
  . simp [maskedMobius]
  . intro m n hmn
    have hmu := ArithmeticFunction.isMultiplicative_moebius.2 hmn
    change (if (m * n).Coprime h then ArithmeticFunction.moebius (m * n) else 0) =
      (if m.Coprime h then ArithmeticFunction.moebius m else 0) *
        (if n.Coprime h then ArithmeticFunction.moebius n else 0)
    by_cases hm : m.Coprime h
    . by_cases hn : n.Coprime h
      . rw [ite_eq_left (Nat.coprime_mul_iff_left.mpr (And.intro hm hn)),
          ite_eq_left hm, ite_eq_left hn]
        exact hmu
      . rw [ite_eq_right (fun hc => hn (Nat.coprime_mul_iff_left.mp hc).2),
          ite_eq_left hm, ite_eq_right hn, mul_zero]
    . rw [ite_eq_right (fun hc => hm (Nat.coprime_mul_iff_left.mp hc).1),
        ite_eq_right hm, zero_mul]

theorem masked_prime_power_zero (h : Nat) {p j : Nat} (hp : Nat.Prime p)
    (hph : Dvd.dvd p h) (hj : Not (j = 0)) : maskedMobius h (p ^ j) = 0 := by
  have hnc : Not ((p ^ j).Coprime h) := by
    intro hc
    exact (hp.coprime_iff_not_dvd.mp (hc.of_dvd_left (dvd_pow_self p hj))) hph
  simp [maskedMobius, hnc]

theorem masked_zeta_eq_smooth (h : Nat) :
    maskedMobius h * (ArithmeticFunction.zeta : ArithmeticFunction Int) =
      smoothIndicator h := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((maskedMobius_multiplicative h).mul ArithmeticFunction.isMultiplicative_zeta.natCast)
    _ (smoothIndicator_multiplicative h)).mpr
  intro p k hp
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  by_cases hph : Dvd.dvd p h
  . rw [Nat.divisors_prime_pow hp, Finset.sum_map]
    have he : (Finset.range (k + 1)).sum (fun j => maskedMobius h (p ^ j)) = 1 := by
      calc
        _ = maskedMobius h (p ^ 0) := by
          apply Finset.sum_eq_single 0
          . intro j _ hj
            exact masked_prime_power_zero h hp hph hj
          . intro hzero
            exact False.elim (hzero (Finset.mem_range.mpr (Nat.zero_lt_succ k)))
        _ = 1 := by simp [maskedMobius]
    change (Finset.range (k + 1)).sum (fun j => maskedMobius h (p ^ j)) =
      (if SupportedOn h (p ^ k) then 1 else 0)
    rw [ite_eq_left ((supported_prime_power h hp).mpr (Or.inr hph))]
    exact he
  . have hc (j : Nat) : (p ^ j).Coprime h :=
      (hp.coprime_iff_not_dvd.mpr hph).pow_left j
    have he :
        (p ^ k).divisors.sum (fun d => maskedMobius h d) =
          (p ^ k).divisors.sum (fun d => ArithmeticFunction.moebius d) := by
      rw [Nat.divisors_prime_pow hp, Finset.sum_map, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro j _
      simp [maskedMobius, hc j]
    rw [he, <- ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
    simp [smoothIndicator, supported_prime_power h hp, hph, hp.ne_one]

theorem smooth_moebius_eq_masked (h : Nat) :
    smoothIndicator h * ArithmeticFunction.moebius = maskedMobius h := by
  rw [<- masked_zeta_eq_smooth h, mul_assoc,
    ArithmeticFunction.coe_zeta_mul_moebius, mul_one]

theorem divisor_coefficient_identity (h n : Nat) :
    (if n.Coprime h then ArithmeticFunction.moebius n else 0) =
      n.divisorsAntidiagonal.sum (fun x =>
        (if SupportedOn h x.1 then (1 : Int) else 0) *
          ArithmeticFunction.moebius x.2) := by
  have he := DFunLike.congr_fun (smooth_moebius_eq_masked h) n
  rw [ArithmeticFunction.mul_apply] at he
  exact he.symm

def twist {R : Type*} [Ring R] (eta : Nat -> R)
    (f : ArithmeticFunction Int) : ArithmeticFunction R where
  toFun n := (f n : R) * eta n
  map_zero' := by simp

theorem twist_mul {R : Type*} [CommRing R] (eta : Nat -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n)
    (f g : ArithmeticFunction Int) :
    twist eta (f * g) = twist eta f * twist eta g := by
  ext n
  change (((f * g) n : Int) : R) * eta n =
    (twist eta f * twist eta g) n
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    Int.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hn : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
  change ((f x.1 * g x.2 : Int) : R) * eta n =
    ((f x.1 : R) * eta x.1) * ((g x.2 : R) * eta x.2)
  rw [Int.cast_mul, <- hn, heta]
  ring

theorem twisted_mask_identity {R : Type*} [CommRing R] (h : Nat) (eta : Nat -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n) :
    twist eta (maskedMobius h) =
      twist eta (smoothIndicator h) * twist eta ArithmeticFunction.moebius := by
  rw [<- twist_mul eta heta, smooth_moebius_eq_masked]

def mertensPrefix {R : Type*} [Ring R] (eta : Nat -> R) (N : Nat) : R :=
  (Finset.Ioc 0 N).sum (fun n => (ArithmeticFunction.moebius n : R) * eta n)

def depletedPrefix {R : Type*} [Ring R] (h : Nat) (eta : Nat -> R) (N : Nat) : R :=
  (Finset.Ioc 0 N).sum (fun n =>
    if n.Coprime h then (ArithmeticFunction.moebius n : R) * eta n else 0)

theorem prefix_depletion_identity {R : Type*} [CommRing R]
    (h : Nat) (eta : Nat -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n) (N : Nat) :
    depletedPrefix h eta N = (Finset.Ioc 0 N).sum (fun d =>
      if SupportedOn h d then eta d * mertensPrefix eta (N / d) else 0) := by
  have hprefix : depletedPrefix h eta N =
      (Finset.Ioc 0 N).sum (fun n => twist eta (maskedMobius h) n) := by
    apply Finset.sum_congr rfl
    intro n _
    by_cases hc : n.Coprime h
    <;> simp [twist, maskedMobius, hc]
  rw [hprefix, twisted_mask_identity h eta heta,
    ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro d _
  change ((smoothIndicator h d : Int) : R) * eta d *
    mertensPrefix eta (N / d) =
      if SupportedOn h d then eta d * mertensPrefix eta (N / d) else 0
  by_cases hd : SupportedOn h d
  <;> simp [smoothIndicator, hd]

end PrimeFactorOscillations.DepletedMobius
