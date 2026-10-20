/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.DetectorPackets.DepletedMobius

/-!
# WeightedDivisorConvolution

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

theorem factors_mem_Ioc {a b n N : Nat} (hn : Membership.mem (Finset.Ioc 0 N) n)
    (hab : a * b = n) :
    Membership.mem (Finset.Ioc 0 N) a /\ Membership.mem (Finset.Ioc 0 N) b := by
  have hnb := Finset.mem_Ioc.mp hn
  have hn0 := Nat.ne_of_gt hnb.1
  have ha0 : Not (a = 0) := by
    intro ha
    apply hn0
    rw [<- hab, ha, zero_mul]
  have hb0 : Not (b = 0) := by
    intro hb
    apply hn0
    rw [<- hab, hb, mul_zero]
  have had : Dvd.dvd a n := by rw [<- hab]; exact dvd_mul_right a b
  have hbd : Dvd.dvd b n := by rw [<- hab]; exact dvd_mul_left b a
  exact And.intro
    (Finset.mem_Ioc.mpr (And.intro (Nat.pos_iff_ne_zero.mpr ha0)
      ((Nat.le_of_dvd hnb.1 had).trans hnb.2)))
    (Finset.mem_Ioc.mpr (And.intro (Nat.pos_iff_ne_zero.mpr hb0)
      ((Nat.le_of_dvd hnb.1 hbd).trans hnb.2)))

theorem sum_divisorsAntidiagonal_hyperbola {R : Type*} [AddCommMonoid R]
    (N : Nat) (F : Nat -> Nat -> R) :
    (Finset.Ioc 0 N).sum (fun n => n.divisorsAntidiagonal.sum (fun x => F x.1 x.2)) =
      (((Finset.Ioc 0 N).product (Finset.Ioc 0 N)).filter
        (fun x => x.1 * x.2 <= N)).sum (fun x => F x.1 x.2) := by
  let A : Finset (Sigma (fun _ : Nat => Prod Nat Nat)) :=
    (Finset.Ioc 0 N).sigma (fun n => n.divisorsAntidiagonal)
  calc
    _ = A.sum (fun x => F x.snd.1 x.snd.2) :=
      (Finset.sum_sigma (Finset.Ioc 0 N) (fun n => n.divisorsAntidiagonal)
        (fun x : Sigma (fun _ : Nat => Prod Nat Nat) => F x.snd.1 x.snd.2)).symm
    _ = _ := by
      apply Finset.sum_bij (fun x _ => x.snd)
      . intro x hx
        have hx' := Finset.mem_sigma.mp hx
        have hp := (Nat.mem_divisorsAntidiagonal.mp hx'.2).1
        have hb := factors_mem_Ioc hx'.1 hp
        apply Finset.mem_filter.mpr
        exact And.intro (Finset.mem_product.mpr hb)
          (by rw [hp]; exact (Finset.mem_Ioc.mp hx'.1).2)
      . intro a ha b hb heq
        have hap := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp ha).2).1
        have hbp := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hb).2).1
        apply Sigma.ext
        . calc
            a.fst = a.snd.1 * a.snd.2 := hap.symm
            _ = b.snd.1 * b.snd.2 := congrArg (fun x : Prod Nat Nat => x.1 * x.2) heq
            _ = b.fst := hbp
        . exact heq_of_eq heq
      . intro x hx
        have hx' := Finset.mem_filter.mp hx
        have hb := Finset.mem_product.mp hx'.1
        have hp : 0 < x.1 * x.2 :=
          Nat.mul_pos (Finset.mem_Ioc.mp hb.1).1 (Finset.mem_Ioc.mp hb.2).1
        let a : Sigma (fun _ : Nat => Prod Nat Nat) := Sigma.mk (x.1 * x.2) x
        have ha : Membership.mem A a := by
          apply Finset.mem_sigma.mpr
          exact And.intro (Finset.mem_Ioc.mpr (And.intro hp hx'.2))
            (Nat.mem_divisorsAntidiagonal.mpr (And.intro rfl (Nat.ne_of_gt hp)))
        exact Exists.intro a (Exists.intro ha rfl)
      . intro _ _
        rfl

theorem weighted_arithmetic_convolution {R : Type*} [Semiring R]
    (f g : ArithmeticFunction R) (w : Nat -> R) (N : Nat) :
    (Finset.Ioc 0 N).sum (fun n => (f * g) n * w n) =
      (((Finset.Ioc 0 N).product (Finset.Ioc 0 N)).filter
        (fun x => x.1 * x.2 <= N)).sum (fun x => f x.1 * g x.2 * w (x.1 * x.2)) := by
  calc
    _ = (Finset.Ioc 0 N).sum (fun n => n.divisorsAntidiagonal.sum
        (fun x => f x.1 * g x.2 * w (x.1 * x.2))) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [ArithmeticFunction.mul_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
    _ = _ := sum_divisorsAntidiagonal_hyperbola (R := R) N
      (fun a b => f a * g b * w (a * b))

def weightedDepleted {R : Type*} [Ring R]
    (h : Nat) (eta w : Nat -> R) (N : Nat) : R :=
  (Finset.Ioc 0 N).sum (fun n =>
    if n.Coprime h then (ArithmeticFunction.moebius n : R) * eta n * w n else 0)

theorem weighted_depletion_hyperbola {R : Type*} [CommRing R]
    (h : Nat) (eta w : Nat -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n) (N : Nat) :
    weightedDepleted h eta w N =
      (((Finset.Ioc 0 N).product (Finset.Ioc 0 N)).filter
        (fun x => x.1 * x.2 <= N)).sum (fun x =>
          if SupportedOn h x.1 then
            eta x.1 * (ArithmeticFunction.moebius x.2 : R) * eta x.2 * w (x.1 * x.2)
          else 0) := by
  have he := weighted_arithmetic_convolution (twist eta (smoothIndicator h))
    (twist eta ArithmeticFunction.moebius) w N
  rw [<- twisted_mask_identity h eta heta] at he
  convert he using 1
  . apply Finset.sum_congr rfl
    intro n _
    by_cases hc : n.Coprime h
    <;> simp [twist, maskedMobius, hc]
    <;> ring
  . apply Finset.sum_congr rfl
    intro x _
    by_cases hs : SupportedOn h x.1
    <;> simp [twist, smoothIndicator, hs]
    <;> ring

def weightedBase {R : Type*} [Ring R] (eta w : Nat -> R) (N : Nat) : R :=
  (Finset.Ioc 0 N).sum (fun n => (ArithmeticFunction.moebius n : R) * eta n * w n)

theorem weighted_depletion_separable {R : Type*} [CommRing R]
    (h : Nat) (eta w : Nat -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n) (N : Nat)
    (hzero : forall n : Nat, N < n -> w n = 0) :
    weightedDepleted h eta w N =
      (Finset.Ioc 0 N).sum (fun d => if SupportedOn h d then
        eta d * weightedBase eta (fun m => w (d * m)) N else 0) := by
  rw [weighted_depletion_hyperbola h eta w heta N, Finset.sum_filter]
  calc
    _ = ((Finset.Ioc 0 N).product (Finset.Ioc 0 N)).sum (fun x =>
        if SupportedOn h x.1 then
          eta x.1 * (ArithmeticFunction.moebius x.2 : R) * eta x.2 * w (x.1 * x.2)
        else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x.1 * x.2 <= N
      . simp only [hx, if_true]
      . have hw := hzero (x.1 * x.2) (Nat.lt_of_not_ge hx)
        simp only [hx, if_false, hw, mul_zero, ite_self]
    _ = _ := by
      rw [Finset.product_eq_sprod, Finset.sum_product (Finset.Ioc 0 N) (Finset.Ioc 0 N)
        (fun x : Prod Nat Nat => if SupportedOn h x.1 then
          eta x.1 * (ArithmeticFunction.moebius x.2 : R) * eta x.2 * w (x.1 * x.2)
        else 0)]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : SupportedOn h d
      . simp only [hd, if_true, weightedBase, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
      . simp only [hd, if_false, Finset.sum_const_zero]

end PrimeFactorOscillations.DepletedMobius
