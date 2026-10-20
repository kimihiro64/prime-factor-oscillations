/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Data.Int.Interval
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# GaussianLatticeCount

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Gaussian norm-ball counting for the quadratic-sieve port

A uniform lattice bound for actual Gaussian integers, including the smallest
positive cutoff. This supplies the counting input used in the arbitrary
square-part extension of the natural square-packet mean. It is not the
Gaussian quadratic large sieve itself.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianLatticeCount

abbrev GaussianInteger := Zsqrtd (-1)

theorem norm_eq (z : GaussianInteger) :
    z.norm = z.re^2 + z.im^2 := by
  dsimp [Zsqrtd.norm]
  ring

def box (R : Nat) : Finset GaussianInteger :=
  (SProd.sprod (Finset.Icc (-(R : Int)) (R : Int))
    (Finset.Icc (-(R : Int)) (R : Int))).image
      (fun p : Prod Int Int => Zsqrtd.mk p.1 p.2)

theorem mem_box (R : Nat) (z : GaussianInteger) :
    Membership.mem (box R) z <->
      (-(R : Int) <= z.re /\ z.re <= (R : Int)) /\
        (-(R : Int) <= z.im /\ z.im <= (R : Int)) := by
  classical
  constructor
  . intro hz
    choose p hp he using Finset.mem_image.mp hz
    have hpair := Finset.mem_product.mp hp
    have hre := congrArg Zsqrtd.re he
    have him := congrArg Zsqrtd.im he
    change p.1 = z.re at hre
    change p.2 = z.im at him
    simpa only [Finset.mem_Icc, hre, him] using hpair
  . intro hz
    apply Finset.mem_image.mpr
    refine Exists.intro (Prod.mk z.re z.im) (And.intro ?_ ?_)
    . exact Finset.mem_product.mpr
        (And.intro (Finset.mem_Icc.mpr hz.1) (Finset.mem_Icc.mpr hz.2))
    . exact Zsqrtd.ext rfl rfl

theorem box_card_le (R : Nat) : (box R).card <= (2*R+1)^2 := by
  have hI : (Finset.Icc (-(R : Int)) (R : Int)).card = 2*R+1 := by
    rw [Int.card_Icc]
    omega
  calc
    _ <= (SProd.sprod (Finset.Icc (-(R : Int)) (R : Int))
        (Finset.Icc (-(R : Int)) (R : Int))).card := Finset.card_image_le
    _ = _ := by
      simpa only [hI, pow_two] using
        (Finset.card_product
          (Finset.Icc (-(R : Int)) (R : Int))
          (Finset.Icc (-(R : Int)) (R : Int)))

private theorem coordinate_bounds (N : Nat) (a b : Int)
    (h : a^2+b^2 <= (N : Int)) :
    -(N.sqrt : Int) <= a /\ a <= (N.sqrt : Int) := by
  have hr : (0 : Int) <= (N.sqrt : Int) := by omega
  have hn : (N : Int) < ((N.sqrt : Int)+1)^2 := by
    have hh : N < (N.sqrt+1)^2 := by
      simpa only [Nat.succ_eq_add_one, pow_two] using Nat.lt_succ_sqrt N
    exact_mod_cast hh
  constructor
  . by_contra hh
    have ha : (N.sqrt : Int)+1 <= -a := by omega
    have hs := mul_self_le_mul_self (by omega : (0 : Int) <= (N.sqrt : Int)+1) ha
    nlinarith [sq_nonneg b]
  . by_contra hh
    have ha : (N.sqrt : Int)+1 <= a := by omega
    have hs := mul_self_le_mul_self (by omega : (0 : Int) <= (N.sqrt : Int)+1) ha
    nlinarith [sq_nonneg b]

theorem mem_box_of_norm_le (N : Nat) (z : GaussianInteger)
    (hz : z.norm <= (N : Int)) : Membership.mem (box N.sqrt) z := by
  rw [norm_eq] at hz
  apply (mem_box N.sqrt z).mpr
  exact And.intro (coordinate_bounds N z.re z.im hz)
    (coordinate_bounds N z.im z.re (by linarith))

def ball (N : Nat) : Finset GaussianInteger :=
  (box N.sqrt).filter (fun z => z.norm <= (N : Int))

theorem mem_ball (N : Nat) (z : GaussianInteger) :
    Membership.mem (ball N) z <-> z.norm <= (N : Int) := by
  classical
  constructor
  . intro hz
    exact (Finset.mem_filter.mp hz).2
  . intro hz
    exact Finset.mem_filter.mpr (And.intro (mem_box_of_norm_le N z hz) hz)

theorem ball_card_le (N : Nat) (hN : 1 <= N) :
    (ball N).card <= 9*N := by
  have hs : N.sqrt*N.sqrt <= N := Nat.le_sqrt.mp (le_refl N.sqrt)
  have hs1 : 1 <= N.sqrt := Nat.le_sqrt.mpr (by simpa using hN)
  have hss : N.sqrt <= N.sqrt*N.sqrt := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left N.sqrt hs1
  apply (Finset.card_filter_le _ _).trans
  apply (box_card_le N.sqrt).trans
  nlinarith

theorem finite_set_card_le (S : Finset GaussianInteger) (N : Nat) (hN : 1 <= N)
    (hS : forall z, Membership.mem S z -> z.norm <= (N : Int)) :
    S.card <= 9*N := by
  apply (Finset.card_le_card ?_).trans (ball_card_le N hN)
  intro z hz
  exact (mem_ball N z).mpr (hS z hz)

end PrimeFactorOscillations.GaussianLatticeCount
