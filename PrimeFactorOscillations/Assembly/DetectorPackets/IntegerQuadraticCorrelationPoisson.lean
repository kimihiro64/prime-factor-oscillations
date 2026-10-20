/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticMaskedPoisson

/-!
# IntegerQuadraticCorrelationPoisson

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
# Poisson transformation of the actual four-factor Jacobi correlation

The two cofactor columns share g. Their fourfold correlation retains
the coprimality mask, every Mobius divisor, the Gauss phase and both scales.
-/


noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticCorrelationPoisson

open IntegerQuadraticCharacter IntegerQuadraticInitial
open IntegerQuadraticMaskedPoisson

def intKernel (z : Int) (n : Nat) : Complex := (jacobiSym z n : Complex)

theorem character_intCast (n : Nat) [NeZero n] (hn : 1 < n) (z : Int) :
    character n hn (z : ZMod n) = intKernel z n := by
  rw [character_apply]
  change (jacobiSym (((z : ZMod n).val : Nat) : Int) n : Complex) =
    (jacobiSym z n : Complex)
  rw [ZMod.val_intCast]
  exact congrArg (fun j : Int => (j : Complex)) (jacobiSym.mod_left z n).symm

theorem int_kernel_mul_right (z : Int) (a b : Nat)
    (ha : Not (a = 0)) (hb : Not (b = 0)) :
    intKernel z (a * b) = intKernel z a * intKernel z b := by
  simp only [intKernel, jacobiSym.mul_right' z ha hb, Int.cast_mul]

theorem int_kernel_square (z : Int) (g : Nat) (hg : Not (g = 0)) :
    intKernel z g ^ 2 = if Nat.Coprime z.natAbs g then (1 : Complex) else 0 := by
  classical
  by_cases hc : Nat.Coprime z.natAbs g
  . have h : z.gcd (g : Int) = 1 := hc
    have hp := congrArg (fun j : Int => (j : Complex)) (jacobiSym.sq_one' h)
    rw [if_pos hc]
    simpa only [intKernel, jacobiSym.pow_left, Int.cast_pow, Int.cast_one] using hp
  . have h : Not (z.gcd (g : Int) = 1) := hc
    have hz : jacobiSym z g = 0 := jacobiSym.eq_zero_iff.mpr (And.intro hg h)
    simp only [intKernel, hz, Int.cast_zero, zero_pow (by decide : Not (2 = 0)), if_neg hc]

theorem common_four_mask (z : Int) (g a b r s : Nat)
    (hg : Not (g = 0)) (ha : Not (a = 0)) (hb : Not (b = 0))
    (hr : Not (r = 0)) (hs : Not (s = 0)) :
    intKernel z (g * a) * intKernel z (g * b) *
      intKernel z r * intKernel z s =
        if Nat.Coprime z.natAbs g then intKernel z ((a * b) * (r * s)) else 0 := by
  classical
  calc
    _ = intKernel z g ^ 2 * intKernel z ((a * b) * (r * s)) := by
      rw [int_kernel_mul_right z g a hg ha, int_kernel_mul_right z g b hg hb,
        int_kernel_mul_right z (a * b) (r * s) (mul_ne_zero ha hb) (mul_ne_zero hr hs),
        int_kernel_mul_right z a b ha hb, int_kernel_mul_right z r s hr hs]
      ring
    _ = _ := by
      rw [int_kernel_square z g hg]
      split_ifs <;> simp

theorem correlation_poisson (g a b r s : Nat)
    [NeZero ((a * b) * (r * s))]
    (hq : Good ((a * b) * (r * s)))
    (hg : 0 < g) (hg2 : Not (Dvd.dvd (2 : Nat) g))
    (ha : Not (a = 0)) (hb : Not (b = 0))
    (hr : Not (r = 0)) (hs : Not (s = 0))
    (T : Real) (hT : 0 < T) (f : SchwartzMap Real Complex) (B : Nat)
    (hB : forall x : Real, (B : Real) < abs x -> f x = 0) :
    tsum (fun z : Int => if Not (Dvd.dvd (2 : Int) z) then
      intKernel z (g * a) * intKernel z (g * b) *
        intKernel z r * intKernel z s * f ((z : Real) / T) else 0) =
      Finset.sum g.divisors (fun e => (ArithmeticFunction.moebius e : Complex) *
        character ((a * b) * (r * s)) hq.1 (e : ZMod ((a * b) * (r * s))) *
          oddDual ((a * b) * (r * s)) hq (T / (e : Real)) f) := by
  classical
  calc
    _ = tsum (fun z : Int => if Nat.Coprime z.natAbs g then
        (if Not (Dvd.dvd (2 : Int) z) then
          character ((a * b) * (r * s)) hq.1 (z : ZMod ((a * b) * (r * s))) *
            f ((z : Real) / T) else 0) else 0) := by
      apply tsum_congr
      intro z
      rw [character_intCast]
      by_cases ho : Not (Dvd.dvd (2 : Int) z)
      . rw [if_pos ho, common_four_mask z g a b r s (Nat.ne_of_gt hg) ha hb hr hs]
        by_cases hc : Nat.Coprime z.natAbs g <;> simp [hc, ho]
      . simp [ho]
    _ = _ := masked_odd_poisson ((a * b) * (r * s)) hq g hg hg2 T hT f B hB

end PrimeFactorOscillations.IntegerQuadraticCorrelationPoisson

