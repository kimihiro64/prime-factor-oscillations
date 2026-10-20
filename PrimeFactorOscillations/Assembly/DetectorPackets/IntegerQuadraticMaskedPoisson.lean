/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticOdd

/-!
# IntegerQuadraticMaskedPoisson

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
# Full coprimality-masked odd quadratic Poisson formula

Every divisor of the shared factor and both Fourier scales are retained.
No estimate, RH assumption or zero-free-strip hypothesis is used.
-/


noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticMaskedPoisson

open IntegerQuadraticCharacter IntegerQuadraticInitial IntegerQuadraticMask
open IntegerQuadraticOdd

theorem tsum_coprime (g : Nat) (hg : 0 < g)
    (F : Int -> Complex) (hF : Summable F) :
    tsum (fun z : Int => if Nat.Coprime z.natAbs g then F z else 0) =
      Finset.sum g.divisors (fun e => (ArithmeticFunction.moebius e : Complex) *
        tsum (fun v : Int => F ((e : Int) * v))) := by
  classical
  have hterm (e : Nat) : Summable (fun z : Int =>
      (ArithmeticFunction.moebius e : Complex) *
        (if Dvd.dvd (e : Int) z then F z else 0)) := by
    have hi : Summable (fun z : Int => if Dvd.dvd (e : Int) z then F z else 0) := by
      apply (hF.indicator (Set.ofPred (fun z : Int => Dvd.dvd (e : Int) z))).congr
      intro z
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    exact hi.mul_left _
  calc
    _ = tsum (fun z : Int => Finset.sum g.divisors (fun e =>
        (ArithmeticFunction.moebius e : Complex) *
          (if Dvd.dvd (e : Int) z then F z else 0))) := by
      apply tsum_congr
      intro z
      exact coprime_mask_weighted g hg z (F z)
    _ = Finset.sum g.divisors (fun e => tsum (fun z : Int =>
        (ArithmeticFunction.moebius e : Complex) *
          (if Dvd.dvd (e : Int) z then F z else 0))) :=
      Summable.tsum_finsetSum (fun e he => hterm e)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      have hd : Dvd.dvd e g := (Nat.mem_divisors.mp he).1
      have he0 : Not (e = 0) := by
        intro hz
        rw [hz, zero_dvd_iff] at hd
        omega
      have hei : Not ((e : Int) = 0) := by exact_mod_cast he0
      rw [tsum_mul_left, tsum_divisible (e : Int) hei F]

theorem int_even_iff_two_dvd (z : Int) : Even z <-> Dvd.dvd (2 : Int) z := by
  constructor
  . intro h
    choose k hk using h
    exact Exists.intro k (by linarith)
  . intro h
    choose k hk using h
    exact Exists.intro k (by linarith)

theorem odd_dilation_point (q : Nat) [NeZero q] (hq : Good q)
    (e : Nat) (he2 : Not (Dvd.dvd (2 : Nat) e))
    (T : Real) (f : SchwartzMap Real Complex) (v : Int) :
    (if Not (Dvd.dvd (2 : Int) ((e : Int) * v)) then
      character q hq.1 (((e : Int) * v : Int) : ZMod q) *
        f ((((e : Int) * v : Int) : Real) / T) else 0) =
      character q hq.1 (e : ZMod q) *
        (if Not (Dvd.dvd (2 : Int) v) then
          character q hq.1 (v : ZMod q) *
            f ((v : Real) / (T / (e : Real))) else 0) := by
  classical
  have heven : Not (Even (e : Int)) := by
    intro h
    exact he2 (Int.natCast_dvd_natCast.mp ((int_even_iff_two_dvd (e : Int)).mp h))
  have hpar : Dvd.dvd (2 : Int) ((e : Int) * v) <-> Dvd.dvd (2 : Int) v := by
    simp only [<- int_even_iff_two_dvd, Int.even_mul, heven, false_or]
  simp only [hpar]
  simp only [Int.cast_mul, Int.cast_natCast, map_mul]
  have ht : (e : Real) * (v : Real) / T = (v : Real) / (T / (e : Real)) := by
    field_simp
  rw [ht]
  by_cases hd : Dvd.dvd (2 : Int) v <;> simp [hd, mul_assoc]

def oddLattice (q : Nat) [NeZero q] (hq : Good q)
    (T : Real) (f : SchwartzMap Real Complex) : Complex :=
  tsum (fun z : Int => if Not (Dvd.dvd (2 : Int) z) then
    character q hq.1 (z : ZMod q) * f ((z : Real) / T) else 0)

def oddDual (q : Nat) [NeZero q] (hq : Good q)
    (T : Real) (f : SchwartzMap Real Complex) : Complex :=
  ((((T / (q : Real) : Real) : Complex) *
    gaussSum (character q hq.1) ZMod.stdAddChar) *
      tsum (fun h : Int => character q hq.1 (h : ZMod q) *
        (FourierTransform.fourier f) ((h : Real) * T / (q : Real)))) -
  character q hq.1 (2 : ZMod q) *
    (((((T / 2) / (q : Real) : Real) : Complex) *
      gaussSum (character q hq.1) ZMod.stdAddChar) *
        tsum (fun h : Int => character q hq.1 (h : ZMod q) *
          (FourierTransform.fourier f) ((h : Real) * (T / 2) / (q : Real))))

theorem masked_odd_poisson (q : Nat) [NeZero q] (hq : Good q)
    (g : Nat) (hg : 0 < g) (hg2 : Not (Dvd.dvd (2 : Nat) g))
    (T : Real) (hT : 0 < T) (f : SchwartzMap Real Complex) (B : Nat)
    (hB : forall x : Real, (B : Real) < abs x -> f x = 0) :
    tsum (fun z : Int => if Nat.Coprime z.natAbs g then
      (if Not (Dvd.dvd (2 : Int) z) then
        character q hq.1 (z : ZMod q) * f ((z : Real) / T) else 0) else 0) =
      Finset.sum g.divisors (fun e => (ArithmeticFunction.moebius e : Complex) *
        character q hq.1 (e : ZMod q) * oddDual q hq (T / (e : Real)) f) := by
  classical
  let F : Int -> Complex := fun z => if Not (Dvd.dvd (2 : Int) z) then
    character q hq.1 (z : ZMod q) * f ((z : Real) / T) else 0
  have hF : Summable F := by
    have hi := (scaled_lattice_summable q hq T hT f B hB).indicator
      (Set.ofPred (fun z : Int => Not (Dvd.dvd (2 : Int) z)))
    apply hi.congr
    intro z
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, F]
  rw [tsum_coprime g hg F hF]
  apply Finset.sum_congr rfl
  intro e he
  have hd : Dvd.dvd e g := (Nat.mem_divisors.mp he).1
  have he0 : Not (e = 0) := by
    intro hz
    rw [hz, zero_dvd_iff] at hd
    omega
  have hepos : (0 : Real) < (e : Real) := by exact_mod_cast Nat.pos_of_ne_zero he0
  have he2 : Not (Dvd.dvd (2 : Nat) e) := fun h => hg2 (Nat.dvd_trans h hd)
  have hr : tsum (fun v : Int => F ((e : Int) * v)) =
      character q hq.1 (e : ZMod q) * oddLattice q hq (T / (e : Real)) f := by
    rw [oddLattice, <- tsum_mul_left]
    apply tsum_congr
    intro v
    exact odd_dilation_point q hq e he2 T f v
  rw [hr]
  have hp : oddLattice q hq (T / (e : Real)) f =
      oddDual q hq (T / (e : Real)) f :=
    odd_poisson q hq (T / (e : Real)) (div_pos hT hepos) f B hB
  rw [hp]
  ring

end PrimeFactorOscillations.IntegerQuadraticMaskedPoisson

