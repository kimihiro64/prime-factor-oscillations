/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticCorrelationPoisson

/-!
# IntegerQuadraticEffectiveFrequency

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

namespace PrimeFactorOscillations.IntegerQuadraticEffectiveFrequency

open IntegerQuadraticCharacter IntegerQuadraticInitial
open IntegerQuadraticCorrelationPoisson IntegerQuadraticMaskedPoisson

theorem effective_phase (q : Nat) [NeZero q] (hq : Good q) (e : Nat) (k : Int) :
    character q hq.1 (e : ZMod q) * character q hq.1 (k : ZMod q) =
      character q hq.1 (((e : Int) * k : Int) : ZMod q) := by
  simp only [Int.cast_mul, Int.cast_natCast, map_mul]

theorem character_square_mask (q : Nat) [NeZero q] (hq : Good q) (d : Nat) :
    character q hq.1 ((d ^ 2 : Nat) : ZMod q) =
      if Nat.Coprime d q then (1 : Complex) else 0 := by
  rw [Nat.cast_pow, map_pow]
  have hc := character_intCast q hq.1 (d : Int)
  have hs := int_kernel_square (d : Int) q (NeZero.ne q)
  rw [<- hc] at hs
  simpa using hs

theorem positive_effective_square_phase (q : Nat) [NeZero q] (hq : Good q)
    (e c : Nat) :
    character q hq.1 (e : ZMod q) *
      character q hq.1 ((e * c ^ 2 : Nat) : ZMod q) =
        if Nat.Coprime (e * c) q then (1 : Complex) else 0 := by
  rw [<- map_mul, <- Nat.cast_mul,
    show e * (e * c ^ 2) = (e * c) ^ 2 by ring, character_square_mask q hq]

theorem negative_effective_square_phase (q : Nat) [NeZero q] (hq : Good q)
    (e c : Nat) :
    character q hq.1 (e : ZMod q) *
      character q hq.1 ((-((e * c ^ 2 : Nat) : Int) : Int) : ZMod q) =
        if Nat.Coprime (e * c) q then character q hq.1 (-1 : ZMod q) else 0 := by
  calc
    _ = character q hq.1 (-1 : ZMod q) *
        (character q hq.1 (e : ZMod q) *
          character q hq.1 ((e * c ^ 2 : Nat) : ZMod q)) := by
      rw [Int.cast_neg, Int.cast_natCast, neg_eq_neg_one_mul, map_mul]
      ring
    _ = _ := by
      rw [positive_effective_square_phase q hq]
      split_ifs <;> simp

theorem squarefree_effective_square_iff (e k : Nat) (he : Squarefree e) :
    Exists (fun d : Nat => e * k = d ^ 2) <->
      Exists (fun c : Nat => k = e * c ^ 2) := by
  constructor
  . intro h
    choose d hd using h
    have hed : Dvd.dvd e d :=
      (he.dvd_pow_iff_dvd (by decide : Not (2 = 0))).mp (Exists.intro k hd.symm)
    choose c hc using hed
    have hmul : e * k = e * (e * c ^ 2) := by
      calc
        _ = d ^ 2 := hd
        _ = (e * c) ^ 2 := by rw [hc]
        _ = _ := by ring
    exact Exists.intro c
      (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he.ne_zero) hmul)
  . intro h
    choose c hc using h
    refine Exists.intro (e * c) ?_
    rw [hc]
    ring

def firstTerm (q : Nat) [NeZero q] (hq : Good q) (e : Nat)
    (T : Real) (f : SchwartzMap Real Complex) (k : Int) : Complex :=
  (ArithmeticFunction.moebius e : Complex) *
    ((((T / (e : Real)) / (q : Real) : Real) : Complex) *
      gaussSum (character q hq.1) ZMod.stdAddChar) *
    character q hq.1 (((e : Int) * k : Int) : ZMod q) *
    (FourierTransform.fourier f) ((k : Real) * (T / (e : Real)) / (q : Real))

def halfTerm (q : Nat) [NeZero q] (hq : Good q) (e : Nat)
    (T : Real) (f : SchwartzMap Real Complex) (k : Int) : Complex :=
  (ArithmeticFunction.moebius e : Complex) * character q hq.1 (2 : ZMod q) *
    (((((T / (e : Real)) / 2) / (q : Real) : Real) : Complex) *
      gaussSum (character q hq.1) ZMod.stdAddChar) *
    character q hq.1 (((e : Int) * k : Int) : ZMod q) *
    (FourierTransform.fourier f) ((k : Real) * ((T / (e : Real)) / 2) / (q : Real))

theorem full_divisor_regroup (q : Nat) [NeZero q] (hq : Good q) (e : Nat)
    (T : Real) (f : SchwartzMap Real Complex) :
    (ArithmeticFunction.moebius e : Complex) * character q hq.1 (e : ZMod q) *
      oddDual q hq (T / (e : Real)) f =
        tsum (firstTerm q hq e T f) - tsum (halfTerm q hq e T f) := by
  unfold oddDual
  rw [mul_sub]
  congr 1
  . simp_rw [<- tsum_mul_left]
    apply tsum_congr
    intro k
    unfold firstTerm
    rw [<- effective_phase q hq e k]
    ring
  . simp_rw [<- tsum_mul_left]
    apply tsum_congr
    intro k
    unfold halfTerm
    rw [<- effective_phase q hq e k]
    ring

theorem positive_first_scale (q e c : Nat) [NeZero q] (he : 0 < e) (T : Real) :
    (((e * c ^ 2 : Nat) : Int) : Real) * (T / (e : Real)) / (q : Real) =
      (c : Real) ^ 2 * T / (q : Real) := by
  have he0 : Not ((e : Real) = 0) := by exact_mod_cast Nat.ne_of_gt he
  have hq0 : Not ((q : Real) = 0) := by exact_mod_cast NeZero.ne q
  push_cast
  field_simp [he0, hq0]
  <;> ring

theorem positive_half_scale (q e c : Nat) [NeZero q] (he : 0 < e) (T : Real) :
    (((e * c ^ 2 : Nat) : Int) : Real) * ((T / (e : Real)) / 2) / (q : Real) =
      (c : Real) ^ 2 * (T / 2) / (q : Real) := by
  have he0 : Not ((e : Real) = 0) := by exact_mod_cast Nat.ne_of_gt he
  have hq0 : Not ((q : Real) = 0) := by exact_mod_cast NeZero.ne q
  push_cast
  field_simp [he0, hq0]
  <;> ring

theorem positive_first_term (q : Nat) [NeZero q] (hq : Good q)
    (e c : Nat) (he : 0 < e) (T : Real) (f : SchwartzMap Real Complex) :
    firstTerm q hq e T f ((e * c ^ 2 : Nat) : Int) =
      if Nat.Coprime (e * c) q then
        (ArithmeticFunction.moebius e : Complex) *
          ((((T / (e : Real)) / (q : Real) : Real) : Complex) *
            gaussSum (character q hq.1) ZMod.stdAddChar) *
          (FourierTransform.fourier f) ((c : Real) ^ 2 * T / (q : Real))
      else 0 := by
  unfold firstTerm
  rw [positive_first_scale q e c he T, <- effective_phase q hq e,
    Int.cast_natCast, positive_effective_square_phase q hq]
  split_ifs <;> simp

theorem positive_half_term (q : Nat) [NeZero q] (hq : Good q)
    (e c : Nat) (he : 0 < e) (T : Real) (f : SchwartzMap Real Complex) :
    halfTerm q hq e T f ((e * c ^ 2 : Nat) : Int) =
      if Nat.Coprime (e * c) q then
        (ArithmeticFunction.moebius e : Complex) * character q hq.1 (2 : ZMod q) *
          (((((T / (e : Real)) / 2) / (q : Real) : Real) : Complex) *
            gaussSum (character q hq.1) ZMod.stdAddChar) *
          (FourierTransform.fourier f) ((c : Real) ^ 2 * (T / 2) / (q : Real))
      else 0 := by
  unfold halfTerm
  rw [positive_half_scale q e c he T, <- effective_phase q hq e,
    Int.cast_natCast, positive_effective_square_phase q hq]
  split_ifs <;> simp


theorem negative_first_scale (q e c : Nat) [NeZero q] (he : 0 < e) (T : Real) :
    ((-((e * c ^ 2 : Nat) : Int) : Int) : Real) *
        (T / (e : Real)) / (q : Real) =
      -((c : Real) ^ 2 * T / (q : Real)) := by
  rw [Int.cast_neg, neg_mul, neg_div, positive_first_scale q e c he T]

theorem negative_half_scale (q e c : Nat) [NeZero q] (he : 0 < e) (T : Real) :
    ((-((e * c ^ 2 : Nat) : Int) : Int) : Real) *
        ((T / (e : Real)) / 2) / (q : Real) =
      -((c : Real) ^ 2 * (T / 2) / (q : Real)) := by
  rw [Int.cast_neg, neg_mul, neg_div, positive_half_scale q e c he T]

theorem negative_first_term (q : Nat) [NeZero q] (hq : Good q)
    (e c : Nat) (he : 0 < e) (T : Real) (f : SchwartzMap Real Complex) :
    firstTerm q hq e T f (-((e * c ^ 2 : Nat) : Int)) =
      if Nat.Coprime (e * c) q then
        (ArithmeticFunction.moebius e : Complex) *
          ((((T / (e : Real)) / (q : Real) : Real) : Complex) *
            gaussSum (character q hq.1) ZMod.stdAddChar) *
          character q hq.1 (-1 : ZMod q) *
          (FourierTransform.fourier f) (-((c : Real) ^ 2 * T / (q : Real)))
      else 0 := by
  unfold firstTerm
  rw [negative_first_scale q e c he T, <- effective_phase q hq e,
    negative_effective_square_phase q hq]
  split_ifs <;> simp

theorem negative_half_term (q : Nat) [NeZero q] (hq : Good q)
    (e c : Nat) (he : 0 < e) (T : Real) (f : SchwartzMap Real Complex) :
    halfTerm q hq e T f (-((e * c ^ 2 : Nat) : Int)) =
      if Nat.Coprime (e * c) q then
        (ArithmeticFunction.moebius e : Complex) * character q hq.1 (2 : ZMod q) *
          (((((T / (e : Real)) / 2) / (q : Real) : Real) : Complex) *
            gaussSum (character q hq.1) ZMod.stdAddChar) *
          character q hq.1 (-1 : ZMod q) *
          (FourierTransform.fourier f) (-((c : Real) ^ 2 * (T / 2) / (q : Real)))
      else 0 := by
  unfold halfTerm
  rw [negative_half_scale q e c he T, <- effective_phase q hq e,
    negative_effective_square_phase q hq]
  split_ifs <;> simp


theorem half_effective_phase (q : Nat) [NeZero q] (hq : Good q)
    (e : Nat) (k : Int) :
    character q hq.1 (2 : ZMod q) *
        character q hq.1 (((e : Int) * k : Int) : ZMod q) =
      character q hq.1 ((((2 * e : Nat) : Int) * k : Int) : ZMod q) := by
  simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul, map_mul]
  ring

theorem half_squarefree_effective_square_iff (e k : Nat)
    (he : Squarefree (2 * e)) :
    Exists (fun d : Nat => (2 * e) * k = d ^ 2) <->
      Exists (fun c : Nat => k = (2 * e) * c ^ 2) :=
  squarefree_effective_square_iff (2 * e) k he

theorem half_principal_scale (q e c : Nat) [NeZero q] (he : 0 < e) (T : Real) :
    ((((2 * e) * c ^ 2 : Nat) : Int) : Real) *
        ((T / (e : Real)) / 2) / (q : Real) =
      (c : Real) ^ 2 * T / (q : Real) := by
  have he0 : Not ((e : Real) = 0) := by exact_mod_cast Nat.ne_of_gt he
  have hq0 : Not ((q : Real) = 0) := by exact_mod_cast NeZero.ne q
  push_cast
  field_simp [he0, hq0]
  <;> ring

theorem half_principal_phase (q : Nat) [NeZero q] (hq : Good q) (e c : Nat) :
    character q hq.1 (2 : ZMod q) *
      character q hq.1
        (((e : Int) * (((2 * e) * c ^ 2 : Nat) : Int) : Int) : ZMod q) =
      if Nat.Coprime ((2 * e) * c) q then (1 : Complex) else 0 := by
  rw [half_effective_phase q hq e, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
    <- Nat.cast_mul]
  have hmul : (2 * e) * ((2 * e) * c ^ 2) = ((2 * e) * c) ^ 2 := by ring
  rw [hmul, character_square_mask q hq]

theorem half_principal_term (q : Nat) [NeZero q] (hq : Good q)
    (e c : Nat) (he : 0 < e) (T : Real) (f : SchwartzMap Real Complex) :
    halfTerm q hq e T f (((2 * e) * c ^ 2 : Nat) : Int) =
      if Nat.Coprime ((2 * e) * c) q then
        (ArithmeticFunction.moebius e : Complex) *
          (((((T / (e : Real)) / 2) / (q : Real) : Real) : Complex) *
            gaussSum (character q hq.1) ZMod.stdAddChar) *
          (FourierTransform.fourier f) ((c : Real) ^ 2 * T / (q : Real))
      else 0 := by
  unfold halfTerm
  rw [half_principal_scale q e c he T]
  have hphase := half_principal_phase q hq e c
  have hregroup (a b d x y : Complex) : a * x * b * y * d = a * b * (x * y) * d := by
    ring
  rw [hregroup, hphase]
  split_ifs <;> simp

theorem odd_modulus_coprime_double (q d : Nat) [NeZero q] (hq : Good q) :
    Nat.Coprime (2 * d) q <-> Nat.Coprime d q := by
  have h2 : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hq.2.1
  rw [Nat.coprime_mul_iff_left]
  exact and_iff_right h2

theorem principal_mode_difference (q : Nat) [NeZero q] (hq : Good q)
    (e c : Nat) (he : 0 < e) (T : Real) (f : SchwartzMap Real Complex) :
    firstTerm q hq e T f ((e * c ^ 2 : Nat) : Int) -
      halfTerm q hq e T f (((2 * e) * c ^ 2 : Nat) : Int) =
      if Nat.Coprime (e * c) q then
        (1 / 2 : Complex) * (ArithmeticFunction.moebius e : Complex) *
          ((((T / (e : Real)) / (q : Real) : Real) : Complex) *
            gaussSum (character q hq.1) ZMod.stdAddChar) *
          (FourierTransform.fourier f) ((c : Real) ^ 2 * T / (q : Real))
      else 0 := by
  rw [positive_first_term q hq e c he, half_principal_term q hq e c he]
  simp only [show (2 * e) * c = 2 * (e * c) by ring,
    odd_modulus_coprime_double q (e * c) hq]
  split_ifs
  . push_cast
    ring
  . simp

end PrimeFactorOscillations.IntegerQuadraticEffectiveFrequency
