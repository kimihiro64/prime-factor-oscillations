/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticMask
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticScale

/-!
# IntegerQuadraticOdd

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

/-! Exact odd-row subtraction with both Poisson scales retained. -/


noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticOdd

open IntegerQuadraticCharacter IntegerQuadraticInitial IntegerQuadraticScale
open IntegerQuadraticPoissonInteger

theorem tsum_divisible (e : Int) (he : Not (e = 0)) (F : Int -> Complex) :
    tsum (fun z : Int => if Dvd.dvd e z then F z else 0) =
      tsum (fun v : Int => F (e * v)) := by
  classical
  have hinj : Function.Injective (fun v : Int => e * v) := by
    intro a b h
    have hz : e * (a - b) = 0 := by nlinarith [h]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left he)
  have hs : Function.support (fun z : Int => if Dvd.dvd e z then F z else 0)
      <= Set.range (fun v : Int => e * v) := by
    intro z hz
    by_cases hd : Dvd.dvd e z
    . choose v hv using hd
      exact Exists.intro v hv.symm
    . change Not ((if Dvd.dvd e z then F z else 0) = 0) at hz
      exact (hz (by simp [hd])).elim
  have ht := hinj.tsum_eq hs
  simpa using ht.symm

theorem tsum_not_two_dvd (F : Int -> Complex) (hF : Summable F) :
    tsum (fun z : Int => if Not (Dvd.dvd (2 : Int) z) then F z else 0) =
      tsum F - tsum (fun v : Int => F (2 * v)) := by
  classical
  have hodd : Summable
      (fun z : Int => if Not (Dvd.dvd (2 : Int) z) then F z else 0) := by
    have hi := hF.indicator (Set.ofPred (fun z : Int => Not (Dvd.dvd (2 : Int) z)))
    apply hi.congr
    intro z
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have heven : Summable
      (fun z : Int => if Dvd.dvd (2 : Int) z then F z else 0) := by
    have hi := hF.indicator (Set.ofPred (fun z : Int => Dvd.dvd (2 : Int) z))
    apply hi.congr
    intro z
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hsum : tsum F =
      tsum (fun z : Int => if Not (Dvd.dvd (2 : Int) z) then F z else 0) +
        tsum (fun z : Int => if Dvd.dvd (2 : Int) z then F z else 0) := by
    rw [<- hodd.tsum_add heven]
    apply tsum_congr
    intro z
    by_cases hd : Dvd.dvd (2 : Int) z <;> simp [hd]
  rw [tsum_divisible 2 (by norm_num) F] at hsum
  rw [hsum]
  ring

theorem scaled_lattice_summable (q : Nat) [NeZero q] (hq : Good q)
    (T : Real) (hT : 0 < T) (f : SchwartzMap Real Complex) (B : Nat)
    (hB : forall x : Real, (B : Real) < abs x -> f x = 0) :
    Summable (fun z : Int => character q hq.1 (z : ZMod q) *
      f ((z : Real) / T)) := by
  have hqpos : (0 : Real) < (q : Real) := by exact_mod_cast NeZero.pos q
  have ha : 0 < (q : Real) / T := div_pos hqpos hT
  choose K hK using dilate_support_bound ((q : Real) / T) ha f B hB
  have hs := compact_lattice_summable q hq
    (dilate ((q : Real) / T) (ne_of_gt ha) f) K hK
  apply hs.congr
  intro z
  rw [dilate_apply]
  congr 2
  field_simp

theorem even_rows (q : Nat) [NeZero q] (hq : Good q)
    (T : Real) (hT : 0 < T) (f : SchwartzMap Real Complex) :
    tsum (fun v : Int => character q hq.1 ((2 * v : Int) : ZMod q) *
      f (((2 * v : Int) : Real) / T)) =
        character q hq.1 (2 : ZMod q) *
          tsum (fun v : Int => character q hq.1 (v : ZMod q) *
            f ((v : Real) / (T / 2))) := by
  rw [<- tsum_mul_left]
  apply tsum_congr
  intro v
  simp only [Int.cast_mul, Int.cast_ofNat, map_mul]
  have ht : (2 : Real) * (v : Real) / T = (v : Real) / (T / 2) := by
    field_simp
  rw [ht]
  ring

theorem odd_poisson (q : Nat) [NeZero q] (hq : Good q)
    (T : Real) (hT : 0 < T) (f : SchwartzMap Real Complex) (B : Nat)
    (hB : forall x : Real, (B : Real) < abs x -> f x = 0) :
    tsum (fun z : Int => if Not (Dvd.dvd (2 : Int) z) then
      character q hq.1 (z : ZMod q) * f ((z : Real) / T) else 0) =
        (((T / (q : Real) : Real) : Complex) *
          gaussSum (character q hq.1) ZMod.stdAddChar) *
            tsum (fun h : Int => character q hq.1 (h : ZMod q) *
              (FourierTransform.fourier f) ((h : Real) * T / (q : Real))) -
        character q hq.1 (2 : ZMod q) *
          (((((T / 2) / (q : Real) : Real) : Complex) *
            gaussSum (character q hq.1) ZMod.stdAddChar) *
              tsum (fun h : Int => character q hq.1 (h : ZMod q) *
                (FourierTransform.fourier f)
                  ((h : Real) * (T / 2) / (q : Real)))) := by
  rw [tsum_not_two_dvd _ (scaled_lattice_summable q hq T hT f B hB)]
  rw [even_rows q hq T hT f]
  rw [poisson_scaled q hq T hT f B hB]
  rw [poisson_scaled q hq (T / 2) (by positivity) f B hB]

end PrimeFactorOscillations.IntegerQuadraticOdd

