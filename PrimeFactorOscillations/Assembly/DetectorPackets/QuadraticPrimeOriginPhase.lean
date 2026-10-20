/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticFourModulus
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticStandardCRT
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticPrimeOrigin

/-!
# QuadraticPrimeOriginPhase

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
# Arithmetic phase identification of the prime-column origin term

The four signed square classes and the odd-row correction are kept.
The endpoint bound applies to this origin term, not to the remaining
squarefree-row or nonzero-frequency corrections.
-/


noncomputable section
namespace PrimeFactorOscillations.QuadraticPrimeOriginPhase

open IntegerQuadraticCharacter IntegerQuadraticSquarefree IntegerQuadraticInitial
open IntegerQuadraticCorrelationPoisson IntegerQuadraticSieve
open IntegerQuadraticStandardCRT QuadraticPrimeOrigin
open QuadraticCarrierPacket

theorem minus_one_value (n : Nat) (hn : Odd n) :
    intKernel (-1) n = if n % 4 = 3 then -1 else 1 := by
  have hz : (n : ZMod 4) = ((n % 4 : Nat) : ZMod 4) := by simp
  have hm := Nat.odd_iff.mp hn
  have hres : Or (n % 4 = 1) (n % 4 = 3) := by omega
  rcases hres with h | h
  all_goals
    simp only [intKernel, jacobiSym.at_neg_one hn]
    rw [hz]
    norm_num [h]

theorem two_value (n : Nat) (hn : Odd n) :
    intKernel 2 n = if Or (n % 8 = 1) (n % 8 = 7) then 1 else -1 := by
  have hz : (n : ZMod 8) = ((n % 8 : Nat) : ZMod 8) := by simp
  have hm := Nat.odd_iff.mp hn
  have hres : Or (n % 8 = 1) (Or (n % 8 = 3) (Or (n % 8 = 5) (n % 8 = 7))) := by omega
  rcases hres with h | h | h | h
  all_goals
    simp only [intKernel, jacobiSym.at_two hn]
    rw [hz]
    norm_num [h]

def localWeight (n : Nat) : Complex :=
  (1 / 2 : Complex) *
    (intKernel 1 n + intKernel (-1) n + intKernel 2 n + intKernel (-2) n) *
    (1 - intKernel 2 n / 2)

theorem localWeight_value (n : Nat) (hn : Odd n) :
    localWeight n = if n % 8 = 1 then 1 else 0 := by
  have hneg : intKernel (-2) n = intKernel (-1) n * intKernel 2 n := by
    simp only [intKernel, <- Int.cast_mul, <- jacobiSym.mul_left]
    norm_num
  have hone : intKernel 1 n = 1 := by simp [intKernel]
  have hm := Nat.odd_iff.mp hn
  have hres : Or (n % 8 = 1) (Or (n % 8 = 3) (Or (n % 8 = 5) (n % 8 = 7))) := by omega
  have hfour : n % 4 = n % 8 % 4 := by omega
  unfold localWeight
  rw [hone, hneg, minus_one_value n hn, two_value n hn, hfour]
  rcases hres with h | h | h | h <;> norm_num [h]

theorem localWeight_product (m n : Nat) (hm : Odd m) (hn : Odd n) :
    localWeight (m * n) = if m % 8 = n % 8 then 1 else 0 := by
  rw [localWeight_value (m * n) (hm.mul hn), Nat.mul_mod]
  have hm2 := Nat.odd_iff.mp hm
  have hn2 := Nat.odd_iff.mp hn
  have hmr : Or (m % 8 = 1) (Or (m % 8 = 3) (Or (m % 8 = 5) (m % 8 = 7))) := by omega
  have hnr : Or (n % 8 = 1) (Or (n % 8 = 3) (Or (n % 8 = 5) (n % 8 = 7))) := by omega
  rcases hmr with h | h | h | h
  all_goals rcases hnr with k | k | k | k <;> norm_num [h, k]

theorem reciprocity_product_same_class (m n : Nat) (hm : Good m) (hn : Good n)
    (hc : Nat.Coprime m n) (hclass : m % 8 = n % 8) :
    character m hm.1 (n : ZMod m) * character n hn.1 (m : ZMod n) =
      character n hn.1 (-1 : ZMod n) := by
  letI : NeZero n := NeZero.mk (by omega)
  have hfour : m % 4 = n % 4 := by omega
  have hsq : kernel n m * kernel n m = 1 := by
    simpa only [character_natCast, pow_two] using
      character_unit_square m hm.1 n hc.symm
  rw [character_natCast, character_natCast]
  change kernel n m * kernel m n = character n hn.1 (-1 : ZMod n)
  have hneg : character n hn.1 (-1 : ZMod n) = intKernel (-1) n := by
    simpa only [Int.cast_neg, Int.cast_one] using character_intCast n hn.1 (-1)
  rw [hneg, minus_one_value n hn.2.1]
  have hrec := reciprocity_split m n hm.2.1 hn.2.1
  by_cases hthree : n % 4 = 3
  . have hmthree : m % 4 = 3 := hfour.trans hthree
    have heq : kernel m n = -kernel n m := by
      simpa [thirdClass, minusClass, hthree, hmthree] using hrec
    rw [if_pos hthree, heq, mul_neg, hsq]
  . have hmthree : Not (m % 4 = 3) := by omega
    have heq : kernel m n = kernel n m := by
      simpa [thirdClass, minusClass, hthree, hmthree] using hrec
    rw [if_neg hthree, heq, hsq]

theorem gauss_same_class (m n : Nat) [NeZero m] [NeZero n]
    (hm : Good m) (hn : Good n) (hc : Nat.Coprime m n)
    (hclass : m % 8 = n % 8) :
    gaussSum (character (m * n) (by nlinarith [hm.1, hn.1])) ZMod.stdAddChar =
      gaussSum (character m hm.1) ZMod.stdAddChar *
        star (gaussSum (character n hn.1) ZMod.stdAddChar) := by
  rw [gauss_std_product hm hn hc,
    reciprocity_product_same_class m n hm hn hc hclass, star_gauss_std hn]
  ring

theorem normalized_same_class (m n : Nat)
    (hm : Good m) (hn : Good n) (hc : Nat.Coprime m n)
    (hclass : m % 8 = n % 8) :
    normalizedGauss (m * n) = normalizedGauss m * star (normalizedGauss n) := by
  letI : NeZero m := NeZero.mk (by omega)
  letI : NeZero n := NeZero.mk (by omega)
  have hmn : Good (m * n) :=
    And.intro (by nlinarith [hm.1, hn.1])
      (And.intro (hm.2.1.mul hn.2.1)
        (Nat.squarefree_mul_iff.mpr (And.intro hc (And.intro hm.2.2 hn.2.2))))
  simp only [normalizedGauss, dif_pos hm, dif_pos hn, dif_pos hmn]
  rw [gauss_same_class m n hm hn hc hclass]
  simp [div_eq_mul_inv]
  ring

theorem origin_pair (m n : Nat) (b : Int)
    (hm : Good m) (hn : Good n) (hc : Nat.Coprime m n) :
    localWeight (m * n) * normalizedGauss (m * n) * intKernel b (m * n) =
      if m % 8 = n % 8 then
        normalizedGauss m * star (normalizedGauss n) * intKernel b m * intKernel b n
      else 0 := by
  rw [localWeight_product m n hm.2.1 hn.2.1]
  by_cases h : m % 8 = n % 8
  . simp only [ite_eq_left h, one_mul]
    rw [normalized_same_class m n hm hn hc h,
      int_kernel_mul_right b m n (by omega) (by omega)]
    ring
  . simp only [ite_eq_right h, zero_mul]

theorem residue_pair_sum (s : Finset Nat) (f : Nat -> Nat -> Complex) :
    (Finset.range 8).sum (fun r =>
      (s.filter (fun p => p % 8 = r)).sum (fun p =>
        (s.filter (fun q => q % 8 = r)).sum (fun q => f p q))) =
      s.sum (fun p => s.sum (fun q => if p % 8 = q % 8 then f p q else 0)) := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hm : Membership.mem (Finset.range 8) (p % 8) :=
    Finset.mem_range.mpr (Nat.mod_lt p (by decide))
  simp [hm, eq_comm]

def sourceOrigin (s : Finset Nat) (lambda : Nat -> Complex)
    (b : Int) (c : Real) (L : Nat) : Complex :=
  -(c : Complex) * s.sum (fun p => s.sum (fun q =>
    if p = q then 0 else
      lambda p * star (lambda q) *
        (localWeight (p * q) * normalizedGauss (p * q) * intKernel b (p * q)) *
        ((p * q).divisors.filter (fun d => d <= L)).sum
          (fun d => (ArithmeticFunction.moebius d : Complex))))

theorem sourceOrigin_eq (s : Finset Nat) (lambda : Nat -> Complex)
    (b : Int) (c : Real) (L : Nat)
    (hprime : forall p, Membership.mem s p -> Nat.Prime p)
    (hodd : forall p, Membership.mem s p -> Odd p)
    (hL : 1 <= L) (hlower : forall p, Membership.mem s p -> L < p) :
    sourceOrigin s lambda b c L = origin s (coefficient lambda b) c := by
  classical
  unfold sourceOrigin origin offDiagonal
  rw [residue_pair_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  by_cases heq : p = q
  . subst q
    simp
  . have hpp := hprime p hp
    have hpq := hprime q hq
    have hgp : Good p := And.intro hpp.one_lt (And.intro (hodd p hp) hpp.squarefree)
    have hgq : Good q := And.intro hpq.one_lt (And.intro (hodd q hq) hpq.squarefree)
    have hc : Nat.Coprime p q := by
      by_cases hlt : p < q
      . exact IntegerQuadraticFourModulus.larger_prime_coprime p q hpp.pos hlt hpq
      . exact (IntegerQuadraticFourModulus.larger_prime_coprime q p hpq.pos
          (by omega) hpp).symm
    simp only [ite_eq_right heq]
    rw [truncated_prime_moebius p q L hpp hpq hL (hlower p hp) (hlower q hq),
      mul_one, origin_pair p q b hgp hgq hc]
    by_cases hclass : p % 8 = q % 8
    . simp only [ite_eq_left hclass]
      simp [coefficient, intKernel]
      ring
    . simp [hclass]

theorem sourceOrigin_upper (s : Finset Nat) (lambda : Nat -> Complex)
    (b : Int) (c N : Real) (L : Nat) (hc : 0 <= c) (hN : 0 < N)
    (hprime : forall p, Membership.mem s p -> Nat.Prime p)
    (hodd : forall p, Membership.mem s p -> Odd p)
    (hL : 1 <= L) (hcut : forall p, Membership.mem s p -> L < p)
    (hlower : forall p, Membership.mem s p -> N <= (p : Real)) :
    (sourceOrigin s lambda b c L).re <=
      (c / N) * s.sum (fun p => norm (lambda p) ^ 2) := by
  rw [sourceOrigin_eq s lambda b c L hprime hodd hL hcut]
  exact prime_origin_upper s lambda b c N hc hN
    (fun p hp => And.intro (hprime p hp).one_lt
      (And.intro (hodd p hp) (hprime p hp).squarefree)) hlower

end PrimeFactorOscillations.QuadraticPrimeOriginPhase

