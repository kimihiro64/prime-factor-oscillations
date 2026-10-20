/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticMask

/-!
# CoprimeDivisorKernel

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
# Exact signed divisor rows for a coprimality-restricted packet

Coprimality is retained through Mobius inversion. The resulting squares
have signed Mobius weights; this does not assert a positive Gram matrix
or an analytic saving.
-/


noncomputable section
namespace PrimeFactorOscillations.CoprimeDivisorKernel

open IntegerQuadraticMask

def amplitude (s : Finset Nat) (a : Nat -> Complex) (h : Nat) : Complex :=
  s.sum (fun n => if Dvd.dvd h n then a n else 0)

theorem coprime_range_mask (N m n : Nat) (hn : 0 < n) (hN : n <= N) :
    (if Nat.Coprime m n then (1 : Complex) else 0) =
      (Finset.range (N + 1)).sum (fun h =>
        (ArithmeticFunction.moebius h : Complex) *
          (if And (Dvd.dvd h n) (Dvd.dvd h m) then 1 else 0)) := by
  classical
  have hsub : forall h, Membership.mem n.divisors h ->
      Membership.mem (Finset.range (N + 1)) h := by
    intro h hh
    apply Finset.mem_range.mpr
    have hle := Nat.le_of_dvd hn (Nat.mem_divisors.mp hh).1
    omega
  calc
    _ = n.divisors.sum (fun h => (ArithmeticFunction.moebius h : Complex) *
        (if Dvd.dvd h m then 1 else 0)) := coprime_mask n m hn
    _ = n.divisors.sum (fun h => (ArithmeticFunction.moebius h : Complex) *
        (if And (Dvd.dvd h n) (Dvd.dvd h m) then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro h hh
      simp only [(Nat.mem_divisors.mp hh).1, true_and]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro h hh hnot
      have hnd : Not (Dvd.dvd h n) := by
        intro hd
        exact hnot (Nat.mem_divisors.mpr (And.intro hd (Nat.ne_of_gt hn)))
      simp [hnd]

theorem coprime_bilinear (s : Finset Nat) (a b : Nat -> Complex) (N : Nat)
    (hs : forall n, Membership.mem s n -> And (0 < n) (n <= N)) :
    s.sum (fun n => s.sum (fun m =>
      if Nat.Coprime n m then a n * star (b m) else 0)) =
      (Finset.range (N + 1)).sum (fun h =>
        (ArithmeticFunction.moebius h : Complex) *
          amplitude s a h * star (amplitude s b h)) := by
  classical
  let T := Finset.range (N + 1)
  let f : Nat -> Nat -> Complex := fun h n =>
    if Dvd.dvd h n then a n else 0
  let g : Nat -> Nat -> Complex := fun h n =>
    if Dvd.dvd h n then b n else 0
  calc
    _ = s.sum (fun n => s.sum (fun m => T.sum (fun h =>
        (ArithmeticFunction.moebius h : Complex) * f h n * star (g h m)))) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      have hw : (if Nat.Coprime n m then a n * star (b m) else 0) =
          (if Nat.Coprime n m then (1 : Complex) else 0) * (a n * star (b m)) := by
        by_cases hc : Nat.Coprime n m <;> simp [hc]
      rw [hw, coprime_range_mask N n m (hs m hm).1 (hs m hm).2,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h hh
      by_cases hdn : Dvd.dvd h n <;> by_cases hdm : Dvd.dvd h m
      all_goals simp [T, f, g, hdn, hdm, mul_assoc]
    _ = s.sum (fun n => T.sum (fun h => s.sum (fun m =>
        (ArithmeticFunction.moebius h : Complex) * f h n * star (g h m)))) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
    _ = T.sum (fun h => s.sum (fun n => s.sum (fun m =>
        (ArithmeticFunction.moebius h : Complex) * f h n * star (g h m)))) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      have hstar : star (s.sum (g h)) = s.sum (fun m => star (g h m)) := by simp
      change s.sum (fun n => s.sum (fun m =>
        (ArithmeticFunction.moebius h : Complex) * f h n * star (g h m))) =
        (ArithmeticFunction.moebius h : Complex) *
          s.sum (f h) * star (s.sum (g h))
      rw [hstar]
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]

theorem coprime_energy_real (s : Finset Nat) (a : Nat -> Complex) (N : Nat)
    (hs : forall n, Membership.mem s n -> And (0 < n) (n <= N)) :
    (s.sum (fun n => s.sum (fun m =>
      if Nat.Coprime n m then a n * star (a m) else 0))).re =
      (Finset.range (N + 1)).sum (fun h =>
        (ArithmeticFunction.moebius h : Real) * norm (amplitude s a h) ^ 2) := by
  rw [coprime_bilinear s a a N hs]
  have hre : ((Finset.range (N + 1)).sum (fun h =>
      (ArithmeticFunction.moebius h : Complex) *
        amplitude s a h * star (amplitude s a h))).re =
      (Finset.range (N + 1)).sum (fun h =>
        ((ArithmeticFunction.moebius h : Complex) *
          amplitude s a h * star (amplitude s a h)).re) :=
    map_sum Complex.reAddGroupHom _ _
  rw [hre]
  apply Finset.sum_congr rfl
  intro h hh
  have hsqu (z : Complex) : (z * star z).re = norm z ^ 2 := by
    calc
      _ = Complex.normSq z := by simp [Complex.mul_re, Complex.normSq]
      _ = _ := Complex.normSq_eq_norm_sq z
  calc
    _ = ((ArithmeticFunction.moebius h : Complex) *
        (amplitude s a h * star (amplitude s a h))).re := by rw [mul_assoc]
    _ = (ArithmeticFunction.moebius h : Real) *
        (amplitude s a h * star (amplitude s a h)).re := by simp [Complex.mul_re]
    _ = _ := by rw [hsqu]

end PrimeFactorOscillations.CoprimeDivisorKernel

