/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeSchwartzPoisson

/-!
# CoprimeSchwartzCenter

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

namespace PrimeFactorOscillations.CoprimeSchwartzCenter

open CoprimeSchwartzPoisson IntegerQuadraticMask
open MeasureTheory

theorem totient_moebius_sum (q : Nat) (hq : 0 < q) :
    q.divisors.sum (fun d => (ArithmeticFunction.moebius d : Complex) * ((q / d : Nat) : Complex)) =
      (q.totient : Complex) := by
  have ht : forall n : Nat, 0 < n ->
      n.divisors.sum (fun d => (d.totient : Complex)) = (n : Complex) := by
    intro n hn
    exact_mod_cast Nat.sum_totient n
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n : Nat => (n.totient : Complex))
    (g := fun n : Nat => (n : Complex))).mp ht q hq
  calc
    _ = q.divisorsAntidiagonal.sum (fun p =>
        (ArithmeticFunction.moebius p.1 : Complex) * (p.2 : Complex)) :=
      (Nat.sum_divisorsAntidiagonal
        (fun d m : Nat => (ArithmeticFunction.moebius d : Complex) * (m : Complex))).symm
    _ = _ := h

theorem totient_reciprocal_sum (q : Nat) (hq : 0 < q) :
    q.divisors.sum (fun d => (ArithmeticFunction.moebius d : Complex) / (d : Complex)) =
      (q.totient : Complex) / (q : Complex) := by
  have hqC : Not ((q : Complex) = 0) := by exact_mod_cast Nat.ne_of_gt hq
  have hmul :
      q.divisors.sum (fun d => (ArithmeticFunction.moebius d : Complex) / (d : Complex)) *
        (q : Complex) = (q.totient : Complex) := by
    calc
      _ = q.divisors.sum (fun d =>
          ((ArithmeticFunction.moebius d : Complex) / (d : Complex)) * (q : Complex)) :=
        Finset.sum_mul _ _ _
      _ = q.divisors.sum (fun d =>
          (ArithmeticFunction.moebius d : Complex) * ((q / d : Nat) : Complex)) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdq := (Nat.mem_divisors.mp hd).1
        have hdpos := Nat.pos_of_dvd_of_pos hdq hq
        have hdC : Not ((d : Complex) = 0) := by exact_mod_cast Nat.ne_of_gt hdpos
        rw [Nat.cast_div hdq hdC]
        ring
      _ = _ := totient_moebius_sum q hq
  calc
    _ = (q.divisors.sum (fun d =>
        (ArithmeticFunction.moebius d : Complex) / (d : Complex)) * (q : Complex)) /
          (q : Complex) := by field_simp
    _ = _ := by rw [hmul]

theorem mobius_scale_sum (q : Nat) (hq : 0 < q) (X : Real) :
    q.divisors.sum (fun d => (ArithmeticFunction.moebius d : Complex) *
      ((X / (d : Real) : Real) : Complex)) =
        ((q.totient : Complex) / (q : Complex)) * (X : Complex) := by
  calc
    _ = q.divisors.sum (fun d => (X : Complex) *
        ((ArithmeticFunction.moebius d : Complex) / (d : Complex))) := by
      apply Finset.sum_congr rfl
      intro d hd
      push_cast
      ring
    _ = (X : Complex) * q.divisors.sum (fun d =>
        (ArithmeticFunction.moebius d : Complex) / (d : Complex)) := (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [totient_reciprocal_sum q hq]; ring

def offZeroSum (f : SchwartzMap Real Complex) (a : Real) : Complex :=
  tsum (fun n : Int => if n = 0 then 0 else f ((n : Real) * a))

theorem samples_split_zero (f : SchwartzMap Real Complex) (a : Real) (ha : 0 < a) :
    tsum (fun n : Int => f ((n : Real) * a)) = f 0 + offZeroSum f a := by
  have hs : Summable (fun n : Int => f ((n : Real) * a)) := by
    simpa only [mul_comm] using scaled_samples_summable a (ne_of_gt ha) f
  simpa only [Int.cast_zero, zero_mul, offZeroSum] using hs.tsum_eq_add_tsum_ite (0 : Int)

theorem centered_coprime_poisson (q : Nat) (hq : 0 < q)
    (X : Real) (hX : 0 < X) (f : SchwartzMap Real Complex) :
    coprimeSum q X f =
      ((q.totient : Complex) / (q : Complex)) * (X : Complex) *
        integral volume (fun x : Real => f x) +
      q.divisors.sum (fun d => (ArithmeticFunction.moebius d : Complex) *
        ((X / (d : Real) : Real) : Complex) *
          offZeroSum (FourierTransform.fourier f) (X / (d : Real))) := by
  have hsplit (d : Nat) (hd : Membership.mem q.divisors d) :
      tsum (fun l : Int => (FourierTransform.fourier f) ((l : Real) * X / (d : Real))) =
        integral volume (fun x : Real => f x) +
          offZeroSum (FourierTransform.fourier f) (X / (d : Real)) := by
    have hdpos := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hq
    have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hdpos
    calc
      _ = tsum (fun l : Int =>
          (FourierTransform.fourier f) ((l : Real) * (X / (d : Real)))) := by
        apply tsum_congr
        intro l
        congr 1
        ring
      _ = (FourierTransform.fourier f) 0 +
          offZeroSum (FourierTransform.fourier f) (X / (d : Real)) :=
        samples_split_zero _ _ (div_pos hX hdR)
      _ = _ := by rw [fourier_at_zero]
  calc
    _ = q.divisors.sum (fun d => (ArithmeticFunction.moebius d : Complex) *
        (((X / (d : Real) : Real) : Complex) *
          (integral volume (fun x : Real => f x) +
            offZeroSum (FourierTransform.fourier f) (X / (d : Real))))) := by
      rw [coprime_poisson q hq X hX f]
      apply Finset.sum_congr rfl
      intro d hd
      rw [hsplit d hd]
    _ = q.divisors.sum (fun d => (ArithmeticFunction.moebius d : Complex) *
        ((X / (d : Real) : Real) : Complex)) * integral volume (fun x : Real => f x) +
      q.divisors.sum (fun d => (ArithmeticFunction.moebius d : Complex) *
        ((X / (d : Real) : Real) : Complex) *
          offZeroSum (FourierTransform.fourier f) (X / (d : Real))) := by
      rw [Finset.sum_mul, <- Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by rw [mobius_scale_sum q hq X]

end PrimeFactorOscillations.CoprimeSchwartzCenter
