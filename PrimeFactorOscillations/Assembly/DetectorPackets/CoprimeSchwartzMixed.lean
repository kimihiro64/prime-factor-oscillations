/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeSchwartzSplit

/-!
# CoprimeSchwartzMixed

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

namespace PrimeFactorOscillations.CoprimeSchwartzMixed

open CoprimeSchwartzPoisson CoprimeSchwartzCenter CoprimeSchwartzSplit
open IntegerQuadraticMask MeasureTheory

def smallDivisors (q : Nat) (Y : Real) : Finset Nat :=
  q.divisors.filter (fun d => (d : Real) <= Y)

def middleDivisors (q : Nat) (Y Z : Real) : Finset Nat :=
  q.divisors.filter (fun d => Y < (d : Real) /\ (d : Real) <= Z)

def largeDivisors (q : Nat) (Z : Real) : Finset Nat :=
  q.divisors.filter (fun d => Z < (d : Real))

def dualRow (f : SchwartzMap Real Complex) (X : Real) (d : Nat) : Complex :=
  (ArithmeticFunction.moebius d : Complex) * ((X / (d : Real) : Real) : Complex) *
    offZeroSum (FourierTransform.fourier f) (X / (d : Real))

def lowDual (q : Nat) (X Y : Real) (f : SchwartzMap Real Complex) : Complex :=
  (smallDivisors q Y).sum (dualRow f X)

def middlePacket (q : Nat) (X Y Z : Real) (L : Nat) (f : SchwartzMap Real Complex) : Complex :=
  (middleDivisors q Y Z).sum (fun d =>
    (ArithmeticFunction.moebius d : Complex) * ((X / (d : Real) : Real) : Complex) *
      frequencyPacket L (FourierTransform.fourier f) (X / (d : Real)))

def middleTail (q : Nat) (X Y Z : Real) (L : Nat) (f : SchwartzMap Real Complex) : Complex :=
  (middleDivisors q Y Z).sum (fun d =>
    (ArithmeticFunction.moebius d : Complex) * ((X / (d : Real) : Real) : Complex) *
      frequencyTail L (FourierTransform.fourier f) (X / (d : Real)))

def highPrimal (q : Nat) (X Z : Real) (f : SchwartzMap Real Complex) : Complex :=
  (largeDivisors q Z).sum (fun d =>
    (ArithmeticFunction.moebius d : Complex) * offZeroSum f ((d : Real) / X))

def largeMain (q : Nat) (X Z : Real) (f : SchwartzMap Real Complex) : Complex :=
  (largeDivisors q Z).sum (fun d =>
    (ArithmeticFunction.moebius d : Complex) * ((X / (d : Real) : Real) : Complex) *
      integral volume (fun x : Real => f x))

def remainder (q : Nat) (X Y Z : Real) (L : Nat) (f : SchwartzMap Real Complex) : Complex :=
  lowDual q X Y f + middleTail q X Y Z L f + highPrimal q X Z f

theorem largeMain_factor (q : Nat) (X Z : Real) (f : SchwartzMap Real Complex) :
    largeMain q X Z f =
      (X : Complex) * integral volume (fun x : Real => f x) *
        (largeDivisors q Z).sum
          (fun d => (ArithmeticFunction.moebius d : Complex) / (d : Complex)) := by
  unfold largeMain
  calc
    _ = (largeDivisors q Z).sum (fun d =>
        ((X : Complex) * integral volume (fun x : Real => f x)) *
          ((ArithmeticFunction.moebius d : Complex) / (d : Complex))) := by
      apply Finset.sum_congr rfl
      intro d hd
      push_cast
      ring
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem dualRow_high (d : Nat) (hd : 0 < d)
    (X : Real) (hX : 0 < X) (f : SchwartzMap Real Complex) :
    dualRow f X d =
      (ArithmeticFunction.moebius d : Complex) * f 0 +
      (ArithmeticFunction.moebius d : Complex) * offZeroSum f ((d : Real) / X) -
      (ArithmeticFunction.moebius d : Complex) * ((X / (d : Real) : Real) : Complex) *
        integral volume (fun x : Real => f x) := by
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hd
  have h := primal_dual_balance f ((d : Real) / X) (div_pos hdR hX)
  have hi : 1 / ((d : Real) / X) = X / (d : Real) := by
    simp only [one_div, inv_div]
  rw [hi] at h
  unfold dualRow
  calc
    _ = (ArithmeticFunction.moebius d : Complex) *
        (((X / (d : Real) : Real) : Complex) *
          (integral volume (fun x : Real => f x) +
            offZeroSum (FourierTransform.fourier f) (X / (d : Real))) -
          ((X / (d : Real) : Real) : Complex) * integral volume (fun x : Real => f x)) := by ring
    _ = _ := by rw [<- h]; ring

theorem dualRow_split (d : Nat) (hd : 0 < d) (X Y Z : Real)
    (hX : 0 < X) (hYZ : Y <= Z) (L : Nat) (f : SchwartzMap Real Complex) :
    dualRow f X d =
      (ArithmeticFunction.moebius d : Complex) * f 0 -
      (if (d : Real) <= Z then (ArithmeticFunction.moebius d : Complex) * f 0 else 0) -
      (if Z < (d : Real) then
        (ArithmeticFunction.moebius d : Complex) * ((X / (d : Real) : Real) : Complex) *
          integral volume (fun x : Real => f x) else 0) +
      (if Y < (d : Real) /\ (d : Real) <= Z then
        (ArithmeticFunction.moebius d : Complex) * ((X / (d : Real) : Real) : Complex) *
          frequencyPacket L (FourierTransform.fourier f) (X / (d : Real)) else 0) +
      (if (d : Real) <= Y then dualRow f X d else 0) +
      (if Y < (d : Real) /\ (d : Real) <= Z then
        (ArithmeticFunction.moebius d : Complex) * ((X / (d : Real) : Real) : Complex) *
          frequencyTail L (FourierTransform.fourier f) (X / (d : Real)) else 0) +
      (if Z < (d : Real) then
        (ArithmeticFunction.moebius d : Complex) * offZeroSum f ((d : Real) / X) else 0) := by
  by_cases hlow : (d : Real) <= Y
  . have hsmall : (d : Real) <= Z := hlow.trans hYZ
    have hnotmid : Not (Y < (d : Real) /\ (d : Real) <= Z) :=
      fun h => (not_lt_of_ge hlow) h.1
    have hnothigh : Not (Z < (d : Real)) := not_lt_of_ge hsmall
    rw [if_pos hsmall, if_neg hnothigh, if_neg hnotmid, if_pos hlow,
      if_neg hnotmid, if_neg hnothigh]
    ring
  . have hlower : Y < (d : Real) := lt_of_not_ge hlow
    by_cases hsmall : (d : Real) <= Z
    . have hmid := And.intro hlower hsmall
      have hnothigh : Not (Z < (d : Real)) := not_lt_of_ge hsmall
      rw [if_pos hsmall, if_neg hnothigh, if_pos hmid, if_neg hlow,
        if_pos hmid, if_neg hnothigh]
      have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hd
      unfold dualRow
      rw [frequency_split L (FourierTransform.fourier f) (X / (d : Real)) (div_pos hX hdR)]
      ring
    . have hhigh : Z < (d : Real) := lt_of_not_ge hsmall
      have hnotmid : Not (Y < (d : Real) /\ (d : Real) <= Z) := fun h => hsmall h.2
      rw [if_neg hsmall, if_pos hhigh, if_neg hnotmid, if_neg hlow,
        if_neg hnotmid, if_pos hhigh, dualRow_high d hd X hX f]
      ring

theorem dual_sum_mixed (q : Nat) (hq : 0 < q) (X Y Z : Real)
    (hX : 0 < X) (hYZ : Y <= Z) (L : Nat) (f : SchwartzMap Real Complex) :
    q.divisors.sum (dualRow f X) =
      f 0 * (if q = 1 then 1 else 0) -
      f 0 * (smallDivisors q Z).sum (fun d => (ArithmeticFunction.moebius d : Complex)) -
      largeMain q X Z f + middlePacket q X Y Z L f +
      lowDual q X Y f + middleTail q X Y Z L f + highPrimal q X Z f := by
  have h0 : q.divisors.sum (fun d => (ArithmeticFunction.moebius d : Complex) * f 0) =
      f 0 * (if q = 1 then 1 else 0) := by
    rw [<- Finset.sum_mul, sum_moebius_divisors]
    ring
  have hsmall : q.divisors.sum (fun d => if (d : Real) <= Z then
      (ArithmeticFunction.moebius d : Complex) * f 0 else 0) =
      f 0 * (smallDivisors q Z).sum (fun d => (ArithmeticFunction.moebius d : Complex)) := by
    calc
      _ = (smallDivisors q Z).sum (fun d =>
          (ArithmeticFunction.moebius d : Complex) * f 0) := by
        unfold smallDivisors
        rw [Finset.sum_filter]
      _ = _ := by rw [<- Finset.sum_mul]; ring
  have hhigh : q.divisors.sum (fun d => if Z < (d : Real) then
      (ArithmeticFunction.moebius d : Complex) * ((X / (d : Real) : Real) : Complex) *
        integral volume (fun x : Real => f x) else 0) = largeMain q X Z f := by
    unfold largeMain largeDivisors
    rw [Finset.sum_filter]
  have hpacket : q.divisors.sum (fun d => if Y < (d : Real) /\ (d : Real) <= Z then
      (ArithmeticFunction.moebius d : Complex) * ((X / (d : Real) : Real) : Complex) *
        frequencyPacket L (FourierTransform.fourier f) (X / (d : Real)) else 0) =
      middlePacket q X Y Z L f := by
    unfold middlePacket middleDivisors
    rw [Finset.sum_filter]
  have hlow : q.divisors.sum (fun d => if (d : Real) <= Y then dualRow f X d else 0) =
      lowDual q X Y f := by
    unfold lowDual smallDivisors
    rw [Finset.sum_filter]
  have htail : q.divisors.sum (fun d => if Y < (d : Real) /\ (d : Real) <= Z then
      (ArithmeticFunction.moebius d : Complex) * ((X / (d : Real) : Real) : Complex) *
        frequencyTail L (FourierTransform.fourier f) (X / (d : Real)) else 0) =
      middleTail q X Y Z L f := by
    unfold middleTail middleDivisors
    rw [Finset.sum_filter]
  have hprimal : q.divisors.sum (fun d => if Z < (d : Real) then
      (ArithmeticFunction.moebius d : Complex) * offZeroSum f ((d : Real) / X) else 0) =
      highPrimal q X Z f := by
    unfold highPrimal largeDivisors
    rw [Finset.sum_filter]
  calc
    _ = q.divisors.sum (fun d =>
      (ArithmeticFunction.moebius d : Complex) * f 0 -
      (if (d : Real) <= Z then (ArithmeticFunction.moebius d : Complex) * f 0 else 0) -
      (if Z < (d : Real) then
        (ArithmeticFunction.moebius d : Complex) * ((X / (d : Real) : Real) : Complex) *
          integral volume (fun x : Real => f x) else 0) +
      (if Y < (d : Real) /\ (d : Real) <= Z then
        (ArithmeticFunction.moebius d : Complex) * ((X / (d : Real) : Real) : Complex) *
          frequencyPacket L (FourierTransform.fourier f) (X / (d : Real)) else 0) +
      (if (d : Real) <= Y then dualRow f X d else 0) +
      (if Y < (d : Real) /\ (d : Real) <= Z then
        (ArithmeticFunction.moebius d : Complex) * ((X / (d : Real) : Real) : Complex) *
          frequencyTail L (FourierTransform.fourier f) (X / (d : Real)) else 0) +
      (if Z < (d : Real) then
        (ArithmeticFunction.moebius d : Complex) * offZeroSum f ((d : Real) / X) else 0)) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact dualRow_split d (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hq)
        X Y Z hX hYZ L f
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        h0, hsmall, hhigh, hpacket, hlow, htail, hprimal]

theorem mixed_poisson (q : Nat) (hq : 0 < q) (X Y Z : Real)
    (hX : 0 < X) (hYZ : Y <= Z) (L : Nat) (f : SchwartzMap Real Complex) :
    coprimeSum q X f =
      ((q.totient : Complex) / (q : Complex)) * (X : Complex) *
        integral volume (fun x : Real => f x) +
      f 0 * (if q = 1 then 1 else 0) -
      f 0 * (smallDivisors q Z).sum (fun d => (ArithmeticFunction.moebius d : Complex)) -
      largeMain q X Z f + middlePacket q X Y Z L f + remainder q X Y Z L f := by
  rw [centered_coprime_poisson q hq X hX f]
  change _ + q.divisors.sum (dualRow f X) = _
  rw [dual_sum_mixed q hq X Y Z hX hYZ L f]
  unfold remainder
  ring

theorem mixed_poisson_q_ge_two (q : Nat) (hq : 2 <= q) (X Y Z : Real)
    (hX : 0 < X) (hYZ : Y <= Z) (L : Nat) (f : SchwartzMap Real Complex) :
    coprimeSum q X f =
      ((q.totient : Complex) / (q : Complex)) * (X : Complex) *
        integral volume (fun x : Real => f x) -
      f 0 * (smallDivisors q Z).sum (fun d => (ArithmeticFunction.moebius d : Complex)) -
      largeMain q X Z f + middlePacket q X Y Z L f + remainder q X Y Z L f := by
  have hq0 : 0 < q := by omega
  have hq1 : Not (q = 1) := by omega
  simpa only [if_neg hq1, mul_zero, add_zero] using mixed_poisson q hq0 X Y Z hX hYZ L f

end PrimeFactorOscillations.CoprimeSchwartzMixed
