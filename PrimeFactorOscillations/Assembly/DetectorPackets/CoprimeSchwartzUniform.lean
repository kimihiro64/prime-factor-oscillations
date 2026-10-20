/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeSchwartzRemainder

/-!
# CoprimeSchwartzUniform

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

namespace PrimeFactorOscillations.CoprimeSchwartzUniform

open MeasureTheory CoprimeSchwartzPoisson CoprimeSchwartzMixed CoprimeSchwartzRemainder

def mainPacket (q : Nat) (X Y Z : Real) (L : Nat) (f : SchwartzMap Real Complex) : Complex :=
  ((q.totient : Complex) / (q : Complex)) * (X : Complex) *
    integral volume (fun x : Real => f x) +
  f 0 * (if q = 1 then 1 else 0) -
  f 0 * (smallDivisors q Z).sum (fun d => (ArithmeticFunction.moebius d : Complex)) -
  (X : Complex) * integral volume (fun x : Real => f x) *
    (largeDivisors q Z).sum
      (fun d => (ArithmeticFunction.moebius d : Complex) / (d : Complex)) +
  middlePacket q X Y Z L f

theorem mixed_poisson_difference (q : Nat) (hq : 0 < q) (X Y Z : Real)
    (hX : 0 < X) (hYZ : Y <= Z) (L : Nat) (f : SchwartzMap Real Complex) :
    coprimeSum q X f - mainPacket q X Y Z L f = remainder q X Y Z L f := by
  rw [mixed_poisson q hq X Y Z hX hYZ L f, largeMain_factor]
  unfold mainPacket
  ring

theorem mixed_poisson_uniform (f : SchwartzMap Real Complex) (A : Real) (hA : 0 < A) :
    exists C : Real, 0 < C /\
      forall (q L : Nat) (X Y Z J : Real), 0 < q -> 1 <= L ->
      0 < X -> 0 < Y -> Y <= X -> X <= Z -> 0 < J ->
      Y * J <= X -> X * J <= Z -> (Z / X) ^ 2 <= (L : Real) ->
      norm (coprimeSum q X f - mainPacket q X Y Z L f) <= C * X / J ^ A := by
  choose C hC hc using remainder_arbitrary_power f A hA
  refine Exists.intro C (And.intro hC ?_)
  intro q L X Y Z J hq hL hX hY hYX hXZ hJ hYJ hXJ hFreq
  rw [mixed_poisson_difference q hq X Y Z hX (hYX.trans hXZ) L f]
  exact hc q L X Y Z J hq hL hX hY hYX hXZ hJ hYJ hXJ hFreq

end PrimeFactorOscillations.CoprimeSchwartzUniform

