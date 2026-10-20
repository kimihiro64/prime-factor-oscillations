/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticGaussCoefficient

/-!
# QuadraticShiftedMass

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

namespace PrimeFactorOscillations.QuadraticShiftedMass

open QuadraticGaussCoefficient QuadraticDivisorMean IntegerQuadraticPrefix

theorem shifted_mass_le (e delta : Nat) (S T : Finset Nat) (a : Nat -> Complex)
    (hDelta : 0 < delta)
    (hImage : forall n, Membership.mem S n -> Membership.mem T (n * delta)) :
    maskedMass e S (fun n => a (n * delta)) <= maskedMass 1 T a := by
  simp only [maskedMass, Nat.one_dvd, ite_true]
  apply Finset.sum_le_sum_of_injOn (fun n : Nat => n * delta)
  . intro n hn m hm hnm
    exact Nat.mul_right_cancel hDelta hnm
  . intro x hx
    choose n hn hnx using Finset.mem_image.mp hx
    rw [<- hnx]
    exact hImage n hn
  . intro n hn
    split_ifs
    . exact le_refl _
    . exact sq_nonneg _
  . intro n hn hnot
    exact sq_nonneg _

theorem shifted_root_mass (e N delta : Nat) (k : Int) (S T : Finset Nat)
    (a : Nat -> Complex) (hDelta : 0 < delta)
    (hS : forall n, Membership.mem S n -> Membership.mem (columns N) n)
    (hImage : forall n, Membership.mem S n -> Membership.mem T (n * delta)) :
    maskedMass e S (rootCoefficient (fun n => a (n * delta)) k) <= maskedMass 1 T a :=
  (rootCoefficient_mass e N k S (fun n => a (n * delta)) hS).trans
    (shifted_mass_le e delta S T a hDelta hImage)

theorem shifted_inverse_mass (e N delta : Nat) (k : Int) (S T : Finset Nat)
    (a : Nat -> Complex) (U : Real) (hU : 0 < U) (hDelta : 0 < delta)
    (hS : forall n, Membership.mem S n -> Membership.mem (columns N) n)
    (hImage : forall n, Membership.mem S n -> Membership.mem T (n * delta))
    (hLower : forall n, Membership.mem S n -> U <= (n : Real)) :
    maskedMass e S (inverseCoefficient (fun n => a (n * delta)) k) <=
      (1 / U) * maskedMass 1 T a :=
  (inverseCoefficient_mass e N k S (fun n => a (n * delta)) U hU hS hLower).trans
    (mul_le_mul_of_nonneg_left (shifted_mass_le e delta S T a hDelta hImage)
      (by positivity))

end PrimeFactorOscillations.QuadraticShiftedMass

