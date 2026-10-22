/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeRecordCoordinates

/-! # The actual one-sided record values at prime jumps

The real regulator is constant on the whole preceding unit interval.
Its left limit and the jump are identified without assuming continuity
across a prime or excluding the exceptional first prime.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter

theorem greedyPrimeRegulatorReal_left_interval (p : Nat) (t : Real)
    (hlo : ((p - 1 : Nat) : Real) <= t) (hhi : t < (p : Real)) :
    greedyPrimeRegulatorReal t = greedyPrimeRegulator (p - 1) := by
  have ht0 : 0 <= t := (Nat.cast_nonneg (p - 1)).trans hlo
  have hup : Nat.floor t < p := by
    exact_mod_cast (Nat.floor_le ht0).trans_lt hhi
  have hlow : p - 1 <= Nat.floor t := Nat.le_floor hlo
  have heq : Nat.floor t = p - 1 := by omega
  simp only [greedyPrimeRegulatorReal, heq]

theorem greedyPrimeRegulatorReal_left_tendsto (p : Nat) (hp : Nat.Prime p) :
    Tendsto greedyPrimeRegulatorReal (nhdsWithin (p : Real) (Set.Iio (p : Real)))
      (nhds (greedyPrimeRegulator (p - 1))) := by
  have hp2 : 2 <= p := hp.two_le
  have hlt : ((p - 1 : Nat) : Real) < (p : Real) := by
    exact_mod_cast (by omega : p - 1 < p)
  have hlo : _root_.Filter.Eventually (fun t : Real => ((p - 1 : Nat) : Real) < t)
      (nhdsWithin (p : Real) (Set.Iio (p : Real))) :=
    _root_.Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hlt)
  have hhi : _root_.Filter.Eventually (fun t : Real => t < (p : Real))
      (nhdsWithin (p : Real) (Set.Iio (p : Real))) := self_mem_nhdsWithin
  have heq : _root_.Filter.Eventually (fun t : Real =>
      greedyPrimeRegulator (p - 1) = greedyPrimeRegulatorReal t)
      (nhdsWithin (p : Real) (Set.Iio (p : Real))) := by
    filter_upwards [hlo, hhi] with t htlo hthi
    exact (greedyPrimeRegulatorReal_left_interval p t htlo.le hthi).symm
  exact Tendsto.congr' heq tendsto_const_nhds

theorem primeRecordJump_left_limit (p : Nat) (hp : Nat.Prime p) :
    And (Tendsto greedyPrimeRegulatorReal
      (nhdsWithin (p : Real) (Set.Iio (p : Real)))
      (nhds (greedyPrimeRegulator (p - 1))))
      (primeRecordJump p =
        greedyPrimeRegulatorReal (p : Real) - greedyPrimeRegulator (p - 1)) := by
  refine And.intro (greedyPrimeRegulatorReal_left_tendsto p hp) ?_
  simpa only [greedyPrimeRegulatorReal, Nat.floor_natCast] using
    primeRecordJump_eq_regulator_sub p hp

theorem greedyPrimeRegulator_one : greedyPrimeRegulator 1 = 0 := by
  have hcount : Nat.count Nat.Prime 2 = 0 := by decide
  simp only [greedyPrimeRegulator, primeCutoffLength, hcount, clockRecord]

theorem greedyPrimeRegulatorReal_left_two :
    Tendsto greedyPrimeRegulatorReal (nhdsWithin (2 : Real) (Set.Iio (2 : Real)))
      (nhds 0) := by
  simpa only [Nat.cast_ofNat, show 2 - 1 = (1 : Nat) by decide,
    greedyPrimeRegulator_one] using
    greedyPrimeRegulatorReal_left_tendsto 2 Nat.prime_two

end PrimeFactorOscillations.PrimeClassDeletion
