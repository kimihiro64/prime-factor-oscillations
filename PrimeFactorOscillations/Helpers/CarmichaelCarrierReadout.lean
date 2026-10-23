/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ModularReturnFourier

/-!
# Intrinsic power-return spectra and physical carrier reconstruction

All coefficients depend only on the modulus and the tested power. The
unknown carrier is not used in the observable. The full signed centering
uses the actual unit count and actual return count. Rank-one multiplicity
then recovers the carrier as the first positive zero frequency.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelCarrierReadout

open scoped BigOperators
open ModularReturnFourier PrimeOrderReturnIndex
open CarmichaelConditionalRigidity CarmichaelMaximalOrderLifts

local instance factorPrime (B : Nat) (p : B.primeFactors) :
    Fact (Nat.Prime (p.val : Nat)) :=
  Fact.mk (Nat.mem_primeFactors.mp p.property).1

def unitCoefficient (B : Nat) (x : ZMod B) : Rat := by
  classical
  exact if IsUnit x then 1 else 0

def powerCoefficient (B k : Nat) (x : ZMod B) : Rat := by
  classical
  exact if IsUnit x then if x ^ k = 1 then 1 else 0 else 0

def unitCount (B : Nat) [NeZero B] : Rat :=
  Finset.univ.sum (unitCoefficient B)

def powerCount (B : Nat) [NeZero B] (k : Nat) : Rat :=
  Finset.univ.sum (powerCoefficient B k)

def centeredPower (B : Nat) [NeZero B] (k : Nat) (x : ZMod B) : Rat :=
  unitCount B * powerCoefficient B k x - powerCount B k * unitCoefficient B x

theorem unit_count_pos (B : Nat) [NeZero B] : 0 < unitCount B := by
  classical
  unfold unitCount
  apply Finset.sum_pos'
  { intro x _
    by_cases hx : IsUnit x <;> simp [unitCoefficient, hx] }
  { exact Exists.intro 1 (And.intro (Finset.mem_univ _) (by simp [unitCoefficient])) }

theorem owner_power_eq_coefficients (B k : Nat) (q : B.primeFactors) (x : ZMod B) :
    ownerPowerObservable B k q x =
      (Finset.univ.sum (unitWeight (q.val : Nat))) * powerCoefficient B k x -
        (Finset.univ.sum (returnWeight (q.val : Nat) k)) * unitCoefficient B x := by
  classical
  by_cases hx : IsUnit x <;>
    simp only [ownerPowerObservable, unitCoefficient, powerCoefficient, hx,
      ite_true, ite_false, mul_one, mul_zero, sub_self]

theorem fourier_zero_frequency (B : Nat) [NeZero B] (f : ZMod B -> Rat) :
    residueFourier B f 0 = ((Finset.univ.sum f : Rat) : Complex) := by
  simp only [residueFourier, Nat.cast_zero, zero_mul, AddChar.map_zero_eq_one,
    mul_one, Rat.cast_sum]

theorem fourier_const_mul (B : Nat) [NeZero B] (c : Rat)
    (f : ZMod B -> Rat) (h : Nat) :
    residueFourier B (fun x => c * f x) h = (c : Complex) * residueFourier B f h := by
  simp only [residueFourier, Rat.cast_mul, mul_assoc, Finset.mul_sum]

theorem owner_mass_balance (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k : Nat) (q : B.primeFactors)
    (hq : Not (Dvd.dvd ((q.val : Nat) - 1) k))
    (hothers : forall p : B.primeFactors, Not (p = q) ->
      Dvd.dvd ((p.val : Nat) - 1) k) :
    (Finset.univ.sum (unitWeight (q.val : Nat))) * powerCount B k =
      (Finset.univ.sum (returnWeight (q.val : Nat) k)) * unitCount B := by
  have hf := (owner_power_zero_iff B hSq k q hq hothers 0).mpr (dvd_zero _)
  rw [fourier_zero_frequency] at hf
  have hz : Finset.univ.sum (ownerPowerObservable B k q) = 0 := by
    exact_mod_cast hf
  have hs : Finset.univ.sum (ownerPowerObservable B k q) =
      (Finset.univ.sum (unitWeight (q.val : Nat))) * powerCount B k -
        (Finset.univ.sum (returnWeight (q.val : Nat) k)) * unitCount B := by
    simp only [powerCount, unitCount]
    simp_rw [owner_power_eq_coefficients]
    rw [Finset.sum_sub_distrib, <- Finset.mul_sum, <- Finset.mul_sum]
  rw [hs] at hz
  exact sub_eq_zero.mp hz

theorem intrinsic_scaling (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k : Nat) (q : B.primeFactors)
    (hq : Not (Dvd.dvd ((q.val : Nat) - 1) k))
    (hothers : forall p : B.primeFactors, Not (p = q) ->
      Dvd.dvd ((p.val : Nat) - 1) k) (x : ZMod B) :
    (Finset.univ.sum (unitWeight (q.val : Nat))) * centeredPower B k x =
      unitCount B * ownerPowerObservable B k q x := by
  have hb := owner_mass_balance B hSq k q hq hothers
  rw [centeredPower, owner_power_eq_coefficients]
  calc
    _ = unitCount B * ((Finset.univ.sum (unitWeight (q.val : Nat))) *
        powerCoefficient B k x) -
        ((Finset.univ.sum (unitWeight (q.val : Nat))) * powerCount B k) *
          unitCoefficient B x := by ring
    _ = _ := by rw [hb]; ring

theorem intrinsic_power_zero_iff (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k : Nat) (q : B.primeFactors)
    (hq : Not (Dvd.dvd ((q.val : Nat) - 1) k))
    (hothers : forall p : B.primeFactors, Not (p = q) ->
      Dvd.dvd ((p.val : Nat) - 1) k) (h : Nat) :
    residueFourier B (centeredPower B k) h = 0 <-> Dvd.dvd (q.val : Nat) h := by
  have hs :
      (fun x => (Finset.univ.sum (unitWeight (q.val : Nat))) * centeredPower B k x) =
        (fun x => unitCount B * ownerPowerObservable B k q x) :=
    funext (intrinsic_scaling B hSq k q hq hothers)
  have hf := congrArg (fun f : ZMod B -> Rat => residueFourier B f h) hs
  rw [fourier_const_mul, fourier_const_mul] at hf
  have hlocal : Not (((Finset.univ.sum (unitWeight (q.val : Nat)) : Rat) : Complex) = 0) := by
    exact_mod_cast ne_of_gt (unit_mass_pos (q.val : Nat))
  have hglobal : Not ((unitCount B : Complex) = 0) := by
    exact_mod_cast ne_of_gt (unit_count_pos B)
  calc
    _ <-> ((Finset.univ.sum (unitWeight (q.val : Nat)) : Rat) : Complex) *
        residueFourier B (centeredPower B k) h = 0 := by simp only [mul_eq_zero, hlocal, false_or]
    _ <-> (unitCount B : Complex) *
        residueFourier B (ownerPowerObservable B k q) h = 0 := by rw [hf]
    _ <-> residueFourier B (ownerPowerObservable B k q) h = 0 := by simp only [mul_eq_zero, hglobal, false_or]
    _ <-> _ := owner_power_zero_iff B hSq k q hq hothers h

theorem first_positive_zero (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k : Nat) (q : B.primeFactors)
    (hq : Not (Dvd.dvd ((q.val : Nat) - 1) k))
    (hothers : forall p : B.primeFactors, Not (p = q) ->
      Dvd.dvd ((p.val : Nat) - 1) k) :
    And (residueFourier B (centeredPower B k) (q.val : Nat) = 0)
      (forall h : Nat, 0 < h -> h < (q.val : Nat) ->
        Not (residueFourier B (centeredPower B k) h = 0)) := by
  constructor
  { exact (intrinsic_power_zero_iff B hSq k q hq hothers _).mpr (dvd_refl _) }
  { intro h hh hlt hz
    have hd := (intrinsic_power_zero_iff B hSq k q hq hothers h).mp hz
    exact (Nat.not_le.mpr hlt) (Nat.le_of_dvd hh hd) }

theorem rank_one_intrinsic_readout (B : Nat) [NeZero B] (hSq : Squarefree B)
    (L : Nat) (l : Nat.Primes) (hRank : returnMultiplicity B L l = 1) :
    exists q : B.primeFactors,
      And (forall p : B.primeFactors,
        Not (Dvd.dvd ((p.val : Nat) - 1) (L / (l : Nat))) <-> p = q)
      (forall h : Nat, residueFourier B (centeredPower B (L / (l : Nat))) h = 0 <->
        Dvd.dvd (q.val : Nat) h) := by
  classical
  unfold returnMultiplicity at hRank
  choose q hset using Finset.card_eq_one.mp hRank
  have hlabel (p : B.primeFactors) :
      Not (Dvd.dvd ((p.val : Nat) - 1) (L / (l : Nat))) <-> p = q := by
    have hm := Finset.ext_iff.mp hset p
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] using hm
  have hq := (hlabel q).mpr rfl
  have hothers : forall p : B.primeFactors, Not (p = q) ->
      Dvd.dvd ((p.val : Nat) - 1) (L / (l : Nat)) := by
    intro p hp
    by_contra h
    exact hp ((hlabel p).mp h)
  exact Exists.intro q (And.intro hlabel
    (intrinsic_power_zero_iff B hSq (L / (l : Nat)) q hq hothers))

theorem near_minimal_small_labels_readout (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B))))
    (Y : Real) (hY : 0 < Y) (hSmall : conditionalExcess m B a < 1 / Y)
    (l : exponentPrimePacket (m * B)) (hlY : ((l.val : Nat) : Real) <= Y) :
    exists q : B.primeFactors,
      And (forall p : B.primeFactors,
        Not (Dvd.dvd ((p.val : Nat) - 1)
          (Monoid.exponent (Units (ZMod (m * B))) / (l.val : Nat))) <-> p = q)
      (forall h : Nat, residueFourier B
        (centeredPower B (Monoid.exponent (Units (ZMod (m * B))) / (l.val : Nat))) h = 0 <->
        Dvd.dvd (q.val : Nat) h) := by
  have hr := near_minimal_small_labels_unique m B hSqB hCoprime a hFeasible
    Y hY hSmall l hlY
  exact rank_one_intrinsic_readout B hSqB
    (Monoid.exponent (Units (ZMod (m * B)))) l.val hr.2

end PrimeFactorOscillations.CarmichaelCarrierReadout
