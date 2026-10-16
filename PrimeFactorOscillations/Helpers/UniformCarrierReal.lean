/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.UniformCarrierClock

/-!
# Uniform Carrier Real

Two anchored probability laws encode every bounded real mark with a uniform quadratic-weight error.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.UniformCarrier

def positiveLaw (u : Nat.Primes -> Real)
    (hu : forall p, -1 <= u p /\ u p <= 1) : PrimeClockLaw :=
  BoundedAmplitudeDetector.law (fun p => (1 + u p) / 2)
    (fun p => by linarith [(hu p).1])
    (fun p => by linarith [(hu p).2])

def negativeLaw (u : Nat.Primes -> Real)
    (hu : forall p, -1 <= u p /\ u p <= 1) : PrimeClockLaw :=
  positiveLaw (fun p => -u p) (fun p => And.intro (by linarith [(hu p).2])
    (by linarith [(hu p).1]))

theorem positiveLaw_compensator (u : Nat.Primes -> Real)
    (hu : forall p, -1 <= u p /\ u p <= 1) (p : Nat.Primes) :
    (positiveLaw u hu).compensator p =
      ((1 + u p) / 2) / (((p : Nat) : Real) - (1 + u p) / 2) := rfl

theorem marked_laws_same (u : Nat.Primes -> Real)
    (hu : forall p, -1 <= u p /\ u p <= 1) (T : Finset Nat.Primes)
    (hSupport : forall p, Not (Membership.mem T p) -> u p = 0) (N : Nat) :
    (forall p, Membership.mem (primeProfilePrefixSet N \ T) p ->
      (positiveLaw u hu).weight p = baseline.weight p /\
      (positiveLaw u hu).compensator p = baseline.compensator p) /\
    (forall p, Membership.mem (primeProfilePrefixSet N \ T) p ->
      (negativeLaw u hu).weight p = baseline.weight p /\
      (negativeLaw u hu).compensator p = baseline.compensator p) := by
  constructor
  . intro p hp
    have hz := hSupport p (Finset.mem_sdiff.mp hp).2
    constructor <;> change ((1 + u p) / 2) / (((p : Nat) : Real) - (1 + u p) / 2) =
      (1 / 2 : Real) / (((p : Nat) : Real) - 1 / 2) <;> rw [hz, add_zero]
  . intro p hp
    have hz := hSupport p (Finset.mem_sdiff.mp hp).2
    constructor <;> change ((1 + -u p) / 2) / (((p : Nat) : Real) - (1 + -u p) / 2) =
      (1 / 2 : Real) / (((p : Nat) : Real) - 1 / 2) <;> rw [hz, neg_zero, add_zero]

theorem marked_clock_pair_error (u : Nat.Primes -> Real)
    (hu : forall p, -1 <= u p /\ u p <= 1) (N : Nat)
    (T : Finset Nat.Primes) (hT : T <= primeProfilePrefixSet N)
    (hSupport : forall p, Not (Membership.mem T p) -> u p = 0) :
    abs ((positiveLaw u hu).arithmeticClock N - (negativeLaw u hu).arithmeticClock N -
      T.sum (fun p => u p / ((p : Nat) : Real))) <=
        2 * T.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) := by
  have hSame := marked_laws_same u hu T hSupport N
  rw [clock_difference_eq (positiveLaw u hu) (negativeLaw u hu) N T hT
    (fun p hp => (hSame.1 p hp).2.trans (hSame.2 p hp).2.symm),
    <- Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hpR : (1 : Real) < (p : Nat) := by exact_mod_cast p.property.one_lt
  have hh := BoundedAmplitudeDetector.anchored_odds_error
    ((p : Nat) : Real) (u p) hpR (hu p).1 (hu p).2
  have hCast : ((((p : Nat) - 1 : Nat) : Real)) = ((p : Nat) : Real) - 1 := by
    rw [Nat.cast_sub p.property.one_lt.le, Nat.cast_one]
  change abs (((1 + u p) / 2) / (((p : Nat) : Real) - (1 + u p) / 2) -
      ((1 + -u p) / 2) / (((p : Nat) : Real) - (1 + -u p) / 2) -
        u p / ((p : Nat) : Real)) <= _
  apply hh.trans
  calc
    2 / (((p : Nat) : Real) * (((p : Nat) : Real) - 1)) <=
        2 / ((((p : Nat) : Real) - 1) ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (by nlinarith : (((p : Nat) : Real) - 1) ^ 2 <= ((p : Nat) : Real) * (((p : Nat) : Real) - 1))
    _ = 2 * (primeProfileWeight (p : Nat)) ^ 2 := by
      rw [primeProfileWeight, hCast, div_pow]
      ring

theorem exists_real_carrier (alpha : Real) (ha : 0 < alpha) :
    exists P0 : Nat, exists C : Real, 1 <= P0 /\ 0 < C /\
      forall P : Nat, P0 <= P ->
      forall T : Finset Nat.Primes, T <= primeProfilePrefixSet (2 * P) ->
      (forall p, Membership.mem T p -> P < (p : Nat)) -> T.card <= P / 100 ->
      forall u : Nat.Primes -> Real,
      forall hu : (forall p, -1 <= u p /\ u p <= 1),
      (forall p, Not (Membership.mem T p) -> u p = 0) ->
      exists UP UM : Real,
        (positiveLaw u hu).densityRatio (2 * P)
          (Nat.floor (alpha * baseline.arithmeticClock (2 * P))) =
            prefixRatio baseline (2 * P) (Nat.floor (alpha * baseline.arithmeticClock (2 * P))) UP /\
        (negativeLaw u hu).densityRatio (2 * P)
          (Nat.floor (alpha * baseline.arithmeticClock (2 * P))) =
            prefixRatio baseline (2 * P) (Nat.floor (alpha * baseline.arithmeticClock (2 * P))) UM /\
        abs (UP - UM - T.sum (fun p => u p / ((p : Nat) : Real))) <=
          C * (T.card : Real) / (P : Real) ^ 2 /\
        abs (UP - baseline.arithmeticClock (2 * P)) <= 1 / 2 /\
        abs (UM - baseline.arithmeticClock (2 * P)) <= 1 / 2 := by
  choose r0 N0 PP C hr0 hN0 hPP hC hInv using
    exists_uniform_carrier_inverse baseline baseline_scale baseline_error
      (alpha / 4) (by positivity) (4 * alpha) (by positivity)
  choose P1 hRank using eventual_carrier_rank alpha ha r0 N0 PP
  let P0 := max 1 P1
  refine Exists.intro P0 (Exists.intro (2 * C + 2)
    (And.intro (le_max_left _ _) (And.intro (by positivity) ?_)))
  intro P hP T hT hprime hcard u hu hSupport
  have hP1 : P1 <= P := (le_max_right _ _).trans hP
  have hPpos : 1 <= P := (le_max_left _ _).trans hP
  have hRanks := hRank P hP1
  let N := 2 * P
  let r := Nat.floor (alpha * baseline.arithmeticClock N)
  have hSame := marked_laws_same u hu T hSupport N
  choose UP hUP hRootP hUniqueP using hInv r hRanks.2.2.2.1 N hRanks.2.1
    hRanks.2.2.1 hRanks.2.2.2.2.1 hRanks.2.2.2.2.2 P hRanks.1
    (positiveLaw u hu) rfl rfl T hT hprime hcard hSame.1
  choose UM hUM hRootM hUniqueM using hInv r hRanks.2.2.2.1 N hRanks.2.1
    hRanks.2.2.1 hRanks.2.2.2.2.1 hRanks.2.2.2.2.2 P hRanks.1
    (negativeLaw u hu) rfl rfl T hT hprime hcard hSame.2
  have hClock := marked_clock_pair_error u hu N T hT hSupport
  have hdelta := (sparse_weight_sums P hPpos T hprime).2
  let BP := (positiveLaw u hu).arithmeticClock N
  let BM := (negativeLaw u hu).arithmeticClock N
  let S := T.sum (fun p => u p / ((p : Nat) : Real))
  refine Exists.intro UP (Exists.intro UM (And.intro hRootP
    (And.intro hRootM (And.intro ?_ (And.intro hUniqueP.2 hUniqueM.2)))))
  calc
    abs (UP - UM - S) = abs ((UP - BP) - (UM - BM) + (BP - BM - S)) := by congr 1; ring
    _ <= abs (UP - BP) + abs (UM - BM) + abs (BP - BM - S) :=
      (abs_add_le _ _).trans (_root_.add_le_add (abs_sub _ _) le_rfl)
    _ <= C * (T.card : Real) / (P : Real) ^ 2 +
        C * (T.card : Real) / (P : Real) ^ 2 +
        2 * ((T.card : Real) / (P : Real) ^ 2) := by
      exact add_le_add (add_le_add hUP hUM)
        (hClock.trans (mul_le_mul_of_nonneg_left hdelta (by norm_num)))
    _ = _ := by ring

end PrimeFactorOscillations.UniformCarrier
