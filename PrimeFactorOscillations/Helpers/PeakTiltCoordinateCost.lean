/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PeakUniformCoefficients

set_option autoImplicit false
set_option Elab.async false

/-!
# Uniform cost of changing tilted prime coordinates

The complete finite-prefix cost retains the exceptional primes explicitly.
This is an input to coefficient comparison, not a signed Mobius estimate.
-/

namespace PrimeFactorOscillations

theorem regularPrimeLaws_tilt_coordinate_cost_le
    (P n : Nat) (hPn : P <= n) (nu K z : Real)
    (hnu : 0 < nu) (hK : 0 <= K) (hz1 : 1 <= z)
    (eta1 eta2 : Nat -> Real)
    (hunit1 : forall p, Nat.Prime p -> 0 <= eta1 p /\ eta1 p <= 1)
    (hunit2 : forall p, Nat.Prime p -> 0 <= eta2 p /\ eta2 p <= 1)
    (hinterior1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p /\ eta1 p < 1)
    (hinterior2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p /\ eta2 p < 1)
    (hlower1 : forall p, Nat.Prime p -> P < p ->
      (nu / 2) / (p : Real) <= eta1 p / (1 - eta1 p))
    (hlower2 : forall p, Nat.Prime p -> P < p ->
      (nu / 2) / (p : Real) <= eta2 p / (1 - eta2 p))
    (herror1 : forall p, Nat.Prime p -> P < p ->
      abs (eta1 p / (1 - eta1 p) - nu / (p : Real)) <= K / (p : Real) ^ 2)
    (herror2 : forall p, Nat.Prime p -> P < p ->
      abs (eta2 p / (1 - eta2 p) - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    (n + 1).primesBelow.sum (fun p =>
      abs (eta1 p * z / (1 - eta1 p + eta1 p * z) -
        eta2 p * z / (1 - eta2 p + eta2 p * z))) <=
          ((P + 1).primesBelow.card : Real) +
            2 * K * (1 / (nu / 2) ^ 2 + 1 / (nu / 2)) := by
  let A := (n + 1).primesBelow
  let B := (P + 1).primesBelow
  let T := A \ B
  let a1 := fun p => eta1 p / (1 - eta1 p)
  let a2 := fun p => eta2 p / (1 - eta2 p)
  let f1 := fun p => eta1 p * z / (1 - eta1 p + eta1 p * z)
  let f2 := fun p => eta2 p * z / (1 - eta2 p + eta2 p * z)
  let d := fun p => abs (f1 p - f2 p)
  have hz : 0 < z := lt_of_lt_of_le (by norm_num) hz1
  have hc : 0 < nu / 2 := div_pos hnu (by norm_num)
  have hT (p : Nat) (hp : Membership.mem T p) :
      Nat.Prime p /\ P < p /\ p <= n := by
    have hh := Finset.mem_sdiff.mp hp
    have hl := Nat.mem_primesBelow.mp hh.1
    have hcut : Not (p < P + 1) := by
      intro h
      exact hh.2 (Nat.mem_primesBelow.mpr (And.intro h hl.2))
    exact And.intro hl.2 (And.intro (by omega) (by omega))
  have hdiff : forall p, Membership.mem T p ->
      abs (a1 p - a2 p) <= (2 * K) / (p : Real) ^ 2 := by
    intro p hp
    have hh := hT p hp
    calc
      _ <= abs (a1 p - nu / (p : Real)) + abs (nu / (p : Real) - a2 p) :=
        abs_sub_le _ _ _
      _ <= K / (p : Real) ^ 2 + K / (p : Real) ^ 2 := by
        apply add_le_add (herror1 p hh.1 hh.2.1)
        rw [abs_sub_comm]
        exact herror2 p hh.1 hh.2.1
      _ = _ := by ring
  have hSN : forall p, Membership.mem T p -> Membership.mem (Finset.range (n + 1)) p := by
    intro p hp
    exact Finset.mem_range.mpr ((Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).1)
  have hkernel := Finset.sum_abs_tiltOdds_sub_le T (n + 1) hSN a1 a2 (nu / 2)
    (2 * K) z hc (mul_nonneg (by norm_num) hK) hz1
    (fun p hp => (hT p hp).1.one_le)
    (fun p hp => hlower1 p (hT p hp).1 (hT p hp).2.1)
    (fun p hp => hlower2 p (hT p hp).1 (hT p hp).2.1) hdiff
  have htilt (eta : Real) (h0 : 0 < eta) (h1 : eta < 1) :
      eta * z / (1 - eta + eta * z) =
        z * (eta / (1 - eta)) / (1 + z * (eta / (1 - eta))) := by
    have hh := Real.localLaw_tilt_eq_odds_tilt eta z h0 h1 hz
    have hid : 1 + (z - 1) * eta = 1 - eta + eta * z := by ring
    rwa [hid] at hh
  have htail : T.sum d <= 2 * K * (1 / (nu / 2) ^ 2 + 1 / (nu / 2)) := by
    calc
      _ = T.sum (fun p => abs (z * a1 p / (1 + z * a1 p) -
          z * a2 p / (1 + z * a2 p))) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hh := hT p hp
        have h1 := hinterior1 p hh.1 hh.2.1
        have h2 := hinterior2 p hh.1 hh.2.1
        dsimp [d, f1, f2]
        rw [htilt (eta1 p) h1.1 h1.2, htilt (eta2 p) h2.1 h2.2]
      _ <= _ := hkernel
  have hsmall : B.sum d <= (B.card : Real) := by
    calc
      _ <= B.sum (fun _ => (1 : Real)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hprime := (Nat.mem_primesBelow.mp hp).2
        have hu1 := hunit1 p hprime
        have hu2 := hunit2 p hprime
        have ht1 := List.bernoulliTilt_mem_unitInterval (eta1 p) z hu1.1 hu1.2 hz
        have ht2 := List.bernoulliTilt_mem_unitInterval (eta2 p) z hu2.1 hu2.2 hz
        change abs (f1 p - f2 p) <= 1
        exact abs_le.mpr (And.intro (by linarith only [ht1.1, ht2.2])
          (by linarith only [ht1.2, ht2.1]))
      _ = _ := by simp
  have hBA : forall p, Membership.mem B p -> Membership.mem A p := by
    intro p hp
    have hh := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr (And.intro (by omega) hh.2)
  have hsplit : T.sum d + B.sum d = A.sum d := Finset.sum_sdiff hBA
  change A.sum d <= (B.card : Real) + _
  linarith only [hsplit, hsmall, htail]

end PrimeFactorOscillations
