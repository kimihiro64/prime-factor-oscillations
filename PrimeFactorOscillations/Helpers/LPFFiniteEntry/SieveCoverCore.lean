/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.CheckRoot

/-! Composite certificates avoid repeated primality searches in finite coverage. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def orbitTreeIntegerCover (tree : OrbitWitnessTree) (j p d : Nat) : Bool :=
  orbitTreeCoveredAt tree j p || decide (p < 2 \/ (1 < d /\ d < p /\ p % d = 0))

theorem orbitTreeIntegerCover_reachable (tree : OrbitWitnessTree)
    (hTree : orbitTreeCheck tree = true) (j p d : Nat) (hp : Nat.Prime p)
    (h : orbitTreeIntegerCover tree j p d = true) :
    Membership.mem (fullOrbit {2} j) p := by
  simp only [orbitTreeIntegerCover, Bool.or_eq_true] at h
  rcases h with hCovered | hComposite
  next => exact orbitTreeCoveredAt_reachable tree hTree j p hCovered
  next =>
    have hProp : p < 2 \/ (1 < d /\ d < p /\ p % d = 0) := of_decide_eq_true hComposite
    rcases hProp with hSmall | hFactor
    next => have hTwo := hp.two_le; omega
    next =>
      have hDvd : Dvd.dvd d p := Nat.dvd_of_mod_eq_zero hFactor.2.2
      have hCases := hp.eq_one_or_self_of_dvd d hDvd
      rcases hCases with hOne | hEqual <;> omega

def orbitTreeSieveIntervalCheck (tree : OrbitWitnessTree) (j : Nat) :
    Nat -> List Nat -> Bool
  | _, [] => true
  | start, d :: ds =>
    orbitTreeIntegerCover tree j start d &&
      orbitTreeSieveIntervalCheck tree j (start + 1) ds

theorem orbitTreeSieveIntervalCheck_reachable (tree : OrbitWitnessTree)
    (hTree : orbitTreeCheck tree = true) (j : Nat) (ds : List Nat) (start : Nat)
    (hInterval : orbitTreeSieveIntervalCheck tree j start ds = true)
    (p : Nat) (hp : Nat.Prime p) (hStart : start <= p) (hEnd : p < start + ds.length) :
    Membership.mem (fullOrbit {2} j) p := by
  induction ds generalizing start with
  | nil => simp only [List.length_nil, Nat.add_zero] at hEnd; omega
  | cons d ds ih =>
    have hParts : And (orbitTreeIntegerCover tree j start d = true)
        (orbitTreeSieveIntervalCheck tree j (start + 1) ds = true) := by
      simpa only [orbitTreeSieveIntervalCheck, Bool.and_eq_true] using hInterval
    by_cases hEqual : p = start
    next =>
      subst p
      exact orbitTreeIntegerCover_reachable tree hTree j start d hp hParts.1
    next =>
      apply ih (start + 1) hParts.2
      next => omega
      next => simp only [List.length_cons] at hEnd; omega

end PrimeFactorOscillations.LPF
