/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFDynamics

/-!
# Exact residue-cover obstructions for one LPF generation

These statements concern arbitrary finite prime states. They do not assert
that an orbit from a designated diagonal seed reaches an obstructed state.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem no_sum_of_prime_residue_cover (S : Finset Nat) (z t : Nat)
    (hPrime : forall p, Membership.mem S p -> Nat.Prime p)
    (hLarge : forall p, Membership.mem S p -> z < p)
    (hCover : forall p, Membership.mem S p -> exists ell : Nat,
      And (Nat.Prime ell) (And (ell <= z)
        (And (Dvd.dvd ell (p - 1)) (Dvd.dvd ell (t - 1))))) :
    Not (exists p, exists q, And (Membership.mem S p)
      (And (Membership.mem S q) (p + q = t))) := by
  intro h
  let p := Classical.choose h
  have hp := Classical.choose_spec h
  let q := Classical.choose hp
  have hq := Classical.choose_spec hp
  let ell := Classical.choose (hCover p hq.1)
  have he := Classical.choose_spec (hCover p hq.1)
  have hp2 := (hPrime p hq.1).two_le
  have hSub : (t - 1) - (p - 1) = q := by omega
  have hDiv : Dvd.dvd ell q := by
    have hd := Nat.dvd_sub he.2.2.2 he.2.2.1
    rwa [hSub] at hd
  have hCases := (Nat.dvd_prime (hPrime q hq.2.1)).mp hDiv
  have he2 := he.1.two_le
  have hqLarge := hLarge q hq.2.1
  rcases hCases with hOne | hEqual
  next => omega
  next => omega

theorem not_mem_step_of_no_sum_three_mod_four (S : Finset Nat) (M r : Nat)
    (hM : 3 <= M) (hAbove : M < r) (hMod : r % 4 = 3)
    (hOdd : forall p, Membership.mem S p -> p % 2 = 1)
    (hBound : forall p, Membership.mem S p -> p <= M)
    (hMissing : Not (exists p, exists q, And (Membership.mem S p)
      (And (Membership.mem S q) (p + q = (r + 1) / 2)))) :
    Not (Membership.mem (step S) r) := by
  intro hr
  rcases Finset.mem_union.mp hr with hOld | hNew
  next =>
    have h := hBound r hOld
    omega
  next =>
    let pair := Classical.choose (Finset.mem_image.mp hNew)
    have hp := Classical.choose_spec (Finset.mem_image.mp hNew)
    have hPair := Finset.mem_product.mp (Finset.mem_filter.mp hp.1).1
    have hpo := hOdd pair.1 hPair.1
    have hqo := hOdd pair.2 hPair.2
    have hpb := hBound pair.1 hPair.1
    have hqb := hBound pair.2 hPair.2
    have hN : 1 < affineValue pair.1 pair.2 := by unfold affineValue; omega
    have hTop : affineValue pair.1 pair.2 < 4 * r := by unfold affineValue; omega
    have hNmod : affineValue pair.1 pair.2 % 4 = 3 := by unfold affineValue; omega
    have hDiv : Dvd.dvd r (affineValue pair.1 pair.2) := by
      rw [<- hp.2]
      exact Nat.largestPrimeFactor_dvd hN
    let k := Classical.choose hDiv
    have hk : affineValue pair.1 pair.2 = r * k := Classical.choose_spec hDiv
    have hklt : k < 4 := by
      by_contra h
      have hge : 4 <= k := by omega
      nlinarith
    have hCases : Or (k = 0) (Or (k = 1) (Or (k = 2) (k = 3))) := by omega
    rcases hCases with hZero | hOne | hTwo | hThree
    next => rw [hZero] at hk; omega
    next =>
      rw [hOne] at hk
      have hSum : pair.1 + pair.2 = (r + 1) / 2 := by
        unfold affineValue at hk
        omega
      exact hMissing (Exists.intro pair.1 (Exists.intro pair.2
        (And.intro hPair.1 (And.intro hPair.2 hSum))))
    next => rw [hTwo] at hk; omega
    next => rw [hThree] at hk; omega

theorem not_mem_step_of_prime_residue_cover (S : Finset Nat) (M r z : Nat)
    (hM : 3 <= M) (hz : 2 <= z) (hAbove : M < r) (hMod : r % 4 = 3)
    (hPrime : forall p, Membership.mem S p -> Nat.Prime p)
    (hLarge : forall p, Membership.mem S p -> z < p)
    (hBound : forall p, Membership.mem S p -> p <= M)
    (hCover : forall p, Membership.mem S p -> exists ell : Nat,
      And (Nat.Prime ell) (And (ell <= z)
        (And (Dvd.dvd ell (p - 1)) (Dvd.dvd ell ((r + 1) / 2 - 1))))) :
    Not (Membership.mem (step S) r) := by
  apply not_mem_step_of_no_sum_three_mod_four S M r hM hAbove hMod
  next =>
    intro p hp
    apply (hPrime p hp).eq_two_or_odd.resolve_left
    have h := hLarge p hp
    omega
  next => exact hBound
  next => exact no_sum_of_prime_residue_cover S z ((r + 1) / 2) hPrime hLarge hCover

end PrimeFactorOscillations.LPF
