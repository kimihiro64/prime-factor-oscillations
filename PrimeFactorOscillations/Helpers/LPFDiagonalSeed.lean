/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime
import PrimeFactorOscillations.Helpers.LPFDynamics

/-!
# Diagonal seeds and their transfer to the current inclusive dynamics

The historical step/orbit lemmas analyze one diagonal followed by distinct
inputs. Current fullStep/fullOrbit permits diagonals every time and starts
from {2,p}. The historical lemmas remain valid for the subordinate operator;
their closure examples do not describe the current dynamics. The final lemmas
transfer the seed into the inclusive orbit and prove its shared access to three.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def diagonalSeed (p : Nat) : Finset Nat :=
  {p, Nat.largestPrimeFactor (4 * p - 1)}

def diagonalSeedWithTwo (p : Nat) : Finset Nat := insert 2 (diagonalSeed p)

private theorem not_dvd_diagonal_self (p : Nat) (hp : 2 <= p) :
    Not (Dvd.dvd p (4 * p - 1)) := by
  intro hd
  have hFour : Dvd.dvd p (4 * p) := dvd_mul_of_dvd_right (dvd_refl p) 4
  have heq : 4 * p = (4 * p - 1) + 1 := by omega
  rw [heq] at hFour
  have hOne : Dvd.dvd p 1 := (Nat.dvd_add_iff_right hd).mpr hFour
  have := Nat.eq_one_of_dvd_one hOne
  omega

private theorem not_dvd_pair_of_dvd_diagonal (p q : Nat)
    (hp : 2 <= p) (hq : 2 <= q) (hd : Dvd.dvd q (4 * p - 1)) :
    Not (Dvd.dvd q (2 * (p + q) - 1)) := by
  intro hb
  have hTwo : Dvd.dvd q (2 * (2 * (p + q) - 1)) :=
    dvd_mul_of_dvd_right hb 2
  have hFour : Dvd.dvd q (4 * q) := dvd_mul_of_dvd_right (dvd_refl q) 4
  have hSum := dvd_add hd hFour
  have heq : (4 * p - 1) + 4 * q = 2 * (2 * (p + q) - 1) + 1 := by omega
  rw [heq] at hSum
  have hOne : Dvd.dvd q 1 := (Nat.dvd_add_iff_right hTwo).mpr hSum
  have := Nat.eq_one_of_dvd_one hOne
  omega

theorem diagonal_factor_ne_self (p : Nat) (hp : Nat.Prime p) :
    Not (Nat.largestPrimeFactor (4 * p - 1) = p) := by
  intro h
  have hp2 := hp.two_le
  have hd := Nat.largestPrimeFactor_dvd (show 1 < 4 * p - 1 by omega)
  rw [h] at hd
  exact not_dvd_diagonal_self p hp2 hd

/-- The unaugmented diagonal seed at three is still closed under distinct inputs. -/
theorem orbit_diagonalSeed_three (j : Nat) : orbit (diagonalSeed 3) j = diagonalSeed 3 := by
  have h3 : Nat.Prime 3 := by decide
  have h11 : Nat.Prime 11 := by decide
  have hd : diagonalSeed 3 = {3, 11} := by
    unfold diagonalSeed
    rw [show 4 * 3 - 1 = 11 by decide, Nat.largestPrimeFactor_of_prime h11]
  have h9 : Nat.largestPrimeFactor (3 * 3) = 3 :=
    Nat.largestPrimeFactor_mul_prime (by decide) h3
      (Nat.largestPrimeFactor_of_prime h3).le
  have h27 : Nat.largestPrimeFactor 27 = 3 :=
    Nat.largestPrimeFactor_mul_prime (m := 3 * 3) (by decide) h3 h9.le
  rw [hd]
  apply orbit_eq_of_step_eq_self
  apply (step_eq_self_iff {3, 11}).mpr
  intro p q hp hq hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  have hv : affineValue p q = 27 := by unfold affineValue; omega
  rw [hv, h27]
  simp

/-- Every prime seed, augmented by its diagonal output and two, grows once. -/
theorem diagonalSeedWithTwo_not_closed (p : Nat) (hp : Nat.Prime p) :
    Not (step (diagonalSeedWithTwo p) = diagonalSeedWithTwo p) := by
  by_cases hp2 : p = 2
  next =>
    subst p
    intro h
    have h7 : Nat.Prime 7 := by decide
    have hd : diagonalSeedWithTwo 2 = {2, 7} := by
      unfold diagonalSeedWithTwo diagonalSeed
      rw [show 4 * 2 - 1 = 7 by decide, Nat.largestPrimeFactor_of_prime h7]
      simp
    have hnew := mem_step_of_pair (diagonalSeedWithTwo 2) (p := 2) (q := 7)
      (by rw [hd]; simp) (by rw [hd]; simp) (by decide)
    change Membership.mem (step (diagonalSeedWithTwo 2)) (Nat.largestPrimeFactor 17) at hnew
    rw [Nat.largestPrimeFactor_of_prime (by decide : Nat.Prime 17), h, hd] at hnew
    norm_num at hnew
  by_cases hp3 : p = 3
  next =>
    subst p
    intro h
    have h11 : Nat.Prime 11 := by decide
    have hd : diagonalSeedWithTwo 3 = {2, 3, 11} := by
      unfold diagonalSeedWithTwo diagonalSeed
      rw [show 4 * 3 - 1 = 11 by decide, Nat.largestPrimeFactor_of_prime h11]
    have hnew := mem_step_of_pair (diagonalSeedWithTwo 3) (p := 2) (q := 11)
      (by rw [hd]; simp) (by rw [hd]; simp) (by decide)
    have h5 : Nat.Prime 5 := by decide
    have h25 : Nat.largestPrimeFactor 25 = 5 :=
      Nat.largestPrimeFactor_mul_prime (m := 5) (by decide) h5
        (Nat.largestPrimeFactor_of_prime h5).le
    change Membership.mem (step (diagonalSeedWithTwo 3)) (Nat.largestPrimeFactor 25) at hnew
    rw [h25, h, hd] at hnew
    norm_num at hnew
  intro hClosed
  let q := Nat.largestPrimeFactor (4 * p - 1)
  let S := diagonalSeedWithTwo p
  have hpLow := hp.two_le
  have hn : 1 < 4 * p - 1 := by omega
  have hqPrime : Nat.Prime q := Nat.largestPrimeFactor_prime hn
  have hqLow := hqPrime.two_le
  have hqDvd : Dvd.dvd q (4 * p - 1) := Nat.largestPrimeFactor_dvd hn
  have hpq : Not (p = q) := Ne.symm (diagonal_factor_ne_self p hp)
  have hClass : forall r, Membership.mem S r -> Or (r = 2) (Or (r = p) (r = q)) := by
    intro r hr
    simpa only [S, diagonalSeedWithTwo, diagonalSeed, Finset.mem_insert,
      Finset.mem_singleton, q] using hr
  have hTwo : Membership.mem S 2 := by simp [S, diagonalSeedWithTwo]
  have hP : Membership.mem S p := by simp [S, diagonalSeedWithTwo, diagonalSeed]
  have hQ : Membership.mem S q := by simp [S, diagonalSeedWithTwo, diagonalSeed, q]
  have hClosedPairs := (step_eq_self_iff S).mp hClosed
  let r := Nat.largestPrimeFactor (2 * p + 3)
  have hrDvd : Dvd.dvd r (2 * p + 3) := Nat.largestPrimeFactor_dvd (by omega)
  have hrMem : Membership.mem S r := by
    have h := hClosedPairs 2 p hTwo hP (Ne.symm hp2)
    have hv : affineValue 2 p = 2 * p + 3 := by unfold affineValue; omega
    simpa only [hv, r] using h
  have hrNe2 : Not (r = 2) := by
    intro h
    rw [h] at hrDvd
    have := Nat.mod_eq_zero_of_dvd hrDvd
    omega
  have hrNeP : Not (r = p) := by
    intro h
    rw [h] at hrDvd
    have hTwoP : Dvd.dvd p (2 * p) := dvd_mul_of_dvd_right (dvd_refl p) 2
    have hThree : Dvd.dvd p 3 := (Nat.dvd_add_iff_right hTwoP).mpr hrDvd
    have := Nat.le_of_dvd (by omega : 0 < 3) hThree
    omega
  have hrEq : r = q := by
    rcases hClass r hrMem with h | h
    next => exact False.elim (hrNe2 h)
    next => exact h.resolve_left hrNeP
  have hqOther : Dvd.dvd q (2 * p + 3) := by simpa only [hrEq] using hrDvd
  have hqSeven : Dvd.dvd q 7 := by
    have hDouble : Dvd.dvd q (2 * (2 * p + 3)) := dvd_mul_of_dvd_right hqOther 2
    have heq : 2 * (2 * p + 3) = (4 * p - 1) + 7 := by omega
    rw [heq] at hDouble
    exact (Nat.dvd_add_iff_right hqDvd).mpr hDouble
  have hqEq : q = 7 := by
    have h := (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hqSeven
    omega
  let t := Nat.largestPrimeFactor (2 * (p + q) - 1)
  have htDvd : Dvd.dvd t (2 * (p + q) - 1) := Nat.largestPrimeFactor_dvd (by omega)
  have htMem : Membership.mem S t := hClosedPairs p q hP hQ hpq
  have htNe2 : Not (t = 2) := by
    intro h
    rw [h] at htDvd
    have := Nat.mod_eq_zero_of_dvd htDvd
    omega
  have htNeQ : Not (t = q) := by
    intro h
    rw [h] at htDvd
    exact not_dvd_pair_of_dvd_diagonal p q hpLow hqLow hqDvd htDvd
  have htEq : t = p := by
    rcases hClass t htMem with h | h
    next => exact False.elim (htNe2 h)
    next => exact h.resolve_right htNeQ
  have hpThirteen : Dvd.dvd p 13 := by
    rw [htEq, hqEq] at htDvd
    have heq : 2 * (p + 7) - 1 = 2 * p + 13 := by omega
    rw [heq] at htDvd
    exact (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right (dvd_refl p) 2)).mpr htDvd
  have hpEq : p = 13 := by
    have h := (Nat.dvd_prime (by decide : Nat.Prime 13)).mp hpThirteen
    omega
  rw [hqEq, hpEq] at hqDvd
  exact (by decide : Not (Dvd.dvd 7 (4 * 13 - 1))) hqDvd

theorem exists_new_prime_diagonalSeedWithTwo (p : Nat) (hp : Nat.Prime p) :
    exists r, And (Nat.Prime r)
      (And (Membership.mem (step (diagonalSeedWithTwo p)) r)
        (Not (Membership.mem (diagonalSeedWithTwo p) r))) := by
  classical
  have hSeed : forall r, Membership.mem (diagonalSeedWithTwo p) r -> Nat.Prime r := by
    intro r hr
    simp only [diagonalSeedWithTwo, diagonalSeed, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with h | h
    next => rw [h]; decide
    next =>
      rcases h with h | h
      next => rw [h]; exact hp
      next =>
        rw [h]
        apply Nat.largestPrimeFactor_prime
        have := hp.two_le
        omega
  by_contra h
  apply diagonalSeedWithTwo_not_closed p hp
  apply le_antisymm ?_ (subset_step _)
  intro r hr
  by_contra hrNot
  exact h (Exists.intro r (And.intro (step_preserves_primes _ hSeed r hr)
    (And.intro hr hrNot)))

private theorem diagonal_cross_divisibility_bound (p q : Nat) (hp : 2 <= p) (hq : 2 <= q)
    (hd : Dvd.dvd q (4 * p - 1)) (he : Dvd.dvd p (2 * q - 1)) : p <= 9 := by
  let k : Nat := Classical.choose hd
  let t : Nat := Classical.choose he
  have hk : 4 * p - 1 = q * k := Classical.choose_spec hd
  have ht : 2 * q - 1 = p * t := Classical.choose_spec he
  have hk' : 4 * p = q * k + 1 := by omega
  have ht' : 2 * q = p * t + 1 := by omega
  have htpos : 1 <= t := by
    by_contra h
    have htzero : t = 0 := by omega
    rw [htzero, Nat.mul_zero] at ht'
    omega
  have hrel : p * (k * t) + (k + 2) = 8 * p := by
    have hmul := congrArg (fun a : Nat => a * k) ht'
    nlinarith
  have hprod : k * t <= 7 := by
    by_contra h
    have hge : 8 <= k * t := by omega
    have hmul := Nat.mul_le_mul_left p hge
    nlinarith
  have hkprod : k <= k * t := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left k htpos
  have hk7 : k <= 7 := hkprod.trans hprod
  have hmul := Nat.mul_le_mul_left p hprod
  nlinarith

theorem diagonalSeed_closed_iff (p : Nat) (hp : Nat.Prime p) :
    step (diagonalSeed p) = diagonalSeed p <-> p = 3 := by
  constructor
  next =>
    intro hClosed
    let q := Nat.largestPrimeFactor (4 * p - 1)
    have hpLow := hp.two_le
    have hn : 1 < 4 * p - 1 := by omega
    have hqPrime : Nat.Prime q := Nat.largestPrimeFactor_prime hn
    have hqLow := hqPrime.two_le
    have hqDvd : Dvd.dvd q (4 * p - 1) := Nat.largestPrimeFactor_dvd hn
    have hpq : Not (p = q) := Ne.symm (diagonal_factor_ne_self p hp)
    have hPair := (step_eq_self_iff (diagonalSeed p)).mp hClosed p q
      (by simp [diagonalSeed]) (by simp [diagonalSeed, q]) hpq
    let r := Nat.largestPrimeFactor (affineValue p q)
    have hrDvd : Dvd.dvd r (2 * (p + q) - 1) :=
      Nat.largestPrimeFactor_dvd (show 1 < 2 * (p + q) - 1 by omega)
    have hNotQ : Not (r = q) := by
      intro h
      rw [h] at hrDvd
      exact not_dvd_pair_of_dvd_diagonal p q hpLow hqLow hqDvd hrDvd
    have hCases : Or (r = p) (r = q) := by
      simpa only [diagonalSeed, Finset.mem_insert, Finset.mem_singleton, r, q] using hPair
    have hrEq : r = p := hCases.resolve_right hNotQ
    have hpDvd : Dvd.dvd p (2 * q - 1) := by
      rw [hrEq] at hrDvd
      have heq : 2 * (p + q) - 1 = 2 * p + (2 * q - 1) := by omega
      rw [heq] at hrDvd
      exact (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right (dvd_refl p) 2)).mpr hrDvd
    have hp9 := diagonal_cross_divisibility_bound p q hpLow hqLow hqDvd hpDvd
    have hSmall : Or (p = 2) (Or (p = 3) (Or (p = 5) (p = 7))) := by
      interval_cases p <;> norm_num at *
    rcases hSmall with h | h | h | h
    next =>
      have hq7 : q = 7 := by
        change Nat.largestPrimeFactor (4 * p - 1) = 7
        rw [h]
        exact Nat.largestPrimeFactor_of_prime (by decide : Nat.Prime 7)
      rw [h, hq7] at hpDvd
      norm_num at hpDvd
    next => exact h
    next =>
      have hq19 : q = 19 := by
        change Nat.largestPrimeFactor (4 * p - 1) = 19
        rw [h]
        exact Nat.largestPrimeFactor_of_prime (by decide : Nat.Prime 19)
      rw [h, hq19] at hpDvd
      norm_num at hpDvd
    next =>
      have h3 : Nat.Prime 3 := by decide
      have h9 : Nat.largestPrimeFactor (3 * 3) = 3 :=
        Nat.largestPrimeFactor_mul_prime (by decide) h3
          (Nat.largestPrimeFactor_of_prime h3).le
      have hq3 : q = 3 := by
        change Nat.largestPrimeFactor (4 * p - 1) = 3
        rw [h]
        exact Nat.largestPrimeFactor_mul_prime (m := 3 * 3) (by decide) h3 h9.le
      rw [h, hq3] at hpDvd
      norm_num at hpDvd
  next =>
    intro h
    subst p
    exact orbit_diagonalSeed_three 1

/-- Independent input seed: two is only added at the immediately closed case. -/
def inputSeed (p : Nat) : Finset Nat := if p = 3 then {2, p} else {p}

/-- Apply the designated p-diagonal once; subsequent orbit steps use distinct inputs. -/
def initializedSeed (p : Nat) : Finset Nat :=
  insert (Nat.largestPrimeFactor (4 * p - 1)) (inputSeed p)

theorem initializedSeed_not_closed (p : Nat) (hp : Nat.Prime p) :
    Not (step (initializedSeed p) = initializedSeed p) := by
  by_cases hp3 : p = 3
  next =>
    have hState : initializedSeed p = diagonalSeedWithTwo p := by
      ext r
      simp [initializedSeed, inputSeed, hp3, diagonalSeedWithTwo, diagonalSeed,
        or_comm, or_left_comm, or_assoc]
    rw [hState]
    exact diagonalSeedWithTwo_not_closed p hp
  next =>
    have hState : initializedSeed p = diagonalSeed p := by
      ext r
      simp [initializedSeed, inputSeed, hp3, diagonalSeed, or_comm]
    rw [hState]
    intro h
    exact hp3 ((diagonalSeed_closed_iff p hp).mp h)

/-- Reaching q with two retained allows q's whole diagonal seed one step later. -/
theorem diagonalSeedWithTwo_subset_fullStep {S : Finset Nat} {q : Nat}
    (hTwo : Membership.mem S 2) (hq : Membership.mem S q) :
    diagonalSeedWithTwo q <= fullStep S := by
  intro r hr
  simp only [diagonalSeedWithTwo, diagonalSeed, Finset.mem_insert,
    Finset.mem_singleton] at hr
  rcases hr with h | h | h
  next => simpa only [h] using subset_fullStep S hTwo
  next => simpa only [h] using subset_fullStep S hq
  next => simpa only [h] using mem_fullStep_diagonal S hq

theorem diagonalSeedWithTwo_subset_fullOrbit_one (p : Nat) :
    diagonalSeedWithTwo p <= fullOrbit (fullSeed p) 1 := by
  simpa only [fullOrbit] using
    (diagonalSeedWithTwo_subset_fullStep (S := fullSeed p) (q := p)
      (by simp [fullSeed]) (by simp [fullSeed]))

theorem diagonalSeedWithTwo_not_fullClosed (p : Nat) (hp : Nat.Prime p) :
    Not (fullStep (diagonalSeedWithTwo p) = diagonalSeedWithTwo p) := by
  intro h
  apply diagonalSeedWithTwo_not_closed p hp
  apply le_antisymm ?_ (subset_step _)
  simpa only [h] using step_subset_fullStep (diagonalSeedWithTwo p)

theorem three_mem_fullOrbit_two : Membership.mem (fullOrbit {2} 2) 3 := by
  have h7 : Membership.mem (fullOrbit {2} 1) 7 := by
    have h := mem_fullStep_diagonal {2} (p := 2) (by simp)
    change Membership.mem (fullStep {2}) (Nat.largestPrimeFactor 7) at h
    simpa only [fullOrbit, Nat.largestPrimeFactor_of_prime (by decide : Nat.Prime 7)] using h
  have h3 : Nat.Prime 3 := by decide
  have h9 : Nat.largestPrimeFactor (3 * 3) = 3 :=
    Nat.largestPrimeFactor_mul_prime (by decide) h3
      (Nat.largestPrimeFactor_of_prime h3).le
  have h27 : Nat.largestPrimeFactor 27 = 3 :=
    Nat.largestPrimeFactor_mul_prime (m := 3 * 3) (by decide) h3 h9.le
  have h := mem_fullStep_diagonal (fullOrbit {2} 1) h7
  change Membership.mem (fullStep (fullOrbit {2} 1)) (Nat.largestPrimeFactor 27) at h
  simpa only [fullOrbit, h27] using h

theorem three_mem_fullOrbit_seed_two (p : Nat) :
    Membership.mem (fullOrbit (fullSeed p) 2) 3 :=
  fullOrbit_two_subset_seed p 2 three_mem_fullOrbit_two

/-- Every prime singleton grows under the current rule, using its diagonal. -/
theorem prime_singleton_not_fullClosed (p : Nat) (hp : Nat.Prime p) :
    Not (fullStep {p} = {p}) := by
  intro hClosed
  have h := mem_fullStep_diagonal {p} (p := p) (by simp)
  rw [hClosed] at h
  exact diagonal_factor_ne_self p hp (Finset.mem_singleton.mp h)

/-- The first current generation from three contains eleven. -/
theorem eleven_mem_fullOrbit_three_one :
    Membership.mem (fullOrbit {3} 1) 11 := by
  have h := mem_fullStep_diagonal {3} (p := 3) (by simp)
  change Membership.mem (fullStep {3}) (Nat.largestPrimeFactor 11) at h
  simpa only [fullOrbit,
    Nat.largestPrimeFactor_of_prime (by decide : Nat.Prime 11)] using h

/-- Reusing the eleven diagonal gives forty-three in the second generation. -/
theorem fortyThree_mem_fullOrbit_three_two :
    Membership.mem (fullOrbit {3} 2) 43 := by
  have h := mem_fullStep_diagonal (fullOrbit {3} 1) eleven_mem_fullOrbit_three_one
  change Membership.mem (fullStep (fullOrbit {3} 1)) (Nat.largestPrimeFactor 43) at h
  simpa only [fullOrbit,
    Nat.largestPrimeFactor_of_prime (by decide : Nat.Prime 43)] using h

/-- The historical distinct-input exception also grows when diagonals recur. -/
theorem diagonalSeed_three_not_fullClosed :
    Not (fullStep (diagonalSeed 3) = diagonalSeed 3) := by
  intro hClosed
  have hEleven : Membership.mem (diagonalSeed 3) 11 := by
    simp [diagonalSeed,
      Nat.largestPrimeFactor_of_prime (by decide : Nat.Prime 11)]
  have h := mem_fullStep_diagonal (diagonalSeed 3) hEleven
  change Membership.mem (fullStep (diagonalSeed 3)) (Nat.largestPrimeFactor 43) at h
  rw [Nat.largestPrimeFactor_of_prime (by decide : Nat.Prime 43), hClosed] at h
  norm_num [diagonalSeed,
    Nat.largestPrimeFactor_of_prime (by decide : Nat.Prime 11)] at h

/-- No prime together with its first diagonal output is closed under fullStep. -/
theorem diagonalSeed_not_fullClosed (p : Nat) (hp : Nat.Prime p) :
    Not (fullStep (diagonalSeed p) = diagonalSeed p) := by
  intro hClosed
  have hDistinct : step (diagonalSeed p) = diagonalSeed p := by
    apply le_antisymm ?_ (subset_step _)
    simpa only [hClosed] using step_subset_fullStep (diagonalSeed p)
  have hpThree := (diagonalSeed_closed_iff p hp).mp hDistinct
  subst p
  exact diagonalSeed_three_not_fullClosed hClosed

end PrimeFactorOscillations.LPF
