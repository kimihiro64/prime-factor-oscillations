/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import PrimeFactorOscillations.Helpers.LPFUpperSieve

/-!
# Upper-sieve energy for fresh canonical LPF fibers

For prime inputs at most M, divide each canonical representation count by
its exact singular divisor product. The existing two-form upper sieve then
bounds every normalized fiber by H = C_2 M / log(M)^2 for M >= 5^8.
Consequently the normalized collision energy is at most H times the
normalized first moment, uniformly for arbitrary prime input subsets.

On a fresh owner the preceding state's canonical count is exactly zero.
The signed old/new expression is kept through this cancellation before
the upper bound is applied. The last two declarations specialize to the
actual fullOrbit {2}, whose fullStep permits diagonals at every stage.
The canonical sum fibers retain 2+2; other input-2 rows are still allowed
by fullStep but need not be represented by this retained packet.

These bounds concern one canonical cofactor per owner, not the full
multi-cofactor owner energy. No assertion of positive fresh first moment,
growth, density, mixing, or unbounded medians is made.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def canonicalSieveWeight (S : Finset Nat) (r : Nat) : Real :=
  ((Finset.sumPartners S (primeTargetSum r)).card : Real) /
    singularDivisorProduct (primeTargetSum r)

theorem sumPartners_card_upper_sieve (M : Nat) (hM : 5 ^ 8 <= M)
    (S : Finset Nat)
    (hS : forall p, Membership.mem S p -> And (Nat.Prime p) (p <= M))
    (t : Nat) (ht : 0 < t) :
    ((Finset.sumPartners S t).card : Real) <=
      sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2) *
        singularDivisorProduct t := by
  apply prime_twoForm_scale_bound M hM t ht
  next =>
    intro p hp
    have hpS := (Finset.mem_filter.mp hp).1
    exact Finset.mem_range.mpr (by have h := (hS p hpS).2; omega)
  next =>
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact And.intro (hS p hpData.1).1 (hS (t - p) hpData.2.1).1

theorem canonicalSieveWeight_nonneg (S : Finset Nat) (r : Nat) :
    0 <= canonicalSieveWeight S r := by
  unfold canonicalSieveWeight
  exact div_nonneg (Nat.cast_nonneg _)
    (zero_le_one.trans (sieve_singularDivisorProduct_one_le _))

theorem canonicalSieveWeight_upper_sieve (M : Nat) (hM : 5 ^ 8 <= M)
    (S : Finset Nat)
    (hS : forall p, Membership.mem S p -> And (Nat.Prime p) (p <= M))
    (r : Nat) (ht : 0 < primeTargetSum r) :
    canonicalSieveWeight S r <=
      sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2) := by
  have hProd : 0 < singularDivisorProduct (primeTargetSum r) :=
    zero_lt_one.trans_le (sieve_singularDivisorProduct_one_le _)
  have hBound := sumPartners_card_upper_sieve M hM S hS (primeTargetSum r) ht
  apply (mul_le_mul_iff_of_pos_right hProd).mp
  have hCancel : canonicalSieveWeight S r *
      singularDivisorProduct (primeTargetSum r) =
        ((Finset.sumPartners S (primeTargetSum r)).card : Real) := by
    unfold canonicalSieveWeight
    field_simp [ne_of_gt hProd]
  rw [hCancel]
  exact hBound

theorem mem_fullStep_of_sumPartners_pos (S : Finset Nat) (r : Nat)
    (hr : Nat.Prime r) (hrThree : 3 <= r)
    (hCount : 0 < (Finset.sumPartners S (primeTargetSum r)).card) :
    Membership.mem (fullStep S) r := by
  let p := Classical.choose (Finset.card_pos.mp hCount)
  have hp := Classical.choose_spec (Finset.card_pos.mp hCount)
  have hpData := Finset.mem_filter.mp hp
  have hSum : p + (primeTargetSum r - p) = primeTargetSum r := by omega
  have hNew := mem_fullStep_of_pair S hpData.1 hpData.2.1
  have hLift := primeTarget_lift r hr hrThree
  have hValue : affineValue p (primeTargetSum r - p) = primeTargetCofactor r * r := by
    unfold affineValue
    rw [hSum]
    omega
  have hOwner := primeTarget_owner r hr hrThree
  rw [hValue, Nat.largestPrimeFactor_mul_prime (Nat.ne_of_gt hOwner.1) hr hOwner.2] at hNew
  exact hNew

theorem sumPartners_eq_zero_on_fresh_owner (A S : Finset Nat)
    (hOld : fullStep A <= S) (r : Nat) (hr : Nat.Prime r) (hrThree : 3 <= r)
    (hFresh : Not (Membership.mem S r)) :
    (Finset.sumPartners A (primeTargetSum r)).card = 0 := by
  by_contra hNonzero
  exact hFresh (hOld (mem_fullStep_of_sumPartners_pos A r hr hrThree
    (Nat.pos_of_ne_zero hNonzero)))

theorem canonicalSieveWeight_energy_upper (M : Nat) (hM : 5 ^ 8 <= M)
    (S G : Finset Nat)
    (hS : forall p, Membership.mem S p -> And (Nat.Prime p) (p <= M))
    (hG : forall r, Membership.mem G r -> And (Nat.Prime r) (3 <= r)) :
    Finset.sum G (fun r => canonicalSieveWeight S r ^ 2) <=
      (sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2)) *
        Finset.sum G (canonicalSieveWeight S) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hLift := primeTarget_lift r (hG r hr).1 (hG r hr).2
  have ht : 0 < primeTargetSum r := by omega
  have hUpper := canonicalSieveWeight_upper_sieve M hM S hS r ht
  have hNonneg := canonicalSieveWeight_nonneg S r
  nlinarith only [mul_le_mul_of_nonneg_right hUpper hNonneg]

theorem canonicalSieveWeight_fresh_birth_energy_upper
    (M : Nat) (hM : 5 ^ 8 <= M) (A S G : Finset Nat) (beta : Real)
    (hS : forall p, Membership.mem S p -> And (Nat.Prime p) (p <= M))
    (hOld : fullStep A <= S)
    (hG : forall r, Membership.mem G r -> And (Nat.Prime r) (3 <= r))
    (hFresh : forall r, Membership.mem G r -> Not (Membership.mem S r)) :
    Finset.sum G (fun r =>
      ((((Finset.sumPartners S (primeTargetSum r)).card : Real) -
        beta * ((Finset.sumPartners A (primeTargetSum r)).card : Real)) /
          singularDivisorProduct (primeTargetSum r)) ^ 2) <=
      (sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2)) *
        Finset.sum G (canonicalSieveWeight S) := by
  have hIdentity : Finset.sum G (fun r =>
      ((((Finset.sumPartners S (primeTargetSum r)).card : Real) -
        beta * ((Finset.sumPartners A (primeTargetSum r)).card : Real)) /
          singularDivisorProduct (primeTargetSum r)) ^ 2) =
      Finset.sum G (fun r => canonicalSieveWeight S r ^ 2) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [sumPartners_eq_zero_on_fresh_owner A S hOld r
      (hG r hr).1 (hG r hr).2 (hFresh r hr)]
    simp only [Nat.cast_zero, mul_zero, sub_zero, canonicalSieveWeight]
  rw [hIdentity]
  exact canonicalSieveWeight_energy_upper M hM S G hS hG

theorem canonicalSieveWeight_fresh_mass_bound
    (M : Nat) (hM : 5 ^ 8 <= M) (S G : Finset Nat)
    (hS : forall p, Membership.mem S p -> And (Nat.Prime p) (p <= M))
    (hG : forall r, Membership.mem G r -> And (Nat.Prime r) (3 <= r))
    (hFresh : forall r, Membership.mem G r -> Not (Membership.mem S r)) :
    Finset.sum G (canonicalSieveWeight S) <=
      (sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2)) *
        ((fullStep S \ S).card : Real) := by
  classical
  let F := G.filter (fun r => 0 < (Finset.sumPartners S (primeTargetSum r)).card)
  let H : Real := sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2)
  have hH : 0 <= H := by
    have hConst := sieveTwoUpperConstant_pos
    dsimp [H]
    positivity
  have hSubset : F <= fullStep S \ S := by
    intro r hr
    have h := Finset.mem_filter.mp hr
    exact Finset.mem_sdiff.mpr (And.intro
      (mem_fullStep_of_sumPartners_pos S r (hG r h.1).1 (hG r h.1).2 h.2)
      (hFresh r h.1))
  have hSum : Finset.sum G (canonicalSieveWeight S) =
      Finset.sum F (canonicalSieveWeight S) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r hrG hrF
    have hZero : (Finset.sumPartners S (primeTargetSum r)).card = 0 := by
      by_contra hNonzero
      exact hrF (Finset.mem_filter.mpr
        (And.intro hrG (Nat.pos_of_ne_zero hNonzero)))
    simp only [canonicalSieveWeight, hZero, Nat.cast_zero, zero_div]
  rw [hSum]
  change Finset.sum F (canonicalSieveWeight S) <= H * ((fullStep S \ S).card : Real)
  calc
    _ <= Finset.sum F (fun _ => H) := by
      apply Finset.sum_le_sum
      intro r hr
      have h := Finset.mem_filter.mp hr
      have hLift := primeTarget_lift r (hG r h.1).1 (hG r h.1).2
      exact canonicalSieveWeight_upper_sieve M hM S hS r (by omega)
    _ = (F.card : Real) * H := by simp
    _ <= ((fullStep S \ S).card : Real) * H :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hSubset) hH
    _ = _ := mul_comm _ _

private theorem fullOrbit_two_all_prime (j : Nat) :
    forall p, Membership.mem (fullOrbit {2} j) p -> Nat.Prime p := by
  induction j with
  | zero =>
    intro p hp
    have hpTwo : p = 2 := Finset.mem_singleton.mp hp
    simpa only [hpTwo] using Nat.prime_two
  | succ j ih =>
    exact fullStep_preserves_primes (fullOrbit {2} j) ih

/-- A uniform arithmetic collision bound for the actual successive birth layers.
The fresh first moment on the right is not asserted to be positive. -/
theorem fullOrbit_two_fresh_canonical_energy_upper
    (j M : Nat) (hM : 5 ^ 8 <= M) (G : Finset Nat) (beta : Real)
    (hBound : forall p, Membership.mem (fullOrbit {2} (j + 1)) p -> p <= M)
    (hG : forall r, Membership.mem G r -> And (Nat.Prime r) (3 <= r)) :
    let A := fullOrbit {2} j
    let S := fullOrbit {2} (j + 1)
    let F := G \ S
    Finset.sum F (fun r =>
      ((((Finset.sumPartners S (primeTargetSum r)).card : Real) -
        beta * ((Finset.sumPartners A (primeTargetSum r)).card : Real)) /
          singularDivisorProduct (primeTargetSum r)) ^ 2) <=
      (sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2)) *
        Finset.sum F (canonicalSieveWeight S) := by
  apply canonicalSieveWeight_fresh_birth_energy_upper
    M hM (fullOrbit {2} j) (fullOrbit {2} (j + 1))
    (G \ fullOrbit {2} (j + 1)) beta
  next =>
    intro p hp
    exact And.intro (fullOrbit_two_all_prime (j + 1) p hp) (hBound p hp)
  next => exact le_refl _
  next =>
    intro r hr
    exact hG r (Finset.mem_sdiff.mp hr).1
  next =>
    intro r hr
    exact (Finset.mem_sdiff.mp hr).2

/-- The positive-supply requirement is visible as an actual normalized first
moment; no mixing, density, or growth premise is used. -/
theorem fullOrbit_two_fresh_canonical_mass_bound
    (j M : Nat) (hM : 5 ^ 8 <= M) (G : Finset Nat)
    (hBound : forall p, Membership.mem (fullOrbit {2} j) p -> p <= M)
    (hG : forall r, Membership.mem G r -> And (Nat.Prime r) (3 <= r)) :
    Finset.sum (G \ fullOrbit {2} j) (canonicalSieveWeight (fullOrbit {2} j)) <=
      (sieveTwoUpperConstant * ((M : Real) / Real.log (M : Real) ^ 2)) *
        ((fullOrbit {2} (j + 1) \ fullOrbit {2} j).card : Real) := by
  apply canonicalSieveWeight_fresh_mass_bound M hM (fullOrbit {2} j)
    (G \ fullOrbit {2} j)
  next =>
    intro p hp
    exact And.intro (fullOrbit_two_all_prime j p hp) (hBound p hp)
  next =>
    intro r hr
    exact hG r (Finset.mem_sdiff.mp hr).1
  next =>
    intro r hr
    exact (Finset.mem_sdiff.mp hr).2


end PrimeFactorOscillations.LPF
