/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFJointTransfer
import PrimeFactorOscillations.Helpers.LPFPrimeTargetMoment

/-!
# Exact arithmetic connecting the prime-row packet to its Euler bound

Distinct prime factors retain the exact totient denominator. The principal
sum is converted without dropping weights or adding an analytic assumption.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

private theorem totient_prime_product (P : Finset Nat)
    (hP : forall p, Membership.mem P p -> Nat.Prime p) :
    (Finset.prod P (fun p => p)).totient = Finset.prod P (fun p => p - 1) := by
  classical
  revert hP
  induction P using Finset.induction_on with
  | empty => intro hP; norm_num
  | @insert p P hp ih =>
    intro hP
    have hPrime := hP p (Finset.mem_insert_self p P)
    have hRest : forall r, Membership.mem P r -> Nat.Prime r := by
      intro r hr
      exact hP r (Finset.mem_insert_of_mem hr)
    have hCoprime : Nat.Coprime p (Finset.prod P (fun r => r)) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro r hr
      apply (Nat.coprime_primes hPrime (hRest r hr)).mpr
      intro heq
      subst r
      exact hp hr
    have hPhi : p.totient = p - 1 :=
      (Nat.totient_eq_iff_prime (by have h := hPrime.two_le; omega)).mpr hPrime
    rw [Finset.prod_insert hp, Finset.prod_insert hp,
      Nat.totient_mul hCoprime, hPhi, ih hRest]

theorem singular_moment_principal_sum_eq (P : Finset Nat) (q : Nat)
    (hP : forall p, Membership.mem P p -> Nat.Prime p) :
    Finset.sum P.powerset (fun A =>
      Finset.prod A (fun p => singularFactor p ^ q - 1) /
        ((Finset.prod A (fun p => p)).totient : Real)) =
      Finset.prod P (fun p => 1 + (singularFactor p ^ q - 1) / ((p : Real) - 1)) := by
  classical
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro A hA
  have hPrimes : forall p, Membership.mem A p -> Nat.Prime p := by
    intro p hp
    exact hP p (Finset.mem_powerset.mp hA hp)
  have hPhi : ((Finset.prod A (fun p => p)).totient : Real) =
      Finset.prod A (fun p => (p : Real) - 1) := by
    rw [totient_prime_product A hPrimes, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    simp only [Nat.cast_sub (hPrimes p hp).one_lt.le, Nat.cast_one]
  rw [hPhi]
  exact (Finset.prod_div_distrib (fun p => singularFactor p ^ q - 1)
    (fun (p : Nat) => (p : Real) - 1)).symm

theorem singular_moment_principal_sum_le (P : Finset Nat) (N q : Nat) (hq : 1 <= q)
    (hP : forall p, Membership.mem P p -> And (Nat.Prime p) (And (3 <= p) (p < N))) :
    Finset.sum P.powerset (fun A =>
      Finset.prod A (fun p => singularFactor p ^ q - 1) /
        ((Finset.prod A (fun p => p)).totient : Real)) <=
      (2 * Real.exp (singularMertensBound + 12) * Real.log ((q : Real) + 2)) ^ q := by
  rw [singular_moment_principal_sum_eq P q (fun p hp => (hP p hp).1)]
  exact singular_euler_moment_le P N q hq hP

/-- The prime-row estimate now consumes the proved uniform principal bound. -/
theorem exists_prime_row_singular_packet_bound :
    exists C : Real, And (0 < C)
      (forall (X y m N : Nat) (P : Finset Nat) (q : Nat)
        (a : (A : Finset Nat) -> Units (ZMod (Finset.prod A (fun p => p)))),
        1 <= q ->
        (forall p, Membership.mem P p -> And (Nat.Prime p) (And (3 <= p) (p < N))) ->
        Finset.sum (Nat.largestPrimeFactorRow X y m) (fun (r : Nat) =>
          Finset.sum P.powerset (fun A =>
            if (r : ZMod (Finset.prod A (fun p => p))) =
                (a A : ZMod (Finset.prod A (fun p => p))) then
              Finset.prod A (fun p => singularFactor p ^ q - 1) else 0)) <=
        ((Nat.largestPrimeFactorRow X y m).card : Real) *
          (2 * Real.exp (singularMertensBound + 12) * Real.log ((q : Real) + 2)) ^ q +
        C * (X : Real) ^ (7 / 8 : Real) *
          (1 + Real.log ((Finset.prod P (fun p => p) : Nat) : Real) +
            Real.log ((X : Real) + 2)) ^ 2 * (Finset.prod P singularFactor) ^ q) := by
  classical
  let C : Real := Classical.choose exists_squarefree_prime_row_moment_bound
  have hC := Classical.choose_spec exists_squarefree_prime_row_moment_bound
  refine Exists.intro C (And.intro hC.1 ?_)
  intro X y m N P q a hq hP
  have hPacket := hC.2 X y m P q a (fun p hp => (hP p hp).2.1)
  have hMain := singular_moment_principal_sum_le P N q hq hP
  have hScaled := mul_le_mul_of_nonneg_left hMain
    (Nat.cast_nonneg (Nat.largestPrimeFactorRow X y m).card)
  exact hPacket.trans (_root_.add_le_add hScaled (le_refl _))

private theorem dvd_nat_distance_iff_cast_eq (d a b : Nat) :
    Dvd.dvd d ((a - b) + (b - a)) <-> (a : ZMod d) = (b : ZMod d) := by
  rcases le_total a b with hab | hba
  next =>
    rw [Nat.sub_eq_zero_of_le hab, Nat.zero_add,
      <- CharP.cast_eq_zero_iff (ZMod d) d (b - a), Nat.cast_sub hab, sub_eq_zero]
    exact eq_comm
  next =>
    rw [Nat.sub_eq_zero_of_le hba, Nat.add_zero,
      <- CharP.cast_eq_zero_iff (ZMod d) d (a - b), Nat.cast_sub hba, sub_eq_zero]

/-- Both cofactor branches give reduced residues, including composite moduli. -/
theorem exists_primeTarget_branch_residue (r n d : Nat)
    (hr : Nat.Prime r) (hr3 : 3 <= r) (hn : Or (n = 1) (n = 3))
    (hd : Nat.Coprime (6 * r) d) :
    exists a : Units (ZMod d), forall s : Nat,
      Nat.Prime s -> 3 <= s -> primeTargetCofactor s = n ->
      (Dvd.dvd d ((primeTargetSum r - primeTargetSum s) +
        (primeTargetSum s - primeTargetSum r)) <-> (s : ZMod d) = (a : ZMod d)) := by
  have hTwo : Nat.Coprime 2 d := hd.of_dvd_left (by
    refine Exists.intro (3 * r) ?_; ring)
  have hN : Nat.Coprime n d := hd.of_dvd_left (by
    rcases hn with hn | hn
    next => subst n; exact one_dvd _
    next => subst n; refine Exists.intro (2 * r) ?_; ring)
  have hR : Nat.Coprime (primeTargetCofactor r * r) d := hd.of_dvd_left (by
    unfold primeTargetCofactor
    split_ifs
    next => refine Exists.intro 2 ?_; ring
    next => refine Exists.intro 6 ?_; ring)
  let un : Units (ZMod d) := ZMod.unitOfCoprime n hN
  let ur : Units (ZMod d) := ZMod.unitOfCoprime (primeTargetCofactor r * r) hR
  let a : Units (ZMod d) := un ^ (-1 : Int) * ur
  have hna : (n : ZMod d) * (a : ZMod d) =
      ((primeTargetCofactor r * r : Nat) : ZMod d) := by
    rw [<- ZMod.coe_unitOfCoprime n hN]
    change ((un * (un ^ (-1 : Int) * ur) : Units (ZMod d)) : ZMod d) = _
    simp only [zpow_neg_one, mul_inv_cancel_left]
    exact ZMod.coe_unitOfCoprime _ _
  have hTwoUnit : IsUnit (2 : ZMod d) := by
    simpa only [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] using
      (ZMod.unitOfCoprime 2 hTwo).isUnit
  have hNUnit : IsUnit (n : ZMod d) := by
    simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime n hN).isUnit
  refine Exists.intro a ?_
  intro s hs hs3 hBranch
  rw [dvd_nat_distance_iff_cast_eq]
  have hLiftR : (2 : ZMod d) * (primeTargetSum r : ZMod d) =
      ((primeTargetCofactor r * r : Nat) : ZMod d) + 1 := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      congrArg (fun k : Nat => (k : ZMod d)) (primeTarget_lift r hr hr3)
  have hLiftS : (2 : ZMod d) * (primeTargetSum s : ZMod d) =
      (n : ZMod d) * (s : ZMod d) + 1 := by
    have h := primeTarget_lift s hs hs3
    rw [hBranch] at h
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      congrArg (fun k : Nat => (k : ZMod d)) h
  constructor
  next =>
    intro h
    have hMul := congrArg (fun z : ZMod d => 2 * z) h
    rw [hLiftR, hLiftS] at hMul
    have hEqual := add_right_cancel hMul
    exact (hNUnit.mul_left_cancel (hna.trans hEqual)).symm
  next =>
    intro h
    apply hTwoUnit.mul_left_cancel
    rw [hLiftR, hLiftS, h, hna]

/-- Every subset modulus in the moment expansion meets the branch conditions. -/
theorem primeTarget_modulus_coprime (r : Nat) (P : Finset Nat) (hr : Nat.Prime r)
    (hP : forall p, Membership.mem P p -> And (Nat.Prime p) (And (3 < p) (p < r))) :
    Nat.Coprime (6 * r) (Finset.prod P (fun p => p)) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  have h := hP p hp
  have hTwo : Nat.Coprime 2 p :=
    (Nat.coprime_primes (by decide : Nat.Prime 2) h.1).mpr (by omega)
  have hThree : Nat.Coprime 3 p :=
    (Nat.coprime_primes (by decide : Nat.Prime 3) h.1).mpr (by omega)
  have hR : Nat.Coprime r p := (Nat.coprime_primes hr h.1).mpr (by omega)
  have hSix : Nat.Coprime 6 p := by convert hTwo.mul_left hThree using 1
  exact hSix.mul_left hR

end PrimeFactorOscillations.LPF
