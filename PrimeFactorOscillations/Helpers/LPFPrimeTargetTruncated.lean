/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPrimeTargetArithmetic

/-!
# Truncated moments of actual LPF prime targets

Both target branches are retained, with the complete summed modulus error.
The finite truncated product is defined even on the diagonal.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem singular_prime_product_dvd_iff (P : Finset Nat) (v : Nat)
    (hP : forall p, Membership.mem P p -> Nat.Prime p) :
    Dvd.dvd (Finset.prod P (fun p => p)) v <->
      forall p, Membership.mem P p -> Dvd.dvd p v := by
  classical
  constructor
  next =>
    intro h p hp
    exact dvd_trans (Finset.dvd_prod_of_mem (fun p : Nat => p) hp) h
  next =>
    revert hP
    induction P using Finset.induction_on with
    | empty => simp
    | @insert p P hp ih =>
      intro hP hd
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
      rw [Finset.prod_insert hp]
      exact hCoprime.mul_dvd_of_dvd_of_dvd
        (hd p (Finset.mem_insert_self p P))
        (ih hRest (fun r hr => hd r (Finset.mem_insert_of_mem hr)))

theorem exists_primeTarget_truncated_branch_bound :
    exists C : Real, And (0 < C)
      (forall (X y m r n q : Nat) (P S : Finset Nat),
        Nat.Prime r -> 3 <= r -> 1 <= q -> Or (n = 1) (n = 3) ->
        (forall p, Membership.mem P p -> And (Nat.Prime p) (And (3 < p) (p < r))) ->
        S <= Nat.largestPrimeFactorRow X y m ->
        (forall s, Membership.mem S s ->
          And (Nat.Prime s) (And (3 <= s) (primeTargetCofactor s = n))) ->
        Finset.sum S (fun s =>
          (Finset.prod (P.filter (fun p => Dvd.dvd p
            ((primeTargetSum r - primeTargetSum s) +
              (primeTargetSum s - primeTargetSum r)))) singularFactor) ^ q) <=
          ((Nat.largestPrimeFactorRow X y m).card : Real) *
            (2 * Real.exp (singularMertensBound + 12) * Real.log ((q : Real) + 2)) ^ q +
          C * (X : Real) ^ (7 / 8 : Real) *
            (1 + Real.log ((Finset.prod P (fun p => p) : Nat) : Real) +
              Real.log ((X : Real) + 2)) ^ 2 * (Finset.prod P singularFactor) ^ q) := by
  classical
  let C : Real := Classical.choose exists_prime_row_singular_packet_bound
  have hC := Classical.choose_spec exists_prime_row_singular_packet_bound
  refine Exists.intro C (And.intro hC.1 ?_)
  intro X y m r n q P S hr hr3 hq hn hP hS hPrimes
  have hResidue : forall A : Finset Nat, A <= P ->
      exists a : Units (ZMod (Finset.prod A (fun p => p))), forall s : Nat,
        Nat.Prime s -> 3 <= s -> primeTargetCofactor s = n ->
        (Dvd.dvd (Finset.prod A (fun p => p))
          ((primeTargetSum r - primeTargetSum s) + (primeTargetSum s - primeTargetSum r)) <->
          (s : ZMod (Finset.prod A (fun p => p))) = (a : ZMod (Finset.prod A (fun p => p)))) := by
    intro A hA
    exact exists_primeTarget_branch_residue r n _ hr hr3 hn
      (primeTarget_modulus_coprime r A hr (fun p hp => hP p (hA hp)))
  let a (A : Finset Nat) : Units (ZMod (Finset.prod A (fun p => p))) :=
    if hA : A <= P then Classical.choose (hResidue A hA) else 1
  have ha : forall A : Finset Nat, A <= P -> forall s : Nat,
      Nat.Prime s -> 3 <= s -> primeTargetCofactor s = n ->
      (Dvd.dvd (Finset.prod A (fun p => p))
        ((primeTargetSum r - primeTargetSum s) + (primeTargetSum s - primeTargetSum r)) <->
        (s : ZMod (Finset.prod A (fun p => p))) = (a A : ZMod (Finset.prod A (fun p => p)))) := by
    intro A hA s hs hs3 hsn
    dsimp [a]
    rw [dite_eq_left hA]
    exact Classical.choose_spec (hResidue A hA) s hs hs3 hsn
  let packet (s : Nat) : Real := Finset.sum P.powerset (fun A =>
    if (s : ZMod (Finset.prod A (fun p => p))) =
        (a A : ZMod (Finset.prod A (fun p => p))) then
      Finset.prod A (fun p => singularFactor p ^ q - 1) else 0)
  have hWeight : forall A : Finset Nat, A <= P ->
      0 <= Finset.prod A (fun p => singularFactor p ^ q - 1) := by
    intro A hA
    apply Finset.prod_nonneg
    intro p hp
    exact singular_moment_weight_nonneg p q (by have h := (hP p (hA hp)).2.1; omega)
  have hExact : forall s, Membership.mem S s ->
      (Finset.prod (P.filter (fun p => Dvd.dvd p
        ((primeTargetSum r - primeTargetSum s) +
          (primeTargetSum s - primeTargetSum r)))) singularFactor) ^ q = packet s := by
    intro s hs
    rw [truncated_singular_moment_expansion]
    apply Finset.sum_congr rfl
    intro A hA
    have hAP := Finset.mem_powerset.mp hA
    have hEquiv := (singular_prime_product_dvd_iff A
      ((primeTargetSum r - primeTargetSum s) + (primeTargetSum s - primeTargetSum r))
      (fun p hp => (hP p (hAP hp)).1)).symm.trans
      (ha A hAP s (hPrimes s hs).1 (hPrimes s hs).2.1 (hPrimes s hs).2.2)
    simp only [hEquiv]
  have hPacketNonneg : forall s : Nat, 0 <= packet s := by
    intro s
    apply Finset.sum_nonneg
    intro A hA
    split_ifs
    next => exact hWeight A (Finset.mem_powerset.mp hA)
    next => exact le_refl 0
  have hCount : Finset.sum S packet <=
      Finset.sum (Nat.largestPrimeFactorRow X y m) packet :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun s _ _ => hPacketNonneg s)
  calc
    _ = Finset.sum S packet := Finset.sum_congr rfl hExact
    _ <= Finset.sum (Nat.largestPrimeFactorRow X y m) packet := hCount
    _ <= _ := hC.2 X y m r P q a hq
      (fun p hp => And.intro (hP p hp).1
        (And.intro (by have h := (hP p hp).2.1; omega) (hP p hp).2.2))

/-- Both cofactor branches, with no assumption on coprimality of input primes. -/
theorem exists_primeTarget_truncated_moment_bound :
    exists C : Real, And (0 < C)
      (forall (X y m r q : Nat) (P S : Finset Nat),
        Nat.Prime r -> 3 <= r -> 1 <= q ->
        (forall p, Membership.mem P p -> And (Nat.Prime p) (And (3 < p) (p < r))) ->
        S <= Nat.largestPrimeFactorRow X y m ->
        (forall s, Membership.mem S s -> And (Nat.Prime s) (3 <= s)) ->
        Finset.sum S (fun s =>
          (Finset.prod (P.filter (fun p => Dvd.dvd p
            ((primeTargetSum r - primeTargetSum s) +
              (primeTargetSum s - primeTargetSum r)))) singularFactor) ^ q) <=
          2 * ((Nat.largestPrimeFactorRow X y m).card : Real) *
            (2 * Real.exp (singularMertensBound + 12) * Real.log ((q : Real) + 2)) ^ q +
          C * (X : Real) ^ (7 / 8 : Real) *
            (1 + Real.log ((Finset.prod P (fun p => p) : Nat) : Real) +
              Real.log ((X : Real) + 2)) ^ 2 * (Finset.prod P singularFactor) ^ q) := by
  classical
  let C : Real := Classical.choose exists_primeTarget_truncated_branch_bound
  have hC := Classical.choose_spec exists_primeTarget_truncated_branch_bound
  refine Exists.intro (2 * C) (And.intro (mul_pos (by norm_num) hC.1) ?_)
  intro X y m r q P S hr hr3 hq hP hS hPrimes
  let F (s : Nat) : Real :=
    (Finset.prod (P.filter (fun p => Dvd.dvd p
      ((primeTargetSum r - primeTargetSum s) +
        (primeTargetSum s - primeTargetSum r)))) singularFactor) ^ q
  have hOne := hC.2 X y m r 1 q P (S.filter (fun s => primeTargetCofactor s = 1))
    hr hr3 hq (Or.inl rfl) hP
    (fun s hs => hS (Finset.mem_filter.mp hs).1)
    (fun s hs => And.intro (hPrimes s (Finset.mem_filter.mp hs).1).1
      (And.intro (hPrimes s (Finset.mem_filter.mp hs).1).2 (Finset.mem_filter.mp hs).2))
  have hThree := hC.2 X y m r 3 q P (S.filter (fun s => primeTargetCofactor s = 3))
    hr hr3 hq (Or.inr rfl) hP
    (fun s hs => hS (Finset.mem_filter.mp hs).1)
    (fun s hs => And.intro (hPrimes s (Finset.mem_filter.mp hs).1).1
      (And.intro (hPrimes s (Finset.mem_filter.mp hs).1).2 (Finset.mem_filter.mp hs).2))
  have hSplit : Finset.sum S F =
      Finset.sum (S.filter (fun s => primeTargetCofactor s = 1)) F +
      Finset.sum (S.filter (fun s => primeTargetCofactor s = 3)) F := by
    rw [Finset.sum_filter, Finset.sum_filter, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hBranch : Or (primeTargetCofactor s = 1) (primeTargetCofactor s = 3) := by
      unfold primeTargetCofactor
      split_ifs <;> simp
    rcases hBranch with h | h <;> simp [F, h]
  change Finset.sum S F <= _
  rw [hSplit]
  have h := _root_.add_le_add hOne hThree
  dsimp [F]
  nlinarith

end PrimeFactorOscillations.LPF
