/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFSieveEuler

/-!
# Upper sieve bounds for actual prime representations

The small forms are counted explicitly, at most z per injective form.
The input diagonal is allowed; distinctness concerns only the two target sums.
-/

namespace PrimeFactorOscillations.LPF

private theorem small_form_card_le (X : Finset Nat) (f : Nat -> Nat) (z : Nat)
    (hPrime : forall k, Membership.mem X k -> Nat.Prime (f k))
    (hInj : Set.InjOn f (X : Set Nat)) :
    (X.filter (fun k => f k <= z)).card <= z := by
  classical
  have hMaps : Set.MapsTo f ((X.filter (fun k => f k <= z)) : Set Nat)
      ((Finset.Icc 1 z) : Set Nat) := by
    intro k hk
    have hs := Finset.mem_filter.mp hk
    exact Finset.mem_Icc.mpr (And.intro (le_of_lt (hPrime k hs.1).one_lt) hs.2)
  have hInjSmall : Set.InjOn f ((X.filter (fun k => f k <= z)) : Set Nat) := by
    intro k hk l hl he
    exact hInj (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hl).1 he
  have h := Finset.card_le_card_of_injOn f hMaps hInjSmall
  simpa [Nat.card_Icc] using h

private theorem prime_sub_input_le (t k : Nat) (h : Nat.Prime (t - k)) : k <= t := by
  have h2 := h.two_le
  omega

private theorem reflected_injective (X : Finset Nat) (t : Nat)
    (hPrime : forall k, Membership.mem X k -> Nat.Prime (t - k)) :
    Set.InjOn (fun k => t - k) (X : Set Nat) := by
  intro k hk l hl he
  have hkT := prime_sub_input_le t k (hPrime k hk)
  have hlT := prime_sub_input_le t l (hPrime l hl)
  change t - k = t - l at he
  omega

private theorem prime_above_not_dvd (p k z : Nat)
    (hp : Nat.Prime p) (hpz : p <= z) (hk : Nat.Prime k) (hzk : z < k) :
    Not (Dvd.dvd p k) := by
  intro h
  rcases (Nat.dvd_prime hk).mp h with h1 | he
  next => have h2 := hp.two_le; omega
  next => omega

private theorem prime_inputs_avoid_two (t z k p : Nat)
    (hk : Nat.Prime k) (ht : Nat.Prime (t - k))
    (hzk : z < k) (hzt : z < t - k)
    (hp : Nat.Prime p) (hpz : p <= z) :
    Not (Membership.mem ({0, (t : ZMod p)} : Finset (ZMod p)) (k : ZMod p)) := by
  classical
  intro h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h0 | he
  next =>
    exact prime_above_not_dvd p k z hp hpz hk hzk ((ZMod.natCast_eq_zero_iff k p).mp h0)
  next =>
    have hMod := (ZMod.natCast_eq_natCast_iff k t p).mp he
    have hDiv := (Nat.modEq_iff_dvd' (prime_sub_input_le t k ht)).mp hMod
    exact prime_above_not_dvd p (t - k) z hp hpz ht hzt hDiv

private theorem prime_inputs_avoid_three (t s z k p : Nat)
    (hk : Nat.Prime k) (ht : Nat.Prime (t - k)) (hs : Nat.Prime (s - k))
    (hzk : z < k) (hzt : z < t - k) (hzs : z < s - k)
    (hp : Nat.Prime p) (hpz : p <= z) :
    Not (Membership.mem ({0, (t : ZMod p), (s : ZMod p)} : Finset (ZMod p)) (k : ZMod p)) := by
  classical
  intro h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h0 | htEq | hsEq
  next =>
    exact prime_above_not_dvd p k z hp hpz hk hzk ((ZMod.natCast_eq_zero_iff k p).mp h0)
  next =>
    have hMod := (ZMod.natCast_eq_natCast_iff k t p).mp htEq
    have hDiv := (Nat.modEq_iff_dvd' (prime_sub_input_le t k ht)).mp hMod
    exact prime_above_not_dvd p (t - k) z hp hpz ht hzt hDiv
  next =>
    have hMod := (ZMod.natCast_eq_natCast_iff k s p).mp hsEq
    have hDiv := (Nat.modEq_iff_dvd' (prime_sub_input_le s k hs)).mp hMod
    exact prime_above_not_dvd p (s - k) z hp hpz hs hzs hDiv

private theorem two_small_exceptions (X : Finset Nat) (t z : Nat)
    (hPrime : forall k, Membership.mem X k -> And (Nat.Prime k) (Nat.Prime (t - k))) :
    X.card <= (X.filter (fun k => And (z < k) (z < t - k))).card + 2 * z := by
  classical
  let G := X.filter (fun k => And (z < k) (z < t - k))
  let B := X.filter (fun k => Not (And (z < k) (z < t - k)))
  let B0 := X.filter (fun k => k <= z)
  let Bt := X.filter (fun k => t - k <= z)
  have hCover : B <= Union.union B0 Bt := by
    intro k hk
    have h := Finset.mem_filter.mp hk
    by_cases h0 : k <= z
    next => exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr (And.intro h.1 h0)))
    next =>
      have h1 : t - k <= z := by
        by_contra hNot
        exact h.2 (And.intro (by omega) (by omega))
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr (And.intro h.1 h1)))
  have h0 := small_form_card_le X (fun k => k) z
    (fun k hk => (hPrime k hk).1) (fun _ _ _ _ h => h)
  have ht := small_form_card_le X (fun k => t - k) z
    (fun k hk => (hPrime k hk).2)
    (reflected_injective X t (fun k hk => (hPrime k hk).2))
  have hCard := Finset.card_le_card hCover
  have hUnion := Finset.card_union_le B0 Bt
  have hPartition := Finset.card_filter_add_card_filter_not (s := X)
    (fun k => And (z < k) (z < t - k))
  change G.card + B.card = X.card at hPartition
  change B0.card <= z at h0
  change Bt.card <= z at ht
  change X.card <= G.card + 2 * z
  omega

private theorem three_small_exceptions (X : Finset Nat) (t s z : Nat)
    (hPrime : forall k, Membership.mem X k ->
      And (Nat.Prime k) (And (Nat.Prime (t - k)) (Nat.Prime (s - k)))) :
    X.card <= (X.filter (fun k => And (z < k) (And (z < t - k) (z < s - k)))).card +
      3 * z := by
  classical
  let G := X.filter (fun k => And (z < k) (And (z < t - k) (z < s - k)))
  let B := X.filter (fun k => Not (And (z < k) (And (z < t - k) (z < s - k))))
  let B0 := X.filter (fun k => k <= z)
  let Bt := X.filter (fun k => t - k <= z)
  let Bs := X.filter (fun k => s - k <= z)
  have hCover : B <= Union.union B0 (Union.union Bt Bs) := by
    intro k hk
    have h := Finset.mem_filter.mp hk
    by_cases h0 : k <= z
    next => exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr (And.intro h.1 h0)))
    next =>
      by_cases h1 : t - k <= z
      next =>
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
          (Or.inl (Finset.mem_filter.mpr (And.intro h.1 h1)))))
      next =>
        have h2 : s - k <= z := by
          by_contra hNot
          exact h.2 (And.intro (by omega) (And.intro (by omega) (by omega)))
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr (And.intro h.1 h2)))))
  have h0 := small_form_card_le X (fun k => k) z
    (fun k hk => (hPrime k hk).1) (fun _ _ _ _ h => h)
  have ht := small_form_card_le X (fun k => t - k) z
    (fun k hk => (hPrime k hk).2.1)
    (reflected_injective X t (fun k hk => (hPrime k hk).2.1))
  have hs := small_form_card_le X (fun k => s - k) z
    (fun k hk => (hPrime k hk).2.2)
    (reflected_injective X s (fun k hk => (hPrime k hk).2.2))
  have hCard := Finset.card_le_card hCover
  have hUnion := Finset.card_union_le B0 (Union.union Bt Bs)
  have hUnion2 := Finset.card_union_le Bt Bs
  have hPartition := Finset.card_filter_add_card_filter_not (s := X)
    (fun k => And (z < k) (And (z < t - k) (z < s - k)))
  change G.card + B.card = X.card at hPartition
  change B0.card <= z at h0
  change Bt.card <= z at ht
  change Bs.card <= z at hs
  change X.card <= G.card + 3 * z
  omega

/-- Actual two-prime representations, with the exact finite small-form allowance. -/
theorem prime_twoForm_card_le (z t : Nat) (hz : 5 <= z) (ht : 0 < t)
    (X : Finset Nat) {N Q : Nat} (hN : 0 < N) (hQ : 1 < Q)
    (hX : X <= Finset.range N)
    (hPrime : forall k, Membership.mem X k -> And (Nat.Prime k) (Nat.Prime (t - k)))
    (hPower : z ^ 4 <= Q) :
    (X.card : Real) <=
      72 * ((N : Real) + (Q : Real) ^ 2) * singularDivisorProduct t /
        (sieveMertensConstant ^ 2 * Real.log (z : Real) ^ 2) + 2 * (z : Real) := by
  classical
  let G := X.filter (fun k => And (z < k) (z < t - k))
  have hGX : G <= Finset.range N := (Finset.filter_subset _ _).trans hX
  have hAvoid : forall k, Membership.mem G k -> forall p,
      Membership.mem (sievePrimeCutoff z) p ->
      Not (Membership.mem ({0, (t : ZMod p)} : Finset (ZMod p)) (k : ZMod p)) := by
    intro k hk p hp
    have hg := Finset.mem_filter.mp hk
    have hpr := hPrime k hg.1
    have hpp := mem_sievePrimeCutoff.mp hp
    exact prime_inputs_avoid_two t z k p hpr.1 hpr.2 hg.2.1 hg.2.2 hpp.1 hpp.2.2
  have hSieve := sifted_twoResidue_card_le z t hz ht G hN hQ hGX hAvoid hPower
  have hSmall : (X.card : Real) <= (G.card : Real) + 2 * (z : Real) := by
    exact_mod_cast two_small_exceptions X t z hPrime
  linarith

/-- Actual three-prime forms, uniformly in both distinct target sums. -/
theorem prime_threeForm_card_le (z t s : Nat) (hz : 5 <= z)
    (ht : 0 < t) (hs : 0 < s) (hne : Not (t = s))
    (X : Finset Nat) {N Q : Nat} (hN : 0 < N) (hQ : 1 < Q)
    (hX : X <= Finset.range N)
    (hPrime : forall k, Membership.mem X k ->
      And (Nat.Prime k) (And (Nat.Prime (t - k)) (Nat.Prime (s - k))))
    (hPower : z ^ 4 <= Q) :
    (X.card : Real) <=
      144 * ((N : Real) + (Q : Real) ^ 2) *
        (singularDivisorProduct t * singularDivisorProduct s *
          singularDivisorProduct ((t - s) + (s - t))) /
        (sieveMertensConstant ^ 3 * Real.log (z : Real) ^ 3) + 3 * (z : Real) := by
  classical
  let G := X.filter (fun k => And (z < k) (And (z < t - k) (z < s - k)))
  have hGX : G <= Finset.range N := (Finset.filter_subset _ _).trans hX
  have hAvoid : forall k, Membership.mem G k -> forall p,
      Membership.mem (sievePrimeCutoff z) p ->
      Not (Membership.mem ({0, (t : ZMod p), (s : ZMod p)} : Finset (ZMod p)) (k : ZMod p)) := by
    intro k hk p hp
    have hg := Finset.mem_filter.mp hk
    have hpr := hPrime k hg.1
    have hpp := mem_sievePrimeCutoff.mp hp
    exact prime_inputs_avoid_three t s z k p hpr.1 hpr.2.1 hpr.2.2
      hg.2.1 hg.2.2.1 hg.2.2.2 hpp.1 hpp.2.2
  have hSieve := sifted_threeResidue_card_le z t s hz ht hs hne G
    hN hQ hGX hAvoid hPower
  have hSmall : (X.card : Real) <= (G.card : Real) + 3 * (z : Real) := by
    exact_mod_cast three_small_exceptions X t s z hPrime
  linarith

end PrimeFactorOscillations.LPF
