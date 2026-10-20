/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.ConditionalLocation.EsymmPrefixOrder
import PrimeFactorOscillations.Helpers.PrimeProfileReferenceInvariance

/-!
# Exact finite-prefix coefficient comparisons for bounded prime reindexing

The supported elementary-symmetric ratio decreases under finite nonnegative
additions. The intended prime-set consumer retains the actual mapped prefix
between the canonical cutoffs N-H and N+H. Every denominator hypothesis is
explicit; no estimate of a signed Nicolas oscillation is assumed here.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Multiset

/-- Finite nonnegative additions retain support and lower the complete adjacent coefficient ratio. -/
theorem esymm_ratio_add_le_rat (s t : Multiset Rat)
    (hs : forall a, Membership.mem s a -> 0 <= a)
    (ht : forall a, Membership.mem t a -> 0 <= a)
    (r : Nat) (hr : 1 <= r) (hden : 0 < s.esymm r) :
    0 < (s + t).esymm r /\
      (s + t).esymm (r - 1) / (s + t).esymm r <=
        s.esymm (r - 1) / s.esymm r := by
  revert ht
  induction t using Multiset.induction_on with
  | empty =>
      intro _
      simpa only [add_zero] using And.intro hden (le_refl (s.esymm (r - 1) / s.esymm r))
  | @cons a t ih =>
      intro ht
      have ha : 0 <= a := ht a (by simp)
      have htn : forall b, Membership.mem t b -> 0 <= b :=
        fun b hb => ht b (by simp [hb])
      have hbase := ih htn
      have hwhole : forall b, Membership.mem (s + t) b -> 0 <= b := by
        intro b hb
        cases Multiset.mem_add.mp hb with
        | inl hb => exact hs b hb
        | inr hb => exact htn b hb
      have hratio := esymm_ratio_cons_le_rat (s + t) hwhole a ha r hr hbase.1
      have hnew : 0 < (s + cons a t).esymm r := by
        rw [Multiset.add_cons]
        cases r with
        | zero => omega
        | succ j =>
            rw [esymm_cons_succ_rat]
            exact add_pos_of_pos_of_nonneg hbase.1
              (mul_nonneg ha (esymm_nonneg_rat (s + t) hwhole j))
      refine And.intro hnew ?_
      simpa only [Multiset.add_cons] using hratio.trans hbase.2

end Multiset

namespace Finset

/-- Inclusion of nonnegative rational-weighted finite sets lowers every supported ratio. -/
theorem esymm_ratio_le_of_subset_rat {I : Type*} (s t : Finset I) (w : I -> Rat)
    (hw : forall i, 0 <= w i)
    (hsub : forall i, Membership.mem s i -> Membership.mem t i)
    (r : Nat) (hr : 1 <= r) (hden : 0 < (s.val.map w).esymm r) :
    0 < (t.val.map w).esymm r /\
      (t.val.map w).esymm (r - 1) / (t.val.map w).esymm r <=
        (s.val.map w).esymm (r - 1) / (s.val.map w).esymm r := by
  classical
  have hval : s.val <= t.val := by
    apply Finset.val_le_iff.mpr
    intro i hi
    exact hsub i hi
  have hex := exists_add_of_le hval
  let u := Classical.choose hex
  have hu : t.val = s.val + u := Classical.choose_spec hex
  have hweights (m : Multiset I) : forall a, Membership.mem (m.map w) a -> 0 <= a := by
    intro a ha
    have hm := Multiset.mem_map.mp ha
    let i := Classical.choose hm
    have hi := Classical.choose_spec hm
    rw [<- hi.2]
    exact hw i
  rw [hu, Multiset.map_add]
  exact Multiset.esymm_ratio_add_le_rat (s.val.map w) (u.map w)
    (hweights s.val) (hweights u) r hr hden

end Finset

namespace PrimeFactorOscillations

/-- The actual local-odds law of any prime permutation with a fixed natural displacement radius. -/
def boundedPrimePermutationLaw (sigma : Equiv.Perm Nat.Primes) (H : Nat)
    (hdispl : forall p : Nat.Primes,
      abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (H : Real)) :
    QuadraticPrimeLaw :=
  boundedPrimeReindexingLaw (fun p => (sigma p : Nat)) (fun p => (sigma p).property)
    (H : Real) (by positivity) hdispl

/-- The image of the actual inclusive prime-coordinate prefix, without repeated coordinates. -/
def permutedPrimePrefix (sigma : Equiv.Perm Nat.Primes) (N : Nat) : Finset Nat.Primes :=
  (primeProfilePrefixSet N).map sigma.toEmbedding

/-- Every bounded prime permutation retains both canonical finite-set cutoff inclusions. -/
theorem permutedPrimePrefix_inclusions (sigma : Equiv.Perm Nat.Primes) (H N : Nat)
    (hHN : H <= N)
    (hdispl : forall p : Nat.Primes,
      abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (H : Real)) :
    (forall q : Nat.Primes, Membership.mem (primeProfilePrefixSet (N - H)) q ->
      Membership.mem (permutedPrimePrefix sigma N) q) /\
    (forall q : Nat.Primes, Membership.mem (permutedPrimePrefix sigma N) q ->
      Membership.mem (primeProfilePrefixSet (N + H)) q) := by
  constructor
  . intro q hq
    let p := sigma.symm q
    have hsig : sigma p = q := sigma.apply_symm_apply q
    have hd := hdispl p
    rw [hsig] at hd
    have hpq : (p : Nat) <= (q : Nat) + H := by
      have hr : ((p : Nat) : Real) <= ((q : Nat) : Real) + (H : Real) := by
        linarith only [(abs_le.mp hd).1]
      exact_mod_cast hr
    have hqN : (q : Nat) <= N - H := (mem_primeProfilePrefixSet q (N - H)).mp hq
    have hpN : (p : Nat) <= N := by omega
    apply Finset.mem_map.mpr
    exact Exists.intro p (And.intro ((mem_primeProfilePrefixSet p N).mpr hpN) hsig)
  . intro q hq
    have hex := Finset.mem_map.mp hq
    let p := Classical.choose hex
    have hp := Classical.choose_spec hex
    have hsig : sigma p = q := hp.2
    have hpN : (p : Nat) <= N := (mem_primeProfilePrefixSet p N).mp hp.1
    have hpq : (sigma p : Nat) <= (p : Nat) + H := by
      have hr : ((sigma p : Nat) : Real) <= ((p : Nat) : Real) + (H : Real) := by
        linarith only [(abs_le.mp (hdispl p)).2]
      exact_mod_cast hr
    apply (mem_primeProfilePrefixSet q (N + H)).mpr
    rw [<- hsig]
    exact hpq.trans (Nat.add_le_add_right hpN H)

/-- The actual family coefficient is exactly the canonical odds coefficient on the mapped prime set. -/
theorem boundedPrimePermutationLaw_prefixEsymm_eq
    (sigma : Equiv.Perm Nat.Primes) (H : Nat)
    (hdispl : forall p : Nat.Primes,
      abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (H : Real))
    (N r : Nat) :
    (boundedPrimePermutationLaw sigma H hdispl).prefixEsymm N r =
      ((permutedPrimePrefix sigma N).val.map
        (fun p : Nat.Primes => primeProfileWeight (p : Nat))).esymm r := by
  change ((primeProfilePrefixSet N).val.map
      (fun p : Nat.Primes => primeProfileWeight (sigma p : Nat))).esymm r =
    (((primeProfilePrefixSet N).val.map sigma.toEmbedding).map
      (fun p : Nat.Primes => primeProfileWeight (p : Nat))).esymm r
  rw [Multiset.map_map]
  rfl

/-- Exact rational canonical odds at a prime-labelled coordinate. -/
def primeOddsRat (p : Nat.Primes) : Rat := 1 / (((p : Nat) - 1 : Nat) : Rat)

/-- The canonical real symmetric coefficient on an arbitrary finite prime set. -/
def primeSetEsymm (s : Finset Nat.Primes) (r : Nat) : Real :=
  (s.val.map (fun p : Nat.Primes => primeProfileWeight (p : Nat))).esymm r

/-- The complete supported ratio of two adjacent coefficients on a finite prime set. -/
def primeSetDensityRatio (s : Finset Nat.Primes) (r : Nat) : Real :=
  primeSetEsymm s (r - 1) / primeSetEsymm s r

/-- The rational-to-real coefficient transfer is exact in every degree. -/
theorem primeSetEsymm_eq_rat_cast (s : Finset Nat.Primes) (r : Nat) :
    primeSetEsymm s r = (((s.val.map primeOddsRat).esymm r : Rat) : Real) := by
  have hcast (p : Nat.Primes) : primeProfileWeight (p : Nat) = (primeOddsRat p : Real) := by
    norm_num [primeProfileWeight, primeOddsRat]
  have hmap : s.val.map (fun p : Nat.Primes => primeProfileWeight (p : Nat)) =
      (s.val.map primeOddsRat).map (Rat.castHom Real) := by
    rw [Multiset.map_map]
    apply congrArg (fun f : Nat.Primes -> Real => s.val.map f)
    funext p
    exact hcast p
  unfold primeSetEsymm
  rw [hmap]
  exact (RingHom.map_multiset_esymm (Rat.castHom Real) (s.val.map primeOddsRat) r).symm

/-- Finite prime-set inclusion lowers the actual real ratio on its positive-denominator domain. -/
theorem primeSetDensityRatio_mono_subset (s t : Finset Nat.Primes)
    (hsub : forall p, Membership.mem s p -> Membership.mem t p)
    (r : Nat) (hr : 1 <= r) (hden : 0 < primeSetEsymm s r) :
    0 < primeSetEsymm t r /\ primeSetDensityRatio t r <= primeSetDensityRatio s r := by
  have hdenRat : 0 < (s.val.map primeOddsRat).esymm r := by
    have hreal : (0 : Real) < (((s.val.map primeOddsRat).esymm r : Rat) : Real) := by
      rw [<- primeSetEsymm_eq_rat_cast s r]
      exact hden
    exact_mod_cast hreal
  have h := Finset.esymm_ratio_le_of_subset_rat s t primeOddsRat
    (fun p => by unfold primeOddsRat; positivity) hsub r hr hdenRat
  constructor
  . rw [primeSetEsymm_eq_rat_cast t r]
    exact_mod_cast h.1
  . unfold primeSetDensityRatio
    rw [primeSetEsymm_eq_rat_cast t (r - 1), primeSetEsymm_eq_rat_cast t r,
      primeSetEsymm_eq_rat_cast s (r - 1), primeSetEsymm_eq_rat_cast s r]
    exact_mod_cast h.2

/-- All bounded prime permutations have a complete canonical ratio sandwich with retained support. -/
theorem bounded_prime_permutation_ratio_sandwich
    (sigma : Equiv.Perm Nat.Primes) (H N : Nat) (hHN : H <= N)
    (hdispl : forall p : Nat.Primes,
      abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (H : Real))
    (r : Nat) (hr : 1 <= r)
    (hden : 0 < canonicalPrimeOddsLaw.prefixEsymm (N - H) r) :
    0 < (boundedPrimePermutationLaw sigma H hdispl).prefixEsymm N r /\
    0 < canonicalPrimeOddsLaw.prefixEsymm (N + H) r /\
      (canonicalPrimeOddsLaw.densityRatio (N + H) r <=
        (boundedPrimePermutationLaw sigma H hdispl).densityRatio N r /\
      (boundedPrimePermutationLaw sigma H hdispl).densityRatio N r <=
        canonicalPrimeOddsLaw.densityRatio (N - H) r) := by
  have hinc := permutedPrimePrefix_inclusions sigma H N hHN hdispl
  have hlo := primeSetDensityRatio_mono_subset (primeProfilePrefixSet (N - H))
    (permutedPrimePrefix sigma N) hinc.1 r hr hden
  have hhi := primeSetDensityRatio_mono_subset (permutedPrimePrefix sigma N)
    (primeProfilePrefixSet (N + H)) hinc.2 r hr hlo.1
  have hratio : (boundedPrimePermutationLaw sigma H hdispl).densityRatio N r =
      primeSetDensityRatio (permutedPrimePrefix sigma N) r := by
    unfold QuadraticPrimeLaw.densityRatio primeSetDensityRatio primeSetEsymm
    rw [boundedPrimePermutationLaw_prefixEsymm_eq sigma H hdispl N (r - 1),
      boundedPrimePermutationLaw_prefixEsymm_eq sigma H hdispl N r]
  have hcanon (M : Nat) : canonicalPrimeOddsLaw.densityRatio M r =
      primeSetDensityRatio (primeProfilePrefixSet M) r := by rfl
  constructor
  . rw [boundedPrimePermutationLaw_prefixEsymm_eq sigma H hdispl N r]
    exact hlo.1
  . refine And.intro hhi.1 ?_
    rw [hratio, hcanon (N + H), hcanon (N - H)]
    exact And.intro hhi.2 hlo.2

end PrimeFactorOscillations
