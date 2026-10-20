/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileTransportParity

/-!
# Pairwise rigidity and separation of prime-profile rearrangements

The full signed transport lies on an even lattice. Comparing two probe
observations with their exact transports preserves a separation of two
up to the explicit sum of their transport errors.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

theorem prime_prefix_transport_eq_of_probes_close
    (e f : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hbudget : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hsmall : 2 < (PrimeFactorUnimodality.primeAt n : Real) - C)
    (hecost : normalizedPrimePrefixDefect e t n <= C)
    (hfcost : normalizedPrimePrefixDefect f t n <= C)
    (v w : Nat -> Real) (hv : 0 < v n) (hw : 0 < w n)
    (hclose : abs (normalizedPrimePrefixDefect e v n - normalizedPrimePrefixDefect f w n) +
      64 * C ^ 2 / (PrimeFactorUnimodality.primeAt n : Real) < 2) :
    Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1) =
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real)) f (n + 1) := by
  have heven := prime_prefix_transport_even_of_cost_le e t n C ht hC0 hbudget hecost hsmall
  have hfven := prime_prefix_transport_even_of_cost_le f t n C ht hC0 hbudget hfcost hsmall
  let K := Classical.choose heven
  let L := Classical.choose hfven
  have hK := Classical.choose_spec heven
  have hL := Classical.choose_spec hfven
  have he := prime_prefix_transport_uniform_error e t n C ht hC0 hbudget hecost v hv
  have hf := prime_prefix_transport_uniform_error f t n C ht hC0 hbudget hfcost w hw
  rw [hK] at he
  rw [hL] at hf
  have hepair := abs_le.mp he
  have hfpair := abs_le.mp hf
  have hobs := abs_le.mp
    (le_refl (abs (normalizedPrimePrefixDefect e v n - normalizedPrimePrefixDefect f w n)))
  have hsplit : 64 * C ^ 2 / (PrimeFactorUnimodality.primeAt n : Real) =
      2 * (32 * C ^ 2 / (PrimeFactorUnimodality.primeAt n : Real)) := by ring
  rw [hsplit] at hclose
  have hKL : (K : Real) < (L : Real) + 1 := by
    linarith only [hepair.1, hfpair.2, hobs.2, hclose]
  have hLK : (L : Real) < (K : Real) + 1 := by
    linarith only [hfpair.1, hepair.2, hobs.1, hclose]
  have hKLn : K < L + 1 := by exact_mod_cast hKL
  have hLKn : L < K + 1 := by exact_mod_cast hLK
  have hEq : K = L := by omega
  rw [hK, hL]
  change 2 * (K : Real) = 2 * (L : Real)
  rw [hEq]

/-- Rearrangements with bounded distortion that differ infinitely often have
arbitrarily late separation almost two, shared by every pair of positive probes. -/
theorem bounded_profiles_uniformly_separated_of_not_eventually_eq
    (e f : Equiv.Perm Nat) (t : Nat -> Real) (ht : forall n, 0 < t n)
    (C : Real) (hC0 : 0 <= C)
    (hcost : exists M : Nat, forall n : Nat, M <= n ->
      normalizedPrimePrefixDefect e t n <= C /\
        normalizedPrimePrefixDefect f t n <= C)
    (hdistinct : Not (exists M : Nat, forall n : Nat, M <= n -> e n = f n)) :
    forall eps : Real, 0 < eps -> forall N : Nat, exists n : Nat, N <= n /\
      forall v w : Nat -> Real, 0 < v n -> 0 < w n ->
        2 - eps <= abs (normalizedPrimePrefixDefect e v n - normalizedPrimePrefixDefect f w n) := by
  let p : Nat -> Real := fun j => PrimeFactorUnimodality.primeAt j
  have hpInject : Function.Injective p := by
    intro i j hij
    dsimp only [p] at hij
    apply PrimeFactorUnimodality.primeAt_strictMono.injective
    exact_mod_cast hij
  have hunequal : forall N : Nat, exists n : Nat, N <= n /\
      Not (Finset.prefixDefect p e (n + 1) = Finset.prefixDefect p f (n + 1)) := by
    intro N
    by_contra h
    have hevent : exists M : Nat, forall k : Nat, M <= k ->
        Finset.prefixDefect p e k = Finset.prefixDefect p f k := by
      refine Exists.intro (N + 1) ?_
      intro k hk
      have hkN : N <= k - 1 := by omega
      have heq : Finset.prefixDefect p e (k - 1 + 1) =
          Finset.prefixDefect p f (k - 1 + 1) := by
        by_contra hn
        exact h (Exists.intro (k - 1) (And.intro hkN hn))
      have hkEq : k - 1 + 1 = k := by omega
      rw [hkEq] at heq
      exact heq
    exact hdistinct ((Finset.prefixDefect_eventually_eq_iff p hpInject e f).mp hevent)
  intro eps heps N
  let M := Classical.choose hcost
  have hM := Classical.choose_spec hcost
  have hQ : exists Q : Nat,
      max (4 * C) (max (2 + C) (64 * C ^ 2 / eps)) < (Q : Real) := exists_nat_gt _
  let Q := Classical.choose hQ
  have hQgt : max (4 * C) (max (2 + C) (64 * C ^ 2 / eps)) < (Q : Real) :=
    Classical.choose_spec hQ
  have hfour : 4 * C < (Q : Real) :=
    (le_max_left (4 * C) (max (2 + C) (64 * C ^ 2 / eps))).trans_lt hQgt
  have hrest : max (2 + C) (64 * C ^ 2 / eps) < (Q : Real) :=
    (le_max_right (4 * C) (max (2 + C) (64 * C ^ 2 / eps))).trans_lt hQgt
  have hsmallQ : 2 + C < (Q : Real) := (le_max_left _ _).trans_lt hrest
  have herrQ : 64 * C ^ 2 / eps < (Q : Real) := (le_max_right _ _).trans_lt hrest
  let n := Classical.choose (hunequal (max N (max M Q)))
  have hn := Classical.choose_spec (hunequal (max N (max M Q)))
  have hMQ : max M Q <= n := (le_max_right N (max M Q)).trans hn.1
  have hMn : M <= n := (le_max_left M Q).trans hMQ
  have hQn : Q <= n := (le_max_right M Q).trans hMQ
  have hprime : (Q : Real) <= p n := by
    dsimp only [p]
    exact_mod_cast hQn.trans (PrimeFactorUnimodality.primeAt_strictMono.id_le n)
  have hp : 0 < p n := by
    dsimp only [p]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hbudget : C < p n / 4 := by linarith only [hfour, hprime]
  have hsmall : 2 < p n - C := by linarith only [hsmallQ, hprime]
  have hratio : 64 * C ^ 2 / eps < p n := herrQ.trans_le hprime
  have hcross : 64 * C ^ 2 < eps * p n := by
    have hm := mul_lt_mul_of_pos_right hratio heps
    have he : 64 * C ^ 2 / eps * eps = 64 * C ^ 2 := by field_simp [heps.ne']
    rw [he] at hm
    linarith only [hm]
  have herr : 64 * C ^ 2 / p n < eps := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt h) hp.le
    have he : 64 * C ^ 2 / p n * p n = 64 * C ^ 2 := by field_simp [hp.ne']
    rw [he] at hm
    exact (not_le_of_gt hcross) hm
  refine Exists.intro n (And.intro ((le_max_left N (max M Q)).trans hn.1) ?_)
  intro v w hv hw
  apply le_of_not_gt
  intro hnear
  have hclose : abs (normalizedPrimePrefixDefect e v n - normalizedPrimePrefixDefect f w n) +
      64 * C ^ 2 / p n < 2 := by linarith only [hnear, herr]
  exact hn.2 (prime_prefix_transport_eq_of_probes_close e f t n C (ht n) hC0
    hbudget hsmall (hM n hMn).1 (hM n hMn).2 v w hv hw hclose)

/-- Within the bounded-distortion class, asymptotically identical defect data
is equivalent to exact agreement of the coordinate permutations on a tail. -/
theorem bounded_profiles_close_iff_eventually_eq
    (e f : Equiv.Perm Nat) (t : Nat -> Real) (ht : forall n, 0 < t n)
    (C : Real) (hC0 : 0 <= C)
    (hcost : exists M : Nat, forall n : Nat, M <= n ->
      normalizedPrimePrefixDefect e t n <= C /\
        normalizedPrimePrefixDefect f t n <= C) :
    (forall eps : Real, 0 < eps -> exists M : Nat, forall n : Nat, M <= n ->
      abs (normalizedPrimePrefixDefect e t n - normalizedPrimePrefixDefect f t n) < eps) <->
    (exists M : Nat, forall n : Nat, M <= n -> e n = f n) := by
  constructor
  . intro hclose
    by_contra hdistinct
    have hsep := bounded_profiles_uniformly_separated_of_not_eventually_eq
      e f t ht C hC0 hcost hdistinct 1 (by norm_num)
    let M := Classical.choose (hclose 1 (by norm_num))
    have hM := Classical.choose_spec (hclose 1 (by norm_num))
    let n := Classical.choose (hsep M)
    have hn := Classical.choose_spec (hsep M)
    have hl := hn.2 t t (ht n) (ht n)
    have hu := hM n hn.1
    linarith only [hl, hu]
  . intro hevent eps heps
    let M := Classical.choose hevent
    have hM := Classical.choose_spec hevent
    refine Exists.intro M ?_
    intro n hn
    have himage := Finset.image_range_eq_of_equal_tail e f M (n + 1) hM (by omega)
    let weight : Nat -> Real := primeLogWeight (t n)
    have he : ((Finset.range (n + 1)).image e).sum weight =
        (Finset.range (n + 1)).sum (fun i => weight (e i)) :=
      Finset.sum_image (fun _ _ _ _ hij => e.injective hij)
    have hf : ((Finset.range (n + 1)).image f).sum weight =
        (Finset.range (n + 1)).sum (fun i => weight (f i)) :=
      Finset.sum_image (fun _ _ _ _ hij => f.injective hij)
    have hprefix : Finset.prefixDefect weight e (n + 1) =
        Finset.prefixDefect weight f (n + 1) := by
      unfold Finset.prefixDefect
      rw [<- he, <- hf, himage]
    have hD : normalizedPrimePrefixDefect e t n = normalizedPrimePrefixDefect f t n := by
      unfold normalizedPrimePrefixDefect
      rw [hprefix]
    rw [hD, sub_self, abs_zero]
    exact heps

end PrimeFactorOscillations.PrimeProfileRigidity
