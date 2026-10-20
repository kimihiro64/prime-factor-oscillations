/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Combinatorics.SeparatedBlockPrefix

/-!
# The complete finite-prefix escape spectrum

For an increasing weight approaching a finite ceiling, the exact budget for
allowing k coordinates to escape every finite set is the ceiling mass minus
the last k prefix weights. The converse already uses finite block swaps.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Finset

/-- The initial prefix minimizes every increasing sum with the same cardinality. -/
theorem sum_range_card_le_sum_monotone (w : Nat -> Real) (hw : Monotone w)
    (s : Finset Nat) : (range s.card).sum w <= s.sum w := by
  have hc : s.card = (range s.card).card := by simp only [card_range]
  have h := card_sdiff_mul_sub_le_sum_sub_sum s (range s.card) w
    (w s.card) (w s.card) hc
    (by
      intro i hi
      apply hw
      have hn := (mem_sdiff.mp hi).2
      have hnot : Not (i < s.card) := fun hi => hn (mem_range.mpr hi)
      omega)
    (by
      intro i hi
      exact hw (Nat.le_of_lt (mem_range.mp (mem_sdiff.mp hi).1)))
  simp only [sub_self, mul_zero] at h
  linarith only [h]

/-- Keep the full remaining prefix while charging k coordinates beyond M. -/
theorem prefixTail_card_lower (w : Nat -> Real) (hw : Monotone w)
    (e : Equiv.Perm Nat) (N k M : Nat)
    (hcard : k <= (((range N).image e) \ range M).card) :
    (k : Real) * w M + (range (N - k)).sum w - (range N).sum w <=
      prefixDefect w e N := by
  let s := (range N).image e
  have hex := exists_subset_card_eq hcard
  let T := Classical.choose hex
  have hT := Classical.choose_spec hex
  have hTs : forall j, Membership.mem T j -> Membership.mem s j := by
    intro j hj
    exact (mem_sdiff.mp (hT.1 hj)).1
  have hcardS : s.card = N := by
    dsimp only [s]
    rw [card_image_iff.mpr (fun _ _ _ _ h => e.injective h), card_range]
  have hcardT : T.card = k := hT.2
  have hcardR : (s \ T).card = N - k := by
    rw [card_sdiff_of_subset hTs, hcardS, hcardT]
  have hmin := sum_range_card_le_sum_monotone w hw (s \ T)
  rw [hcardR] at hmin
  have hlow : (k : Real) * w M <= T.sum w := by
    have h := sum_le_sum (s := T) (fun i hi => hw (show M <= i from by
      have hn := (mem_sdiff.mp (hT.1 hi)).2
      have hnot : Not (i < M) := fun h => hn (mem_range.mpr h)
      omega))
    simpa only [sum_const, nsmul_eq_mul, hcardT] using h
  have hsum := sum_sdiff (f := w) hTs
  have himage : s.sum w = (range N).sum (fun i => w (e i)) := by
    dsimp only [s]
    exact sum_image (fun _ _ _ _ h => e.injective h)
  unfold prefixDefect
  rw [<- himage]
  linarith only [hmin, hlow, hsum]

/-- The ceiling cost of losing the last k coordinates of a prefix of length N. -/
def prefixTailSaturation (w : Nat -> Real) (l : Real) (N k : Nat) : Real :=
  (k : Real) * l - ((range N).sum w - (range (N - k)).sum w)

/-- Every strict subcritical budget bounds the number of coordinates outside one finite prefix. -/
theorem prefixTail_bounded_of_cost_lt_saturation
    (w : Nat -> Real) (l : Real) (hw : Monotone w)
    (hco : forall a : Real, a < l -> exists M : Nat, a < w M)
    (N k : Nat) (hk : 0 < k) (C : Real)
    (hC : C < prefixTailSaturation w l N k) :
    exists M : Nat, forall e : Equiv.Perm Nat, prefixDefect w e N <= C ->
      (((range N).image e) \ range M).card < k := by
  let A := (range N).sum w - (range (N - k)).sum w
  let a := (C + A) / (k : Real)
  have hkR : (0 : Real) < k := by exact_mod_cast hk
  have hid : a * (k : Real) = C + A := by
    dsimp only [a]
    simp [div_eq_mul_inv, hkR.ne']
  change C < (k : Real) * l - A at hC
  have ha : a < l := by
    by_contra hn
    have h := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hkR.le
    nlinarith only [h, hid, hC]
  have hM := hco a ha
  let M := Classical.choose hM
  have hMgt := Classical.choose_spec hM
  refine Exists.intro M ?_
  intro e he
  by_contra hn
  have hcard : k <= (((range N).image e) \ range M).card := le_of_not_gt hn
  have hlow := prefixTail_card_lower w hw e N k M hcard
  have hmul := mul_lt_mul_of_pos_right hMgt hkR
  have hstrict : C < (k : Real) * w M - A := by nlinarith only [hmul, hid]
  dsimp only [A] at hstrict
  linarith only [hstrict, hlow, he]

/-- One canonical block permutation pays at most the saturation for every upper-bounded weight. -/
theorem prefixDefect_separatedBlockSwap_le_saturation
    (w : Nat -> Real) (l : Real) (hupper : forall i : Nat, w i <= l)
    (N k b : Nat) (hk : k <= N) (hNb : N <= b) :
    prefixDefect w (Equiv.separatedBlockSwap (N - k) b k (by omega)) N <=
      prefixTailSaturation w l N k := by
  have haN : N - k + k = N := by omega
  have hsep : N - k + k <= b := by omega
  have hid := prefixDefect_separatedBlockSwap w (N - k) b k hsep
  rw [haN] at hid
  have hprefix := sum_range_add w (N - k) k
  rw [haN] at hprefix
  have hsum := sum_le_sum (s := range k) (fun i hi => hupper (b + i))
  simp only [sum_const, nsmul_eq_mul, card_range] at hsum
  unfold prefixTailSaturation
  linarith only [hid, hprefix, hsum]

/-- The same finite block exchange escapes simultaneously for an arbitrary weight family. -/
theorem exists_common_prefixTail_escape_at_saturation
    {J : Type*} (w : J -> Nat -> Real) (l : J -> Real)
    (hupper : forall j : J, forall i : Nat, w j i <= l j)
    (N k M : Nat) (hk : k <= N) :
    exists e : Equiv.Perm Nat, exists L : Nat,
      (forall i : Nat, L <= i -> e i = i) /\
      k <= (((range N).image e) \ range M).card /\
      (forall j : J, prefixDefect (w j) e N <= prefixTailSaturation (w j) (l j) N k) := by
  let a := N - k
  let b := max N M
  have haN : a + k = N := by dsimp only [a]; omega
  have hsep : a + k <= b := by dsimp only [a, b]; omega
  let e := Equiv.separatedBlockSwap a b k hsep
  have htail := card_le_prefixTail_separatedBlockSwap a b k M hsep
    (by dsimp only [b]; exact le_max_right _ _)
  rw [haN] at htail
  refine Exists.intro e (Exists.intro (b + k) (And.intro ?_ (And.intro htail ?_)))
  . intro i hi
    exact Equiv.separatedBlockSwap_apply_tail a b k hsep i hi
  . intro j
    exact prefixDefect_separatedBlockSwap_le_saturation (w j) (l j) (hupper j)
      N k b hk (by dsimp only [b]; exact le_max_left _ _)

/-- A finite block permutation realizes k escaping coordinates at the saturation budget. -/
theorem exists_prefixTail_escape_at_saturation
    (w : Nat -> Real) (l : Real) (hupper : forall i : Nat, w i <= l)
    (N k M : Nat) (hk : k <= N) :
    exists e : Equiv.Perm Nat, exists L : Nat,
      (forall i : Nat, L <= i -> e i = i) /\
      k <= (((range N).image e) \ range M).card /\
      prefixDefect w e N <= prefixTailSaturation w l N k := by
  have h := exists_common_prefixTail_escape_at_saturation
    (fun _ : Unit => w) (fun _ : Unit => l) (fun _ => hupper) N k M hk
  let e := Classical.choose h
  have hL := Classical.choose_spec h
  let L := Classical.choose hL
  have he := Classical.choose_spec hL
  exact Exists.intro e (Exists.intro L (And.intro he.1
    (And.intro he.2.1 (he.2.2 Unit.unit))))

/-- Every escape multiplicity has its exact cost threshold, including the critical equality. -/
theorem prefixTail_locality_iff
    (w : Nat -> Real) (l : Real) (hw : Monotone w)
    (hupper : forall i : Nat, w i <= l)
    (hco : forall a : Real, a < l -> exists M : Nat, a < w M)
    (N k : Nat) (hkpos : 0 < k) (hk : k <= N) (C : Real) :
    (exists M : Nat, forall e : Equiv.Perm Nat, prefixDefect w e N <= C ->
      (((range N).image e) \ range M).card < k) <->
    C < prefixTailSaturation w l N k := by
  constructor
  . intro h
    let M := Classical.choose h
    have hcover := Classical.choose_spec h
    by_contra hn
    have hTC : prefixTailSaturation w l N k <= C := le_of_not_gt hn
    have hex := exists_prefixTail_escape_at_saturation w l hupper N k M hk
    let e := Classical.choose hex
    have hL := Classical.choose_spec hex
    let L := Classical.choose hL
    have he := Classical.choose_spec hL
    have hcost : prefixDefect w e N <= C := he.2.2.trans hTC
    exact (not_le_of_gt (hcover e hcost)) he.2.1
  . intro hC
    exact prefixTail_bounded_of_cost_lt_saturation w l hw hco N k hkpos C hC

/-- Simultaneous budgets localize exactly when one member is strictly subcritical, even for infinite families. -/
theorem prefixTail_joint_locality_iff
    {J : Type*} (w : J -> Nat -> Real) (l C : J -> Real)
    (hw : forall j : J, Monotone (w j))
    (hupper : forall j : J, forall i : Nat, w j i <= l j)
    (hco : forall j : J, forall a : Real, a < l j -> exists M : Nat, a < w j M)
    (N k : Nat) (hkpos : 0 < k) (hk : k <= N) :
    (exists M : Nat, forall e : Equiv.Perm Nat,
      (forall j : J, prefixDefect (w j) e N <= C j) ->
      (((range N).image e) \ range M).card < k) <->
    (exists j : J, C j < prefixTailSaturation (w j) (l j) N k) := by
  constructor
  . intro h
    let M := Classical.choose h
    have hcover := Classical.choose_spec h
    by_contra hn
    have hTC : forall j : J, prefixTailSaturation (w j) (l j) N k <= C j := by
      intro j
      exact le_of_not_gt (fun hbad => hn (Exists.intro j hbad))
    have hex := exists_common_prefixTail_escape_at_saturation w l hupper N k M hk
    let e := Classical.choose hex
    have hL := Classical.choose_spec hex
    let L := Classical.choose hL
    have he := Classical.choose_spec hL
    have hcost : forall j : J, prefixDefect (w j) e N <= C j := by
      intro j
      exact (he.2.2 j).trans (hTC j)
    exact (not_le_of_gt (hcover e hcost)) he.2.1
  . intro h
    let j := Classical.choose h
    have hj := Classical.choose_spec h
    have hM := prefixTail_bounded_of_cost_lt_saturation
      (w j) (l j) (hw j) (hco j) N k hkpos (C j) hj
    let M := Classical.choose hM
    have hcover := Classical.choose_spec hM
    exact Exists.intro M (fun e he => hcover e (he j))

end Finset
