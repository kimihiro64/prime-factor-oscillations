/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.NumberTheory.PrimeCounting
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliPrefixBounds

/-! # Uniform comparison of mixed finite Bernoulli arrays

A uniform replacement modulus, canonical deleted-array representations and
exact exceptional-coordinate odds budgets supply the finite inputs for comparing
regular families. Deterministic endpoints retain their exact rank transport.
-/

set_option autoImplicit false
set_option Elab.async false

universe u v

namespace List

theorem bernoulliMass_uniform_replacement_modulus (A epsilon : Real)
    (hA : 0 <= A) (hepsilon : 0 < epsilon) :
    exists delta : Real, 0 < delta /\ delta < 1 /\
      forall (front : List Real) (ps : List (Prod Real Real)) (r : Nat),
        (forall a, List.Mem a front -> 0 <= a /\ a <= 1) ->
        (forall p, List.Mem p ps ->
          (0 <= p.1 /\ p.1 <= 1) /\ (0 <= p.2 /\ p.2 <= 1)) ->
        (forall (left right : List (Prod Real Real)) (a b : Real),
          ps = left ++ (a, b) :: right ->
            0 < bernoulliMass (front ++ left.map Prod.fst ++ right.map Prod.snd) (r + 1) /\
              abs (bernoulliMass (front ++ left.map Prod.fst ++ right.map Prod.snd) r /
                bernoulliMass (front ++ left.map Prod.fst ++ right.map Prod.snd) (r + 1) -
                  1) <= delta) ->
        0 < bernoulliMass (front ++ ps.map Prod.snd) (r + 1) ->
        (ps.map (fun p => abs (p.1 - p.2))).sum <= A ->
          abs (bernoulliMass (front ++ ps.map Prod.fst) (r + 1) /
            bernoulliMass (front ++ ps.map Prod.snd) (r + 1) - 1) <= epsilon := by
  let t := 8 * (A + 1)
  have ht : 0 < t := mul_pos (by norm_num) (by linarith only [hA])
  let delta := min (1 / 4) (min (1 / t) (epsilon / t))
  have hd : 0 < delta :=
    lt_min (by norm_num) (lt_min (div_pos (by norm_num) ht) (div_pos hepsilon ht))
  have hdquarter : delta <= 1 / 4 := min_le_left _ _
  have hd1 : delta < 1 := by linarith only [hdquarter]
  have hdt : delta <= 1 / t := (min_le_right _ _).trans (min_le_left _ _)
  have hde : delta <= epsilon / t := (min_le_right _ _).trans (min_le_right _ _)
  refine Exists.intro delta (And.intro hd (And.intro hd1 ?_))
  intro front ps r hfront hpairs hcontrol hpos hcost
  have hcost0 : 0 <= (ps.map (fun p => abs (p.1 - p.2))).sum := by
    apply List.sum_nonneg
    intro b hb
    have hp := List.mem_map.mp hb
    choose p hp using hp
    rw [<- hp.2]
    exact abs_nonneg _
  have hden : 0 < 1 - delta := sub_pos.mpr hd1
  have hratio : delta / (1 - delta) <= 2 * delta := by
    calc
      _ <= delta / (1 / 2) := div_le_div_of_nonneg_left hd.le (by norm_num)
        (by linarith only [hdquarter])
      _ = _ := by ring
  let B := delta / (1 - delta) * (ps.map (fun p => abs (p.1 - p.2))).sum
  have hB0 : 0 <= B := mul_nonneg (div_nonneg hd.le hden.le) hcost0
  have hB : B <= 2 * delta * A :=
    mul_le_mul hratio hcost hcost0 (mul_nonneg (by norm_num) hd.le)
  have htone : (1 / t) * t = 1 := by field_simp [ne_of_gt ht]
  have hte : (epsilon / t) * t = epsilon := by field_simp [ne_of_gt ht]
  have hbt := mul_le_mul_of_nonneg_right hdt ht.le
  have hbe := mul_le_mul_of_nonneg_right hde ht.le
  rw [htone] at hbt
  rw [hte] at hbe
  dsimp [t] at hbt hbe
  have hBquarter : B <= 1 / 4 := by linarith only [hB, hbt, hd.le]
  have hBepsilon : B <= epsilon / 4 := by linarith only [hB, hbe, hd.le]
  have hB1 : B < 1 := by linarith only [hBquarter]
  have hc := bernoulliMass_replacement_ratio_bound front ps r delta hd.le hd1
    hfront hpairs hcontrol hpos hB1
  have hfinal : B / (1 - B) <= epsilon := by
    calc
      _ <= B / (1 / 2) := div_le_div_of_nonneg_left hB0 (by norm_num)
        (by linarith only [hBquarter])
      _ = 2 * B := by ring
      _ <= epsilon := by linarith only [hBepsilon, hepsilon]
  exact hc.trans hfinal

end List

namespace List

theorem map_decomposition_with_coordinate {alpha : Type u} {beta : Type v}
    (f : alpha -> beta) (original : List alpha)
    (left right : List beta) (value : beta)
    (h : original.map f = left ++ value :: right) :
    exists (before : List alpha) (x : alpha) (after : List alpha),
      original = before ++ x :: after /\ before.map f = left /\
        f x = value /\ after.map f = right := by
  have hs := List.map_eq_append_iff.mp h
  choose before rest hs using hs
  have hx := List.map_eq_cons_iff.mp hs.2.2
  choose x after hx using hx
  refine Exists.intro before (Exists.intro x (Exists.intro after ?_))
  exact And.intro (by rw [hs.1, hx.1])
    (And.intro hs.2.1 (And.intro hx.2.1 hx.2.2))

theorem hybrid_deleted_map_perm {alpha : Type u} {beta : Type v}
    [DecidableEq alpha] (original left right : List alpha) (deleted : alpha)
    (hnodup : original.Nodup) (hdecomp : original = left ++ deleted :: right)
    (f g : alpha -> beta) :
    exists h : alpha -> beta,
      (forall x, h x = f x \/ h x = g x) /\
        (left.map f ++ right.map g).Perm
          ((original.toFinset.erase deleted).toList.map h) := by
  classical
  have hN : (left ++ deleted :: right).Nodup := by rw [<- hdecomp]; exact hnodup
  have hp := List.nodup_append.mp hN
  have hr := List.nodup_cons.mp hp.2.1
  have hnotleft : Not (List.Mem deleted left) := by
    intro hh
    exact hp.2.2 deleted hh deleted (List.Mem.head _) rfl
  have hdisjoint : forall x, List.Mem x left -> Not (List.Mem x right) := by
    intro x hx hy
    exact hp.2.2 x hx x (List.Mem.tail _ hy) rfl
  have hboth : (left ++ right).Nodup := List.nodup_append.mpr
    (And.intro hp.1 (And.intro hr.2
      (fun x hx y hy => hp.2.2 x hx y (List.Mem.tail _ hy))))
  let h := fun x => if List.Mem x left then f x else g x
  have hleft : left.map f = left.map h := by
    apply List.map_congr_left
    intro x hx
    change f x = if List.Mem x left then f x else g x
    rw [ite_eq_left (show List.Mem x left from hx)]
  have hright : right.map g = right.map h := by
    apply List.map_congr_left
    intro x hx
    have hnot : Not (List.Mem x left) := by
      intro hh
      exact hdisjoint x hh hx
    simp [h, hnot]
  have hmap : left.map f ++ right.map g = (left ++ right).map h := by
    rw [List.map_append, hleft, hright]
  have hE : (left ++ right).toFinset = original.toFinset.erase deleted := by
    apply Finset.ext
    intro x
    constructor
    next =>
      intro hx
      have hm := List.mem_append.mp (List.mem_toFinset.mp hx)
      apply Finset.mem_erase.mpr
      constructor
      next =>
        intro heq
        subst x
        cases hm with
        | inl hl => exact hnotleft hl
        | inr hh => exact hr.1 hh
      next =>
        apply List.mem_toFinset.mpr
        rw [hdecomp]
        cases hm with
        | inl hl => exact List.mem_append.mpr (Or.inl hl)
        | inr hh =>
            exact List.mem_append.mpr (Or.inr (List.Mem.tail _ hh))
    next =>
      intro hx
      have hh := Finset.mem_erase.mp hx
      have hm := List.mem_toFinset.mp hh.2
      rw [hdecomp] at hm
      apply List.mem_toFinset.mpr
      apply List.mem_append.mpr
      cases List.mem_append.mp hm with
      | inl hl => exact Or.inl hl
      | inr hc =>
          cases List.mem_cons.mp hc with
          | inl heq => exact False.elim (hh.1 heq)
          | inr hr => exact Or.inr hr
  refine Exists.intro h (And.intro ?_ ?_)
  next =>
    intro x
    by_cases hx : List.Mem x left
    next => exact Or.inl (by simp [h, hx])
    next => exact Or.inr (by simp [h, hx])
  next =>
    have hperm := (List.toFinset_toList hboth).map h
    rw [hE] at hperm
    rw [hmap]
    exact hperm.symm

end List

namespace Real

/-- This is the zero-extended odds observable at the deterministic endpoints.
Its later consumer is a sum over bernoulliInterior, where every denominator
is positive. The endpoint value here is deliberately zero. -/
theorem tilt_zeroExtendedOdds (a z : Real) (ha0 : 0 <= a) (ha1 : a <= 1)
    (hz : 0 < z) :
    (a * z / (1 - a + a * z)) / (1 - a * z / (1 - a + a * z)) =
      z * (a / (1 - a)) := by
  by_cases hone : a = 1
  next => simp [hone, ne_of_gt hz]
  next =>
    have hlt : a < 1 := lt_of_le_of_ne ha1 hone
    have hm : 0 < 1 - a := sub_pos.mpr hlt
    have hd : 0 < 1 - a + a * z := List.bernoulliFactor_pos a z ha0 ha1 hz
    have hid : 1 - a * z / (1 - a + a * z) =
        (1 - a) / (1 - a + a * z) := by
      field_simp [ne_of_gt hd]
      ring
    rw [hid]
    field_simp [ne_of_gt hm, ne_of_gt hd]

end Real

namespace List

theorem sum_interior_odds_tilt (s : List Real)
    (hs : forall a, List.Mem a s -> 0 <= a /\ a <= 1)
    (z : Real) (hz : 0 < z) :
    ((bernoulliInterior (s.map (fun a => a * z / (1 - a + a * z)))).map
      (fun a => a / (1 - a))).sum =
        z * ((bernoulliInterior s).map (fun a => a / (1 - a))).sum := by
  let t := s.map (fun a => a * z / (1 - a + a * z))
  have ht : forall b, List.Mem b t -> 0 <= b /\ b <= 1 := by
    intro b hb
    have ha := List.mem_map.mp hb
    choose a ha using ha
    rw [<- ha.2]
    exact bernoulliTilt_mem_unitInterval a z (hs a ha.1).1 (hs a ha.1).2 hz
  have hmap : t.map (fun a => a / (1 - a)) =
      s.map (fun a => z * (a / (1 - a))) := by
    simp only [t, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro a ha
    exact Real.tilt_zeroExtendedOdds a z (hs a ha).1 (hs a ha).2 hz
  change ((bernoulliInterior t).map (fun a => a / (1 - a))).sum = _
  rw [sum_map_bernoulliInterior t ht (fun a => a / (1 - a)) (by simp) (by simp)]
  rw [hmap]
  rw [sum_map_bernoulliInterior s hs (fun a => a / (1 - a)) (by simp) (by simp)]
  clear hs ht hmap t
  induction s with
  | nil => simp
  | cons a s ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem bernoulliInterior_append_of_interior (front tail : List Real)
    (htail : forall a, List.Mem a tail -> 0 < a /\ a < 1) :
    bernoulliInterior (front ++ tail) = bernoulliInterior front ++ tail := by
  have ht : bernoulliInterior tail = tail := by
    unfold bernoulliInterior
    apply List.filter_eq_self.mpr
    intro a ha
    simpa only [decide_eq_true_eq] using htail a ha
  unfold bernoulliInterior at *
  rw [List.filter_append, ht]

theorem count_one_append_of_interior (front tail : List Real)
    (htail : forall a, List.Mem a tail -> 0 < a /\ a < 1) :
    (front ++ tail).count 1 = front.count 1 := by
  have hnot : Not (List.Mem (1 : Real) tail) := by
    intro hh
    exact (lt_irrefl (1 : Real)) (htail 1 hh).2
  rw [List.count_append, List.count_eq_zero.mpr hnot, add_zero]

end List

namespace Finset

/-- A fixed finite budget controls every retained small-coordinate mixture.
Only interior odds are summed, including at deterministic endpoint inputs. -/
theorem sum_interior_odds_tilt_mixture_le {alpha : Type u} [DecidableEq alpha]
    (B E : Finset alpha)
    (hEB : forall p, Membership.mem E p -> Membership.mem B p)
    (f g eta : alpha -> Real)
    (hf : forall p, Membership.mem B p -> 0 <= f p /\ f p <= 1)
    (hg : forall p, Membership.mem B p -> 0 <= g p /\ g p <= 1)
    (hchoice : forall p, Membership.mem E p -> eta p = f p \/ eta p = g p)
    (z : Real) (hz : 0 < z) :
    ((List.bernoulliInterior (E.toList.map
      (fun p => eta p * z / (1 - eta p + eta p * z)))).map
        (fun a => a / (1 - a))).sum <=
          z * B.sum (fun p => f p / (1 - f p) + g p / (1 - g p)) := by
  have he : forall p, Membership.mem E p -> 0 <= eta p /\ eta p <= 1 := by
    intro p hp
    cases hchoice p hp with
    | inl hh => rw [hh]; exact hf p (hEB p hp)
    | inr hh => rw [hh]; exact hg p (hEB p hp)
  have hs : forall a, List.Mem a (E.toList.map eta) -> 0 <= a /\ a <= 1 := by
    intro a ha
    have hp := List.mem_map.mp ha
    choose p hp using hp
    rw [<- hp.2]
    exact he p (Finset.mem_toList.mp hp.1)
  have ht := List.sum_interior_odds_tilt (E.toList.map eta) hs z hz
  have hid :
      ((List.bernoulliInterior (E.toList.map
        (fun p => eta p * z / (1 - eta p + eta p * z)))).map
          (fun a => a / (1 - a))).sum =
        z * ((List.bernoulliInterior (E.toList.map eta)).map
          (fun a => a / (1 - a))).sum := by
    simpa only [List.map_map, Function.comp_def] using ht
  have ho : ((List.bernoulliInterior (E.toList.map eta)).map
      (fun a => a / (1 - a))).sum = E.sum (fun p => eta p / (1 - eta p)) := by
    rw [List.sum_map_bernoulliInterior (E.toList.map eta) hs
      (fun a => a / (1 - a)) (by simp) (by simp)]
    simp
  rw [hid, ho]
  apply mul_le_mul_of_nonneg_left _ hz.le
  calc
    _ <= E.sum (fun p => f p / (1 - f p) + g p / (1 - g p)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hfn := div_nonneg (hf p (hEB p hp)).1 (sub_nonneg.mpr (hf p (hEB p hp)).2)
      have hgn := div_nonneg (hg p (hEB p hp)).1 (sub_nonneg.mpr (hg p (hEB p hp)).2)
      cases hchoice p hp with
      | inl hh => rw [hh]; linarith only [hgn]
      | inr hh => rw [hh]; linarith only [hfn]
    _ <= _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hEB
      intro p hp hnot
      exact add_nonneg
        (div_nonneg (hf p hp).1 (sub_nonneg.mpr (hf p hp).2))
        (div_nonneg (hg p hp).1 (sub_nonneg.mpr (hg p hp).2))

/-- The retained support splits into its selected low part and its disjoint
complement, preserving the exact coefficient array up to permutation. -/
theorem toList_perm_filter_sdiff {alpha : Type u} [DecidableEq alpha]
    (E B : Finset alpha) :
    E.toList.Perm ((E.filter (fun p => Membership.mem B p)).toList ++ (E \ B).toList) := by
  have hN : ((E.filter (fun p => Membership.mem B p)).toList ++ (E \ B).toList).Nodup := by
    apply List.nodup_append.mpr
    refine And.intro (Finset.nodup_toList _) (And.intro (Finset.nodup_toList _) ?_)
    intro a ha b hb heq
    have hBa := (Finset.mem_filter.mp (Finset.mem_toList.mp ha)).2
    have hBb := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2
    apply hBb
    rw [<- heq]
    exact hBa
  apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList E) hN).mpr
  intro p
  by_cases hp : Membership.mem B p
  next => simp [hp]
  next => simp [hp]


/-- The complete tilted coordinate-change cost for two regular prime laws
is bounded independently of the upper prime cutoff and of every tilt z >= 1. -/
theorem sum_abs_regularPrimeLaws_tilt_sub_le
    (P n : Nat) (hPn : P <= n) (nu K z : Real)
    (hnu : 0 < nu) (hK : 0 <= K) (hz1 : 1 <= z)
    (eta1 eta2 : Nat -> Real)
    (hunit1 : forall p, Nat.Prime p -> 0 <= eta1 p /\ eta1 p <= 1)
    (hunit2 : forall p, Nat.Prime p -> 0 <= eta2 p /\ eta2 p <= 1)
    (hinterior1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p /\ eta1 p < 1)
    (hinterior2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p /\ eta2 p < 1)
    (hlower1 : forall p, Nat.Prime p -> P < p ->
      (nu / 2) / (p : Real) <= eta1 p / (1 - eta1 p))
    (hlower2 : forall p, Nat.Prime p -> P < p ->
      (nu / 2) / (p : Real) <= eta2 p / (1 - eta2 p))
    (herror1 : forall p, Nat.Prime p -> P < p ->
      abs (eta1 p / (1 - eta1 p) - nu / (p : Real)) <= K / (p : Real) ^ 2)
    (herror2 : forall p, Nat.Prime p -> P < p ->
      abs (eta2 p / (1 - eta2 p) - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    (n + 1).primesBelow.sum (fun p =>
      abs (eta1 p * z / (1 - eta1 p + eta1 p * z) -
        eta2 p * z / (1 - eta2 p + eta2 p * z))) <=
          ((P + 1).primesBelow.card : Real) +
            2 * K * (1 / (nu / 2) ^ 2 + 1 / (nu / 2)) := by
  let A := (n + 1).primesBelow
  let B := (P + 1).primesBelow
  let T := A \ B
  let a1 := fun p => eta1 p / (1 - eta1 p)
  let a2 := fun p => eta2 p / (1 - eta2 p)
  let f1 := fun p => eta1 p * z / (1 - eta1 p + eta1 p * z)
  let f2 := fun p => eta2 p * z / (1 - eta2 p + eta2 p * z)
  let d := fun p => abs (f1 p - f2 p)
  have hz : 0 < z := lt_of_lt_of_le (by norm_num) hz1
  have hc : 0 < nu / 2 := div_pos hnu (by norm_num)
  have hT (p : Nat) (hp : Membership.mem T p) :
      Nat.Prime p /\ P < p /\ p <= n := by
    have hh := Finset.mem_sdiff.mp hp
    have hl := Nat.mem_primesBelow.mp hh.1
    have hcut : Not (p < P + 1) := by
      intro h
      exact hh.2 (Nat.mem_primesBelow.mpr (And.intro h hl.2))
    exact And.intro hl.2 (And.intro (by omega) (by omega))
  have hdiff : forall p, Membership.mem T p ->
      abs (a1 p - a2 p) <= (2 * K) / (p : Real) ^ 2 := by
    intro p hp
    have hh := hT p hp
    calc
      _ <= abs (a1 p - nu / (p : Real)) + abs (nu / (p : Real) - a2 p) :=
        abs_sub_le _ _ _
      _ <= K / (p : Real) ^ 2 + K / (p : Real) ^ 2 := by
        apply add_le_add (herror1 p hh.1 hh.2.1)
        rw [abs_sub_comm]
        exact herror2 p hh.1 hh.2.1
      _ = _ := by ring
  have hSN : forall p, Membership.mem T p -> Membership.mem (Finset.range (n + 1)) p := by
    intro p hp
    exact Finset.mem_range.mpr ((Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).1)
  have hkernel := Finset.sum_abs_tiltOdds_sub_le T (n + 1) hSN a1 a2 (nu / 2)
    (2 * K) z hc (mul_nonneg (by norm_num) hK) hz1
    (fun p hp => (hT p hp).1.one_le)
    (fun p hp => hlower1 p (hT p hp).1 (hT p hp).2.1)
    (fun p hp => hlower2 p (hT p hp).1 (hT p hp).2.1) hdiff
  have htilt (eta : Real) (h0 : 0 < eta) (h1 : eta < 1) :
      eta * z / (1 - eta + eta * z) =
        z * (eta / (1 - eta)) / (1 + z * (eta / (1 - eta))) := by
    have hh := Real.localLaw_tilt_eq_odds_tilt eta z h0 h1 hz
    have hid : 1 + (z - 1) * eta = 1 - eta + eta * z := by ring
    rwa [hid] at hh
  have htail : T.sum d <= 2 * K * (1 / (nu / 2) ^ 2 + 1 / (nu / 2)) := by
    calc
      _ = T.sum (fun p => abs (z * a1 p / (1 + z * a1 p) -
          z * a2 p / (1 + z * a2 p))) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hh := hT p hp
        have h1 := hinterior1 p hh.1 hh.2.1
        have h2 := hinterior2 p hh.1 hh.2.1
        dsimp [d, f1, f2]
        rw [htilt (eta1 p) h1.1 h1.2, htilt (eta2 p) h2.1 h2.2]
      _ <= _ := hkernel
  have hsmall : B.sum d <= (B.card : Real) := by
    calc
      _ <= B.sum (fun _ => (1 : Real)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hprime := (Nat.mem_primesBelow.mp hp).2
        have hu1 := hunit1 p hprime
        have hu2 := hunit2 p hprime
        have ht1 : 0 <= f1 p /\ f1 p <= 1 :=
          List.bernoulliTilt_mem_unitInterval (eta1 p) z hu1.1 hu1.2 hz
        have ht2 : 0 <= f2 p /\ f2 p <= 1 :=
          List.bernoulliTilt_mem_unitInterval (eta2 p) z hu2.1 hu2.2 hz
        change abs (f1 p - f2 p) <= 1
        have hl := _root_.sub_le_sub ht1.1 ht2.2
        have hu := _root_.sub_le_sub ht1.2 ht2.1
        exact abs_le.mpr (And.intro (by simpa using hl) (by simpa using hu))
      _ = _ := by simp
  have hBA : forall p, Membership.mem B p -> Membership.mem A p := by
    intro p hp
    have hh := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr (And.intro (by omega) hh.2)
  have hsplit : T.sum d + B.sum d = A.sum d := Finset.sum_sdiff hBA
  change A.sum d <= (B.card : Real) + _
  rw [<- hsplit]
  exact (add_le_add htail hsmall).trans_eq (add_comm _ _)



end Finset
