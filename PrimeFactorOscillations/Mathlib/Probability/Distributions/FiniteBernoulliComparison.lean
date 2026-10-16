/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliBounds
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliTilt

/-! # Finite Bernoulli coefficient comparison by coordinate replacement

Adjacent-coefficient flatness controls a whole sequence of coordinate changes
through their total absolute probability change. Largest-weight odds bounds
supply the flatness criterion. Every probability and denominator condition is
explicit, including deterministic coordinates in the replacement comparison.
-/

set_option autoImplicit false
set_option Elab.async false

namespace List

/-- All finite Bernoulli coefficients are nonnegative for probability coordinates. -/
theorem bernoulliMass_nonneg (s : List Real)
    (h : forall a, List.Mem a s -> 0 <= a /\ a <= 1) (r : Nat) :
    0 <= bernoulliMass s r := by
  revert h
  induction s generalizing r with
  | nil => intro h; cases r <;> simp [bernoulliMass]
  | cons a s ih =>
    intro h
    have ha := h a (List.Mem.head _)
    have hs : forall b, List.Mem b s -> 0 <= b /\ b <= 1 :=
      fun b hb => h b (List.Mem.tail _ hb)
    cases r with
    | zero => exact mul_nonneg (sub_nonneg.mpr ha.2) (ih 0 hs)
    | succ r =>
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr ha.2) (ih (r + 1) hs))
        (mul_nonneg ha.1 (ih r hs))

private theorem replacementCost_nonneg (ps : List (Prod Real Real)) :
    0 <= (ps.map (fun p => abs (p.1 - p.2))).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih => exact add_nonneg (abs_nonneg _) ih

private theorem relative_budget_comp (x y z a b : Real)
    (hx : 0 <= x) (hz : 0 <= z) (ha : 0 <= a) (hb : 0 <= b)
    (hab : a + b <= 1)
    (hxy : (1 - a) * x <= y) (hyx : (1 - a) * y <= x)
    (hyz : (1 - b) * y <= z) (hzy : (1 - b) * z <= y) :
    (1 - (a + b)) * x <= z /\ (1 - (a + b)) * z <= x := by
  have ha1 : 0 <= 1 - a := by linarith only [hab, hb]
  have hb1 : 0 <= 1 - b := by linarith only [hab, ha]
  constructor
  next =>
    have hprod := mul_nonneg (mul_nonneg ha hb) hx
    have hpoly : (1 - (a + b)) * x <= (1 - b) * ((1 - a) * x) := by
      nlinarith only [hprod]
    exact hpoly.trans ((mul_le_mul_of_nonneg_left hxy hb1).trans hyz)
  next =>
    have hprod := mul_nonneg (mul_nonneg ha hb) hz
    have hpoly : (1 - (a + b)) * z <= (1 - a) * ((1 - b) * z) := by
      nlinarith only [hprod]
    exact hpoly.trans ((mul_le_mul_of_nonneg_left hzy ha1).trans hyx)

/-- A nearly flat pair of adjacent coefficients gives relative stability under
one probability replacement, including either deterministic endpoint. -/
theorem bernoulliMass_cons_relative_change (s : List Real) (r : Nat)
    (a b epsilon : Real) (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1)
    (he0 : 0 <= epsilon) (he1 : epsilon < 1)
    (hbase : 0 < bernoulliMass s (r + 1))
    (hflat : abs (bernoulliMass s r / bernoulliMass s (r + 1) - 1) <= epsilon) :
    0 < bernoulliMass (a :: s) (r + 1) /\
    0 < bernoulliMass (b :: s) (r + 1) /\
    abs (bernoulliMass (a :: s) (r + 1) - bernoulliMass (b :: s) (r + 1)) <=
      (epsilon / (1 - epsilon) * abs (a - b)) * bernoulliMass (a :: s) (r + 1) /\
    abs (bernoulliMass (a :: s) (r + 1) - bernoulliMass (b :: s) (r + 1)) <=
      (epsilon / (1 - epsilon) * abs (a - b)) * bernoulliMass (b :: s) (r + 1) := by
  let A := bernoulliMass s (r + 1)
  let B := bernoulliMass s r
  have hA : 0 < A := hbase
  have hAne : Not (A = 0) := ne_of_gt hA
  have hmargin : 0 < 1 - epsilon := sub_pos.mpr he1
  have hmarginNe : Not (1 - epsilon = 0) := ne_of_gt hmargin
  have hflatA : abs (B - A) <= epsilon * A := by
    have hid : (B - A) / A = B / A - 1 := by field_simp
    have hf : abs ((B - A) / A) <= epsilon := by
      rw [hid]
      exact hflat
    have hm := mul_le_mul_of_nonneg_right hf hA.le
    have hc : abs ((B - A) / A) * A = abs (B - A) := by
      rw [abs_div, abs_of_pos hA]
      field_simp
    rwa [hc] at hm
  have hlower (u : Real) (hu0 : 0 <= u) (hu1 : u <= 1) :
      (1 - epsilon) * A <= bernoulliMass (u :: s) (r + 1) := by
    have hl := mul_le_mul_of_nonneg_left (abs_le.mp hflatA).1 hu0
    have hu := mul_le_mul_of_nonneg_right hu1 (mul_nonneg he0 hA.le)
    change (1 - epsilon) * A <= (1 - u) * A + u * B
    nlinarith only [hl, hu]
  have hpa := (mul_pos hmargin hA).trans_le (hlower a ha0 ha1)
  have hpb := (mul_pos hmargin hA).trans_le (hlower b hb0 hb1)
  have hdiff :
      abs (bernoulliMass (a :: s) (r + 1) - bernoulliMass (b :: s) (r + 1)) =
        abs (a - b) * abs (B - A) := by
    have hid : bernoulliMass (a :: s) (r + 1) - bernoulliMass (b :: s) (r + 1) =
        (a - b) * (B - A) := by
      simp only [bernoulliMass]
      dsimp [A, B]
      ring
    rw [hid, abs_mul]
  have hdiffBound :
      abs (bernoulliMass (a :: s) (r + 1) - bernoulliMass (b :: s) (r + 1)) <=
        epsilon * abs (a - b) * A := by
    rw [hdiff]
    calc
      _ <= abs (a - b) * (epsilon * A) :=
        mul_le_mul_of_nonneg_left hflatA (abs_nonneg _)
      _ = _ := by ring
  have hfactor : 0 <= epsilon / (1 - epsilon) * abs (a - b) :=
    mul_nonneg (div_nonneg he0 hmargin.le) (abs_nonneg _)
  have hcancel :
      (epsilon / (1 - epsilon) * abs (a - b)) * ((1 - epsilon) * A) =
        epsilon * abs (a - b) * A := by field_simp
  have hbound (u : Real) (hu0 : 0 <= u) (hu1 : u <= 1) :
      abs (bernoulliMass (a :: s) (r + 1) - bernoulliMass (b :: s) (r + 1)) <=
        (epsilon / (1 - epsilon) * abs (a - b)) * bernoulliMass (u :: s) (r + 1) := by
    have hh := mul_le_mul_of_nonneg_left (hlower u hu0 hu1) hfactor
    rw [hcancel] at hh
    exact hdiffBound.trans hh
  exact And.intro hpa (And.intro hpb
    (And.intro (hbound a ha0 ha1) (hbound b hb0 hb1)))

/-- A finite sequence of replacements has an additive relative error budget.
Only the canonical prefix-replacement arrays are required in the hypotheses. -/
theorem bernoulliMass_replacement_bound (front : List Real)
    (ps : List (Prod Real Real)) (r : Nat) (epsilon : Real)
    (he0 : 0 <= epsilon) (he1 : epsilon < 1) :
    (forall a, List.Mem a front -> 0 <= a /\ a <= 1) ->
    (forall p, List.Mem p ps ->
      (0 <= p.1 /\ p.1 <= 1) /\ (0 <= p.2 /\ p.2 <= 1)) ->
    (forall (left right : List (Prod Real Real)) (a b : Real),
      ps = left ++ (a, b) :: right ->
      0 < bernoulliMass (front ++ left.map Prod.fst ++ right.map Prod.snd) (r + 1) /\
      abs (bernoulliMass (front ++ left.map Prod.fst ++ right.map Prod.snd) r /
        bernoulliMass (front ++ left.map Prod.fst ++ right.map Prod.snd) (r + 1) - 1)
        <= epsilon) ->
    epsilon / (1 - epsilon) * (ps.map (fun p => abs (p.1 - p.2))).sum <= 1 ->
    (1 - epsilon / (1 - epsilon) * (ps.map (fun p => abs (p.1 - p.2))).sum) *
        bernoulliMass (front ++ ps.map Prod.snd) (r + 1) <=
      bernoulliMass (front ++ ps.map Prod.fst) (r + 1) /\
    (1 - epsilon / (1 - epsilon) * (ps.map (fun p => abs (p.1 - p.2))).sum) *
        bernoulliMass (front ++ ps.map Prod.fst) (r + 1) <=
      bernoulliMass (front ++ ps.map Prod.snd) (r + 1) := by
  induction ps generalizing front with
  | nil => intro hpref hpairs hcontrol hbudget; simp
  | cons p ps ih =>
    intro hpref hpairs hcontrol hbudget
    let delta := epsilon / (1 - epsilon)
    let d := delta * abs (p.1 - p.2)
    let D := delta * (ps.map (fun p => abs (p.1 - p.2))).sum
    have hd0 : 0 <= delta := div_nonneg he0 (sub_pos.mpr he1).le
    have hd : 0 <= d := mul_nonneg hd0 (abs_nonneg _)
    have hsum := replacementCost_nonneg ps
    have hD : 0 <= D := mul_nonneg hd0 hsum
    have htotal :
        epsilon / (1 - epsilon) *
          ((p :: ps).map (fun p => abs (p.1 - p.2))).sum = d + D := by
      simp only [map_cons, sum_cons]
      dsimp [delta, d, D]
      ring
    rw [htotal] at hbudget
    have hD1 : D <= 1 := by linarith only [hd, hbudget]
    have hp := hpairs p (List.Mem.head _)
    have ht : forall q, List.Mem q ps ->
        (0 <= q.1 /\ q.1 <= 1) /\ (0 <= q.2 /\ q.2 <= 1) :=
      fun q hq => hpairs q (List.Mem.tail _ hq)
    have hpref' : forall a, List.Mem a (front ++ [p.1]) -> 0 <= a /\ a <= 1 := by
      intro a ha
      cases List.mem_append.mp ha with
      | inl h => exact hpref a h
      | inr h =>
        have haeq := List.mem_singleton.mp h
        rw [haeq]
        exact hp.1
    have hcontrol' :
        forall (left right : List (Prod Real Real)) (a b : Real),
        ps = left ++ (a, b) :: right ->
        0 < bernoulliMass ((front ++ [p.1]) ++ left.map Prod.fst ++
            right.map Prod.snd) (r + 1) /\
        abs (bernoulliMass ((front ++ [p.1]) ++ left.map Prod.fst ++
            right.map Prod.snd) r /
          bernoulliMass ((front ++ [p.1]) ++ left.map Prod.fst ++
            right.map Prod.snd) (r + 1) - 1) <= epsilon := by
      intro left right a b heq
      have hwhole : p :: ps = (p :: left) ++ (a, b) :: right := by rw [heq]; rfl
      have hh := hcontrol (p :: left) right a b hwhole
      simpa only [map_cons, append_assoc, singleton_append] using hh
    have htail := ih (front ++ [p.1]) hpref' ht hcontrol' hD1
    simp only [append_assoc, singleton_append] at htail
    have hfirst := hcontrol [] ps p.1 p.2 (by rfl)
    simp only [map_nil, append_nil] at hfirst
    have hstep := bernoulliMass_cons_relative_change
      (front ++ ps.map Prod.snd) r p.1 p.2 epsilon
      hp.1.1 hp.1.2 hp.2.1 hp.2.2 he0 he1 hfirst.1 hfirst.2
    have hpa :
        bernoulliMass (front ++ p.1 :: ps.map Prod.snd) (r + 1) =
          bernoulliMass (p.1 :: (front ++ ps.map Prod.snd)) (r + 1) :=
      bernoulliMass_perm perm_middle (r + 1)
    have hpb :
        bernoulliMass (front ++ p.2 :: ps.map Prod.snd) (r + 1) =
          bernoulliMass (p.2 :: (front ++ ps.map Prod.snd)) (r + 1) :=
      bernoulliMass_perm perm_middle (r + 1)
    rw [<- hpa, <- hpb] at hstep
    have hlo :
        (1 - d) * bernoulliMass (front ++ p.2 :: ps.map Prod.snd) (r + 1) <=
          bernoulliMass (front ++ p.1 :: ps.map Prod.snd) (r + 1) := by
      have hh := (abs_le.mp hstep.2.2.2).1
      change -(d * bernoulliMass (front ++ p.2 :: ps.map Prod.snd) (r + 1)) <=
        bernoulliMass (front ++ p.1 :: ps.map Prod.snd) (r + 1) -
          bernoulliMass (front ++ p.2 :: ps.map Prod.snd) (r + 1) at hh
      linarith only [hh]
    have hhi :
        (1 - d) * bernoulliMass (front ++ p.1 :: ps.map Prod.snd) (r + 1) <=
          bernoulliMass (front ++ p.2 :: ps.map Prod.snd) (r + 1) := by
      have hh := (abs_le.mp hstep.2.2.1).2
      change bernoulliMass (front ++ p.1 :: ps.map Prod.snd) (r + 1) -
          bernoulliMass (front ++ p.2 :: ps.map Prod.snd) (r + 1) <=
        d * bernoulliMass (front ++ p.1 :: ps.map Prod.snd) (r + 1) at hh
      linarith only [hh]
    have hfinal0 : 0 <= bernoulliMass (front ++ p.1 :: ps.map Prod.fst) (r + 1) :=
      (mul_nonneg (sub_nonneg.mpr hD1) hstep.1.le).trans htail.1
    have hh := relative_budget_comp
      (bernoulliMass (front ++ p.2 :: ps.map Prod.snd) (r + 1))
      (bernoulliMass (front ++ p.1 :: ps.map Prod.snd) (r + 1))
      (bernoulliMass (front ++ p.1 :: ps.map Prod.fst) (r + 1))
      d D hstep.2.1.le hfinal0 hd hD hbudget hlo hhi htail.1 htail.2
    rw [htotal]
    simpa only [map_cons] using hh


private theorem relative_ratio_bound (x y d : Real) (hy : 0 < y)
    (_hd0 : 0 <= d) (hd1 : d < 1)
    (hlo : (1 - d) * y <= x) (hhi : (1 - d) * x <= y) :
    abs (x / y - 1) <= d / (1 - d) := by
  have hyne : Not (y = 0) := ne_of_gt hy
  have hm : 0 < 1 - d := sub_pos.mpr hd1
  have hmne : Not (1 - d = 0) := ne_of_gt hm
  have hqlo : 1 - d <= x / y := by
    have hh := mul_le_mul_of_nonneg_right hlo
      (div_nonneg (show (0 : Real) <= 1 by norm_num) hy.le)
    have hid : ((1 - d) * y) * (1 / y) = 1 - d := by field_simp
    simpa only [hid, mul_one_div] using hh
  have hqhi : x / y <= 1 / (1 - d) := by
    have hq : (1 - d) * (x / y) <= 1 := by
      rw [<- mul_div_assoc]
      exact (div_le_one hy).mpr hhi
    have hh := mul_le_mul_of_nonneg_right hq
      (div_nonneg (show (0 : Real) <= 1 by norm_num) hm.le)
    have hid : ((1 - d) * (x / y)) * (1 / (1 - d)) = x / y := by field_simp
    simpa only [hid, one_mul] using hh
  have hdiff : 1 / (1 - d) - 1 = d / (1 - d) := by field_simp; ring
  have hgain : d <= d / (1 - d) := by
    have hh : 0 <= d ^ 2 / (1 - d) := div_nonneg (sq_nonneg d) hm.le
    have hid : d / (1 - d) - d = d ^ 2 / (1 - d) := by field_simp; ring
    rw [<- hid] at hh
    exact sub_nonneg.mp hh
  apply abs_le.mpr
  constructor
  next => linarith only [hqlo, hgain]
  next =>
    have hh := sub_le_sub_right hqhi 1
    rwa [hdiff] at hh

/-- Quantitative relative comparison of the actual finite Bernoulli
coefficients. The denominator coefficient and both scalar denominators are
guarded explicitly; the bound depends on total probability change, not length. -/
theorem bernoulliMass_replacement_ratio_bound (front : List Real)
    (ps : List (Prod Real Real)) (r : Nat) (epsilon : Real)
    (he0 : 0 <= epsilon) (he1 : epsilon < 1)
    (hpref : forall a, List.Mem a front -> 0 <= a /\ a <= 1)
    (hpairs : forall p, List.Mem p ps ->
      (0 <= p.1 /\ p.1 <= 1) /\ (0 <= p.2 /\ p.2 <= 1))
    (hcontrol : forall (left right : List (Prod Real Real)) (a b : Real),
      ps = left ++ (a, b) :: right ->
      0 < bernoulliMass (front ++ left.map Prod.fst ++ right.map Prod.snd) (r + 1) /\
      abs (bernoulliMass (front ++ left.map Prod.fst ++ right.map Prod.snd) r /
        bernoulliMass (front ++ left.map Prod.fst ++ right.map Prod.snd) (r + 1) - 1)
        <= epsilon)
    (hpos : 0 < bernoulliMass (front ++ ps.map Prod.snd) (r + 1))
    (hbudget : epsilon / (1 - epsilon) * (ps.map (fun p => abs (p.1 - p.2))).sum < 1) :
    abs (bernoulliMass (front ++ ps.map Prod.fst) (r + 1) /
        bernoulliMass (front ++ ps.map Prod.snd) (r + 1) - 1) <=
      (epsilon / (1 - epsilon) * (ps.map (fun p => abs (p.1 - p.2))).sum) /
        (1 - epsilon / (1 - epsilon) * (ps.map (fun p => abs (p.1 - p.2))).sum) := by
  have hnonneg : 0 <= epsilon / (1 - epsilon) *
      (ps.map (fun p => abs (p.1 - p.2))).sum :=
    mul_nonneg (div_nonneg he0 (sub_pos.mpr he1).le) (replacementCost_nonneg ps)
  have hb := bernoulliMass_replacement_bound front ps r epsilon he0 he1
    hpref hpairs hcontrol hbudget.le
  exact relative_ratio_bound _ _ _ hpos hnonneg hbudget hb.1 hb.2

/-- Relative flatness of actual finite Bernoulli coefficients follows from
the total odds and the largest-weight deletion allowance. -/
theorem bernoulliMass_ratio_stability_largest (s : List Real)
    (hs : forall a, List.Mem a s -> 0 < a /\ a < 1)
    (r : Nat) (hr : 1 <= r) (epsilon : Real)
    (he0 : 0 <= epsilon) (he1 : epsilon < 1)
    (hrest : (1 - epsilon) * (r : Real) <=
      (s.map (fun a => a / (1 - a))).sum -
        largestWeightSum (s.map (fun a => a / (1 - a))) (r - 1))
    (htotal : (s.map (fun a => a / (1 - a))).sum <=
      (1 + epsilon) * (r : Real)) :
    r <= s.length /\ 0 < bernoulliMass s r /\
      abs (bernoulliMass s (r - 1) / bernoulliMass s r - 1) <=
        epsilon / (1 - epsilon) := by
  let w := s.map (fun a => a / (1 - a))
  let C := w.sum - largestWeightSum w (r - 1)
  let R := bernoulliMass s (r - 1) / bernoulliMass s r
  have hr0 : 0 < (r : Real) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hr)
  have hm : 0 < 1 - epsilon := sub_pos.mpr he1
  have hc : 0 < C := (mul_pos hm hr0).trans_le hrest
  have hB : 0 <= largestWeightSum w (r - 1) := by
    apply List.sum_nonneg
    intro a ha
    have ht := List.mem_of_mem_take ha
    have hw := (descendingWeightList_perm w).mem_iff.mp ht
    have hpre := Classical.choose_spec (List.mem_map.mp hw)
    rw [<- hpre.2]
    exact (div_pos (hs _ hpre.1).1 (sub_pos.mpr (hs _ hpre.1).2)).le
  have hS : 0 < w.sum := by
    dsimp [C] at hc
    linarith only [hc, hB]
  have hb := bernoulliMass_ratio_bounds_largest s hs r hr hc
  have hR : 0 <= R :=
    (div_pos hr0 hS).le.trans hb.2.2.1
  have hlo : 1 - epsilon <= R := by
    apply le_trans ?_ hb.2.2.1
    have hh := mul_le_mul_of_nonneg_left htotal hm.le
    have hsq := mul_nonneg (sq_nonneg epsilon) hr0.le
    have hc' : (1 - epsilon) * w.sum <= (r : Real) := by
      nlinarith only [hh, hsq]
    have hh' := mul_le_mul_of_nonneg_right hc'
      (div_nonneg (show (0 : Real) <= 1 by norm_num) hS.le)
    have hid : ((1 - epsilon) * w.sum) * (1 / w.sum) = 1 - epsilon := by
      field_simp
    simpa only [hid, mul_one_div] using hh'
  have hhi : (1 - epsilon) * R <= 1 := by
    have hup := mul_le_mul_of_nonneg_right hb.2.2.2 hc.le
    have hid : ((r : Real) / C) * C = (r : Real) := by field_simp
    rw [hid] at hup
    have hh := mul_le_mul_of_nonneg_right hrest hR
    have hprod : (r : Real) * ((1 - epsilon) * R) <= (r : Real) * 1 := by
      calc
        (r : Real) * ((1 - epsilon) * R) =
            ((1 - epsilon) * (r : Real)) * R := by ring
        _ <= C * R := hh
        _ <= (r : Real) * 1 := by nlinarith only [hup]
    by_contra hn
    have hbad := mul_lt_mul_of_pos_left (lt_of_not_ge hn) hr0
    exact (not_lt_of_ge hprod) hbad
  have hh := relative_ratio_bound R 1 epsilon (by norm_num) he0 he1
    (by simpa only [mul_one] using hlo) hhi
  exact And.intro hb.1 (And.intro hb.2.1 (by simpa only [div_one] using hh))

/-- Deterministic exceptional coordinates produce their exact rank shift in
the actual neighboring-coefficient stability estimate. -/
theorem bernoulliMass_forced_ratio_stability_largest (s : List Real)
    (hs : forall a, List.Mem a s -> 0 <= a /\ a <= 1)
    (r : Nat) (hr : 1 <= r) (epsilon : Real)
    (he0 : 0 <= epsilon) (he1 : epsilon < 1)
    (hrest : (1 - epsilon) * (r : Real) <=
      ((bernoulliInterior s).map (fun a => a / (1 - a))).sum -
        largestWeightSum ((bernoulliInterior s).map (fun a => a / (1 - a))) (r - 1))
    (htotal : ((bernoulliInterior s).map (fun a => a / (1 - a))).sum <=
      (1 + epsilon) * (r : Real)) :
    r <= (bernoulliInterior s).length /\
      0 < bernoulliMass s (s.count 1 + r) /\
      abs (bernoulliMass s (s.count 1 + r - 1) /
        bernoulliMass s (s.count 1 + r) - 1) <= epsilon / (1 - epsilon) := by
  have hb := bernoulliMass_ratio_stability_largest (bernoulliInterior s)
    (bernoulliInterior_mem s) r hr epsilon he0 he1 hrest htotal
  refine And.intro hb.1 (And.intro ?_ ?_)
  next =>
    rw [bernoulliMass_interior_count_one_add s hs r]
    exact hb.2.1
  next =>
    rw [bernoulliMass_ratio_interior s hs r hr]
    exact hb.2.2

end List
