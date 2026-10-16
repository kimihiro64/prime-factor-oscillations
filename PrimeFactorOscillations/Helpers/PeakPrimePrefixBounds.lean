/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliPrefixBounds
import PrimeFactorUnimodality.Helpers.Analytic.MertensProvider

/-! # Uniform prime-prefix odds bounds

The proved unconditional Mertens provider and the finite retained-support error
bound give a total-odds estimate uniform in the upper prime cutoff. All small
primes are isolated by the exact difference of two finite prime prefixes.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

/-- A single explicit constant controls the unconditional Mertens error for
all cutoffs. This consumes the proved dependency estimate directly. -/
theorem reciprocalPrimeSumBelow_uniform_error (n : Nat) (hn : 2 <= n) :
    abs (PrimeFactorUnimodality.reciprocalPrimeSumBelow (n + 1) -
      Real.log (Real.log (n : Real))) <=
        abs Mertens.M + abs PrimeFactorUnimodality.mertensErrorConstant /
          Real.log 2 := by
  have h2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hln : Real.log (2 : Real) <= Real.log (n : Real) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hnpos : 0 < Real.log (n : Real) := h2.trans_le hln
  have hi := one_div_le_one_div_of_le h2 hln
  have hcap : PrimeFactorUnimodality.mertensErrorConstant / Real.log (n : Real) <=
      abs PrimeFactorUnimodality.mertensErrorConstant / Real.log 2 := by
    calc
      _ <= abs PrimeFactorUnimodality.mertensErrorConstant / Real.log (n : Real) :=
        div_le_div_of_nonneg_right (le_abs_self _) hnpos.le
      _ <= _ := by
        have hh := mul_le_mul_of_nonneg_left hi
          (abs_nonneg PrimeFactorUnimodality.mertensErrorConstant)
        simpa only [mul_one_div] using hh
  have he := PrimeFactorUnimodality.hasMertensReciprocalPrimeEstimate n hn
  have hm := abs_le.mp (le_refl (abs Mertens.M))
  have hl := (abs_le.mp he).1
  have hu := (abs_le.mp he).2
  apply abs_le.mpr
  constructor <;> linarith only [hl, hu, hm.1, hm.2, hcap]

/-- The complete tail-prefix odds error is uniform in the upper cutoff.
The finite support is exactly the two prime prefixes' set difference. -/
theorem tailPrimeOdds_uniform_logLog_error (n P : Nat)
    (hn : 2 <= n) (hP : 1 <= P) (hPn : P <= n)
    (a : Nat -> Real) (nu K : Real) (hnu : 0 <= nu) (hK : 0 <= K)
    (herror : forall p, Nat.Prime p -> P < p -> p <= n ->
      abs (a p - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    abs ((((n + 1).primesBelow \ (P + 1).primesBelow).sum a) -
      nu * Real.log (Real.log (n : Real))) <=
        2 * K / (P : Real) + nu *
          (abs (PrimeFactorUnimodality.reciprocalPrimeSumBelow (P + 1)) +
            (abs Mertens.M + abs PrimeFactorUnimodality.mertensErrorConstant /
              Real.log 2)) := by
  let S := (n + 1).primesBelow \ (P + 1).primesBelow
  let H := PrimeFactorUnimodality.reciprocalPrimeSumBelow
  let L := Real.log (Real.log (n : Real))
  let A := abs Mertens.M + abs PrimeFactorUnimodality.mertensErrorConstant / Real.log 2
  have hinside (p : Nat) (hp : Membership.mem S p) :
      Nat.Prime p /\ P < p /\ p <= n := by
    have hlarge := Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1
    have hnot := (Finset.mem_sdiff.mp hp).2
    have hPnot : Not (p < P + 1) := by
      intro h
      exact hnot (Nat.mem_primesBelow.mpr (And.intro h hlarge.2))
    exact And.intro hlarge.2 (And.intro (by omega) (by omega))
  have hs : forall p, Membership.mem S p -> P < p := fun p hp => (hinside p hp).2.1
  have he : abs (S.sum a - nu * S.sum (fun p => 1 / (p : Real))) <=
      2 * K / (P : Real) := by
    apply Finset.abs_sum_sub_reciprocal_reference_le S P hP hs a nu K hK
    intro p hp
    exact herror p (hinside p hp).1 (hinside p hp).2.1 (hinside p hp).2.2
  have hsub : forall p, Membership.mem (P + 1).primesBelow p ->
      Membership.mem (n + 1).primesBelow p := by
    intro p hp
    have hh := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr (And.intro (by omega) hh.2)
  have hsplit : S.sum (fun p => 1 / (p : Real)) + H (P + 1) = H (n + 1) := by
    exact Finset.sum_sdiff hsub
  have hm : abs (H (n + 1) - L) <= A := reciprocalPrimeSumBelow_uniform_error n hn
  have hid : S.sum a - nu * L =
      (S.sum a - nu * S.sum (fun p => 1 / (p : Real))) +
        nu * (H (n + 1) - L) + (-(nu * H (P + 1))) := by
    rw [<- hsplit]
    ring
  change abs (S.sum a - nu * L) <= 2 * K / (P : Real) + nu * (abs (H (P + 1)) + A)
  rw [hid]
  calc
    _ <= abs ((S.sum a - nu * S.sum (fun p => 1 / (p : Real))) +
        nu * (H (n + 1) - L)) + abs (-(nu * H (P + 1))) := abs_add_le _ _
    _ <= (abs (S.sum a - nu * S.sum (fun p => 1 / (p : Real))) +
        abs (nu * (H (n + 1) - L))) + abs (-(nu * H (P + 1))) :=
      add_le_add (abs_add_le _ _) (le_refl _)
    _ = abs (S.sum a - nu * S.sum (fun p => 1 / (p : Real))) +
        nu * abs (H (n + 1) - L) + nu * abs (H (P + 1)) := by
      simp only [abs_neg, abs_mul, abs_of_nonneg hnu]
    _ <= 2 * K / (P : Real) + nu * A + nu * abs (H (P + 1)) :=
      add_le_add (add_le_add he (mul_le_mul_of_nonneg_left hm hnu)) (le_refl _)
    _ = _ := by ring

/-- The actual regular prime odds have a largest-weight allowance controlled
by a shorter prime prefix, uniformly in the full upper cutoff. -/
theorem largestPrimeOdds_le_lowPrefix (n P H r : Nat)
    (_hn : 2 <= n) (hP : 1 <= P) (hH : 2 <= H)
    (hPH : P <= H) (hHn : H <= n)
    (a : Nat -> Real) (nu K : Real) (hnu : 0 <= nu) (hK : 0 <= K)
    (hpos : forall p, Nat.Prime p -> P < p -> p <= n -> 0 <= a p)
    (hupper : forall p, Nat.Prime p -> P < p -> p <= n ->
      a p <= 2 * nu / (p : Real))
    (herror : forall p, Nat.Prime p -> P < p -> p <= n ->
      abs (a p - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    List.largestWeightSum
      (((n + 1).primesBelow \ (P + 1).primesBelow).toList.map a) r <=
        (r : Real) * (2 * nu / (H : Real)) +
          nu * Real.log (Real.log (H : Real)) +
            (2 * K / (P : Real) + nu *
              (abs (PrimeFactorUnimodality.reciprocalPrimeSumBelow (P + 1)) +
                (abs Mertens.M + abs PrimeFactorUnimodality.mertensErrorConstant /
                  Real.log 2))) := by
  let S := (n + 1).primesBelow \ (P + 1).primesBelow
  have hinside (p : Nat) (hp : Membership.mem S p) :
      Nat.Prime p /\ P < p /\ p <= n := by
    have hl := Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1
    have hpnot := (Finset.mem_sdiff.mp hp).2
    have hcut : Not (p < P + 1) := by
      intro h
      exact hpnot (Nat.mem_primesBelow.mpr (And.intro h hl.2))
    exact And.intro hl.2 (And.intro (by omega) (by omega))
  have hHR : 0 < (H : Real) := by exact_mod_cast (show 0 < H by omega)
  have hnon : forall p, Membership.mem S p -> 0 <= a p := by
    intro p hp
    exact hpos p (hinside p hp).1 (hinside p hp).2.1 (hinside p hp).2.2
  have hhi : forall p, Membership.mem S p -> Not (p <= H) ->
      a p <= 2 * nu / (H : Real) := by
    intro p hp hh
    have hHp : (H : Real) <= (p : Real) := by exact_mod_cast (show H <= p by omega)
    exact (hupper p (hinside p hp).1 (hinside p hp).2.1 (hinside p hp).2.2).trans
      (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hnu) hHR hHp)
  have hc := List.largestWeightSum_le_filtered_prefix S a (fun p => p <= H)
    (2 * nu / (H : Real))
    (div_nonneg (mul_nonneg (by norm_num) hnu) hHR.le) hnon hhi r
  have hfilter : S.filter (fun p => p <= H) =
      (H + 1).primesBelow \ (P + 1).primesBelow := by
    apply Finset.ext
    intro p
    constructor
    next =>
      intro hp
      have hh := Finset.mem_filter.mp hp
      have hl := Finset.mem_sdiff.mp hh.1
      have hprime := (Nat.mem_primesBelow.mp hl.1).2
      exact Finset.mem_sdiff.mpr (And.intro
        (Nat.mem_primesBelow.mpr (And.intro (by omega) hprime)) hl.2)
    next =>
      intro hp
      have hh := Finset.mem_sdiff.mp hp
      have hl := Nat.mem_primesBelow.mp hh.1
      exact Finset.mem_filter.mpr (And.intro
        (Finset.mem_sdiff.mpr (And.intro
          (Nat.mem_primesBelow.mpr (And.intro (by omega) hl.2)) hh.2)) (by omega))
  rw [hfilter] at hc
  have he := tailPrimeOdds_uniform_logLog_error H P hH hP hPH a nu K hnu hK
    (fun p hp hpc hph => herror p hp hpc (hph.trans hHn))
  change List.largestWeightSum (S.toList.map a) r <= _
  linarith only [hc, (abs_le.mp he).2]


/-- A complete finite coefficient criterion for mixed regular prime odds,
retained tail coordinates and a finite exceptional interior prefix. The last
clause restores all excluded and forced coordinates at their exact rank. -/
theorem mixedPrimePrefix_tilted_adjacent_flatness
    (n P H r : Nat) (hn : 2 <= n) (hP : 1 <= P) (hH : 2 <= H)
    (hPH : P <= H) (hHn : H <= n) (hr : 1 <= r)
    (S : Finset Nat)
    (hS : forall p, Membership.mem S p ->
      Membership.mem ((n + 1).primesBelow \ (P + 1).primesBelow) p)
    (a : Nat -> Real) (front : List Real) (nu K E z delta D F J : Real)
    (hnu : 0 <= nu) (hK : 0 <= K) (hz : 0 < z)
    (hd0 : 0 <= delta) (hd1 : delta < 1)
    (hpos : forall p, Nat.Prime p -> P < p -> p <= n -> 0 < a p)
    (hupper : forall p, Nat.Prime p -> P < p -> p <= n ->
      a p <= 2 * nu / (p : Real))
    (herror : forall p, Nat.Prime p -> P < p -> p <= n ->
      abs (a p - nu / (p : Real)) <= K / (p : Real) ^ 2)
    (hE : 2 * K / (P : Real) + nu *
      (abs (PrimeFactorUnimodality.reciprocalPrimeSumBelow (P + 1)) +
        (abs Mertens.M + abs PrimeFactorUnimodality.mertensErrorConstant /
          Real.log 2)) <= E)
    (hfront : forall b, List.Mem b front -> 0 < b /\ b < 1)
    (hfrontbudget : (front.map (fun b => b / (1 - b))).sum <= z * F)
    (hmissing : (((n + 1).primesBelow \ (P + 1).primesBelow) \ S).sum a <= D)
    (hcenter : abs (z * (nu * Real.log (Real.log (n : Real))) - (r : Real)) <= J)
    (hbudget : J + z * (2 * E + D + F +
      2 * nu * ((r - 1 : Nat) : Real) / (H : Real) +
        nu * Real.log (Real.log (H : Real))) <= delta * (r : Real))
    (hupperbudget : J + z * (E + F) <= delta * (r : Real)) :
    let s := front ++ S.toList.map (fun p => z * a p / (1 + z * a p))
    r <= front.length + S.card /\ 0 < List.bernoulliMass s r /\
      abs (List.bernoulliMass s (r - 1) / List.bernoulliMass s r - 1) <=
        delta / (1 - delta) /\
      forall original : List Real,
        (forall b, List.Mem b original -> 0 <= b /\ b <= 1) ->
        List.bernoulliInterior original = s ->
          0 < List.bernoulliMass original (original.count 1 + r) /\
            abs (List.bernoulliMass original (original.count 1 + r - 1) /
              List.bernoulliMass original (original.count 1 + r) - 1) <=
                delta / (1 - delta) := by
  let A := (n + 1).primesBelow \ (P + 1).primesBelow
  let B := (H + 1).primesBelow \ (P + 1).primesBelow
  let tail := S.toList.map (fun p => z * a p / (1 + z * a p))
  let s := front ++ tail
  let f := front.map (fun b => b / (1 - b))
  have hinside (p : Nat) (hp : Membership.mem A p) :
      Nat.Prime p /\ P < p /\ p <= n := by
    have hl := Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1
    have hpnot := (Finset.mem_sdiff.mp hp).2
    have hcut : Not (p < P + 1) := by
      intro hh
      exact hpnot (Nat.mem_primesBelow.mpr (And.intro hh hl.2))
    exact And.intro hl.2 (And.intro (by omega) (by omega))
  have ha (p : Nat) (hp : Membership.mem A p) : 0 < a p :=
    hpos p (hinside p hp).1 (hinside p hp).2.1 (hinside p hp).2.2
  have hBA : forall p, Membership.mem B p -> Membership.mem A p := by
    intro p hp
    have hh := Finset.mem_sdiff.mp hp
    have hl := Nat.mem_primesBelow.mp hh.1
    exact Finset.mem_sdiff.mpr (And.intro
      (Nat.mem_primesBelow.mpr (And.intro (by omega) hl.2)) hh.2)
  have hfpos : forall b, List.Mem b f -> 0 <= b := by
    intro b hb
    have hx := List.mem_map.mp hb
    choose x hx using hx
    rw [<- hx.2]
    exact div_nonneg (hfront x hx.1).1.le (sub_pos.mpr (hfront x hx.1).2).le
  have hfsum : 0 <= f.sum := List.sum_nonneg hfpos
  have htail : forall b, List.Mem b tail -> 0 < b /\ b < 1 := by
    intro b hb
    have hp := List.mem_map.mp hb
    choose p hp using hp
    have hin : Membership.mem S p := Finset.mem_toList.mp hp.1
    rw [<- hp.2]
    exact Real.oddsProbability_mem_open (z * a p) (mul_pos hz (ha p (hS p hin)))
  have hsprob : forall b, List.Mem b s -> 0 < b /\ b < 1 := by
    intro b hb
    cases List.mem_append.mp hb with
    | inl hf => exact hfront b hf
    | inr ht => exact htail b ht
  have htmap : tail.map (fun b => b / (1 - b)) =
      S.toList.map (fun p => z * a p) := by
    simp only [tail, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p hp
    exact Real.oddsProbability_odds (z * a p)
      (mul_pos hz (ha p (hS p (Finset.mem_toList.mp hp)))).le
  have hmap : s.map (fun b => b / (1 - b)) =
      f ++ S.toList.map (fun p => z * a p) := by
    simp only [s, List.map_append, htmap, f]
  have hsum : (s.map (fun b => b / (1 - b))).sum = f.sum + z * S.sum a := by
    rw [hmap, List.sum_append]
    simp [Finset.mul_sum]
  have he : abs (A.sum a - nu * Real.log (Real.log (n : Real))) <= E :=
    (tailPrimeOdds_uniform_logLog_error n P hn hP (hPH.trans hHn)
      a nu K hnu hK herror).trans hE
  have heH : abs (B.sum a - nu * Real.log (Real.log (H : Real))) <= E :=
    (tailPrimeOdds_uniform_logLog_error H P hH hP hPH a nu K hnu hK
      (fun p hp hpc hph => herror p hp hpc (hph.trans hHn))).trans hE
  have hsplit : (A \ S).sum a + S.sum a = A.sum a := Finset.sum_sdiff hS
  have hmisspos : 0 <= (A \ S).sum a := by
    apply Finset.sum_nonneg
    intro p hp
    exact (ha p (Finset.mem_sdiff.mp hp).1).le
  have hSlo : nu * Real.log (Real.log (n : Real)) - E - D <= S.sum a := by
    linarith only [(abs_le.mp he).1, hmissing, hsplit]
  have hSup : S.sum a <= nu * Real.log (Real.log (n : Real)) + E := by
    linarith only [(abs_le.mp he).2, hmisspos, hsplit]
  have hlo : (r : Real) - J - z * (E + D) <=
      (s.map (fun b => b / (1 - b))).sum := by
    rw [hsum]
    have hh := mul_le_mul_of_nonneg_left hSlo hz.le
    have hc := (abs_le.mp hcenter).1
    linarith only [hh, hc, hfsum]
  have hup : (s.map (fun b => b / (1 - b))).sum <=
      (r : Real) + J + z * (E + F) := by
    rw [hsum]
    have hh := mul_le_mul_of_nonneg_left hSup hz.le
    have hc := (abs_le.mp hcenter).2
    linarith only [hh, hc, hfrontbudget]
  have hHR : 0 < (H : Real) := by exact_mod_cast (show 0 < H by omega)
  have ht0 : 0 <= 2 * nu * z / (H : Real) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hnu) hz.le) hHR.le
  have hhigh : forall p, Membership.mem S p -> Not (p <= H) ->
      z * a p <= 2 * nu * z / (H : Real) := by
    intro p hp hh
    have hin := hinside p (hS p hp)
    have hHp : (H : Real) <= (p : Real) := by exact_mod_cast (show H <= p by omega)
    have hu := (hupper p hin.1 hin.2.1 hin.2.2).trans
      (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hnu) hHR hHp)
    calc
      _ <= z * (2 * nu / (H : Real)) := mul_le_mul_of_nonneg_left hu hz.le
      _ = _ := by ring
  have hb0 := List.largestWeightSum_append_filtered_prefix f S (fun p => z * a p)
    (fun p => p <= H) (2 * nu * z / (H : Real)) ht0 hfpos
    (fun p hp => (mul_pos hz (ha p (hS p hp))).le) hhigh (r - 1)
  have hlowB : forall p, Membership.mem (S.filter (fun p => p <= H)) p ->
      Membership.mem B p := by
    intro p hp
    have hh := Finset.mem_filter.mp hp
    have hin := Finset.mem_sdiff.mp (hS p hh.1)
    have hprime := (Nat.mem_primesBelow.mp hin.1).2
    exact Finset.mem_sdiff.mpr (And.intro
      (Nat.mem_primesBelow.mpr (And.intro (by omega) hprime)) hin.2)
  have hlowsum : (S.filter (fun p => p <= H)).sum (fun p => z * a p) <=
      z * (nu * Real.log (Real.log (H : Real)) + E) := by
    calc
      _ <= B.sum (fun p => z * a p) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hlowB
        intro p hp hnot
        exact (mul_pos hz (ha p (hBA p hp))).le
      _ = z * B.sum a := by rw [Finset.mul_sum]
      _ <= _ := mul_le_mul_of_nonneg_left (by linarith only [(abs_le.mp heH).2]) hz.le
  have hb : List.largestWeightSum (s.map (fun b => b / (1 - b))) (r - 1) <=
      z * (2 * nu * ((r - 1 : Nat) : Real) / (H : Real) + F +
        nu * Real.log (Real.log (H : Real)) + E) := by
    rw [hmap]
    have hfb : f.sum <= z * F := hfrontbudget
    calc
      _ <= ((r - 1 : Nat) : Real) * (2 * nu * z / (H : Real)) +
          f.sum + (S.filter (fun p => p <= H)).sum (fun p => z * a p) := hb0
      _ <= ((r - 1 : Nat) : Real) * (2 * nu * z / (H : Real)) +
          z * F + z * (nu * Real.log (Real.log (H : Real)) + E) :=
        _root_.add_le_add (_root_.add_le_add (le_refl _) hfb) hlowsum
      _ = _ := by ring
  have hrest : (1 - delta) * (r : Real) <=
      (s.map (fun b => b / (1 - b))).sum -
        List.largestWeightSum (s.map (fun b => b / (1 - b))) (r - 1) := by
    linarith only [hlo, hb, hbudget]
  have htotal : (s.map (fun b => b / (1 - b))).sum <=
      (1 + delta) * (r : Real) := by
    linarith only [hup, hupperbudget]
  have hc := List.bernoulliMass_ratio_stability_largest s hsprob r hr delta hd0 hd1
    hrest htotal
  refine And.intro (by simpa [s, tail] using hc.1)
    (And.intro hc.2.1 (And.intro hc.2.2 ?_))
  intro original horiginal hrepr
  constructor
  next =>
    rw [List.bernoulliMass_interior_count_one_add original horiginal r, hrepr]
    exact hc.2.1
  next =>
    rw [List.bernoulliMass_ratio_interior original horiginal r hr, hrepr]
    exact hc.2.2


end PrimeFactorOscillations
