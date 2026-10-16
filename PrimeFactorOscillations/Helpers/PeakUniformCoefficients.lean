/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PeakPrimePrefixBounds
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliArrayComparison
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliAsymptotics

/-! # Uniform neighboring coefficients for regular prime laws

A single rank threshold controls every retained tail subset and every mixed
regular odds array on the logarithmic band. Finite exceptional coordinates,
missing tail coordinates and bounded rank displacements retain explicit budgets.
The exact transport includes all zero and forced probability coordinates.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter

namespace PrimeFactorOscillations

/-- Uniform adjacent coefficient flatness for the actual tilted array.
The denominator is positive, and all deterministic ranks are restored exactly. -/
theorem mixedPrimePrefix_uniform_adjacent_flatness
    (P : Nat) (nu alpha K E D F J : Real) (hP : 1 <= P)
    (hnu : 0 < nu) (halpha : 0 < alpha) (hK : 0 <= K)
    (hE : 2 * K / (P : Real) + nu *
      (abs (PrimeFactorUnimodality.reciprocalPrimeSumBelow (P + 1)) +
        (abs Mertens.M + abs PrimeFactorUnimodality.mertensErrorConstant /
          Real.log 2)) <= E)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    Filter.Eventually (fun k : Nat => forall (n r : Nat),
      k ^ 2 <= n -> alpha * Real.log (k : Real) <= Real.log (Real.log (n : Real)) ->
      abs ((k : Real) - (r : Real)) <= J ->
      let z := (k : Real) / (nu * Real.log (Real.log (n : Real)))
      forall (S : Finset Nat) (a : Nat -> Real) (front : List Real),
        (forall p, Membership.mem S p ->
          Membership.mem ((n + 1).primesBelow \ (P + 1).primesBelow) p) ->
        (forall p, Nat.Prime p -> P < p -> p <= n -> 0 < a p) ->
        (forall p, Nat.Prime p -> P < p -> p <= n ->
          a p <= 2 * nu / (p : Real)) ->
        (forall p, Nat.Prime p -> P < p -> p <= n ->
          abs (a p - nu / (p : Real)) <= K / (p : Real) ^ 2) ->
        (forall b, List.Mem b front -> 0 < b /\ b < 1) ->
        (front.map (fun b => b / (1 - b))).sum <= z * F ->
        (((n + 1).primesBelow \ (P + 1).primesBelow) \ S).sum a <= D ->
        let s := front ++ S.toList.map (fun p => z * a p / (1 + z * a p))
        r <= front.length + S.card /\ 0 < List.bernoulliMass s r /\
          abs (List.bernoulliMass s (r - 1) / List.bernoulliMass s r - 1) <= epsilon /\
          forall original : List Real,
            (forall b, List.Mem b original -> 0 <= b /\ b <= 1) ->
            List.bernoulliInterior original = s ->
              0 < List.bernoulliMass original (original.count 1 + r) /\
                abs (List.bernoulliMass original (original.count 1 + r - 1) /
                  List.bernoulliMass original (original.count 1 + r) - 1) <= epsilon)
        Filter.atTop := by
  let delta := min (epsilon / 4) (1 / 4)
  have hd : 0 < delta := lt_min (div_pos hepsilon (by norm_num)) (by norm_num)
  have hdquarter : delta <= 1 / 4 := min_le_right _ _
  have hd1 : delta < 1 := by linarith only [hdquarter]
  have hdepsilon : 2 * delta <= epsilon := by
    have hh := min_le_left (epsilon / 4) (1 / 4)
    change delta <= epsilon / 4 at hh
    linarith only [hh, hepsilon]
  have hfrac : delta / (1 - delta) <= epsilon := by
    have hden : (1 / 2 : Real) <= 1 - delta := by linarith only [hdquarter]
    calc
      _ <= delta / (1 / 2) :=
        div_le_div_of_nonneg_left hd.le (by norm_num) hden
      _ = 2 * delta := by ring
      _ <= _ := hdepsilon
  have hbud := Real.eventually_primeTilt_error_budgets P nu alpha E D F J delta
    hnu halpha hd
  filter_upwards [hbud] with k hk
  intro n r hkn hband hshift
  dsimp only
  intro S a front hS hpos hupper herror hfront hfrontbudget hmissing
  let L := Real.log (Real.log (n : Real))
  let z := (k : Real) / (nu * L)
  have hk2 : 2 <= k := hk.1
  have hkp : k <= k ^ 2 := by nlinarith
  have hH2 : 2 <= k ^ 2 := hk2.trans hkp
  have hn : 2 <= n := hH2.trans hkn
  have hkpos : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
  have hlog : 0 < Real.log (k : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hL : 0 < L := (mul_pos halpha hlog).trans_le hband
  have hnL : 0 < nu * L := mul_pos hnu hL
  have hz : 0 < z := div_pos hkpos hnL
  have hcenter : z * (nu * L) = (k : Real) := by
    dsimp [z]
    field_simp [ne_of_gt hnL]
  have hb := hk.2.2 r L z hband hz.le hcenter hshift
  have hshifted : abs (z * (nu * Real.log (Real.log (n : Real))) -
      (r : Real)) <= J := by
    change abs (z * (nu * L) - (r : Real)) <= J
    rw [hcenter]
    exact hshift
  have hc := mixedPrimePrefix_tilted_adjacent_flatness n P (k ^ 2) r hn hP hH2
    hk.2.1 hkn hb.1 S hS a front nu K E z delta D F J
    hnu.le hK hz hd.le hd1 hpos hupper herror hE hfront
    hfrontbudget hmissing hshifted hb.2.1 hb.2.2
  refine And.intro hc.1 (And.intro hc.2.1 (And.intro (hc.2.2.1.trans hfrac) ?_))
  intro original horiginal hrepr
  have ho := hc.2.2.2 original horiginal hrepr
  exact And.intro ho.1 (ho.2.trans hfrac)


/-- Uniform neighboring coefficient convergence for every actual pointwise
mixture of two regular prime laws, with at most one coordinate removed.
All exceptional coordinates and exact forced ranks are handled internally. -/
theorem regularPrimeArrays_uniform_adjacent_flatness
    (P : Nat) (nu alpha K : Real) (hP : 1 <= P)
    (hnu : 0 < nu) (halpha : 0 < alpha) (hK : 0 <= K)
    (eta1 eta2 : Nat -> Real)
    (hunit1 : forall p, Nat.Prime p -> 0 <= eta1 p /\ eta1 p <= 1)
    (hunit2 : forall p, Nat.Prime p -> 0 <= eta2 p /\ eta2 p <= 1)
    (hinterior1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p /\ eta1 p < 1)
    (hinterior2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p /\ eta2 p < 1)
    (hupper1 : forall p, Nat.Prime p -> P < p ->
      eta1 p / (1 - eta1 p) <= 2 * nu / (p : Real))
    (hupper2 : forall p, Nat.Prime p -> P < p ->
      eta2 p / (1 - eta2 p) <= 2 * nu / (p : Real))
    (herror1 : forall p, Nat.Prime p -> P < p ->
      abs (eta1 p / (1 - eta1 p) - nu / (p : Real)) <= K / (p : Real) ^ 2)
    (herror2 : forall p, Nat.Prime p -> P < p ->
      abs (eta2 p / (1 - eta2 p) - nu / (p : Real)) <= K / (p : Real) ^ 2)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    Filter.Eventually (fun k : Nat => forall (n : Nat) (E : Finset Nat) (eta : Nat -> Real),
      k ^ 2 <= n -> alpha * Real.log (k : Real) <= Real.log (Real.log (n : Real)) ->
      (forall p, Membership.mem E p -> Membership.mem (n + 1).primesBelow p) ->
      ((n + 1).primesBelow \ E).card <= 1 ->
      (forall p, Nat.Prime p -> eta p = eta1 p \/ eta p = eta2 p) ->
      let z := (k : Real) / (nu * Real.log (Real.log (n : Real)))
      let probs := E.toList.map (fun p => eta p * z / (1 - eta p + eta p * z))
      0 < List.bernoulliMass probs k /\
        abs (List.bernoulliMass probs (k - 1) / List.bernoulliMass probs k - 1) <= epsilon)
      Filter.atTop := by
  let B := (P + 1).primesBelow
  let F := B.sum (fun p => eta1 p / (1 - eta1 p) + eta2 p / (1 - eta2 p))
  let J := (B.card : Real)
  let C := 2 * K / (P : Real) + nu *
    (abs (PrimeFactorUnimodality.reciprocalPrimeSumBelow (P + 1)) +
      (abs Mertens.M + abs PrimeFactorUnimodality.mertensErrorConstant / Real.log 2))
  have hflat := mixedPrimePrefix_uniform_adjacent_flatness P nu alpha K C (2 * nu) F J
    hP hnu halpha hK (le_refl _) epsilon hepsilon
  filter_upwards [hflat, Filter.eventually_ge_atTop (max (P + 2) (B.card + 2))]
    with k hk hklarge
  intro n E eta hkn hband hE hmissing hchoice
  let A := (n + 1).primesBelow
  let T := A \ B
  let small := E.filter (fun p => Membership.mem B p)
  let S := E \ B
  let a := fun p => eta p / (1 - eta p)
  let z := (k : Real) / (nu * Real.log (Real.log (n : Real)))
  let tilt := fun p => eta p * z / (1 - eta p + eta p * z)
  let frontRaw := small.toList.map tilt
  let tail := S.toList.map (fun p => z * a p / (1 + z * a p))
  let original := frontRaw ++ tail
  let front := List.bernoulliInterior frontRaw
  let c := frontRaw.count 1
  let r := k - c
  have hk2 : 2 <= k := by have hh := (le_max_left _ _).trans hklarge; omega
  have hkP : P <= k := by have hh := (le_max_left _ _).trans hklarge; omega
  have hkB : B.card + 2 <= k := (le_max_right _ _).trans hklarge
  have hkp : k <= k ^ 2 := by nlinarith
  have hPn : P <= n := hkP.trans (hkp.trans hkn)
  have hkpos : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
  have hlog : 0 < Real.log (k : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hLpos : 0 < Real.log (Real.log (n : Real)) :=
    (mul_pos halpha hlog).trans_le hband
  have hz : 0 < z := div_pos hkpos (mul_pos hnu hLpos)
  have hunit (p : Nat) (hp : Nat.Prime p) : 0 <= eta p /\ eta p <= 1 := by
    cases hchoice p hp with
    | inl hh => rw [hh]; exact hunit1 p hp
    | inr hh => rw [hh]; exact hunit2 p hp
  have hinterior (p : Nat) (hp : Nat.Prime p) (hpc : P < p) :
      0 < eta p /\ eta p < 1 := by
    cases hchoice p hp with
    | inl hh => rw [hh]; exact hinterior1 p hp hpc
    | inr hh => rw [hh]; exact hinterior2 p hp hpc
  have hu (p : Nat) (hp : Nat.Prime p) (hpc : P < p) :
      a p <= 2 * nu / (p : Real) := by
    cases hchoice p hp with
    | inl hh => change eta p / (1 - eta p) <= _; rw [hh]; exact hupper1 p hp hpc
    | inr hh => change eta p / (1 - eta p) <= _; rw [hh]; exact hupper2 p hp hpc
  have herr (p : Nat) (hp : Nat.Prime p) (hpc : P < p) :
      abs (a p - nu / (p : Real)) <= K / (p : Real) ^ 2 := by
    cases hchoice p hp with
    | inl hh => change abs (eta p / (1 - eta p) - _) <= _; rw [hh]; exact herror1 p hp hpc
    | inr hh => change abs (eta p / (1 - eta p) - _) <= _; rw [hh]; exact herror2 p hp hpc
  have hT (p : Nat) (hp : Membership.mem T p) :
      Nat.Prime p /\ P < p /\ p <= n := by
    have hh := Finset.mem_sdiff.mp hp
    have hl := Nat.mem_primesBelow.mp hh.1
    have hcut : Not (p < P + 1) := by
      intro hhP
      exact hh.2 (Nat.mem_primesBelow.mpr (And.intro hhP hl.2))
    exact And.intro hl.2 (And.intro (by omega) (by omega))
  have hST : forall p, Membership.mem S p -> Membership.mem T p := by
    intro p hp
    have hh := Finset.mem_sdiff.mp hp
    exact Finset.mem_sdiff.mpr (And.intro (hE p hh.1) hh.2)
  have ha (p : Nat) (hp : Membership.mem T p) : 0 < a p :=
    div_pos (hinterior p (hT p hp).1 (hT p hp).2.1).1
      (sub_pos.mpr (hinterior p (hT p hp).1 (hT p hp).2.1).2)
  have htilt (p : Nat) (hp : Membership.mem S p) :
      tilt p = z * a p / (1 + z * a p) := by
    have hh := hT p (hST p hp)
    have hi := hinterior p hh.1 hh.2.1
    have hid : 1 + (z - 1) * eta p = 1 - eta p + eta p * z := by ring
    have he := Real.localLaw_tilt_eq_odds_tilt (eta p) z hi.1 hi.2 hz
    rw [hid] at he
    exact he
  have htailmap : S.toList.map tilt = tail := by
    apply List.map_congr_left
    intro p hp
    exact htilt p (Finset.mem_toList.mp hp)
  have htail : forall b, List.Mem b tail -> 0 < b /\ b < 1 := by
    intro b hb
    have hp := List.mem_map.mp hb
    choose p hp using hp
    rw [<- hp.2]
    exact Real.oddsProbability_mem_open (z * a p)
      (mul_pos hz (ha p (hST p (Finset.mem_toList.mp hp.1))))
  have hperm : (E.toList.map tilt).Perm original := by
    have hp := (Finset.toList_perm_filter_sdiff E B).map tilt
    simp only [List.map_append] at hp
    change (E.toList.map tilt).Perm (frontRaw ++ S.toList.map tilt) at hp
    rw [htailmap] at hp
    exact hp
  have hsmallB : forall p, Membership.mem small p -> Membership.mem B p :=
    fun p hp => (Finset.mem_filter.mp hp).2
  have hfrontunit : forall b, List.Mem b frontRaw -> 0 <= b /\ b <= 1 := by
    intro b hb
    have hp := List.mem_map.mp hb
    choose p hp using hp
    have hprime := (Nat.mem_primesBelow.mp (hsmallB p (Finset.mem_toList.mp hp.1))).2
    rw [<- hp.2]
    exact List.bernoulliTilt_mem_unitInterval (eta p) z
      (hunit p hprime).1 (hunit p hprime).2 hz
  have horiginal : forall b, List.Mem b original -> 0 <= b /\ b <= 1 := by
    intro b hb
    cases List.mem_append.mp hb with
    | inl hf => exact hfrontunit b hf
    | inr ht => exact And.intro (htail b ht).1.le (htail b ht).2.le
  have hfrontbudget : (front.map (fun b => b / (1 - b))).sum <= z * F := by
    exact Finset.sum_interior_odds_tilt_mixture_le B small hsmallB eta1 eta2 eta
      (fun p hp => hunit1 p (Nat.mem_primesBelow.mp hp).2)
      (fun p hp => hunit2 p (Nat.mem_primesBelow.mp hp).2)
      (fun p hp => hchoice p (Nat.mem_primesBelow.mp (hsmallB p hp)).2) z hz
  have hcount : original.count 1 = c :=
    List.count_one_append_of_interior frontRaw tail htail
  have hcB : c <= B.card := by
    have hh : frontRaw.count 1 <= frontRaw.length := List.count_le_length
    have hhcard : small.card <= B.card := Finset.card_le_card hsmallB
    have hh' : c <= small.card := by
      simpa only [frontRaw, List.length_map, Finset.length_toList] using hh
    exact hh'.trans hhcard
  have hck : c <= k := by omega
  have hindex : original.count 1 + r = k := by rw [hcount]; dsimp [r]; omega
  have hshift : abs ((k : Real) - (r : Real)) <= J := by
    have hr : (r : Real) = (k : Real) - (c : Real) := by
      dsimp [r]
      rw [Nat.cast_sub hck]
    have hid : (k : Real) - ((k : Real) - (c : Real)) = (c : Real) := by ring
    rw [hr, hid, abs_of_nonneg (Nat.cast_nonneg c)]
    change (c : Real) <= (B.card : Real)
    exact_mod_cast hcB
  have hmissSubset : forall p, Membership.mem (T \ S) p -> Membership.mem (A \ E) p := by
    intro p hp
    have hh := Finset.mem_sdiff.mp hp
    have ht := Finset.mem_sdiff.mp hh.1
    apply Finset.mem_sdiff.mpr
    refine And.intro ht.1 ?_
    intro he
    exact hh.2 (Finset.mem_sdiff.mpr (And.intro he ht.2))
  have hmissCard : (T \ S).card <= 1 :=
    (Finset.card_le_card hmissSubset).trans hmissing
  have hmissbudget : (T \ S).sum a <= 2 * nu := by
    have hbound : forall p, Membership.mem (T \ S) p -> a p <= 2 * nu := by
      intro p hp
      have hh := hT p (Finset.mem_sdiff.mp hp).1
      have hp1 : (1 : Real) <= (p : Real) := by exact_mod_cast hh.1.one_le
      have hu0 : 0 <= 2 * nu := mul_nonneg (by norm_num) hnu.le
      calc
        _ <= 2 * nu / (p : Real) := hu p hh.1 hh.2.1
        _ <= (2 * nu) / 1 := div_le_div_of_nonneg_left hu0 (by norm_num) hp1
        _ = _ := by ring
    calc
      _ <= (T \ S).sum (fun _ => 2 * nu) := Finset.sum_le_sum hbound
      _ = ((T \ S).card : Real) * (2 * nu) := by simp [nsmul_eq_mul]
      _ <= 2 * nu := by
        have hcr : ((T \ S).card : Real) <= 1 := by exact_mod_cast hmissCard
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hcr
          (mul_nonneg (by norm_num) hnu.le)
  have hrflat := hk n r hkn hband hshift S a front hST
    (fun p hp hpc hpn => div_pos (hinterior p hp hpc).1 (sub_pos.mpr (hinterior p hp hpc).2))
    (fun p hp hpc hpn => hu p hp hpc)
    (fun p hp hpc hpn => herr p hp hpc)
    (List.bernoulliInterior_mem frontRaw) hfrontbudget hmissbudget
  have hrepr : List.bernoulliInterior original = front ++ tail :=
    List.bernoulliInterior_append_of_interior frontRaw tail htail
  have ho := hrflat.2.2.2 original horiginal hrepr
  rw [hindex] at ho
  have hm := List.bernoulliMass_perm hperm k
  have hml := List.bernoulliMass_perm hperm (k - 1)
  change 0 < List.bernoulliMass (E.toList.map tilt) k /\
    abs (List.bernoulliMass (E.toList.map tilt) (k - 1) /
      List.bernoulliMass (E.toList.map tilt) k - 1) <= epsilon
  rw [hm, hml]
  exact ho


end PrimeFactorOscillations
