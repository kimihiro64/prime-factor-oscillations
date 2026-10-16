/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PeakUniformCoefficients

/-! # Uniform coefficient comparison for regular prime laws

At a common explicit exponential tilt, the complete coefficient arrays of two
regular prime laws have positive coefficients and ratio tending uniformly to
one on every fixed logarithmic band. Finite exceptional primes, deterministic
coordinates and all canonical replacement arrays are handled internally.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter

namespace PrimeFactorOscillations

/-- The full two-law tilted coefficient comparison, uniform in the prime
cutoff throughout the stated band, with both denominator and numerator positive. -/
theorem regularPrimeLaws_uniform_tilted_coefficient_ratio
    (P : Nat) (nu alpha beta K : Real) (hP : 1 <= P)
    (hnu : 0 < nu) (halpha : 0 < alpha) (_hbeta : 0 < beta) (hK : 0 <= K)
    (eta1 eta2 : Nat -> Real)
    (hunit1 : forall p, Nat.Prime p -> 0 <= eta1 p /\ eta1 p <= 1)
    (hunit2 : forall p, Nat.Prime p -> 0 <= eta2 p /\ eta2 p <= 1)
    (hinterior1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p /\ eta1 p < 1)
    (hinterior2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p /\ eta2 p < 1)
    (hlower1 : forall p, Nat.Prime p -> P < p ->
      (nu / 2) / (p : Real) <= eta1 p / (1 - eta1 p))
    (hlower2 : forall p, Nat.Prime p -> P < p ->
      (nu / 2) / (p : Real) <= eta2 p / (1 - eta2 p))
    (hupper1 : forall p, Nat.Prime p -> P < p ->
      eta1 p / (1 - eta1 p) <= 2 * nu / (p : Real))
    (hupper2 : forall p, Nat.Prime p -> P < p ->
      eta2 p / (1 - eta2 p) <= 2 * nu / (p : Real))
    (herror1 : forall p, Nat.Prime p -> P < p ->
      abs (eta1 p / (1 - eta1 p) - nu / (p : Real)) <= K / (p : Real) ^ 2)
    (herror2 : forall p, Nat.Prime p -> P < p ->
      abs (eta2 p / (1 - eta2 p) - nu / (p : Real)) <= K / (p : Real) ^ 2)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    Filter.Eventually (fun k : Nat => forall n : Nat,
      k ^ 2 <= n -> alpha * Real.log (k : Real) <= Real.log (Real.log (n : Real)) ->
      Real.log (Real.log (n : Real)) <= beta * Real.log (k : Real) ->
      let z := (k : Real) / (nu * Real.log (Real.log (n : Real)))
      let s1 := (n + 1).primesBelow.toList.map
        (fun p => eta1 p * z / (1 - eta1 p + eta1 p * z))
      let s2 := (n + 1).primesBelow.toList.map
        (fun p => eta2 p * z / (1 - eta2 p + eta2 p * z))
      0 < List.bernoulliMass s1 k /\ 0 < List.bernoulliMass s2 k /\
        abs (List.bernoulliMass s1 k / List.bernoulliMass s2 k - 1) <= epsilon)
      Filter.atTop := by
  let B := (P + 1).primesBelow
  let cost := (B.card : Real) + 2 * K * (1 / (nu / 2) ^ 2 + 1 / (nu / 2))
  have hc : 0 < nu / 2 := div_pos hnu (by norm_num)
  have hcost0 : 0 <= cost := add_nonneg (Nat.cast_nonneg B.card)
    (mul_nonneg (mul_nonneg (by norm_num) hK)
      (add_nonneg (div_nonneg (by norm_num) (sq_nonneg _))
        (div_nonneg (by norm_num) hc.le)))
  have hmod := List.bernoulliMass_uniform_replacement_modulus cost epsilon hcost0 hepsilon
  choose delta hd using hmod
  have hflat := regularPrimeArrays_uniform_adjacent_flatness P nu alpha K hP hnu halpha hK
    eta1 eta2 hunit1 hunit2 hinterior1 hinterior2 hupper1 hupper2 herror1 herror2
    delta hd.1
  have ho := (_root_.isLittleO_log_rpow_rpow_atTop (1 : Real)
    (by norm_num : (0 : Real) < 1)).const_mul_left (nu * beta)
  have hlogbound := (tendsto_natCast_atTop_atTop (R := Real)).eventually
    (ho.bound (by norm_num : (0 : Real) < 1))
  filter_upwards [hflat, hlogbound, Filter.eventually_ge_atTop (P + 2)]
    with k hk hklog hkP
  intro n hkn hlo hhi
  let A := (n + 1).primesBelow
  let z := (k : Real) / (nu * Real.log (Real.log (n : Real)))
  let f1 := fun p => eta1 p * z / (1 - eta1 p + eta1 p * z)
  let f2 := fun p => eta2 p * z / (1 - eta2 p + eta2 p * z)
  let pair := fun p => Prod.mk (f1 p) (f2 p)
  let ps := A.toList.map pair
  have hk2 : 2 <= k := by omega
  have hk1 : 1 <= k := by omega
  have hkp : k <= k ^ 2 := by nlinarith
  have hPn : P <= n := (show P <= k by omega).trans (hkp.trans hkn)
  have hkpos : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
  have hlogpos : 0 < Real.log (k : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hL : 0 < Real.log (Real.log (n : Real)) :=
    (mul_pos halpha hlogpos).trans_le hlo
  have hden : 0 < nu * Real.log (Real.log (n : Real)) := mul_pos hnu hL
  have hz : 0 < z := div_pos hkpos hden
  have hz1 : 1 <= z := by
    have hk0 : 0 <= (k : Real) := Nat.cast_nonneg k
    simp only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg hk0, one_mul] at hklog
    have hh : nu * Real.log (Real.log (n : Real)) <= (k : Real) := by
      calc
        _ <= nu * (beta * Real.log (k : Real)) :=
          mul_le_mul_of_nonneg_left hhi hnu.le
        _ = (nu * beta) * Real.log (k : Real) := by ring
        _ <= _ := (le_abs_self _).trans hklog
    have hhdiv := div_le_div_of_nonneg_right hh hden.le
    rw [div_self (ne_of_gt hden)] at hhdiv
    exact hhdiv
  have hdegree : k - 1 + 1 = k := Nat.sub_add_cancel hk1
  have hbase1 := hk n A eta1 hkn hlo (fun p hp => hp) (by simp [A])
    (fun p hp => Or.inl rfl)
  have hbase2 := hk n A eta2 hkn hlo (fun p hp => hp) (by simp [A])
    (fun p hp => Or.inr rfl)
  have hpsprob : forall q, List.Mem q ps ->
      (0 <= q.1 /\ q.1 <= 1) /\ (0 <= q.2 /\ q.2 <= 1) := by
    intro q hq
    have hp := List.mem_map.mp hq
    choose p hp using hp
    have hprime := (Nat.mem_primesBelow.mp (Finset.mem_toList.mp hp.1)).2
    rw [<- hp.2]
    exact And.intro
      (List.bernoulliTilt_mem_unitInterval (eta1 p) z (hunit1 p hprime).1 (hunit1 p hprime).2 hz)
      (List.bernoulliTilt_mem_unitInterval (eta2 p) z (hunit2 p hprime).1 (hunit2 p hprime).2 hz)
  have hcost : (ps.map (fun q => abs (q.1 - q.2))).sum <= cost := by
    have hh := Finset.sum_abs_regularPrimeLaws_tilt_sub_le P n hPn nu K z hnu hK hz1
      eta1 eta2 hunit1 hunit2 hinterior1 hinterior2 hlower1 hlower2 herror1 herror2
    simpa [ps, pair, A, B, cost, f1, f2] using hh
  have hcontrol : forall (left right : List (Prod Real Real)) (a b : Real),
      ps = left ++ (a, b) :: right ->
        0 < List.bernoulliMass (left.map Prod.fst ++ right.map Prod.snd) k /\
          abs (List.bernoulliMass (left.map Prod.fst ++ right.map Prod.snd) (k - 1) /
            List.bernoulliMass (left.map Prod.fst ++ right.map Prod.snd) k - 1) <= delta := by
    intro left right a b hps
    have hdecomp := List.map_decomposition_with_coordinate pair A.toList left right (a, b) hps
    choose before p after hp using hdecomp
    have hhybrid := List.hybrid_deleted_map_perm A.toList before after p
      (Finset.nodup_toList A) hp.1 eta1 eta2
    choose mixed hmixed using hhybrid
    let E := A.erase p
    have hE : forall q, Membership.mem E q -> Membership.mem A q :=
      fun q hq => (Finset.mem_erase.mp hq).2
    have hmissing : (A \ E).card <= 1 := by
      have hs : forall q, Membership.mem (A \ E) q -> Membership.mem ({p} : Finset Nat) q := by
        intro q hq
        have hh := Finset.mem_sdiff.mp hq
        apply Finset.mem_singleton.mpr
        by_contra hnot
        exact hh.2 (Finset.mem_erase.mpr (And.intro hnot hh.1))
      have hh := Finset.card_le_card hs
      simpa using hh
    have hdel := hk n E mixed hkn hlo hE hmissing (fun q hq => hmixed.1 q)
    have hleft : left.map Prod.fst = before.map f1 := by
      rw [<- hp.2.1]
      simp [pair]
    have hright : right.map Prod.snd = after.map f2 := by
      rw [<- hp.2.2.2]
      simp [pair]
    have hperm := hmixed.2.map (fun x : Real => x * z / (1 - x + x * z))
    rw [Finset.toList_toFinset] at hperm
    simp only [List.map_append, List.map_map, Function.comp_def] at hperm
    have hperm' : (left.map Prod.fst ++ right.map Prod.snd).Perm
        (E.toList.map (fun q => mixed q * z / (1 - mixed q + mixed q * z))) := by
      rw [hleft, hright]
      exact hperm
    have hm := List.bernoulliMass_perm hperm' k
    have hml := List.bernoulliMass_perm hperm' (k - 1)
    rw [hm, hml]
    exact hdel
  have hmap1 : ps.map Prod.fst = A.toList.map f1 := by simp [ps, pair]
  have hmap2 : ps.map Prod.snd = A.toList.map f2 := by simp [ps, pair]
  have hcompare := hd.2.2 [] ps (k - 1) (by intro a ha; cases ha) hpsprob
    (by
      intro left right a b hps
      simpa only [List.nil_append, hdegree] using hcontrol left right a b hps)
    (by simpa only [List.nil_append, hdegree, hmap2] using hbase2.1)
    hcost
  have hratio : abs (List.bernoulliMass (A.toList.map f1) k /
      List.bernoulliMass (A.toList.map f2) k - 1) <= epsilon := by
    simpa only [List.nil_append, hdegree, hmap1, hmap2] using hcompare
  exact And.intro hbase1.1 (And.intro hbase2.1 hratio)


end PrimeFactorOscillations
