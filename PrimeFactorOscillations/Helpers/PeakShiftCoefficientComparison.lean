import PrimeFactorOscillations.Helpers.PeakRankShifts

/-!
# Two-law coefficient comparison at fixed integer rank shifts

Two-law coefficient comparison at fixed integer rank shifts for the peak-height comparison of regular prime Bernoulli laws.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter Topology

namespace PrimeFactorOscillations

theorem regularPrimeLaws_uniform_shifted_tilted_coefficient_ratio
    (P : Nat) (nu alpha beta K J : Real) (hP : 1 <= P)
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
    (hJ : 0 <= J) (epsilon : Real) (hepsilon : 0 < epsilon) :
    Filter.Eventually (fun k : Nat => forall n m : Nat,
      k ^ 2 <= n -> alpha * Real.log (k : Real) <= Real.log (Real.log (n : Real)) ->
      Real.log (Real.log (n : Real)) <= beta * Real.log (k : Real) ->
      abs ((k : Real) - (m : Real)) <= J ->
      let z := (k : Real) / (nu * Real.log (Real.log (n : Real)))
      let s1 := (n + 1).primesBelow.toList.map
        (fun p => eta1 p * z / (1 - eta1 p + eta1 p * z))
      let s2 := (n + 1).primesBelow.toList.map
        (fun p => eta2 p * z / (1 - eta2 p + eta2 p * z))
      0 < List.bernoulliMass s1 m /\ 0 < List.bernoulliMass s2 m /\
        abs (List.bernoulliMass s1 m / List.bernoulliMass s2 m - 1) <= epsilon)
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
  have hflat := regularPrimeArrays_uniform_shifted_adjacent_flatness P nu alpha K J hP hnu halpha hK
    eta1 eta2 hunit1 hunit2 hinterior1 hinterior2 hupper1 hupper2 herror1 herror2
    hJ delta hd.1
  have ho := (_root_.isLittleO_log_rpow_rpow_atTop (1 : Real)
    (by norm_num : (0 : Real) < 1)).const_mul_left (nu * beta)
  have hlogbound := (tendsto_natCast_atTop_atTop (R := Real)).eventually
    (ho.bound (by norm_num : (0 : Real) < 1))
  have hbound := (tendsto_natCast_atTop_atTop (R := Real)).eventually
    (Filter.eventually_ge_atTop (J + 2))
  filter_upwards [hflat, hlogbound, Filter.eventually_ge_atTop (P + 2), hbound]
    with k hk hklog hkP hkbound
  intro n m hkn hlo hhi hshift
  have hmR : (1 : Real) <= (m : Real) := by
    linarith only [hkbound, (abs_le.mp hshift).2]
  have hm1 : 1 <= m := by exact_mod_cast hmR
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
  have hdegree : m - 1 + 1 = m := Nat.sub_add_cancel hm1
  have hbase1 := hk n m A eta1 hkn hlo hshift (fun p hp => hp) (by simp [A])
    (fun p hp => Or.inl rfl)
  have hbase2 := hk n m A eta2 hkn hlo hshift (fun p hp => hp) (by simp [A])
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
        0 < List.bernoulliMass (left.map Prod.fst ++ right.map Prod.snd) m /\
          abs (List.bernoulliMass (left.map Prod.fst ++ right.map Prod.snd) (m - 1) /
            List.bernoulliMass (left.map Prod.fst ++ right.map Prod.snd) m - 1) <= delta := by
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
    have hdel := hk n m E mixed hkn hlo hshift hE hmissing (fun q hq => hmixed.1 q)
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
    have hm := List.bernoulliMass_perm hperm' m
    have hml := List.bernoulliMass_perm hperm' (m - 1)
    rw [hm, hml]
    exact hdel
  have hmap1 : ps.map Prod.fst = A.toList.map f1 := by simp [ps, pair]
  have hmap2 : ps.map Prod.snd = A.toList.map f2 := by simp [ps, pair]
  have hcompare := hd.2.2 [] ps (m - 1) (by intro a ha; cases ha) hpsprob
    (by
      intro left right a b hps
      simpa only [List.nil_append, hdegree] using hcontrol left right a b hps)
    (by simpa only [List.nil_append, hdegree, hmap2] using hbase2.1)
    hcost
  have hratio : abs (List.bernoulliMass (A.toList.map f1) m /
      List.bernoulliMass (A.toList.map f2) m - 1) <= epsilon := by
    simpa only [List.nil_append, hdegree, hmap1, hmap2] using hcompare
  exact And.intro hbase1.1 (And.intro hbase2.1 hratio)

end PrimeFactorOscillations
namespace PrimeFactorOscillations

noncomputable def primeTiltedMass (eta : Nat -> Real) (n : Nat) (z : Real) (m : Nat) : Real :=
  List.bernoulliMass
    ((n + 1).primesBelow.toList.map (fun p => eta p * z / (1 - eta p + eta p * z))) m

theorem regularPrimeLaw_tendsto_shifted_adjacent_ratio
    (P : Nat) (nu alpha K J : Real) (hP : 1 <= P)
    (hnu : 0 < nu) (halpha : 0 < alpha) (hK : 0 <= K) (hJ : 0 <= J)
    (eta : Nat -> Real)
    (hunit : forall p, Nat.Prime p -> 0 <= eta p /\ eta p <= 1)
    (hinterior : forall p, Nat.Prime p -> P < p -> 0 < eta p /\ eta p < 1)
    (hupper : forall p, Nat.Prime p -> P < p ->
      eta p / (1 - eta p) <= 2 * nu / (p : Real))
    (herror : forall p, Nat.Prime p -> P < p ->
      abs (eta p / (1 - eta p) - nu / (p : Real)) <= K / (p : Real) ^ 2)
    (n m : Nat -> Nat)
    (hband : Filter.Eventually (fun k : Nat =>
      k ^ 2 <= n k /\ alpha * Real.log (k : Real) <=
        Real.log (Real.log (n k : Real))) atTop)
    (hshift : Filter.Eventually (fun k : Nat =>
      abs ((k : Real) - (m k : Real)) <= J) atTop) :
    let z := fun k : Nat => (k : Real) / (nu * Real.log (Real.log (n k : Real)))
    Filter.Eventually (fun k : Nat => 0 < primeTiltedMass eta (n k) (z k) (m k)) atTop /\
      Tendsto (fun k : Nat => primeTiltedMass eta (n k) (z k) (m k - 1) /
        primeTiltedMass eta (n k) (z k) (m k)) atTop (nhds 1) := by
  let z := fun k : Nat => (k : Real) / (nu * Real.log (Real.log (n k : Real)))
  have hcontrol (e : Real) (he : 0 < e) :=
    regularPrimeArrays_uniform_shifted_adjacent_flatness P nu alpha K J hP hnu halpha hK
      eta eta hunit hunit hinterior hinterior hupper hupper herror herror hJ e he
  constructor
  case left =>
    filter_upwards [hcontrol 1 (by norm_num), hband, hshift] with k hk hb hs
    have hh := hk (n k) (m k) (n k + 1).primesBelow eta hb.1 hb.2 hs
      (fun p hp => hp) (by simp) (fun p hp => Or.inl rfl)
    exact hh.1
  case right =>
    apply Metric.tendsto_nhds.2
    intro e he
    filter_upwards [hcontrol (e / 2) (half_pos he), hband, hshift] with k hk hb hs
    have hh := hk (n k) (m k) (n k + 1).primesBelow eta hb.1 hb.2 hs
      (fun p hp => hp) (by simp) (fun p hp => Or.inl rfl)
    change abs (primeTiltedMass eta (n k) (z k) (m k - 1) /
      primeTiltedMass eta (n k) (z k) (m k) - 1) < e
    exact hh.2.trans_lt (half_lt_self he)

theorem regularPrimeLaws_tendsto_shifted_same_rank_ratio
    (P : Nat) (nu alpha beta K J : Real) (hP : 1 <= P)
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) (hK : 0 <= K) (hJ : 0 <= J)
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
    (n m : Nat -> Nat)
    (hband : Filter.Eventually (fun k : Nat => k ^ 2 <= n k /\
      alpha * Real.log (k : Real) <= Real.log (Real.log (n k : Real)) /\
        Real.log (Real.log (n k : Real)) <= beta * Real.log (k : Real)) atTop)
    (hshift : Filter.Eventually (fun k : Nat =>
      abs ((k : Real) - (m k : Real)) <= J) atTop) :
    let z := fun k : Nat => (k : Real) / (nu * Real.log (Real.log (n k : Real)))
    Filter.Eventually (fun k : Nat =>
      0 < primeTiltedMass eta1 (n k) (z k) (m k) /\
        0 < primeTiltedMass eta2 (n k) (z k) (m k)) atTop /\
      Tendsto (fun k : Nat => primeTiltedMass eta1 (n k) (z k) (m k) /
        primeTiltedMass eta2 (n k) (z k) (m k)) atTop (nhds 1) := by
  let z := fun k : Nat => (k : Real) / (nu * Real.log (Real.log (n k : Real)))
  have hcontrol (e : Real) (he : 0 < e) :=
    regularPrimeLaws_uniform_shifted_tilted_coefficient_ratio P nu alpha beta K J hP
      hnu halpha hbeta hK eta1 eta2 hunit1 hunit2 hinterior1 hinterior2
      hlower1 hlower2 hupper1 hupper2 herror1 herror2 hJ e he
  constructor
  case left =>
    filter_upwards [hcontrol 1 (by norm_num), hband, hshift] with k hk hb hs
    have hh := hk (n k) (m k) hb.1 hb.2.1 hb.2.2 hs
    exact And.intro hh.1 hh.2.1
  case right =>
    apply Metric.tendsto_nhds.2
    intro e he
    filter_upwards [hcontrol (e / 2) (half_pos he), hband, hshift] with k hk hb hs
    have hh := hk (n k) (m k) hb.1 hb.2.1 hb.2.2 hs
    change abs (primeTiltedMass eta1 (n k) (z k) (m k) /
      primeTiltedMass eta2 (n k) (z k) (m k) - 1) < e
    exact hh.2.2.trans_lt (half_lt_self he)

end PrimeFactorOscillations
namespace PrimeFactorOscillations

theorem tendsto_coefficient_ratio_fixed_int_shifts
    (a : Nat -> Nat -> Real)
    (hpos : forall h : Int, Filter.Eventually
      (fun k : Nat => 0 < a k (shiftedPeakRank k h)) atTop)
    (hadj : forall h : Int, Tendsto
      (fun k : Nat => a k (shiftedPeakRank k h - 1) /
        a k (shiftedPeakRank k h)) atTop (nhds 1))
    (h1 h2 : Int) :
    Tendsto (fun k : Nat => a k (shiftedPeakRank k h1) /
      a k (shiftedPeakRank k h2)) atTop (nhds 1) := by
  have hforward (h : Int) (d : Nat) :
      Tendsto (fun k : Nat => a k (shiftedPeakRank k h) /
        a k (shiftedPeakRank k (h + (d : Int)))) atTop (nhds 1) := by
    let r := fun k : Nat => shiftedPeakRank k h
    have hp (j : Nat) : Filter.Eventually (fun k : Nat => 0 < a k (r k + j)) atTop := by
      filter_upwards [hpos (h + (j : Int)), eventually_shiftedPeakRank_add h j] with k hk he
      rw [he] at hk
      exact hk
    have ha (j : Nat) : Tendsto
        (fun k : Nat => a k (r k + j) / a k (r k + j + 1)) atTop (nhds 1) := by
      apply (hadj (h + ((j + 1 : Nat) : Int))).congr'
      filter_upwards [eventually_shiftedPeakRank_add h (j + 1)] with k hk
      rw [hk]
      have hsub : r k + (j + 1) - 1 = r k + j := by omega
      have hadd : r k + (j + 1) = r k + j + 1 := by omega
      change a k (r k + (j + 1) - 1) / a k (r k + (j + 1)) =
        a k (r k + j) / a k (r k + j + 1)
      rw [hsub, hadd]
    have ht := Real.tendsto_ratio_nat_shift_of_adjacent a r hp ha d
    apply ht.congr'
    filter_upwards [eventually_shiftedPeakRank_add h d] with k hk
    rw [hk]
  by_cases hle : h1 <= h2
  case pos =>
    let d := Int.toNat (h2 - h1)
    have he : h2 = h1 + (d : Int) := by dsimp [d]; omega
    rw [he]
    exact hforward h1 d
  case neg =>
    let d := Int.toNat (h1 - h2)
    have he : h1 = h2 + (d : Int) := by dsimp [d]; omega
    have hr := hforward h2 d
    rw [<- he] at hr
    have hc : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hi := hc.div hr (by norm_num : Not ((1 : Real) = 0))
    have hi' : Tendsto (fun k : Nat =>
        1 / (a k (shiftedPeakRank k h2) / a k (shiftedPeakRank k h1)))
          atTop (nhds 1) := by
      change Tendsto (fun k : Nat =>
        (1 : Real) / (a k (shiftedPeakRank k h2) / a k (shiftedPeakRank k h1)))
          atTop (nhds ((1 : Real) / 1)) at hi
      simpa only [div_one] using hi
    apply hi'.congr'
    filter_upwards [hpos h1, hpos h2] with k hk1 hk2
    field_simp [ne_of_gt hk1, ne_of_gt hk2]

theorem regularPrimeLaws_tendsto_fixed_shift_tilted_coefficient_ratio
    (P : Nat) (nu alpha beta K : Real) (hP : 1 <= P)
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) (hK : 0 <= K)
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
    (n : Nat -> Nat) (h1 h2 : Int)
    (hband : Filter.Eventually (fun k : Nat => k ^ 2 <= n k /\
      alpha * Real.log (k : Real) <= Real.log (Real.log (n k : Real)) /\
        Real.log (Real.log (n k : Real)) <= beta * Real.log (k : Real)) atTop) :
    let z := fun k : Nat => (k : Real) / (nu * Real.log (Real.log (n k : Real)))
    Filter.Eventually (fun k : Nat =>
      0 < primeTiltedMass eta1 (n k) (z k) (shiftedPeakRank k h1) /\
        0 < primeTiltedMass eta2 (n k) (z k) (shiftedPeakRank k h2)) atTop /\
      Tendsto (fun k : Nat =>
        primeTiltedMass eta1 (n k) (z k) (shiftedPeakRank k h1) /
          primeTiltedMass eta2 (n k) (z k) (shiftedPeakRank k h2)) atTop (nhds 1) := by
  let z := fun k : Nat => (k : Real) / (nu * Real.log (Real.log (n k : Real)))
  let a := fun k m : Nat => primeTiltedMass eta2 (n k) (z k) m
  have hshift (h : Int) : Filter.Eventually (fun k : Nat =>
      abs ((k : Real) - (shiftedPeakRank k h : Real)) <= abs (h : Real)) atTop := by
    filter_upwards [eventually_shiftedPeakRank_distance h] with k hk
    exact hk.le
  have hbandlo : Filter.Eventually (fun k : Nat =>
      k ^ 2 <= n k /\ alpha * Real.log (k : Real) <= Real.log (Real.log (n k : Real)))
        atTop := by
    filter_upwards [hband] with k hk
    exact And.intro hk.1 hk.2.1
  have hflat (h : Int) :=
    regularPrimeLaw_tendsto_shifted_adjacent_ratio P nu alpha K (abs (h : Real)) hP
      hnu halpha hK (abs_nonneg _) eta2 hunit2 hinterior2 hupper2 herror2 n
      (fun k => shiftedPeakRank k h) hbandlo (hshift h)
  have hsame :=
    regularPrimeLaws_tendsto_shifted_same_rank_ratio P nu alpha beta K (abs (h1 : Real))
      hP hnu halpha hbeta hK (abs_nonneg _) eta1 eta2 hunit1 hunit2 hinterior1 hinterior2
      hlower1 hlower2 hupper1 hupper2 herror1 herror2 n
      (fun k => shiftedPeakRank k h1) hband (hshift h1)
  have hinteger := tendsto_coefficient_ratio_fixed_int_shifts a
    (fun h => (hflat h).1) (fun h => (hflat h).2) h1 h2
  constructor
  case left =>
    filter_upwards [hsame.1, (hflat h2).1] with k hk hh
    exact And.intro hk.1 hh
  case right =>
    have hp := hsame.2.mul hinteger
    have hp' : Tendsto (fun k : Nat =>
        (primeTiltedMass eta1 (n k) (z k) (shiftedPeakRank k h1) /
          primeTiltedMass eta2 (n k) (z k) (shiftedPeakRank k h1)) *
        (primeTiltedMass eta2 (n k) (z k) (shiftedPeakRank k h1) /
          primeTiltedMass eta2 (n k) (z k) (shiftedPeakRank k h2))) atTop (nhds 1) := by
      simpa only [mul_one] using hp
    apply hp'.congr'
    filter_upwards [hsame.1, (hflat h2).1] with k hk hh
    dsimp only [z]
    field_simp [ne_of_gt hk.2, ne_of_gt hh]

end PrimeFactorOscillations

