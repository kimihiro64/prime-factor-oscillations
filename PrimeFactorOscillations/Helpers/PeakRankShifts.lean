import PrimeFactorOscillations.Helpers.PeakCoefficientComparison
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliPeakScale

/-!
# Uniform coefficient flatness with bounded integer rank shifts

Uniform coefficient flatness with bounded integer rank shifts for the peak-height comparison of regular prime Bernoulli laws.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter Topology

namespace PrimeFactorOscillations

def shiftedPeakRank (k : Nat) (h : Int) : Nat := Int.toNat ((k : Int) + h)

theorem eventually_shiftedPeakRank_cast (h : Int) :
    Filter.Eventually (fun k : Nat =>
      ((shiftedPeakRank k h : Nat) : Real) = (k : Real) + (h : Real)) atTop := by
  have hn := tendsto_natCast_atTop_atTop (R := Int)
  filter_upwards [hn.eventually (eventually_ge_atTop (-h))] with k hk
  have hnonneg : 0 <= (k : Int) + h := by omega
  have he : ((Int.toNat ((k : Int) + h) : Nat) : Int) = (k : Int) + h := by omega
  dsimp [shiftedPeakRank]
  exact_mod_cast he

theorem eventually_shiftedPeakRank_add (h : Int) (d : Nat) :
    Filter.Eventually (fun k : Nat =>
      shiftedPeakRank k (h + (d : Int)) = shiftedPeakRank k h + d) atTop := by
  have hn := tendsto_natCast_atTop_atTop (R := Int)
  filter_upwards [hn.eventually (eventually_ge_atTop (-h))] with k hk
  dsimp [shiftedPeakRank]
  omega

theorem eventually_shiftedPeakRank_distance (h : Int) :
    Filter.Eventually (fun k : Nat =>
      abs ((k : Real) - ((shiftedPeakRank k h : Nat) : Real)) = abs (h : Real)) atTop := by
  filter_upwards [eventually_shiftedPeakRank_cast h] with k hk
  rw [hk]
  have he : (k : Real) - ((k : Real) + (h : Real)) = -(h : Real) := by ring
  rw [he, abs_neg]

end PrimeFactorOscillations
namespace PrimeFactorOscillations

theorem tendsto_shiftedPeakRank_atTop (h : Int) :
    Tendsto (fun k : Nat => shiftedPeakRank k h) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro N
  have hn := tendsto_natCast_atTop_atTop (R := Int)
  filter_upwards [hn.eventually (eventually_ge_atTop ((N : Int) - h))] with k hk
  dsimp [shiftedPeakRank]
  omega

end PrimeFactorOscillations
namespace PrimeFactorOscillations

theorem regularPrimeArrays_uniform_shifted_adjacent_flatness
    (P : Nat) (nu alpha K J : Real) (hP : 1 <= P)
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
    (hJ : 0 <= J) (epsilon : Real) (hepsilon : 0 < epsilon) :
    Filter.Eventually (fun k : Nat => forall (n m : Nat) (E : Finset Nat) (eta : Nat -> Real),
      k ^ 2 <= n -> alpha * Real.log (k : Real) <= Real.log (Real.log (n : Real)) ->
      abs ((k : Real) - (m : Real)) <= J ->
      (forall p, Membership.mem E p -> Membership.mem (n + 1).primesBelow p) ->
      ((n + 1).primesBelow \ E).card <= 1 ->
      (forall p, Nat.Prime p -> eta p = eta1 p \/ eta p = eta2 p) ->
      let z := (k : Real) / (nu * Real.log (Real.log (n : Real)))
      let probs := E.toList.map (fun p => eta p * z / (1 - eta p + eta p * z))
      0 < List.bernoulliMass probs m /\
        abs (List.bernoulliMass probs (m - 1) / List.bernoulliMass probs m - 1) <= epsilon)
      Filter.atTop := by
  let B := (P + 1).primesBelow
  let F := B.sum (fun p => eta1 p / (1 - eta1 p) + eta2 p / (1 - eta2 p))
  let shiftBudget := (B.card : Real) + J
  let C := 2 * K / (P : Real) + nu *
    (abs (PrimeFactorUnimodality.reciprocalPrimeSumBelow (P + 1)) +
      (abs Mertens.M + abs PrimeFactorUnimodality.mertensErrorConstant / Real.log 2))
  have hflat := mixedPrimePrefix_uniform_adjacent_flatness P nu alpha K C (2 * nu) F shiftBudget
    hP hnu halpha hK (le_refl _) epsilon hepsilon
  have hbound := (tendsto_natCast_atTop_atTop (R := Real)).eventually
    (Filter.eventually_ge_atTop (J + (B.card : Real) + 2))
  filter_upwards [hflat, Filter.eventually_ge_atTop (max (P + 2) (B.card + 2)), hbound]
    with k hk hklarge hkbound
  intro n m E eta hkn hband hshiftm hE hmissing hchoice
  have hmBReal : (B.card : Real) + 2 <= (m : Real) := by
    linarith only [hkbound, (abs_le.mp hshiftm).2]
  have hmB : B.card + 2 <= m := by exact_mod_cast hmBReal
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
  let r := m - c
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
  have hck : c <= m := by omega
  have hindex : original.count 1 + r = m := by rw [hcount]; dsimp [r]; omega
  have hshift : abs ((k : Real) - (r : Real)) <= shiftBudget := by
    have hr : (r : Real) = (m : Real) - (c : Real) := by
      dsimp [r]
      rw [Nat.cast_sub hck]
    have hcR : (c : Real) <= (B.card : Real) := by exact_mod_cast hcB
    calc
      _ = abs (((k : Real) - (m : Real)) + (c : Real)) := by rw [hr]; congr 1; ring
      _ <= abs ((k : Real) - (m : Real)) + abs (c : Real) := abs_add_le _ _
      _ <= J + (B.card : Real) :=
        add_le_add hshiftm (by
          simpa only [abs_of_nonneg (show (0 : Real) <= (c : Real) from Nat.cast_nonneg c)]
            using hcR)
      _ = shiftBudget := by dsimp [shiftBudget]; ring
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
  have hm := List.bernoulliMass_perm hperm m
  have hml := List.bernoulliMass_perm hperm (m - 1)
  change 0 < List.bernoulliMass (E.toList.map tilt) m /\
    abs (List.bernoulliMass (E.toList.map tilt) (m - 1) /
      List.bernoulliMass (E.toList.map tilt) m - 1) <= epsilon
  rw [hm, hml]
  exact ho

end PrimeFactorOscillations

