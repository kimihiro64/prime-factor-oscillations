import PrimeFactorOscillations.Helpers.PeakOuterSuppression
import PrimeFactorOscillations.Helpers.PeakRankShifts

/-!
# Attainment and localization of every prime-density maximum

Attainment and localization of every prime-density maximum for the peak-height comparison of regular prime Bernoulli laws.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter Topology

namespace PrimeFactorOscillations

theorem regularPrimeLaw_all_tail_maximizers_localized
    (P : Nat) (hP : 2 <= P) (eta : Nat -> Real) (front : List Real)
    (hf : forall a, List.Mem a front -> 0 <= a /\ a <= 1) (hA : 0 < front.prod)
    (nu K c C alpha beta : Real) (hnu : 0 < nu) (hK : 0 <= K) (hc : 0 < c)
    (hC : 0 < C) (halpha : 0 < alpha) (halpha1 : alpha < 1) (hbeta : 1 < beta)
    (hunit : forall p, Nat.Prime p -> P < p -> 0 <= eta p /\ eta p < 1)
    (hlower : forall p, Nat.Prime p -> P < p -> c / (p : Real) <= eta p)
    (hterminal : forall p, Nat.Prime p -> P < p -> eta p <= C / (p : Real))
    (hupper : forall p, Nat.Prime p -> P < p ->
      eta p / (1 - eta p) <= 2 * nu / (p : Real))
    (herror : forall p, Nat.Prime p -> P < p ->
      abs (eta p / (1 - eta p) - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    Filter.Eventually (fun k : Nat => forall r : Nat, Nat.Prime r -> P < r ->
      (forall p : Nat, Nat.Prime p -> P < p ->
        primeTailDensityWithFront P eta front k p <= primeTailDensityWithFront P eta front k r) ->
      alpha * Real.log (k : Real) < Real.log (Real.log (r : Real)) /\
        Real.log (r : Real) < (k : Real) ^ beta) atTop := by
  have hleft := regularPrimeLaw_left_outer_suppression P hP eta front hf hA nu K c
    alpha hnu hK hc halpha halpha1 hunit hlower hupper herror
  have hright := regularPrimeLaw_right_outer_suppression P hP eta front hf hA
    nu K c C beta hnu hK hc hC hbeta hunit hlower hterminal hupper herror
  filter_upwards [hleft, hright] with k hkleft hkright
  intro r hr hPr hmax
  choose qL hL using hkleft
  choose qR hR using hkright
  constructor
  case left =>
    by_contra hnot
    have hh := hL.2.2 r hr hPr (le_of_not_gt hnot)
    exact (not_lt_of_ge (hmax qL hL.1 hL.2.1)) hh
  case right =>
    by_contra hnot
    have hh := hR.2.2.2 r hr hPr (le_of_not_gt hnot)
    exact (not_lt_of_ge (hmax qR hR.1 hR.2.1)) hh

theorem primeTailDensityWithFront_exists_max_of_positive
    (P : Nat) (eta : Nat -> Real) (front : List Real)
    (hf : forall a, List.Mem a front -> 0 <= a /\ a <= 1)
    (C : Real) (hC : 0 <= C)
    (hunit : forall p, Nat.Prime p -> P < p -> 0 <= eta p /\ eta p < 1)
    (hterminal : forall p, Nat.Prime p -> P < p -> eta p <= C / (p : Real))
    (k q : Nat) (hq : Nat.Prime q) (hPq : P < q)
    (hpositive : 0 < primeTailDensityWithFront P eta front k q) :
    exists r : Nat, Nat.Prime r /\ P < r /\
      0 < primeTailDensityWithFront P eta front k r /\
      forall p : Nat, Nat.Prime p -> P < p ->
        primeTailDensityWithFront P eta front k p <=
          primeTailDensityWithFront P eta front k r := by
  classical
  let D := fun p : Nat => primeTailDensityWithFront P eta front k p
  change 0 < D q at hpositive
  choose N hN using exists_nat_gt (max (C / D q) (q : Real))
  have hCN : C / D q < (N : Real) := (le_max_left _ _).trans_lt hN
  have hqN : q <= N := by
    have hh : (q : Real) < (N : Real) := (le_max_right _ _).trans_lt hN
    exact_mod_cast hh.le
  let S := (N + 1).primesBelow \ (P + 1).primesBelow
  have hqS : Membership.mem S q := by
    apply Finset.mem_sdiff.mpr
    refine And.intro (Nat.mem_primesBelow.mpr (And.intro (by omega) hq)) ?_
    intro hh
    have ht := (Nat.mem_primesBelow.mp hh).1
    omega
  have hex := Finset.exists_max_image S D (Exists.intro q hqS)
  choose r hr using hex
  have hrmem := Finset.mem_sdiff.mp hr.1
  have hrprime := (Nat.mem_primesBelow.mp hrmem.1).2
  have hPr : P < r := by
    by_contra hnot
    exact hrmem.2 (Nat.mem_primesBelow.mpr (And.intro (by omega) hrprime))
  have hqmax := hr.2 q hqS
  refine Exists.intro r (And.intro hrprime (And.intro hPr
    (And.intro (hpositive.trans_le hqmax) ?_)))
  intro p hp hPp
  by_cases hpN : p <= N
  case pos =>
    apply hr.2 p
    apply Finset.mem_sdiff.mpr
    refine And.intro (Nat.mem_primesBelow.mpr (And.intro (by omega) hp)) ?_
    intro hh
    have ht := (Nat.mem_primesBelow.mp hh).1
    omega
  case neg =>
    have hnp : (N : Real) < (p : Real) := by exact_mod_cast (show N < p by omega)
    have hcpp : C / D q < (p : Real) := hCN.trans hnp
    have hmul := mul_lt_mul_of_pos_right hcpp hpositive
    have hid : (C / D q) * D q = C := by field_simp [ne_of_gt hpositive]
    rw [hid] at hmul
    have hppos : 0 < (p : Real) := by exact_mod_cast hp.pos
    have hquot : C / (p : Real) < D q := by
      by_contra hnot
      have hh := mul_le_mul_of_nonneg_right (le_of_not_gt hnot) hppos.le
      have he : (C / (p : Real)) * (p : Real) = C := by
        field_simp [ne_of_gt hppos]
      rw [he] at hh
      nlinarith only [hmul, hh]
    have hfull : forall b,
        List.Mem b (front ++ (p.primesBelow \ (P + 1).primesBelow).toList.map eta) ->
          0 <= b /\ b <= 1 := by
      intro b hb
      cases List.mem_append.mp hb with
      | inl hb => exact hf b hb
      | inr hb =>
          have hm := List.mem_map.mp hb
          choose a ha using hm
          have hs := Finset.mem_sdiff.mp (Finset.mem_toList.mp ha.1)
          have hap := (Nat.mem_primesBelow.mp hs.1).2
          have hPa : P < a := by
            by_contra hnot
            exact hs.2 (Nat.mem_primesBelow.mpr (And.intro (by omega) hap))
          rw [<- ha.2]
          exact And.intro (hunit a hap hPa).1 (hunit a hap hPa).2.le
    have ht := mul_le_mul_of_nonneg_left
      (List.bernoulliMass_le_one _ hfull k) (hunit p hp hPp).1
    simp only [mul_one] at ht
    change D p <= D r
    exact ((ht.trans (hterminal p hp hPp)).trans hquot.le).trans hqmax

theorem regularPrimeLaw_eventually_tail_peak_exists
    (P : Nat) (hP : 2 <= P) (eta : Nat -> Real) (front : List Real)
    (hf : forall a, List.Mem a front -> 0 <= a /\ a <= 1) (hA : 0 < front.prod)
    (nu K c C : Real) (hnu : 0 < nu) (hK : 0 <= K) (hc : 0 < c) (hC : 0 < C)
    (hunit : forall p, Nat.Prime p -> P < p -> 0 <= eta p /\ eta p < 1)
    (hlower : forall p, Nat.Prime p -> P < p -> c / (p : Real) <= eta p)
    (hterminal : forall p, Nat.Prime p -> P < p -> eta p <= C / (p : Real))
    (hupper : forall p, Nat.Prime p -> P < p ->
      eta p / (1 - eta p) <= 2 * nu / (p : Real))
    (herror : forall p, Nat.Prime p -> P < p ->
      abs (eta p / (1 - eta p) - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    Filter.Eventually (fun k : Nat => exists r : Nat, Nat.Prime r /\ P < r /\
      0 < primeTailDensityWithFront P eta front k r /\
      forall p : Nat, Nat.Prime p -> P < p ->
        primeTailDensityWithFront P eta front k p <=
          primeTailDensityWithFront P eta front k r) atTop := by
  have hh := regularPrimeLaw_right_outer_suppression P hP eta front hf hA
    nu K c C 2 hnu hK hc hC (by norm_num) hunit hlower hterminal hupper herror
  filter_upwards [hh] with k hk
  choose q hq using hk
  exact primeTailDensityWithFront_exists_max_of_positive P eta front hf C hC.le
    hunit hterminal k q hq.1 hq.2.1 hq.2.2.1

end PrimeFactorOscillations
namespace PrimeFactorOscillations

theorem regularPrimeLaw_eventually_prime_peak_exists
    (P : Nat) (hP : 2 <= P) (eta : Nat -> Real)
    (nu K c C : Real) (hnu : 0 < nu) (hK : 0 <= K) (hc : 0 < c) (hC : 0 < C)
    (hunit : forall p, Nat.Prime p -> 0 <= eta p /\ eta p <= 1)
    (hinterior : forall p, Nat.Prime p -> P < p -> eta p < 1)
    (hlower : forall p, Nat.Prime p -> P < p -> c / (p : Real) <= eta p)
    (hterminal : forall p, Nat.Prime p -> P < p -> eta p <= C / (p : Real))
    (hupper : forall p, Nat.Prime p -> P < p ->
      eta p / (1 - eta p) <= 2 * nu / (p : Real))
    (herror : forall p, Nat.Prime p -> P < p ->
      abs (eta p / (1 - eta p) - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    Filter.Eventually (fun k : Nat => exists r : Nat, Nat.Prime r /\
      0 < primeBernoulliDensity eta k r /\
      forall p : Nat, Nat.Prime p ->
        primeBernoulliDensity eta k p <= primeBernoulliDensity eta k r) atTop := by
  let front := smallPrimePositiveFront P eta
  have hf := smallPrimePositiveFront_properties P eta hunit
  have ht := regularPrimeLaw_eventually_tail_peak_exists P hP eta front
    (fun a ha => And.intro (hf.1 a ha).1.le (hf.1 a ha).2) hf.2 nu K c C
    hnu hK hc hC (fun p hp hPp => And.intro (hunit p hp).1 (hinterior p hp hPp))
    hlower hterminal hupper herror
  filter_upwards [ht, eventually_ge_atTop ((P + 1).primesBelow.card + 1)] with k hk hkrank
  choose r hr using hk
  have hre := primeBernoulliDensity_eq_tailDensityWithFront P r k eta hr.2.1
  have hrpos : 0 < primeBernoulliDensity eta k r := by
    rw [hre]
    exact hr.2.2.1
  refine Exists.intro r (And.intro hr.1 (And.intro hrpos ?_))
  intro p hp
  by_cases hPp : P < p
  case pos =>
    rw [primeBernoulliDensity_eq_tailDensityWithFront P p k eta hPp, hre]
    exact hr.2.2.2 p hp hPp
  case neg =>
    rw [primeBernoulliDensity_small_prime_eq_zero P p k eta (by omega) (by omega)]
    exact hrpos.le

theorem regularPrimeLaw_all_prime_maximizers_localized
    (P : Nat) (hP : 2 <= P) (eta : Nat -> Real)
    (nu K c C alpha beta : Real) (hnu : 0 < nu) (hK : 0 <= K) (hc : 0 < c)
    (hC : 0 < C) (halpha : 0 < alpha) (halpha1 : alpha < 1) (hbeta : 1 < beta)
    (hunit : forall p, Nat.Prime p -> 0 <= eta p /\ eta p <= 1)
    (hinterior : forall p, Nat.Prime p -> P < p -> eta p < 1)
    (hlower : forall p, Nat.Prime p -> P < p -> c / (p : Real) <= eta p)
    (hterminal : forall p, Nat.Prime p -> P < p -> eta p <= C / (p : Real))
    (hupper : forall p, Nat.Prime p -> P < p ->
      eta p / (1 - eta p) <= 2 * nu / (p : Real))
    (herror : forall p, Nat.Prime p -> P < p ->
      abs (eta p / (1 - eta p) - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    Filter.Eventually (fun k : Nat => forall r : Nat, Nat.Prime r ->
      (forall p : Nat, Nat.Prime p ->
        primeBernoulliDensity eta k p <= primeBernoulliDensity eta k r) ->
      P < r /\ 0 < primeBernoulliDensity eta k r /\
        alpha * Real.log (k : Real) < Real.log (Real.log (r : Real)) /\
        Real.log (r : Real) < (k : Real) ^ beta) atTop := by
  let front := smallPrimePositiveFront P eta
  have hf := smallPrimePositiveFront_properties P eta hunit
  have ht := regularPrimeLaw_all_tail_maximizers_localized P hP eta front
    (fun a ha => And.intro (hf.1 a ha).1.le (hf.1 a ha).2) hf.2 nu K c C alpha beta
    hnu hK hc hC halpha halpha1 hbeta
    (fun p hp hPp => And.intro (hunit p hp).1 (hinterior p hp hPp))
    hlower hterminal hupper herror
  have he := regularPrimeLaw_eventually_prime_peak_exists P hP eta nu K c C hnu hK hc hC
    hunit hinterior hlower hterminal hupper herror
  filter_upwards [ht, he, eventually_ge_atTop ((P + 1).primesBelow.card + 1)] with
    k hk hke hkrank
  intro r hr hmax
  choose q hq using hke
  have hrpos : 0 < primeBernoulliDensity eta k r := hq.2.1.trans_le (hmax q hq.1)
  have hPr : P < r := by
    by_contra hnot
    have hz := primeBernoulliDensity_small_prime_eq_zero P r k eta (by omega) (by omega)
    rw [hz] at hrpos
    exact (lt_irrefl 0) hrpos
  have hre := primeBernoulliDensity_eq_tailDensityWithFront P r k eta hPr
  have htailmax : forall p : Nat, Nat.Prime p -> P < p ->
      primeTailDensityWithFront P eta front k p <=
        primeTailDensityWithFront P eta front k r := by
    intro p hp hPp
    have hh := hmax p hp
    rw [primeBernoulliDensity_eq_tailDensityWithFront P p k eta hPp, hre] at hh
    exact hh
  exact And.intro hPr (And.intro hrpos (hk r hr hPr htailmax))

end PrimeFactorOscillations
namespace PrimeFactorOscillations

def IsPrimeBernoulliPeak (eta : Nat -> Real) (k r : Nat) : Prop :=
  Nat.Prime r /\ forall p : Nat, Nat.Prime p ->
    primeBernoulliDensity eta k p <= primeBernoulliDensity eta k r

noncomputable def primePeakPrime (eta : Nat -> Real) (k : Nat) : Nat := by
  classical
  exact if h : exists r : Nat, IsPrimeBernoulliPeak eta k r then Classical.choose h else 2

noncomputable def primePeakHeight (eta : Nat -> Real) (k : Nat) : Real :=
  primeBernoulliDensity eta k (primePeakPrime eta k)

theorem primePeakPrime_spec (eta : Nat -> Real) (k : Nat)
    (hex : exists r : Nat, IsPrimeBernoulliPeak eta k r) :
    IsPrimeBernoulliPeak eta k (primePeakPrime eta k) := by
  classical
  unfold primePeakPrime
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem regularPrimeLaw_eventually_peakPrime_spec
    (P : Nat) (hP : 2 <= P) (eta : Nat -> Real)
    (nu K c C : Real) (hnu : 0 < nu) (hK : 0 <= K) (hc : 0 < c) (hC : 0 < C)
    (hunit : forall p, Nat.Prime p -> 0 <= eta p /\ eta p <= 1)
    (hinterior : forall p, Nat.Prime p -> P < p -> eta p < 1)
    (hlower : forall p, Nat.Prime p -> P < p -> c / (p : Real) <= eta p)
    (hterminal : forall p, Nat.Prime p -> P < p -> eta p <= C / (p : Real))
    (hupper : forall p, Nat.Prime p -> P < p ->
      eta p / (1 - eta p) <= 2 * nu / (p : Real))
    (herror : forall p, Nat.Prime p -> P < p ->
      abs (eta p / (1 - eta p) - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    Filter.Eventually (fun k : Nat => IsPrimeBernoulliPeak eta k (primePeakPrime eta k) /\
      0 < primePeakHeight eta k) atTop := by
  have ht := regularPrimeLaw_eventually_prime_peak_exists P hP eta nu K c C hnu hK hc hC
    hunit hinterior hlower hterminal hupper herror
  filter_upwards [ht] with k hk
  choose r hr using hk
  have hex : exists r : Nat, IsPrimeBernoulliPeak eta k r :=
    Exists.intro r (And.intro hr.1 hr.2.2)
  have hs := primePeakPrime_spec eta k hex
  exact And.intro hs (hr.2.1.trans_le (hs.2 r hr.1))

theorem regularPrimeLaw_peakPrime_cutoff_scale
    (P : Nat) (hP : 2 <= P) (eta : Nat -> Real)
    (nu K c C : Real) (hnu : 0 < nu) (hK : 0 <= K) (hc : 0 < c) (hC : 0 < C)
    (hunit : forall p, Nat.Prime p -> 0 <= eta p /\ eta p <= 1)
    (hinterior : forall p, Nat.Prime p -> P < p -> eta p < 1)
    (hlower : forall p, Nat.Prime p -> P < p -> c / (p : Real) <= eta p)
    (hterminal : forall p, Nat.Prime p -> P < p -> eta p <= C / (p : Real))
    (hupper : forall p, Nat.Prime p -> P < p ->
      eta p / (1 - eta p) <= 2 * nu / (p : Real))
    (herror : forall p, Nat.Prime p -> P < p ->
      abs (eta p / (1 - eta p) - nu / (p : Real)) <= K / (p : Real) ^ 2)
    (d : Int) :
    let p := fun k : Nat => primePeakPrime eta (shiftedPeakRank k d)
    Filter.Eventually (fun k : Nat => 3 <= p k) atTop /\
      Tendsto (fun k : Nat =>
        Real.log (Real.log ((p k - 1 : Nat) : Real)) / Real.log (k : Real)) atTop (nhds 1) := by
  let m := fun k : Nat => shiftedPeakRank k d
  let p := fun k : Nat => primePeakPrime eta (m k)
  have hs := regularPrimeLaw_eventually_peakPrime_spec P hP eta nu K c C hnu hK hc hC
    hunit hinterior hlower hterminal hupper herror
  have hspec := (tendsto_shiftedPeakRank_atTop d).eventually hs
  have hglobal (alpha beta : Real) (ha : 0 < alpha) (ha1 : alpha < 1) (hb : 1 < beta) :
      Filter.Eventually (fun k : Nat => P < p k /\
        0 < primeBernoulliDensity eta (m k) (p k) /\
        alpha * Real.log (m k : Real) < Real.log (Real.log (p k : Real)) /\
          Real.log (p k : Real) < (m k : Real) ^ beta) atTop := by
    have hh := regularPrimeLaw_all_prime_maximizers_localized P hP eta nu K c C alpha beta
      hnu hK hc hC ha ha1 hb hunit hinterior hlower hterminal hupper herror
    have ht := (tendsto_shiftedPeakRank_atTop d).eventually hh
    filter_upwards [ht, hspec] with k hk hsk
    exact hk (p k) hsk.1.1 hsk.1.2
  have hp3 : Filter.Eventually (fun k : Nat => 3 <= p k) atTop := by
    filter_upwards [hglobal (1 / 2) 2 (by norm_num) (by norm_num) (by norm_num)] with k hk
    omega
  have hshift : Filter.Eventually (fun k : Nat =>
      abs ((k : Real) - (m k : Real)) <= abs (d : Real)) atTop := by
    filter_upwards [eventually_shiftedPeakRank_distance d] with k hk
    exact hk.le
  refine And.intro hp3 ?_
  apply Real.tendsto_logLog_predecessor_of_peak_localization m p (abs (d : Real))
    (abs_nonneg _) hshift hp3
  intro alpha beta ha ha1 hb
  filter_upwards [hglobal alpha beta ha ha1 hb] with k hk
  exact hk.2.2

end PrimeFactorOscillations

