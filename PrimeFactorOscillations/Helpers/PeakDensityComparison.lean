import PrimeFactorOscillations.Helpers.PeakGrowingProducts
import PrimeFactorOscillations.Helpers.PeakShiftCoefficientComparison

/-!
# Density comparison at the common standard asymptotic scale

Density comparison at the common standard asymptotic scale for the peak-height comparison of regular prime Bernoulli laws.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter Topology

namespace PrimeFactorOscillations

theorem primeBernoulliProduct_tilt (eta : Nat -> Real) (n m : Nat) (z : Real)
    (hunit : forall p, Nat.Prime p -> 0 <= eta p /\ eta p <= 1) (hz : 0 < z) :
    primeBernoulliProduct eta n z * primeTiltedMass eta n z m =
      z ^ m * List.bernoulliMass ((n + 1).primesBelow.toList.map eta) m := by
  have hf : forall a, List.Mem a ((n + 1).primesBelow.toList.map eta) ->
      Not (1 - a + a * z = 0) := by
    intro a ha
    have hh := List.mem_map.mp ha
    choose p hp using hh
    rw [<- hp.2]
    have hpp := (Nat.mem_primesBelow.mp (Finset.mem_toList.mp hp.1)).2
    exact ne_of_gt (List.bernoulliFactor_pos (eta p) z
      (hunit p hpp).1 (hunit p hpp).2 hz)
  have hh := List.bernoulliMass_tilt ((n + 1).primesBelow.toList.map eta) z m hf
  simpa [primeBernoulliProduct, primeTiltedMass, List.map_map, Function.comp_def] using hh

theorem primeBernoulliMass_pos_of_tilt (eta : Nat -> Real) (n m : Nat) (z : Real)
    (hunit : forall p, Nat.Prime p -> 0 <= eta p /\ eta p <= 1) (hz : 0 < z)
    (ht : 0 < primeTiltedMass eta n z m) :
    0 < List.bernoulliMass ((n + 1).primesBelow.toList.map eta) m := by
  have hp := mul_pos (primeBernoulliProduct_pos eta n z hunit hz) ht
  rw [primeBernoulliProduct_tilt eta n m z hunit hz] at hp
  by_contra hnot
  have hh := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hz.le m) (le_of_not_gt hnot)
  exact (not_le_of_gt hp) hh

theorem regularPrimeLaws_tendsto_fixed_shift_density_tilt_scale
    (P : Nat) (eta1 eta2 : Nat -> Real) (nu b1 b2 C1 C2 K alpha beta : Real)
    (hP : 1 <= P) (hnu : 0 < nu) (hC1 : 0 <= C1) (hC2 : 0 <= C2) (hK : 0 <= K)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hunit1 : forall p, Nat.Prime p -> 0 <= eta1 p /\ eta1 p <= 1)
    (hunit2 : forall p, Nat.Prime p -> 0 <= eta2 p /\ eta2 p <= 1)
    (h1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p /\ eta1 p < 1)
    (h2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p /\ eta2 p < 1)
    (herr1 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta1 p - (p : Real) / nu - b1) <= C1 / (p : Real))
    (herr2 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta2 p - (p : Real) / nu - b2) <= C2 / (p : Real))
    (hscale1 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b1 + C1)) <= (p : Real))
    (hscale2 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b2 + C2)) <= (p : Real))
    (hlower1 : forall p, Nat.Prime p -> P < p ->
      (nu / 2) / (p : Real) <= eta1 p / (1 - eta1 p))
    (hlower2 : forall p, Nat.Prime p -> P < p ->
      (nu / 2) / (p : Real) <= eta2 p / (1 - eta2 p))
    (hupper1 : forall p, Nat.Prime p -> P < p ->
      eta1 p / (1 - eta1 p) <= 2 * nu / (p : Real))
    (hupper2 : forall p, Nat.Prime p -> P < p ->
      eta2 p / (1 - eta2 p) <= 2 * nu / (p : Real))
    (hodds1 : forall p, Nat.Prime p -> P < p ->
      abs (eta1 p / (1 - eta1 p) - nu / (p : Real)) <= K / (p : Real) ^ 2)
    (hodds2 : forall p, Nat.Prime p -> P < p ->
      abs (eta2 p / (1 - eta2 p) - nu / (p : Real)) <= K / (p : Real) ^ 2)
    (n : Nat -> Nat) (d1 d2 : Int)
    (hband : Filter.Eventually (fun k : Nat => k ^ 2 <= n k /\
      alpha * Real.log (k : Real) <= Real.log (Real.log (n k : Real)) /\
        Real.log (Real.log (n k : Real)) <= beta * Real.log (k : Real)) atTop)
    (hprime : Filter.Eventually (fun k : Nat => Nat.Prime (n k + 1)) atTop) :
    let z := fun k : Nat => (k : Real) / (nu * Real.log (Real.log (n k : Real)))
    let s1 := (smallPrimePositiveFront P eta1).length
    let s2 := (smallPrimePositiveFront P eta2).length
    let E := (s1 : Real) - (s2 : Real) - (d1 : Real) + (d2 : Real)
    let B := ((smallPrimePositiveFront P eta1).prod / (smallPrimePositiveFront P eta2).prod) *
      primeComparisonEulerConstant P eta1 eta2 nu b1 b2
    0 < B /\
      Filter.Eventually (fun k : Nat =>
        0 < primeBernoulliDensity eta1 (shiftedPeakRank k d1) (n k + 1) /\
          0 < primeBernoulliDensity eta2 (shiftedPeakRank k d2) (n k + 1)) atTop /\
      Tendsto (fun k : Nat =>
        (primeBernoulliDensity eta1 (shiftedPeakRank k d1) (n k + 1) /
          primeBernoulliDensity eta2 (shiftedPeakRank k d2) (n k + 1)) /
            (Real.rpow (z k) E * Real.rpow (Real.log (z k)) (nu * (b2 - b1))))
              atTop (nhds B) := by
  let z := fun k : Nat => (k : Real) / (nu * Real.log (Real.log (n k : Real)))
  let m1 := fun k : Nat => shiftedPeakRank k d1
  let m2 := fun k : Nat => shiftedPeakRank k d2
  let s1 := (smallPrimePositiveFront P eta1).length
  let s2 := (smallPrimePositiveFront P eta2).length
  let E := (s1 : Real) - (s2 : Real) - (d1 : Real) + (d2 : Real)
  let B := ((smallPrimePositiveFront P eta1).prod / (smallPrimePositiveFront P eta2).prod) *
    primeComparisonEulerConstant P eta1 eta2 nu b1 b2
  have hp : Tendsto (fun k : Nat => n k + 1) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro N
    filter_upwards [hband, eventually_ge_atTop (max N 1)] with k hk hNk
    have hk1 : 1 <= k := (le_max_right _ _).trans hNk
    have hkk : k <= k ^ 2 := by nlinarith only [hk1]
    have hNk' : N <= k := (le_max_left _ _).trans hNk
    omega
  have he := regularPrimeLaws_tendsto_terminal_ratio P eta1 eta2 nu b1 b2 C1 C2
    hnu hC1 hC2 (fun p hp hPp => (h1 p hp hPp).1)
    (fun p hp hPp => (h2 p hp hPp).1) herr1 herr2 (fun k => n k + 1) hp hprime
  have hc := regularPrimeLaws_tendsto_fixed_shift_tilted_coefficient_ratio P nu alpha beta K
    hP hnu halpha hbeta hK eta1 eta2 hunit1 hunit2 h1 h2 hlower1 hlower2
    hupper1 hupper2 hodds1 hodds2 n d1 d2 hband
  have hg := regularPrimeLaws_tendsto_full_product_sequence P eta1 eta2
    nu b1 b2 C1 C2 alpha beta hnu hC1 hC2 halpha hbeta hunit1 hunit2
    (fun p hp hPp => (h1 p hp hPp).1) (fun p hp hPp => (h2 p hp hPp).1)
    herr1 herr2 hscale1 hscale2 n hband
  have hz := Real.primeTilt_sequence_atTop_and_cutoff nu alpha beta hnu halpha hbeta n hband
  have hpositive : Filter.Eventually (fun k : Nat =>
      0 < primeBernoulliDensity eta1 (m1 k) (n k + 1) /\
        0 < primeBernoulliDensity eta2 (m2 k) (n k + 1)) atTop := by
    filter_upwards [hc.1, hz.2, hprime, hp.eventually (eventually_ge_atTop (P + 2))] with
      k hk hzk hpk hPk
    exact And.intro
      (mul_pos (h1 (n k + 1) hpk (by omega)).1
        (primeBernoulliMass_pos_of_tilt eta1 (n k) (m1 k) (z k) hunit1 hzk.1 hk.1))
      (mul_pos (h2 (n k + 1) hpk (by omega)).1
        (primeBernoulliMass_pos_of_tilt eta2 (n k) (m2 k) (z k) hunit2 hzk.1 hk.2))
  refine And.intro hg.1 (And.intro hpositive ?_)
  have hprod := (he.mul hc.2).mul hg.2
  have hprod' : Tendsto (fun k : Nat =>
      (eta1 (n k + 1) / eta2 (n k + 1)) *
      (primeTiltedMass eta1 (n k) (z k) (m1 k) /
        primeTiltedMass eta2 (n k) (z k) (m2 k)) *
      (((primeBernoulliProduct eta1 (n k) (z k) / (z k) ^ s1) /
        (primeBernoulliProduct eta2 (n k) (z k) / (z k) ^ s2)) /
          Real.rpow (Real.log (z k)) (nu * (b2 - b1)))) atTop (nhds B) := by
    simpa only [one_mul] using hprod
  apply hprod'.congr'
  filter_upwards [hc.1, hz.1.eventually (eventually_gt_atTop (1 : Real)),
    hprime, hp.eventually (eventually_ge_atTop (P + 2)),
    eventually_shiftedPeakRank_cast d1, eventually_shiftedPeakRank_cast d2] with
      k hk hzk hpk hPk hcast1 hcast2
  have hzp : 0 < z k := zero_lt_one.trans hzk
  have hZn (j : Nat) : Not ((z k) ^ j = 0) := pow_ne_zero _ (ne_of_gt hzp)
  have hG2 : Not (primeBernoulliProduct eta2 (n k) (z k) = 0) :=
    ne_of_gt (primeBernoulliProduct_pos eta2 (n k) (z k) hunit2 hzp)
  have hT2 : Not (primeTiltedMass eta2 (n k) (z k) (m2 k) = 0) := ne_of_gt hk.2
  have hEta2 : Not (eta2 (n k + 1) = 0) := ne_of_gt (h2 (n k + 1) hpk (by omega)).1
  have hR : Not (Real.rpow (Real.log (z k)) (nu * (b2 - b1)) = 0) :=
    ne_of_gt (Real.rpow_pos_of_pos (Real.log_pos hzk) _)
  have hcast1' : (m1 k : Real) = (k : Real) + (d1 : Real) := hcast1
  have hcast2' : (m2 k : Real) = (k : Real) + (d2 : Real) := hcast2
  have hE : E = (s1 : Real) - (s2 : Real) + (m2 k : Real) - (m1 k : Real) := by
    rw [hcast1', hcast2']
    dsimp [E]
    ring
  have hbal := Real.rpow_nat_power_balance (z k) hzp s1 s2 (m1 k) (m2 k)
  rw [<- hE] at hbal
  have hrpow : Real.rpow (z k) E =
      ((z k) ^ s1 * (z k) ^ (m2 k)) / ((z k) ^ s2 * (z k) ^ (m1 k)) := by
    calc
      _ = (Real.rpow (z k) E * (z k) ^ s2 * (z k) ^ (m1 k)) /
          ((z k) ^ s2 * (z k) ^ (m1 k)) := by field_simp [hZn s2, hZn (m1 k)]
      _ = _ := by rw [hbal]
  have hm1 :
      List.bernoulliMass ((n k + 1).primesBelow.toList.map eta1) (m1 k) =
        (primeBernoulliProduct eta1 (n k) (z k) *
          primeTiltedMass eta1 (n k) (z k) (m1 k)) / (z k) ^ (m1 k) := by
    calc
      _ = ((z k) ^ (m1 k) *
          List.bernoulliMass ((n k + 1).primesBelow.toList.map eta1) (m1 k)) /
            (z k) ^ (m1 k) := by field_simp [hZn (m1 k)]
      _ = _ := by rw [<- primeBernoulliProduct_tilt eta1 (n k) (m1 k) (z k) hunit1 hzp]
  have hm2 :
      List.bernoulliMass ((n k + 1).primesBelow.toList.map eta2) (m2 k) =
        (primeBernoulliProduct eta2 (n k) (z k) *
          primeTiltedMass eta2 (n k) (z k) (m2 k)) / (z k) ^ (m2 k) := by
    calc
      _ = ((z k) ^ (m2 k) *
          List.bernoulliMass ((n k + 1).primesBelow.toList.map eta2) (m2 k)) /
            (z k) ^ (m2 k) := by field_simp [hZn (m2 k)]
      _ = _ := by rw [<- primeBernoulliProduct_tilt eta2 (n k) (m2 k) (z k) hunit2 hzp]
  change (eta1 (n k + 1) / eta2 (n k + 1)) *
      (primeTiltedMass eta1 (n k) (z k) (m1 k) /
        primeTiltedMass eta2 (n k) (z k) (m2 k)) *
      (((primeBernoulliProduct eta1 (n k) (z k) / (z k) ^ s1) /
        (primeBernoulliProduct eta2 (n k) (z k) / (z k) ^ s2)) /
          Real.rpow (Real.log (z k)) (nu * (b2 - b1))) =
    ((eta1 (n k + 1) *
      List.bernoulliMass ((n k + 1).primesBelow.toList.map eta1) (m1 k)) /
      (eta2 (n k + 1) *
        List.bernoulliMass ((n k + 1).primesBelow.toList.map eta2) (m2 k))) /
      (Real.rpow (z k) E * Real.rpow (Real.log (z k)) (nu * (b2 - b1)))
  rw [hm1, hm2, hrpow]
  field_simp [hZn s1, hZn s2, hZn (m1 k), hZn (m2 k), hG2, hT2, hEta2, hR]

end PrimeFactorOscillations
namespace PrimeFactorOscillations

theorem regularPrimeLaws_tendsto_fixed_shift_density_standard_scale
    (P : Nat) (eta1 eta2 : Nat -> Real) (nu b1 b2 C1 C2 K : Real)
    (hP : 1 <= P) (hnu : 0 < nu) (hC1 : 0 <= C1) (hC2 : 0 <= C2) (hK : 0 <= K)
    (hunit1 : forall p, Nat.Prime p -> 0 <= eta1 p /\ eta1 p <= 1)
    (hunit2 : forall p, Nat.Prime p -> 0 <= eta2 p /\ eta2 p <= 1)
    (h1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p /\ eta1 p < 1)
    (h2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p /\ eta2 p < 1)
    (herr1 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta1 p - (p : Real) / nu - b1) <= C1 / (p : Real))
    (herr2 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta2 p - (p : Real) / nu - b2) <= C2 / (p : Real))
    (hscale1 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b1 + C1)) <= (p : Real))
    (hscale2 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b2 + C2)) <= (p : Real))
    (hlower1 : forall p, Nat.Prime p -> P < p ->
      (nu / 2) / (p : Real) <= eta1 p / (1 - eta1 p))
    (hlower2 : forall p, Nat.Prime p -> P < p ->
      (nu / 2) / (p : Real) <= eta2 p / (1 - eta2 p))
    (hupper1 : forall p, Nat.Prime p -> P < p ->
      eta1 p / (1 - eta1 p) <= 2 * nu / (p : Real))
    (hupper2 : forall p, Nat.Prime p -> P < p ->
      eta2 p / (1 - eta2 p) <= 2 * nu / (p : Real))
    (hodds1 : forall p, Nat.Prime p -> P < p ->
      abs (eta1 p / (1 - eta1 p) - nu / (p : Real)) <= K / (p : Real) ^ 2)
    (hodds2 : forall p, Nat.Prime p -> P < p ->
      abs (eta2 p / (1 - eta2 p) - nu / (p : Real)) <= K / (p : Real) ^ 2)
    (n : Nat -> Nat) (d1 d2 : Int)
    (hn2 : Filter.Eventually (fun k : Nat => 2 <= n k) atTop)
    (hratio : Tendsto (fun k : Nat =>
      Real.log (Real.log (n k : Real)) / Real.log (k : Real)) atTop (nhds 1))
    (hprime : Filter.Eventually (fun k : Nat => Nat.Prime (n k + 1)) atTop) :
    let w := fun k : Nat => (k : Real) / (nu * Real.log (k : Real))
    let s1 := (smallPrimePositiveFront P eta1).length
    let s2 := (smallPrimePositiveFront P eta2).length
    let E := (s1 : Real) - (s2 : Real) - (d1 : Real) + (d2 : Real)
    let B := ((smallPrimePositiveFront P eta1).prod / (smallPrimePositiveFront P eta2).prod) *
      primeComparisonEulerConstant P eta1 eta2 nu b1 b2
    0 < B /\
      Filter.Eventually (fun k : Nat =>
        0 < primeBernoulliDensity eta1 (shiftedPeakRank k d1) (n k + 1) /\
          0 < primeBernoulliDensity eta2 (shiftedPeakRank k d2) (n k + 1)) atTop /\
      Tendsto (fun k : Nat =>
        (primeBernoulliDensity eta1 (shiftedPeakRank k d1) (n k + 1) /
          primeBernoulliDensity eta2 (shiftedPeakRank k d2) (n k + 1)) /
            (Real.rpow (w k) E * Real.rpow (Real.log (k : Real)) (nu * (b2 - b1))))
              atTop (nhds B) := by
  let z := fun k : Nat => (k : Real) / (nu * Real.log (Real.log (n k : Real)))
  let w := fun k : Nat => (k : Real) / (nu * Real.log (k : Real))
  let s1 := (smallPrimePositiveFront P eta1).length
  let s2 := (smallPrimePositiveFront P eta2).length
  let E := (s1 : Real) - (s2 : Real) - (d1 : Real) + (d2 : Real)
  let theta := nu * (b2 - b1)
  let B := ((smallPrimePositiveFront P eta1).prod / (smallPrimePositiveFront P eta2).prod) *
    primeComparisonEulerConstant P eta1 eta2 nu b1 b2
  let Fz := fun k : Nat => Real.rpow (z k) E * Real.rpow (Real.log (z k)) theta
  let Fw := fun k : Nat => Real.rpow (w k) E * Real.rpow (Real.log (k : Real)) theta
  let U := fun k : Nat =>
    primeBernoulliDensity eta1 (shiftedPeakRank k d1) (n k + 1) /
      primeBernoulliDensity eta2 (shiftedPeakRank k d2) (n k + 1)
  have hb := Real.eventually_prime_cutoff_band_of_log_ratio n hn2 hratio
  have ht := regularPrimeLaws_tendsto_fixed_shift_density_tilt_scale P eta1 eta2
    nu b1 b2 C1 C2 K (1 / 2) 2 hP hnu hC1 hC2 hK (by norm_num) (by norm_num)
    hunit1 hunit2 h1 h2 herr1 herr2 hscale1 hscale2
    hlower1 hlower2 hupper1 hupper2 hodds1 hodds2 n d1 d2 hb hprime
  have hn := Real.primeTilt_sequence_normalizer_ratio nu E theta hnu n hn2 hratio
  have hz := Real.primeTilt_sequence_atTop_and_cutoff nu (1 / 2) 2 hnu (by norm_num)
    (by norm_num) n hb
  refine And.intro ht.1 (And.intro ht.2.1 ?_)
  have hm := ht.2.2.mul hn
  have hm' : Tendsto (fun k : Nat => (U k / Fz k) * (Fz k / Fw k)) atTop (nhds B) := by
    simpa only [mul_one] using hm
  apply hm'.congr'
  filter_upwards [ht.2.1, hz.1.eventually (eventually_gt_atTop (1 : Real)),
      eventually_ge_atTop 2] with k hk hzk hk2
  have hkp : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
  have hlk : 0 < Real.log (k : Real) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hzp : 0 < z k := zero_lt_one.trans hzk
  have hwp : 0 < w k := div_pos hkp (mul_pos hnu hlk)
  have hFz : Not (Fz k = 0) := ne_of_gt
    (mul_pos (Real.rpow_pos_of_pos hzp E)
      (Real.rpow_pos_of_pos (Real.log_pos hzk) theta))
  have hFw : Not (Fw k = 0) := ne_of_gt
    (mul_pos (Real.rpow_pos_of_pos hwp E) (Real.rpow_pos_of_pos hlk theta))
  have hD2 : Not (primeBernoulliDensity eta2 (shiftedPeakRank k d2) (n k + 1) = 0) :=
    ne_of_gt hk.2
  change (U k / Fz k) * (Fz k / Fw k) = U k / Fw k
  field_simp [hFz, hFw, hD2]

end PrimeFactorOscillations

