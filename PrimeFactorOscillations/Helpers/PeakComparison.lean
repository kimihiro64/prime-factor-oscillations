import PrimeFactorOscillations.Helpers.PeakDensityComparison
import PrimeFactorOscillations.Helpers.PeakLocalization

/-!
# General peak-height comparison with exceptional primes and rank shifts

General peak-height comparison with exceptional primes and rank shifts for the peak-height comparison of regular prime Bernoulli laws.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter Topology

namespace PrimeFactorOscillations

theorem regularPrimeLaws_peak_height_comparison_explicit_cutoff
    (P : Nat) (hP : 2 <= P) (eta1 eta2 : Nat -> Real) (nu b1 b2 C1 C2 : Real)
    (hnu : 0 < nu) (hC1 : 0 <= C1) (hC2 : 0 <= C2)
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
    (hoddsScale1 : forall p, Nat.Prime p -> P < p ->
      2 * nu * (C1 + abs (b1 - 1)) <= (p : Real))
    (hoddsScale2 : forall p, Nat.Prime p -> P < p ->
      2 * nu * (C2 + abs (b2 - 1)) <= (p : Real))
    (d1 d2 : Int) :
    let s1 := (smallPrimePositiveFront P eta1).length
    let s2 := (smallPrimePositiveFront P eta2).length
    let E := (s1 : Real) - (s2 : Real) - (d1 : Real) + (d2 : Real)
    let B := ((smallPrimePositiveFront P eta1).prod / (smallPrimePositiveFront P eta2).prod) *
      primeComparisonEulerConstant P eta1 eta2 nu b1 b2
    let F := fun k : Nat => Real.rpow ((k : Real) / (nu * Real.log (k : Real))) E *
      Real.rpow (Real.log (k : Real)) (nu * (b2 - b1))
    0 < B /\
      Filter.Eventually (fun k : Nat =>
        0 < primePeakHeight eta1 (shiftedPeakRank k d1) /\
          0 < primePeakHeight eta2 (shiftedPeakRank k d2)) atTop /\
      Tendsto (fun k : Nat =>
        (primePeakHeight eta1 (shiftedPeakRank k d1) /
          primePeakHeight eta2 (shiftedPeakRank k d2)) / F k) atTop (nhds B) := by
  let K1 := 2 * nu ^ 2 * (C1 + abs (b1 - 1))
  let K2 := 2 * nu ^ 2 * (C2 + abs (b2 - 1))
  let K := max K1 K2
  have hK1 : 0 <= K1 := by dsimp [K1]; positivity
  have hK2 : 0 <= K2 := by dsimp [K2]; positivity
  have hK : 0 <= K := hK1.trans (le_max_left _ _)
  have hb1 (p : Nat) (hp : Nat.Prime p) (hPp : P < p) :=
    Real.regular_localLaw_peak_bounds (p : Real) nu (eta1 p) b1 C1
      (by exact_mod_cast hp.one_le) hnu (h1 p hp hPp).1 (h1 p hp hPp).2
      hC1 (herr1 p hp hPp) (hscale1 p hp hPp) (hoddsScale1 p hp hPp)
  have hb2 (p : Nat) (hp : Nat.Prime p) (hPp : P < p) :=
    Real.regular_localLaw_peak_bounds (p : Real) nu (eta2 p) b2 C2
      (by exact_mod_cast hp.one_le) hnu (h2 p hp hPp).1 (h2 p hp hPp).2
      hC2 (herr2 p hp hPp) (hscale2 p hp hPp) (hoddsScale2 p hp hPp)

  have hEtaLo1 (p : Nat) (hp : Nat.Prime p) (hPp : P < p) :=
    (hb1 p hp hPp).1
  have hEtaHi1 (p : Nat) (hp : Nat.Prime p) (hPp : P < p) :=
    (hb1 p hp hPp).2.1
  have hOddsLo1 (p : Nat) (hp : Nat.Prime p) (hPp : P < p) :=
    (hb1 p hp hPp).2.2.1
  have hOddsHi1 (p : Nat) (hp : Nat.Prime p) (hPp : P < p) :=
    (hb1 p hp hPp).2.2.2.1
  have hOddsErr1 (p : Nat) (hp : Nat.Prime p) (hPp : P < p) :
      abs (eta1 p / (1 - eta1 p) - nu / (p : Real)) <= K / (p : Real) ^ 2 :=
    (hb1 p hp hPp).2.2.2.2.trans
      (div_le_div_of_nonneg_right (le_max_left K1 K2) (sq_nonneg _))

  have hEtaLo2 (p : Nat) (hp : Nat.Prime p) (hPp : P < p) :=
    (hb2 p hp hPp).1
  have hEtaHi2 (p : Nat) (hp : Nat.Prime p) (hPp : P < p) :=
    (hb2 p hp hPp).2.1
  have hOddsLo2 (p : Nat) (hp : Nat.Prime p) (hPp : P < p) :=
    (hb2 p hp hPp).2.2.1
  have hOddsHi2 (p : Nat) (hp : Nat.Prime p) (hPp : P < p) :=
    (hb2 p hp hPp).2.2.2.1
  have hOddsErr2 (p : Nat) (hp : Nat.Prime p) (hPp : P < p) :
      abs (eta2 p / (1 - eta2 p) - nu / (p : Real)) <= K / (p : Real) ^ 2 :=
    (hb2 p hp hPp).2.2.2.2.trans
      (div_le_div_of_nonneg_right (le_max_right K1 K2) (sq_nonneg _))

  let m1 := fun k : Nat => shiftedPeakRank k d1
  let m2 := fun k : Nat => shiftedPeakRank k d2
  let p1 := fun k : Nat => primePeakPrime eta1 (m1 k)
  let p2 := fun k : Nat => primePeakPrime eta2 (m2 k)
  let n1 := fun k : Nat => p1 k - 1
  let n2 := fun k : Nat => p2 k - 1
  let E := ((smallPrimePositiveFront P eta1).length : Real) -
    ((smallPrimePositiveFront P eta2).length : Real) - (d1 : Real) + (d2 : Real)
  let B := ((smallPrimePositiveFront P eta1).prod / (smallPrimePositiveFront P eta2).prod) *
    primeComparisonEulerConstant P eta1 eta2 nu b1 b2
  let F := fun k : Nat => Real.rpow ((k : Real) / (nu * Real.log (k : Real))) E *
    Real.rpow (Real.log (k : Real)) (nu * (b2 - b1))
  have hs1 := regularPrimeLaw_eventually_peakPrime_spec P hP eta1 nu K (nu / 2) (2 * nu)
    hnu hK (by positivity) (by positivity) hunit1 (fun p hp hPp => (h1 p hp hPp).2)
    hEtaLo1 hEtaHi1 hOddsHi1 hOddsErr1
  have hs2 := regularPrimeLaw_eventually_peakPrime_spec P hP eta2 nu K (nu / 2) (2 * nu)
    hnu hK (by positivity) (by positivity) hunit2 (fun p hp hPp => (h2 p hp hPp).2)
    hEtaLo2 hEtaHi2 hOddsHi2 hOddsErr2
  have hspec1 := (tendsto_shiftedPeakRank_atTop d1).eventually hs1
  have hspec2 := (tendsto_shiftedPeakRank_atTop d2).eventually hs2
  have hscaleSeq1 := regularPrimeLaw_peakPrime_cutoff_scale P hP eta1 nu K (nu / 2) (2 * nu)
    hnu hK (by positivity) (by positivity) hunit1 (fun p hp hPp => (h1 p hp hPp).2)
    hEtaLo1 hEtaHi1 hOddsHi1 hOddsErr1 d1
  have hscaleSeq2 := regularPrimeLaw_peakPrime_cutoff_scale P hP eta2 nu K (nu / 2) (2 * nu)
    hnu hK (by positivity) (by positivity) hunit2 (fun p hp hPp => (h2 p hp hPp).2)
    hEtaLo2 hEtaHi2 hOddsHi2 hOddsErr2 d2
  have hend1 : Filter.Eventually (fun k : Nat => n1 k + 1 = p1 k) atTop := by
    filter_upwards [hscaleSeq1.1] with k hk
    change 3 <= p1 k at hk
    change p1 k - 1 + 1 = p1 k
    omega
  have hend2 : Filter.Eventually (fun k : Nat => n2 k + 1 = p2 k) atTop := by
    filter_upwards [hscaleSeq2.1] with k hk
    change 3 <= p2 k at hk
    change p2 k - 1 + 1 = p2 k
    omega
  have hn1 : Filter.Eventually (fun k : Nat => 2 <= n1 k) atTop := by
    filter_upwards [hscaleSeq1.1] with k hk
    change 3 <= p1 k at hk
    change 2 <= p1 k - 1
    omega
  have hn2 : Filter.Eventually (fun k : Nat => 2 <= n2 k) atTop := by
    filter_upwards [hscaleSeq2.1] with k hk
    change 3 <= p2 k at hk
    change 2 <= p2 k - 1
    omega
  have hp1 : Filter.Eventually (fun k : Nat => Nat.Prime (n1 k + 1)) atTop := by
    filter_upwards [hend1, hspec1] with k hk hs
    rw [hk]
    exact hs.1.1
  have hp2 : Filter.Eventually (fun k : Nat => Nat.Prime (n2 k + 1)) atTop := by
    filter_upwards [hend2, hspec2] with k hk hs
    rw [hk]
    exact hs.1.1
  have hd1 := regularPrimeLaws_tendsto_fixed_shift_density_standard_scale P eta1 eta2
    nu b1 b2 C1 C2 K (by omega) hnu hC1 hC2 hK hunit1 hunit2 h1 h2 herr1 herr2
    hscale1 hscale2 hOddsLo1 hOddsLo2 hOddsHi1 hOddsHi2 hOddsErr1 hOddsErr2
    n1 d1 d2 hn1 hscaleSeq1.2 hp1
  have hd2 := regularPrimeLaws_tendsto_fixed_shift_density_standard_scale P eta1 eta2
    nu b1 b2 C1 C2 K (by omega) hnu hC1 hC2 hK hunit1 hunit2 h1 h2 herr1 herr2
    hscale1 hscale2 hOddsLo1 hOddsLo2 hOddsHi1 hOddsHi2 hOddsErr1 hOddsErr2
    n2 d1 d2 hn2 hscaleSeq2.2 hp2
  let u1 := fun k : Nat => primeBernoulliDensity eta1 (m1 k) (p1 k)
  let u2 := fun k : Nat => primeBernoulliDensity eta1 (m1 k) (p2 k)
  let v1 := fun k : Nat => primeBernoulliDensity eta2 (m2 k) (p1 k)
  let v2 := fun k : Nat => primeBernoulliDensity eta2 (m2 k) (p2 k)
  have hpos : Filter.Eventually (fun k : Nat =>
      0 <= u1 k /\ 0 < v1 k /\ 0 < v2 k /\ 0 < F k) atTop := by
    filter_upwards [hd1.2.1, hd2.2.1, hend1, hend2, eventually_ge_atTop 2] with
      k hk1 hk2 he1 he2 hk
    rw [he1] at hk1
    rw [he2] at hk2
    have hkp : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
    have hlk : 0 < Real.log (k : Real) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    have hF : 0 < F k := mul_pos
      (Real.rpow_pos_of_pos (div_pos hkp (mul_pos hnu hlk)) E)
      (Real.rpow_pos_of_pos hlk (nu * (b2 - b1)))
    exact And.intro hk1.1.le (And.intro hk1.2 (And.intro hk2.2 hF))
  have hmax : Filter.Eventually (fun k : Nat => u2 k <= u1 k /\ v1 k <= v2 k) atTop := by
    filter_upwards [hspec1, hspec2] with k hk1 hk2
    exact And.intro (hk1.1.2 (p2 k) hk2.1.1) (hk2.1.2 (p1 k) hk1.1.1)
  have hR1 : Tendsto (fun k : Nat => (u1 k / v1 k) / F k) atTop (nhds B) := by
    apply hd1.2.2.congr'
    filter_upwards [hend1] with k hk
    rw [hk]
  have hR2 : Tendsto (fun k : Nat => (u2 k / v2 k) / F k) atTop (nhds B) := by
    apply hd2.2.2.congr'
    filter_upwards [hend2] with k hk
    rw [hk]
  refine And.intro hd1.1 ?_
  constructor
  case left =>
    filter_upwards [hspec1, hspec2] with k hk1 hk2
    exact And.intro hk1.2 hk2.2
  case right =>
    exact Real.tendsto_two_maximum_ratio u1 u2 v1 v2 F B hpos hmax hR1 hR2

end PrimeFactorOscillations
namespace PrimeFactorOscillations

/-- The paper's rank k uses coefficient index k - 1. -/
noncomputable def primeRankPeakHeight (eta : Nat -> Real) (k : Nat) : Real :=
  primePeakHeight eta (k - 1)

theorem eventually_shiftedPeakRank_pred (h : Int) :
    Filter.Eventually (fun k : Nat =>
      shiftedPeakRank k h - 1 = shiftedPeakRank k (h - 1)) atTop := by
  filter_upwards [eventually_shiftedPeakRank_add (h - 1) 1] with k hk
  have he : shiftedPeakRank k h = shiftedPeakRank k (h - 1) + 1 := by
    simpa using hk
  omega

theorem regularPrimeLaws_rank_peak_height_comparison_explicit_cutoff
    (P : Nat) (hP : 2 <= P) (eta1 eta2 : Nat -> Real) (nu b1 b2 C1 C2 : Real)
    (hnu : 0 < nu) (hC1 : 0 <= C1) (hC2 : 0 <= C2)
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
    (hoddsScale1 : forall p, Nat.Prime p -> P < p ->
      2 * nu * (C1 + abs (b1 - 1)) <= (p : Real))
    (hoddsScale2 : forall p, Nat.Prime p -> P < p ->
      2 * nu * (C2 + abs (b2 - 1)) <= (p : Real))
    (d1 d2 : Int) :
    let s1 := (smallPrimePositiveFront P eta1).length
    let s2 := (smallPrimePositiveFront P eta2).length
    let E := (s1 : Real) - (s2 : Real) - (d1 : Real) + (d2 : Real)
    let B := ((smallPrimePositiveFront P eta1).prod / (smallPrimePositiveFront P eta2).prod) *
      primeComparisonEulerConstant P eta1 eta2 nu b1 b2
    let F := fun k : Nat => Real.rpow ((k : Real) / (nu * Real.log (k : Real))) E *
      Real.rpow (Real.log (k : Real)) (nu * (b2 - b1))
    0 < B /\
      Filter.Eventually (fun k : Nat =>
        0 < primeRankPeakHeight eta1 (shiftedPeakRank k d1) /\
          0 < primeRankPeakHeight eta2 (shiftedPeakRank k d2)) atTop /\
      Tendsto (fun k : Nat =>
        (primeRankPeakHeight eta1 (shiftedPeakRank k d1) /
          primeRankPeakHeight eta2 (shiftedPeakRank k d2)) / F k) atTop (nhds B) := by
  have ht := regularPrimeLaws_peak_height_comparison_explicit_cutoff P hP eta1 eta2
    nu b1 b2 C1 C2 hnu hC1 hC2 hunit1 hunit2 h1 h2 herr1 herr2
    hscale1 hscale2 hoddsScale1 hoddsScale2 (d1 - 1) (d2 - 1)
  dsimp only at ht
  dsimp only
  have he : ((smallPrimePositiveFront P eta1).length : Real) -
      ((smallPrimePositiveFront P eta2).length : Real) - ((d1 - 1 : Int) : Real) +
      ((d2 - 1 : Int) : Real) =
      ((smallPrimePositiveFront P eta1).length : Real) -
      ((smallPrimePositiveFront P eta2).length : Real) - (d1 : Real) + (d2 : Real) := by
    simp only [Int.cast_sub, Int.cast_one]
    ring
  rw [he] at ht
  refine And.intro ht.1 ?_
  constructor
  case left =>
    filter_upwards [ht.2.1, eventually_shiftedPeakRank_pred d1,
      eventually_shiftedPeakRank_pred d2] with k hk hi hj
    simpa only [primeRankPeakHeight, hi, hj] using hk
  case right =>
    apply ht.2.2.congr'
    filter_upwards [eventually_shiftedPeakRank_pred d1,
      eventually_shiftedPeakRank_pred d2] with k hi hj
    simp only [primeRankPeakHeight, hi, hj]

theorem regularPrimeLaws_peak_height_comparison
    (P0 : Nat) (eta1 eta2 : Nat -> Real) (nu b1 b2 C1 C2 : Real)
    (hnu : 0 < nu) (hC1 : 0 <= C1) (hC2 : 0 <= C2)
    (hunit1 : forall p, Nat.Prime p -> 0 <= eta1 p /\ eta1 p <= 1)
    (hunit2 : forall p, Nat.Prime p -> 0 <= eta2 p /\ eta2 p <= 1)
    (h1 : forall p, Nat.Prime p -> P0 < p -> 0 < eta1 p /\ eta1 p < 1)
    (h2 : forall p, Nat.Prime p -> P0 < p -> 0 < eta2 p /\ eta2 p < 1)
    (herr1 : forall p, Nat.Prime p -> P0 < p ->
      abs (1 / eta1 p - (p : Real) / nu - b1) <= C1 / (p : Real))
    (herr2 : forall p, Nat.Prime p -> P0 < p ->
      abs (1 / eta2 p - (p : Real) / nu - b2) <= C2 / (p : Real))
    : exists N : Nat, P0 <= N /\ 2 <= N /\
      forall P : Nat, N <= P -> forall d1 d2 : Int,
    let s1 := (smallPrimePositiveFront P eta1).length
    let s2 := (smallPrimePositiveFront P eta2).length
    let E := (s1 : Real) - (s2 : Real) - (d1 : Real) + (d2 : Real)
    let B := ((smallPrimePositiveFront P eta1).prod / (smallPrimePositiveFront P eta2).prod) *
      primeComparisonEulerConstant P eta1 eta2 nu b1 b2
    let F := fun k : Nat => Real.rpow ((k : Real) / (nu * Real.log (k : Real))) E *
      Real.rpow (Real.log (k : Real)) (nu * (b2 - b1))
    0 < B /\
      Filter.Eventually (fun k : Nat =>
        0 < primeRankPeakHeight eta1 (shiftedPeakRank k d1) /\
          0 < primeRankPeakHeight eta2 (shiftedPeakRank k d2)) atTop /\
      Tendsto (fun k : Nat =>
        (primeRankPeakHeight eta1 (shiftedPeakRank k d1) /
          primeRankPeakHeight eta2 (shiftedPeakRank k d2)) / F k) atTop (nhds B) := by
  let S1 := 2 * (nu * (abs b1 + C1))
  let S2 := 2 * (nu * (abs b2 + C2))
  let O1 := 2 * nu * (C1 + abs (b1 - 1))
  let O2 := 2 * nu * (C2 + abs (b2 - 1))
  let M := max (max (P0 : Real) 2) (max (max S1 S2) (max O1 O2))
  choose N hN using exists_nat_gt M
  have hp0 : (P0 : Real) <= M := (le_max_left _ _).trans (le_max_left _ _)
  have htwo : (2 : Real) <= M := (le_max_right _ _).trans (le_max_left _ _)
  have hs1 : S1 <= M :=
    (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hs2 : S2 <= M :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have ho1 : O1 <= M :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have ho2 : O2 <= M :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hP0N : P0 <= N := by exact_mod_cast hp0.trans hN.le
  have h2N : 2 <= N := by exact_mod_cast htwo.trans hN.le
  refine Exists.intro N (And.intro hP0N (And.intro h2N ?_))
  intro P hNP d1 d2
  have hinherit : forall p : Nat, P < p -> P0 < p := by omega
  have hsc1 : forall p : Nat, Nat.Prime p -> P < p ->
      2 * (nu * (abs b1 + C1)) <= (p : Real) := by
    intro p _ hp
    exact hs1.trans (hN.le.trans (by exact_mod_cast (show N <= p by omega)))
  have hsc2 : forall p : Nat, Nat.Prime p -> P < p ->
      2 * (nu * (abs b2 + C2)) <= (p : Real) := by
    intro p _ hp
    exact hs2.trans (hN.le.trans (by exact_mod_cast (show N <= p by omega)))
  have hoc1 : forall p : Nat, Nat.Prime p -> P < p ->
      2 * nu * (C1 + abs (b1 - 1)) <= (p : Real) := by
    intro p _ hp
    exact ho1.trans (hN.le.trans (by exact_mod_cast (show N <= p by omega)))
  have hoc2 : forall p : Nat, Nat.Prime p -> P < p ->
      2 * nu * (C2 + abs (b2 - 1)) <= (p : Real) := by
    intro p _ hp
    exact ho2.trans (hN.le.trans (by exact_mod_cast (show N <= p by omega)))
  exact regularPrimeLaws_rank_peak_height_comparison_explicit_cutoff
    P (h2N.trans hNP) eta1 eta2 nu b1 b2 C1 C2 hnu hC1 hC2 hunit1 hunit2
    (fun p hp hPp => h1 p hp (hinherit p hPp))
    (fun p hp hPp => h2 p hp (hinherit p hPp))
    (fun p hp hPp => herr1 p hp (hinherit p hPp))
    (fun p hp hPp => herr2 p hp (hinherit p hPp))
    hsc1 hsc2 hoc1 hoc2 d1 d2

theorem primeComparisonEulerConstant_eq_literal
    (P : Nat) (eta1 eta2 : Nat -> Real) (nu b1 b2 C1 C2 : Real)
    (hnu : 0 < nu) (hC1 : 0 <= C1) (hC2 : 0 <= C2)
    (h1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p)
    (h2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p)
    (herr1 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta1 p - (p : Real) / nu - b1) <= C1 / (p : Real))
    (herr2 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta2 p - (p : Real) / nu - b2) <= C2 / (p : Real))
    (hscale1 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b1 + C1)) <= (p : Real))
    (hscale2 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b2 + C2)) <= (p : Real)) :
    primeComparisonEulerConstant P eta1 eta2 nu b1 b2 =
      Real.rpow (Real.exp Real.eulerMascheroniConstant *
        (P + 1).primesBelow.prod (fun p => 1 - 1 / (p : Real))) (nu * (b2 - b1)) *
          tprod (fun p : Nat => if Nat.Prime p /\ P < p then
            (eta1 p / eta2 p) *
              Real.rpow (1 - 1 / (p : Real)) (nu * (b2 - b1)) else 1) := by
  exact regularPrimeLaws_euler_constant_eq P eta1 eta2 nu b1 b2 C1 C2
    hnu hC1 hC2 h1 h2 herr1 herr2 hscale1 hscale2

end PrimeFactorOscillations

