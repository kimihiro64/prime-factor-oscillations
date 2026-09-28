import PrimeFactorOscillations.Helpers.GapSpectrum
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Exp.CeilDoubleExp
import PrimeFactorOscillations.Proof.Upper.ReciprocalSmoothEnvelope

/-! # The actual prime-gap spectrum bounds reciprocal-smooth reversal growth -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.ReciprocalSmoothLaw

open PrimeFactorUnimodality

private theorem gap_count_at_ceil_scale
    (H : Nat) (a b : Real) (ha : 0 < a)
    (hab : primeGapFrequencyExponent H * a < b) :
    exists K : Nat, forall k : Nat, K <= k ->
      (primeGapFrequencyCount H (Nat.ceil (Real.exp (Real.exp (a * k))) + 1) : Real) <=
        Real.exp (Real.exp (b * k)) := by
  let gamma := primeGapFrequencyExponent H
  have hg := primeGapFrequencyExponent_bounds H
  change 0 <= gamma /\ gamma <= 1 at hg
  change gamma * a < b at hab
  let d : Real := min 1 ((b - gamma * a) / (2 * (a + 2)))
  have hd : 0 < d := by
    apply lt_min
    next => norm_num
    next => exact div_pos (by linarith) (by positivity)
  have hd1 : d <= 1 := min_le_left _ _
  have hdq : d <= (b - gamma * a) / (2 * (a + 2)) := min_le_right _ _
  have hden : 0 < 2 * (a + 2) := by positivity
  have hcost := mul_le_mul_of_nonneg_right hdq hden.le
  have hc : ((b - gamma * a) / (2 * (a + 2))) * (2 * (a + 2)) =
      b - gamma * a := by field_simp [ne_of_gt hden]
  rw [hc] at hcost
  have hprod := mul_nonneg hd.le (show 0 <= 2 - gamma - d by linarith only [hg.2, hd1])
  have hcoef : (gamma + d) * (a + d) < b := by
    nlinarith only [hcost, hprod, hab]
  have model : exists A : Real, exists K : Nat, forall X : Nat, K <= X ->
      3 + (primeGapFrequencyCount H X : Real) <=
        Real.exp (Real.exp (A * Real.log (Real.log (X : Real)))) :=
    Exists.intro (2 : Real) (Real.eventually_linear_count_le_double_exp_log_log
      (fun X => (primeGapFrequencyCount H X : Real)) (fun X => Nat.cast_nonneg _)
      (fun X => by exact_mod_cast primeGapFrequencyCount_le H X) 2 (by norm_num))
  have hgauge := Real.limsup_log_log_div_gauge_le_iff
    (fun X => (primeGapFrequencyCount H X : Real))
    (fun X : Nat => Real.log (Real.log (X : Real)))
    (fun X => Nat.cast_nonneg _) (Real.eventually_le_log_log_nat 1) model gamma
  have hself : Filter.limsup
      (fun X : Nat => Real.log (Real.log (3 + (primeGapFrequencyCount H X : Real))) /
        Real.log (Real.log (X : Real))) Filter.atTop <= gamma := le_refl _
  choose KX hKX using hgauge.mp hself (gamma + d) (by linarith)
  choose K hK using Real.eventually_ceil_double_exp_scale_bounds a (a + d) ha
    (by linarith) (max 3 KX)
  refine Exists.intro K ?_
  intro k hk
  let U := Nat.ceil (Real.exp (Real.exp (a * k))) + 1
  have hU := hK k hk
  have hUX : KX <= U := (le_max_right 3 KX).trans hU.1
  have hU3 : (3 : Real) <= U := by exact_mod_cast (le_max_left 3 KX).trans hU.1
  have hlog := Real.log_le_log (show (0 : Real) < U by linarith) hU.2.2
  rw [Real.log_exp] at hlog
  have hloglog := Real.log_le_log (Real.log_pos (show (1 : Real) < U by linarith)) hlog
  rw [Real.log_exp] at hloglog
  have hscaled := mul_le_mul_of_nonneg_left hloglog (show 0 <= gamma + d by linarith)
  have hco := mul_le_mul_of_nonneg_right hcoef.le (Nat.cast_nonneg k : (0 : Real) <= k)
  have hexp := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (hscaled.trans
    (by simpa only [mul_assoc] using hco)))
  have hcount := hKX U hUX
  change (primeGapFrequencyCount H U : Real) <= _
  linarith only [hcount, hexp]

/-- Every sufficiently high-rank reversal family has size at most the
double exponential of any coefficient above the actual prime-gap spectrum.
This uses no positive lower estimate for prime gaps. -/
theorem reversal_counts_eventually_le_spectrum
    (law : ReciprocalSmoothLaw) (b : Real) (hb : primeGapSpectrum law.nu < b) :
    exists K : Nat, forall k : Nat, K <= k -> forall m : Nat,
      HasAtLeastReversals (law.rankDensity k) m ->
      (m : Real) <= Real.exp (Real.exp (b * k)) := by
  classical
  have hnu := law.nu_pos
  let S := primeGapSpectrum law.nu
  have hS : 0 <= S := (primeGapSpectrum_bounds law.nu law.nu_pos).1
  change S < b at hb
  let A : Real := (S + b) / 2
  let e : Real := (A - S) / 2
  let u : Real := A / 2
  have hA : 0 < A := by dsimp only [A]; linarith
  have hAb : A < b := by dsimp only [A]; linarith
  have he : 0 < e := by dsimp only [e, A]; linarith
  have hu : 0 < u := by dsimp only [u]; linarith
  have huA : u < A := by dsimp only [u]; linarith
  have hSe : S + e < A := by dsimp only [e, A]; linarith
  choose J hJ using exists_nat_gt (1 / u)
  have hJmul := mul_lt_mul_of_pos_right hJ hu
  have hiu : (1 / u) * u = (1 : Real) := by field_simp [ne_of_gt hu]
  rw [hiu] at hJmul
  have hJden : 0 < (J : Real) + 1 + law.nu := by positivity
  have hJinv : (1 / ((J : Real) + 1 + law.nu)) * ((J : Real) + 1 + law.nu) = (1 : Real) := by
    field_simp [ne_of_gt hJden]
  have hJu : 1 / ((J : Real) + 1 + law.nu) < u := by
    by_contra hn
    have hmul := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hJden.le
    rw [hJinv] at hmul
    nlinarith only [hmul, hJmul, hu, hnu]
  choose K0 Q hbase using reversal_count_le_sharp_gap_envelope law J u e hJu he
  choose KT hKT using Real.eventually_ceil_double_exp_scale_bounds u A hu huA Q
  let c := fun g : Nat => 1 / ((g : Real) + law.nu) + e
  let U := fun g k : Nat => Nat.ceil (Real.exp (Real.exp (c g * k))) + 1
  have hgrowth : forall g : Nat, exists K : Nat, forall k : Nat, K <= k ->
      Q <= U g k /\ c g * k <= Real.log (Real.log (U g k - 1 : Nat)) /\
      (primeGapFrequencyCount g (U g k) : Real) <= Real.exp (Real.exp (A * k)) := by
    intro g
    have hden : 0 < (g : Real) + law.nu := by positivity
    have hcpos : 0 < c g := by dsimp only [c]; positivity
    have hgamma := primeGapFrequencyExponent_bounds g
    have hratio := primeGapFrequency_ratio_le_spectrum g law.nu law.nu_pos
    change primeGapFrequencyExponent g / ((g : Real) + law.nu) <= S at hratio
    have hsmall := mul_nonneg (show 0 <= 1 - primeGapFrequencyExponent g by linarith)
      he.le
    have hcoef : primeGapFrequencyExponent g * c g < A := by
      dsimp only [c]
      rw [mul_add, mul_one_div]
      nlinarith only [hratio, hsmall, hSe]
    choose KG hKG using gap_count_at_ceil_scale g (c g) A hcpos hcoef
    choose KU hKU using Real.eventually_ceil_double_exp_scale_bounds
      (c g) (c g + 1) hcpos (by linarith) Q
    refine Exists.intro (max KG KU) ?_
    intro k hk
    have hcut := hKU k ((le_max_right KG KU).trans hk)
    exact And.intro hcut.1 (And.intro hcut.2.1 (hKG k ((le_max_left KG KU).trans hk)))
  choose Ks hKs using hgrowth
  let KC := (Finset.range (J + 1)).sup Ks
  choose KL hKL using Real.eventually_mul_double_exp_add_one_le A b ((J : Real) + 2)
    hA.le hAb (by positivity)
  refine Exists.intro (max K0 (max KT (max KC KL))) ?_
  intro k hk m hm
  have hk0 : K0 <= k := by omega
  have hkT : KT <= k := by omega
  have hkC : KC <= k := by omega
  have hkL : KL <= k := by omega
  let T := Nat.ceil (Real.exp (Real.exp (u * k))) + 1
  have hT := hKT k hkT
  have hall : forall g : Nat, g <= J ->
      Q <= U g k /\ c g * k <= Real.log (Real.log (U g k - 1 : Nat)) /\
      (primeGapFrequencyCount g (U g k) : Real) <= Real.exp (Real.exp (A * k)) := by
    intro g hg
    have hgm : Membership.mem (Finset.range (J + 1)) g := Finset.mem_range.mpr (by omega)
    have hgK : Ks g <= KC := Finset.le_sup (f := Ks) hgm
    exact hKs g k (hgK.trans hkC)
  have hcount := hbase.2.2 k hk0 T hT.1 hT.2.1 (fun g => U g k)
    (fun g hg => And.intro (hall g hg).1 (hall g hg).2.1) m hm
  change m <= T + (Finset.range (J + 1)).sum (fun g => primeGapFrequencyCount g (U g k))
    at hcount
  have hcountR : (m : Real) <= (T : Real) +
      (Finset.range (J + 1)).sum (fun g => (primeGapFrequencyCount g (U g k) : Real)) := by
    exact_mod_cast hcount
  have hsum : (Finset.range (J + 1)).sum
      (fun g => (primeGapFrequencyCount g (U g k) : Real)) <=
      ((J : Real) + 1) * Real.exp (Real.exp (A * k)) := by
    calc
      _ <= (Finset.range (J + 1)).sum (fun _ => Real.exp (Real.exp (A * k))) := by
        apply Finset.sum_le_sum
        intro g hg
        exact (hall g (by have hh := Finset.mem_range.mp hg; omega)).2.2
      _ = _ := by simp
  have hbudget := hKL k hkL
  have hJnon : (0 : Real) <= J := Nat.cast_nonneg J
  have hTupper : (T : Real) <= Real.exp (Real.exp (A * k)) := hT.2.2
  nlinarith only [hcountR, hsum, hbudget, hTupper, hJnon]

/-- The sharp upper rate applies to any sequence of actual reversal-family
sizes, hence in particular to the attained maximal reversal numbers. -/
theorem reversal_limsup_le_spectrum
    (law : ReciprocalSmoothLaw) (n : Nat -> Nat)
    (hn : exists K : Nat, forall k : Nat, K <= k ->
      HasAtLeastReversals (law.rankDensity k) (n k)) :
    Filter.limsup (fun k : Nat =>
      Real.log (Real.log (3 + (n k : Real))) / k) Filter.atTop <= primeGapSpectrum law.nu := by
  choose Kn hKn using hn
  have hbound : forall b : Real, primeGapSpectrum law.nu < b ->
      exists K : Nat, forall k : Nat, K <= k ->
        (n k : Real) <= Real.exp (Real.exp (b * k)) := by
    intro b hb
    choose K hK using reversal_counts_eventually_le_spectrum law b hb
    refine Exists.intro (max Kn K) ?_
    intro k hk
    exact hK k ((le_max_right Kn K).trans hk) (n k)
      (hKn k ((le_max_left Kn K).trans hk))
  have hS := (primeGapSpectrum_bounds law.nu law.nu_pos).1
  have hmodel : exists A : Real, 0 <= A /\ exists K : Nat,
      forall k : Nat, K <= k -> (n k : Real) <= Real.exp (Real.exp (A * k)) :=
    Exists.intro (primeGapSpectrum law.nu + 1) (And.intro (by linarith)
      (hbound (primeGapSpectrum law.nu + 1) (by linarith)))
  exact (Real.limsup_log_log_rate_le_iff_eventual_double_exp
    (fun k => (n k : Real)) (fun k => Nat.cast_nonneg _) hmodel
    (primeGapSpectrum law.nu) hS).mpr hbound

end PrimeFactorOscillations.ReciprocalSmoothLaw
