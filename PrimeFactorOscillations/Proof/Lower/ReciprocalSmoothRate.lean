import PrimeFactorOscillations.Helpers.GapFrequencyBounds
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Exp.CeilDoubleExp
import PrimeFactorOscillations.Proof.Lower.ReciprocalSmoothWindows

/-! # Recurrent prime-gap frequency gives the full lower reversal coefficient -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.ReciprocalSmoothLaw

private theorem gap_frequency_frequently_large
    (H : Nat) (g : Real) (hg : g < primeGapFrequencyExponent H) :
    forall Y0 : Nat, exists Y : Nat, Y0 <= Y /\
      Real.exp (Real.exp (g * Real.log (Real.log (Y : Real)))) <
        3 + (primeGapFrequencyCount H Y : Real) := by
  have model : exists A : Real, exists K : Nat, forall X : Nat, K <= X ->
      3 + (primeGapFrequencyCount H X : Real) <=
        Real.exp (Real.exp (A * Real.log (Real.log (X : Real)))) :=
    Exists.intro (2 : Real) (Real.eventually_linear_count_le_double_exp_log_log
      (fun X => (primeGapFrequencyCount H X : Real)) (fun X => Nat.cast_nonneg _)
      (fun X => by exact_mod_cast primeGapFrequencyCount_le H X) 2 (by norm_num))
  have hh := Real.le_limsup_log_log_div_gauge_iff
    (fun X => (primeGapFrequencyCount H X : Real))
    (fun X : Nat => Real.log (Real.log (X : Real)))
    (fun X => Nat.cast_nonneg _) (Real.eventually_le_log_log_nat 1) model
    (primeGapFrequencyExponent H)
  exact hh.mp (le_refl _) g hg

/-- Recurrent, possibly irregular gap supply is enough. The endpoint-to-rank
rounding and the initial segment/factorial-cell losses are handled uniformly. -/
theorem frequently_reversal_supply_at_gap_rate
    (law : ReciprocalSmoothLaw) (H : Nat) (a g v0 v : Real)
    (ha : 0 < a) (hg : 0 < g) (hgamma : g < primeGapFrequencyExponent H)
    (hv0 : 0 < v0) (hvv : v0 < v) (hmargin : ((H : Real) + law.nu) * v < 1)
    (hag : a < g * v0) :
    forall K : Nat, exists k : Nat, K <= k /\ exists m : Nat,
      Real.exp (Real.exp (a * k)) <= (m : Real) /\
        HasAtLeastReversals (law.rankDensity k) m := by
  let u : Real := a / 4
  let w : Real := a / 2
  let b : Real := (a + g * v0) / 2
  have hu : 0 < u := by dsimp only [u]; positivity
  have huw : u < w := by dsimp only [u, w]; linarith
  have hwa : w < a := by dsimp only [w]; linarith
  have hab : a < b := by dsimp only [b]; linarith
  have hbg : b < g * v0 := by dsimp only [b]; linarith
  choose L0 hL0 using exists_nat_gt (2 / u)
  let L := max (H + 1) L0
  have hL : 2 / u < (L : Real) := hL0.trans_le (by exact_mod_cast le_max_right (H + 1) L0)
  have hHL : H + 1 <= L := le_max_left _ _
  let B := 2 * (Nat.factorial L + H)
  have hB : (0 : Real) <= B := Nat.cast_nonneg B
  choose P hP using law.reversal_counts_of_gap_frequency_band H L u v hu
    (hv0.trans hvv) hmargin hL hHL
  choose KB hKB using Filter.eventually_atTop.mp hP
  choose KX hKX using Real.eventually_ceil_double_exp_scale_bounds u w hu huw
    (max P (Nat.factorial L + 2))
  choose KY hKY using Real.eventually_mul_double_exp_add_one_le v0 v ((H : Real) + 1)
    hv0.le hvv (by positivity)
  choose KC hKC using Real.eventually_mul_double_exp_add_one_le a b ((B : Real) + 4)
    ha.le hab (by positivity)
  choose KR hKR using exists_nat_gt ((g * v0) / (g * v0 - b))
  intro K
  let R := max 1 (max K (max KB (max KX (max KY (max KC KR)))))
  have hR1 : 1 <= R := by omega
  choose Y0 hY0 using Real.eventually_le_log_log_nat (v0 * R)
  choose Y hY using gap_frequency_frequently_large H g hgamma (max 3 Y0)
  have hY3 : (3 : Real) <= Y := by exact_mod_cast (le_max_left 3 Y0).trans hY.1
  have hYpos : (0 : Real) < Y := by linarith
  have hlogY : 0 < Real.log (Y : Real) := Real.log_pos (by linarith)
  let t := Real.log (Real.log (Y : Real))
  have ht : v0 * R <= t := hY0 Y ((le_max_right 3 Y0).trans hY.1)
  have htpos : 0 < t := by
    have hRreal : (1 : Real) <= R := by exact_mod_cast hR1
    have hvr := mul_le_mul_of_nonneg_left hRreal hv0.le
    nlinarith only [ht, hvr, hv0]
  let k := Nat.ceil (t / v0)
  have hceil : t / v0 <= (k : Real) := Nat.le_ceil _
  have hceilHi : (k : Real) < t / v0 + 1 := Nat.ceil_lt_add_one (div_nonneg htpos.le hv0.le)
  have hcancel : (t / v0) * v0 = t := by field_simp [ne_of_gt hv0]
  have hlo := mul_le_mul_of_nonneg_right hceil hv0.le
  have hhi := mul_lt_mul_of_pos_right hceilHi hv0
  rw [hcancel] at hlo
  have htupper : t <= v0 * k := by nlinarith only [hlo]
  have htlow : v0 * k - v0 < t := by nlinarith only [hhi, hcancel]
  have hkR : R <= k := by
    have hr : (R : Real) <= k := by nlinarith only [ht, htupper, hv0]
    exact_mod_cast hr
  have hkK : K <= k := by omega
  have hkB : KB <= k := by omega
  have hkX : KX <= k := by omega
  have hkY : KY <= k := by omega
  have hkC : KC <= k := by omega
  have hkRR : (KR : Real) <= k := by exact_mod_cast (show KR <= k by omega)
  have hreserve := mul_le_mul_of_nonneg_right (hKR.le.trans hkRR)
    (show 0 <= g * v0 - b by linarith)
  have hrescancel : ((g * v0) / (g * v0 - b)) * (g * v0 - b) = g * v0 := by
    field_simp [ne_of_gt (show 0 < g * v0 - b by linarith)]
  rw [hrescancel] at hreserve
  have hgt := mul_lt_mul_of_pos_left htlow hg
  have hscale : b * k <= g * t := by nlinarith only [hreserve, hgt]
  have hsupply : Real.exp (Real.exp (b * k)) <
      3 + (primeGapFrequencyCount H Y : Real) :=
    (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hscale)).trans_lt hY.2
  let X := Nat.ceil (Real.exp (Real.exp (u * k))) + 1
  have hX := hKX k hkX
  have hXP : P <= X := (le_max_left P (Nat.factorial L + 2)).trans hX.1
  have hXF : Nat.factorial L + 2 <= X :=
    (le_max_right P (Nat.factorial L + 2)).trans hX.1
  have hX3 : 3 <= X := by have hfac := Nat.factorial_pos L; omega
  have hYbound : (Y : Real) <= Real.exp (Real.exp (v0 * k)) := by
    have he := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr htupper)
    dsimp only [t] at he
    rwa [Real.exp_log hlogY, Real.exp_log hYpos] at he
  have hEnd : ((Y + H : Nat) : Real) <= Real.exp (Real.exp (v * k)) := by
    have hc := hKY k hkY
    have hH : (0 : Real) <= H := Nat.cast_nonneg H
    have hE := Real.exp_pos (Real.exp (v0 * k))
    have hmul := mul_nonneg hH hE.le
    push_cast
    nlinarith only [hYbound, hc, hH, hmul]
  have hband : forall p : Nat, X <= p -> p <= Y + H ->
      u * k <= Real.log (Real.log (p - 1 : Nat)) /\
        Real.log (Real.log (p - 1 : Nat)) <= v * k := by
    intro p hp hpY
    have hXp : (1 : Real) < ((X - 1 : Nat) : Real) := by
      exact_mod_cast (show 1 < X - 1 by omega)
    have hpref : ((X - 1 : Nat) : Real) <= ((p - 1 : Nat) : Real) := by
      exact_mod_cast Nat.sub_le_sub_right hp 1
    have hp1 : (1 : Real) < ((p - 1 : Nat) : Real) := hXp.trans_le hpref
    have hlow := Real.log_le_log (Real.log_pos hXp)
      (Real.log_le_log (by linarith) hpref)
    have hpEnd : ((p - 1 : Nat) : Real) <= ((Y + H : Nat) : Real) := by
      exact_mod_cast (show p - 1 <= Y + H by omega)
    have hlog := Real.log_le_log (by linarith : (0 : Real) < ((p - 1 : Nat) : Real))
      (hpEnd.trans hEnd)
    rw [Real.log_exp] at hlog
    have hupp := Real.log_le_log (Real.log_pos hp1) hlog
    rw [Real.log_exp] at hupp
    exact And.intro (hX.2.1.trans hlow) hupp
  choose m hm using hKB k hkB X Y hXP hXF hband
  have hcount : (primeGapFrequencyCount H Y : Real) <=
      (X : Real) + (B : Real) * ((m : Real) + 1) := by
    exact_mod_cast hm.1
  have hXsmall : (X : Real) <= Real.exp (Real.exp (a * k)) :=
    hX.2.2.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hwa.le (Nat.cast_nonneg k))))
  have hbudget := hKC k hkC
  have hmLarge : Real.exp (Real.exp (a * k)) <= (m : Real) := by
    by_contra hn
    have hmle := (lt_of_not_ge hn).le
    have hmul := mul_le_mul_of_nonneg_left hmle hB
    have hE := Real.exp_pos (Real.exp (a * k))
    nlinarith only [hbudget, hsupply, hcount, hXsmall, hmul, hE]
  exact Exists.intro k (And.intro hkK (Exists.intro m (And.intro hmLarge hm.2)))

/-- Every positive coefficient strictly below the gap-frequency quotient
occurs at arbitrarily high ranks, for the actual reciprocal-smooth law. -/
theorem frequently_reversal_supply_below_gap_exponent
    (law : ReciprocalSmoothLaw) (H : Nat) (a : Real) (ha : 0 < a)
    (haH : a < primeGapFrequencyExponent H / ((H : Real) + law.nu)) :
    forall K : Nat, exists k : Nat, K <= k /\ exists m : Nat,
      Real.exp (Real.exp (a * k)) <= (m : Real) /\
        HasAtLeastReversals (law.rankDensity k) m := by
  let d : Real := (H : Real) + law.nu
  have hd : 0 < d := by
    dsimp only [d]
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg H) law.nu_pos
  have hquot := mul_lt_mul_of_pos_right haH hd
  have hcancel : (primeGapFrequencyExponent H / d) * d = primeGapFrequencyExponent H := by
    field_simp [ne_of_gt hd]
  change a * d < (primeGapFrequencyExponent H / d) * d at hquot
  rw [hcancel] at hquot
  choose g hg using exists_between hquot
  have hgpos : 0 < g := (mul_pos ha hd).trans hg.1
  have hfrac : a / g < 1 / d := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) (mul_pos hgpos hd).le
    have hc1 : (1 / d) * (g * d) = g := by field_simp [ne_of_gt hd]
    have hc2 : (a / g) * (g * d) = a * d := by field_simp [ne_of_gt hgpos]
    rw [hc1, hc2] at hm
    exact (not_lt_of_ge hm) hg.1
  choose v0 hv0 using exists_between hfrac
  have hv0pos : 0 < v0 := (div_pos ha hgpos).trans hv0.1
  choose v hv using exists_between hv0.2
  have hmargin : ((H : Real) + law.nu) * v < 1 := by
    have hm := mul_lt_mul_of_pos_right hv.2 hd
    have hc : (1 / d) * d = (1 : Real) := by field_simp [ne_of_gt hd]
    rw [hc] at hm
    change d * v < 1
    simpa only [mul_comm] using hm
  have hag : a < g * v0 := by
    have hm := mul_lt_mul_of_pos_right hv0.1 hgpos
    have hc : (a / g) * g = a := by field_simp [ne_of_gt hgpos]
    rw [hc] at hm
    simpa only [mul_comm] using hm
  exact law.frequently_reversal_supply_at_gap_rate H a g v0 v ha hgpos hg.2
    hv0pos hv.1 hmargin hag

end PrimeFactorOscillations.ReciprocalSmoothLaw
