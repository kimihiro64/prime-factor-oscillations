import PrimeFactorOscillations.Proof.Lower.AdditiveBandSigns

/-! # Late ascents from recurring short prime gaps -/

set_option autoImplicit false

namespace PrimeFactorOscillations

/-- Recurrence alone gives simultaneous late ascents at arbitrarily large ranks.
This is a location statement; it assumes no quantitative gap count. -/
theorem late_ascents_of_recurrent_short_gaps (H : Nat) (hH : 1 <= H) (b : Real)
    (hb : 1 / (2 * ((H : Real) + 1)) < b)
    (hmargin : ((H : Real) + 1) * b < 1)
    (hrec : forall Q : Nat, exists i : Nat,
      Q <= PrimeFactorUnimodality.primeAt i /\
      PrimeFactorUnimodality.primeAt (i + 1) <=
        PrimeFactorUnimodality.primeAt i + H) :
    forall K Q : Nat, exists k i : Nat, K <= k /\
      Q <= PrimeFactorUnimodality.primeAt i /\
      b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) /\
      genericOddDensity k i < genericOddDensity k (i + 1) /\
      ordinaryDensity k i < ordinaryDensity k (i + 1) := by
  have hb0 : 0 < b := (by positivity :
    (0 : Real) < 1 / (2 * ((H : Real) + 1))).trans hb
  have hHreal : (1 : Real) <= H := by exact_mod_cast hH
  have hbhalf : b < (1 : Real) / 2 := by nlinarith
  have hblog : b < Real.log 2 := hbhalf.trans (by linarith [Real.log_two_gt_d9])
  choose K0 hK0 using both_density_gap_signs_eventually_on_additive_band H b hb hmargin
  intro K Q
  let M : Nat := max K K0
  choose R hR using exists_nat_gt (max (3 : Real) (Real.exp (Real.exp (b * M)) + 1))
  choose i hi using hrec (max Q R)
  have hpQ : Q <= PrimeFactorUnimodality.primeAt i := (le_max_left Q R).trans hi.1
  have hpR : R <= PrimeFactorUnimodality.primeAt i := (le_max_right Q R).trans hi.1
  have hpRreal : (R : Real) <= PrimeFactorUnimodality.primeAt i := by exact_mod_cast hpR
  have hp3real : (3 : Real) < PrimeFactorUnimodality.primeAt i :=
    ((le_max_left _ _).trans_lt hR).trans_le hpRreal
  have hp : 2 < PrimeFactorUnimodality.primeAt i := by exact_mod_cast (by linarith :
    (2 : Real) < PrimeFactorUnimodality.primeAt i)
  have hpone : 1 <= PrimeFactorUnimodality.primeAt i := by omega
  have hlarge : Real.exp (Real.exp (b * M)) <=
      (PrimeFactorUnimodality.primeAt i - 1 : Nat) := by
    rw [Nat.cast_sub hpone, Nat.cast_one]
    have h := (le_max_right _ _).trans_lt hR
    linarith only [h, hpRreal]
  let t : Real := Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat))
  have ht : b * M <= t := by
    have h1 := Real.log_le_log (Real.exp_pos _) hlarge
    rw [Real.log_exp] at h1
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    simpa only [Real.log_exp, t] using h2
  have hM : (0 : Real) <= M := Nat.cast_nonneg M
  have ht0 : 0 <= t := (mul_nonneg hb0.le hM).trans ht
  let k : Nat := Nat.floor (t / b)
  have hcancel : (t / b) * b = t := by field_simp
  have hMk : M <= k := Nat.le_floor (by nlinarith only [ht, hcancel, hb0])
  have hkK : K <= k := (le_max_left K K0).trans hMk
  have hkK0 : K0 <= k := (le_max_right K K0).trans hMk
  have hfloor : (k : Real) <= t / b := Nat.floor_le (div_nonneg ht0 hb0.le)
  have hscale : b * k <= t := by nlinarith only [hfloor, hcancel, hb0]
  have hceil : t / b < (k : Real) + 1 := Nat.lt_floor_add_one (t / b)
  have hband : t <= b * k + Real.log 2 := by
    nlinarith only [hceil, hcancel, hb0, hblog]
  have hlow : b * k - Real.log 2 <= t := by
    have hlog : 0 < Real.log 2 := hb0.trans hblog
    linarith only [hscale, hlog]
  have hsigns := (hK0.2 k hkK0 i hp hlow hband).1 hi.2
  exact Exists.intro k (Exists.intro i (And.intro hkK
    (And.intro hpQ (And.intro hscale hsigns))))

/-- A scale below the exact threshold has arbitrarily large simultaneous
ascents whenever gaps at most H recur. No frequency estimate is needed. -/
theorem late_ascents_below_recurrent_gap_scale (H : Nat) (hH : 1 <= H) (b : Real)
    (hb : 0 < b) (hupper : b < 1 / ((H : Real) + 1))
    (hrec : forall Q : Nat, exists i : Nat,
      Q <= PrimeFactorUnimodality.primeAt i /\
      PrimeFactorUnimodality.primeAt (i + 1) <=
        PrimeFactorUnimodality.primeAt i + H) :
    forall K Q : Nat, exists k i : Nat, K <= k /\
      Q <= PrimeFactorUnimodality.primeAt i /\
      b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) /\
      genericOddDensity k i < genericOddDensity k (i + 1) /\
      ordinaryDensity k i < ordinaryDensity k (i + 1) := by
  let r : Real := 1 / ((H : Real) + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hbr : b < r := hupper
  let c : Real := (max b (r / 2) + r) / 2
  have hm : max b (r / 2) < r := max_lt hbr (by linarith only [hr])
  have hmc : max b (r / 2) < c := by dsimp [c]; linarith only [hm]
  have hbc : b < c := (le_max_left b (r / 2)).trans_lt hmc
  have hhalf : 1 / (2 * ((H : Real) + 1)) < c := by
    have heq : 1 / (2 * ((H : Real) + 1)) = r / 2 := by dsimp [r]; field_simp
    rw [heq]
    exact (le_max_right b (r / 2)).trans_lt hmc
  have hcr : c < r := by dsimp [c]; linarith only [hm]
  have hmargin : ((H : Real) + 1) * c < 1 := by
    have h := mul_lt_mul_of_pos_left hcr
      (by positivity : (0 : Real) < (H : Real) + 1)
    have hc : ((H : Real) + 1) * r = 1 := by dsimp [r]; field_simp
    rwa [hc] at h
  intro K Q
  choose k i hi using late_ascents_of_recurrent_short_gaps H hH c hhalf hmargin hrec K Q
  have hscale : b * k <= Real.log (Real.log (PrimeFactorUnimodality.primeAt i - 1 : Nat)) :=
    (mul_le_mul_of_nonneg_right hbc.le (Nat.cast_nonneg k)).trans hi.2.2.1
  exact Exists.intro k (Exists.intro i (And.intro hi.1
    (And.intro hi.2.1 (And.intro hscale hi.2.2.2))))

end PrimeFactorOscillations
