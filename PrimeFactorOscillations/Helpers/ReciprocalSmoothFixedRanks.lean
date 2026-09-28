import PrimeFactorOscillations.Definitions.RealLocalDensity
import PrimeFactorOscillations.Helpers.ReciprocalSmoothPrefixes

/-! # Fixed-rank Bernoulli dominance with every forced-coordinate case retained -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.ReciprocalSmoothLaw
open scoped Classical

theorem eventually_prefix_previous_le_half (law : ReciprocalSmoothLaw)
    (r : Nat) (hr : 1 <= r) :
    exists P : Nat, forall p : Nat, P <= p ->
      law.prefixMass p (r - 1) <= (1 / 2 : Real) * law.prefixMass p r := by
  choose A hA hM using law.prime_prefix_interior_mertens_bound
  choose C hC hlarge using law.prime_prefix_largest_weights_log_bound
  let B : Real := C * (2 + Real.log r)
  have hB : 0 <= B := by
    have hlog : 0 <= Real.log (r : Real) := Real.log_nonneg (by exact_mod_cast hr)
    dsimp only [B]
    positivity
  let L : Real := (2 * r + B + A + 1) / law.nu
  have hlogs : Filter.Tendsto (fun n : Nat => Real.log (Real.log (n : Real)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  choose P hP using Filter.eventually_atTop.mp
    (hlogs.eventually (Filter.eventually_ge_atTop L))
  refine Exists.intro (max (P + 1) 3) ?_
  intro p hp
  let n := p - 1
  have hn : 2 <= n := by dsimp only [n]; omega
  have hpn : n + 1 = p := by dsimp only [n]; omega
  have hPn : P <= n := by dsimp only [n]; omega
  let s := law.prefixProbabilities p
  let w := (List.bernoulliInterior s).map (fun a => a / (1 - a))
  have hs : forall a, List.Mem a s -> 0 <= a /\ a <= 1 :=
    law.prime_prefix_probability_bounds p
  have hsum : abs (w.sum - law.nu * Real.log (Real.log n)) <= A := by
    simpa only [w, s, prefixProbabilities, hpn] using hM n hn
  have hW : 2 * (r : Real) + B < w.sum := by
    have hscale := mul_le_mul_of_nonneg_left (hP n hPn) law.nu_pos.le
    have hcancel : law.nu * L = 2 * r + B + A + 1 := by
      dsimp only [L]
      field_simp [ne_of_gt law.nu_pos]
    rw [hcancel] at hscale
    linarith only [hscale, (abs_le.mp hsum).1]
  have hweight (t : Nat) (ht : 1 <= t) (htr : t <= r) :
      List.largestWeightSum w (t - 1) <= B := by
    by_cases hzero : t - 1 = 0
    next =>
      simpa only [hzero, List.largestWeightSum, List.take_zero, List.sum_nil] using hB
    next =>
      have hj : 1 <= t - 1 := by omega
      have hjR : (0 : Real) < ((t - 1 : Nat) : Real) := by
        exact_mod_cast (show 0 < t - 1 by omega)
      have hlog : Real.log (t - 1 : Nat) <= Real.log (r : Real) :=
        Real.log_le_log hjR (by exact_mod_cast (show t - 1 <= r by omega))
      calc
        _ <= C * (2 + Real.log (t - 1 : Nat)) := hlarge p (t - 1) hj
        _ <= B := by dsimp only [B]; nlinarith only [hlog, hC]
  change List.bernoulliMass s (r - 1) <= (1 / 2 : Real) * List.bernoulliMass s r
  by_cases hf : r < s.count 1
  next =>
    rw [List.bernoulliMass_eq_zero_of_lt_count_one s r hf,
      List.bernoulliMass_eq_zero_of_lt_count_one s (r - 1) (by omega)]
    norm_num
  next =>
    by_cases heq : r = s.count 1
    next =>
      have hprev := List.bernoulliMass_eq_zero_of_lt_count_one s (r - 1) (by omega)
      have hmass : 0 < List.bernoulliMass s r := by
        have hid := List.bernoulliMass_interior_count_one_add s hs 0
        rw [Nat.add_zero, <- heq] at hid
        rw [hid]
        exact List.bernoulliMass_pos_of_interior _ (List.bernoulliInterior_mem s) 0 (Nat.zero_le _)
      rw [hprev]
      positivity
    next =>
      let t := r - s.count 1
      have ht : 1 <= t := by dsimp only [t]; omega
      have htr : t <= r := Nat.sub_le _ _
      have hrt : s.count 1 + t = r := by dsimp only [t]; omega
      let D := w.sum - List.largestWeightSum w (t - 1)
      have hDlarge : 2 * (r : Real) < D := by
        have hw := hweight t ht htr
        dsimp only [D]
        linarith only [hW, hw]
      have hD : 0 < D := by
        have hrR : (0 : Real) <= r := Nat.cast_nonneg r
        linarith only [hDlarge, hrR]
      have hb := List.bernoulliMass_forced_ratio_bounds s hs t ht hD
      rw [hrt] at hb
      have hsmall : (t : Real) / D <= (1 / 2 : Real) := by
        have htrR : (t : Real) <= r := by exact_mod_cast htr
        have hcancel : ((t : Real) / D) * D = t := by field_simp [ne_of_gt hD]
        by_contra hnot
        have hmul := mul_lt_mul_of_pos_right (lt_of_not_ge hnot) hD
        rw [hcancel] at hmul
        nlinarith only [hmul, hDlarge, htrR]
      have hratio := hb.2.2.2.trans hsmall
      have hmul := mul_le_mul_of_nonneg_right hratio hb.2.1.le
      have hcancel : (List.bernoulliMass s (r - 1) / List.bernoulliMass s r) *
          List.bernoulliMass s r = List.bernoulliMass s (r - 1) := by
        field_simp [ne_of_gt hb.2.1]
      rwa [hcancel] at hmul

end PrimeFactorOscillations.ReciprocalSmoothLaw
