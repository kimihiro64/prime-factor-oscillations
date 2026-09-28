/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliBounds

/-! # Uniform normalization of finite Bernoulli ratios from moment estimates -/

set_option autoImplicit false
set_option Elab.async false

open Filter

namespace List

private theorem eventually_log_allowance (A C epsilon : Real) (he : 0 < epsilon) :
    Filter.Eventually (fun k : Nat =>
      A + C * Real.log (k : Real) <= epsilon * k) Filter.atTop := by
  have ho := (_root_.isLittleO_log_rpow_rpow_atTop (1 : Real)
    (by norm_num : (0 : Real) < 1)).const_mul_left C
  have hn := (tendsto_natCast_atTop_atTop (R := Real)).eventually (ho.bound (half_pos he))
  choose K hK using exists_nat_gt (A / (epsilon / 2))
  filter_upwards [hn, Filter.eventually_ge_atTop K] with k hk hkg
  have hk0 : (0 : Real) <= k := Nat.cast_nonneg k
  simp only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg hk0] at hk
  have hl : C * Real.log (k : Real) <= (epsilon / 2) * k := (le_abs_self _).trans hk
  have hkr : (K : Real) <= k := by exact_mod_cast hkg
  have hconst := mul_lt_mul_of_pos_right (hK.trans_le hkr) (half_pos he)
  have hc : (A / (epsilon / 2)) * (epsilon / 2) = A := by
    field_simp [ne_of_gt (half_pos he)]
  rw [hc] at hconst
  linarith only [hl, hconst]

private theorem normalized_ratio_stability
    (T k r S B R theta : Real) (hT : 0 < T) (hk : 0 < k)
    (hr : 0 < r) (hS : 0 < S) (ht0 : 0 <= theta) (ht : theta <= 1 / 4)
    (hrlo : (1 - theta) * k <= r) (hrhi : r <= k)
    (hShi : S <= (1 + theta) * T)
    (hClo : (1 - theta) * T <= S - B)
    (hRlo : r / S <= R) (hRhi : R <= r / (S - B)) :
    abs (T * R / k - 1) <= 2 * theta := by
  have htheta : 0 < 1 - theta := by linarith
  have hcomp : 0 < S - B := (mul_pos htheta hT).trans_le hClo
  have hRpos : 0 < R := (div_pos hr hS).trans_le hRlo
  have hl := mul_le_mul_of_nonneg_right hRlo hS.le
  have hu := mul_le_mul_of_nonneg_right hRhi hcomp.le
  have hlc : (r / S) * S = r := by field_simp
  have huc : (r / (S - B)) * (S - B) = r := by field_simp
  rw [hlc] at hl
  rw [huc] at hu
  let Z := T * R / k
  have hZ : Z * k = T * R := by dsimp [Z]; field_simp
  have hlo : (1 - theta) * k <= (1 + theta) * (T * R) := by
    calc
      _ <= r := hrlo
      _ <= R * S := hl
      _ <= R * ((1 + theta) * T) := mul_le_mul_of_nonneg_left hShi hRpos.le
      _ = _ := by ring
  have hhi : (1 - theta) * (T * R) <= k := by
    calc
      _ = R * ((1 - theta) * T) := by ring
      _ <= R * (S - B) := mul_le_mul_of_nonneg_left hClo hRpos.le
      _ <= r := hu
      _ <= k := hrhi
  rw [<- hZ] at hlo hhi
  have hloS : 1 - theta <= (1 + theta) * Z := by
    by_contra hn
    have hh := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hk
    nlinarith only [hlo, hh]
  have hhiS : (1 - theta) * Z <= 1 := by
    by_contra hn
    have hh := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hk
    nlinarith only [hhi, hh]
  have hzlo : 1 - 2 * theta <= Z := by
    by_contra hn
    have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hn)
      (show 0 < 1 + theta by linarith only [ht0])
    nlinarith only [hloS, hh, sq_nonneg theta]
  have hzhi : Z <= 1 + 2 * theta := by
    by_contra hn
    have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hn) htheta
    have hquad := mul_nonneg ht0 (show 0 <= 1 - 2 * theta by linarith only [ht])
    nlinarith only [hhiS, hh, hquad]
  exact abs_le.mpr (And.intro (by linarith only [hzlo]) (by linarith only [hzhi]))

/-- Uniform growing-rank ratio for finite probability lists whose total odds
have the specified main term and whose largest-weight allowance is logarithmic.
The forced count is retained exactly and bounded independently of the rank.
No density-ratio assumption occurs among the hypotheses. -/
theorem bernoulliMass_uniform_normalized_ratio
    (nu u A C : Real) (F : Nat) (hnu : 0 < nu) (hu : 0 < u)
    (hC : 0 <= C) (epsilon : Real) (he : 0 < epsilon) :
    Filter.Eventually (fun k : Nat => forall s : List Real,
      (forall a, List.Mem a s -> 0 <= a /\ a <= 1) ->
      s.count 1 <= F -> forall L : Real, u * k <= L ->
      abs (((bernoulliInterior s).map (fun a => a / (1 - a))).sum - nu * L) <= A ->
      largestWeightSum ((bernoulliInterior s).map (fun a => a / (1 - a)))
        (k - 1 - s.count 1 - 1) <= C * (2 + Real.log k) ->
      0 < bernoulliMass s (k - 1) /\
      abs (nu * L * (bernoulliMass s (k - 2) / bernoulliMass s (k - 1)) /
        (k : Real) - 1) <= epsilon) Filter.atTop := by
  let theta := min (epsilon / 4) (1 / 4)
  have htpos : 0 < theta := lt_min (by linarith) (by norm_num)
  have htquarter : theta <= 1 / 4 := min_le_right _ _
  have hte : 2 * theta <= epsilon := by
    have h := min_le_left (epsilon / 4) (1 / 4)
    dsimp [theta]
    linarith only [h, he]
  have hcost := eventually_log_allowance (A + 2 * C) C (theta * nu * u)
    (mul_pos (mul_pos htpos hnu) hu)
  have hforced := eventually_log_allowance ((F : Real) + 1) 0 theta htpos
  filter_upwards [hcost, hforced, Filter.eventually_ge_atTop (F + 2)] with k hkcost hkforced hk
  intro s hs hf L hL hsum hdeleted
  have hkpos : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hLpos : 0 < L := (mul_pos hu hkpos).trans_le hL
  let T := nu * L
  let r := k - 1 - s.count 1
  let S := ((bernoulliInterior s).map (fun a => a / (1 - a))).sum
  let B := largestWeightSum ((bernoulliInterior s).map (fun a => a / (1 - a))) (r - 1)
  have hT : 0 < T := mul_pos hnu hLpos
  have hr : 1 <= r := by dsimp [r]; omega
  have hrpos : (0 : Real) < r := by exact_mod_cast (show 0 < r by omega)
  have hlog : 0 <= Real.log (k : Real) :=
    Real.log_nonneg (by exact_mod_cast (show 1 <= k by omega))
  have htail : 0 <= C * (2 + Real.log (k : Real)) :=
    mul_nonneg hC (by linarith only [hlog])
  have hscaled := mul_le_mul_of_nonneg_left hL (mul_nonneg htpos.le hnu.le)
  have hcostT : A + C * (2 + Real.log (k : Real)) <= theta * T := by
    dsimp [T]
    nlinarith only [hkcost, hscaled]
  have hsumle := abs_le.mp hsum
  have hSlo : (1 - theta) * T <= S := by
    dsimp [S, T]
    dsimp [T] at hcostT
    nlinarith only [hsumle.1, hcostT, htail]
  have hShi : S <= (1 + theta) * T := by
    dsimp [S, T]
    dsimp [T] at hcostT
    nlinarith only [hsumle.2, hcostT, htail]
  have hClo : (1 - theta) * T <= S - B := by
    change B <= C * (2 + Real.log k) at hdeleted
    have hlow : -A <= S - T := hsumle.1
    nlinarith only [hlow, hcostT, hdeleted]
  have hmargin : 0 < 1 - theta := by linarith only [htquarter]
  have hSpos : 0 < S := (mul_pos hmargin hT).trans_le hSlo
  have hcomp : 0 < S - B := (mul_pos hmargin hT).trans_le hClo
  have hbounds := bernoulliMass_forced_ratio_bounds s hs r hr hcomp
  have hindex : s.count 1 + r = k - 1 := by dsimp [r]; omega
  have hindexlo : s.count 1 + r - 1 = k - 2 := by omega
  rw [hindexlo, hindex] at hbounds
  have hrhi : (r : Real) <= k := by exact_mod_cast (show r <= k by dsimp [r]; omega)
  have hrval : (r : Real) = (k : Real) - 1 - s.count 1 := by
    dsimp [r]
    rw [Nat.cast_sub (by omega : s.count 1 <= k - 1),
      Nat.cast_sub (by omega : 1 <= k), Nat.cast_one]
  have hfr : (s.count 1 : Real) <= F := by exact_mod_cast hf
  have hrlo : (1 - theta) * k <= (r : Real) := by
    simp only [zero_mul, add_zero] at hkforced
    nlinarith only [hkforced, hfr, hrval]
  have hnear := normalized_ratio_stability T k r S B
    (bernoulliMass s (k - 2) / bernoulliMass s (k - 1)) theta hT hkpos hrpos hSpos
    htpos.le htquarter hrlo hrhi hShi hClo hbounds.2.2.1 hbounds.2.2.2
  exact And.intro hbounds.2.1 (hnear.trans hte)

end List
