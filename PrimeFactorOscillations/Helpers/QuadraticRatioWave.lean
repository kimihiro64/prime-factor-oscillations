/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Helpers.NicolasSparseSampling
import PrimeFactorOscillations.Helpers.QuadraticProfileCanonicalLinearization

/-!
# Normalized moving-rank ratios

The full reference profile removes family effects. The actual floor rank and both eventual positive denominators are retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.QuadraticPrimeLaw

open Filter Robin1984
open scoped Topology

/-- Centered normalized actual ratio, with the complete canonical reference. -/
def normalizedRatioWave (law : QuadraticPrimeLaw) (N r : Nat) : Real :=
  -((law.referenceClock N) ^ 2 / (law.nu * (r : Real))) *
      ((N : Real) ^ (1 / 2 : Real) * Real.log (N : Real)) *
      (law.densityRatio N r - law.referenceRatio r (law.referenceClock N)) - 2

/-- The uniform coefficient theorem survives the full wave normalization. -/
theorem exists_eventually_normalizedRatioWave_error
    (law : QuadraticPrimeLaw) (b : Real) (hb : 0 < b) :
    exists r0 : Nat, exists K : Real, 0 < r0 /\ 0 <= K /\
      Filter.Eventually (fun N : Nat =>
        1 < Chebyshev.theta (N : Real) /\ 2 <= law.referenceClock N /\
        forall r : Nat, r0 <= r -> (r : Real) / law.referenceClock N <= b ->
          0 < law.prefixEsymm N r /\
          0 < Nat.factorialConvolution law.realCoefficient r (law.referenceClock N) /\
          abs (law.normalizedRatioWave N r + 2 +
            (N : Real) ^ (1 / 2 : Real) * Real.log (N : Real) *
              nicolasLogMertensOscillation (N : Real)) <=
            K * (((N : Real) ^ (1 / 2 : Real) * Real.log (N : Real)) *
                abs (nicolasLogMertensOscillation (N : Real)) / (r : Real) +
              (law.referenceClock N) ^ 2 / (law.nu * (r : Real) ^ 2) *
                (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real)))) atTop := by
  choose r0 K hr0 hK hApprox using law.exists_eventually_densityRatio_linearization b hb
  refine Exists.intro r0 (Exists.intro K (And.intro hr0 (And.intro hK ?_)))
  filter_upwards [hApprox, eventually_ge_atTop (2 : Nat)] with N hN hTwo
  refine And.intro hN.1 (And.intro hN.2.1 ?_)
  intro r hr hBand
  have h := hN.2.2 r hr hBand
  refine And.intro h.1 (And.intro h.2.1 ?_)
  have hNOne : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
  have hNPos : (0 : Real) < N := zero_lt_one.trans hNOne
  have hLPos : 0 < law.referenceClock N := by linarith only [hN.2.1]
  have hrPos : (0 : Real) < r := by exact_mod_cast hr0.trans_le hr
  have hRoot := Real.rpow_pos_of_pos hNPos (1 / 2 : Real)
  have hLog := Real.log_pos hNOne
  let X : Real := (N : Real) ^ (1 / 2 : Real) * Real.log (N : Real)
  let T : Real := (law.referenceClock N) ^ 2 / (law.nu * (r : Real)) * X
  have hX : 0 < X := mul_pos hRoot hLog
  have hT : 0 < T := mul_pos (div_pos (sq_pos_of_pos hLPos)
    (mul_pos law.nu_pos hrPos)) hX
  have hId : law.normalizedRatioWave N r + 2 +
      (N : Real) ^ (1 / 2 : Real) * Real.log (N : Real) *
        nicolasLogMertensOscillation (N : Real) =
      -T * (law.densityRatio N r - law.referenceRatio r (law.referenceClock N) -
        ((r : Real) / (law.referenceClock N) ^ 2) *
          (law.nu * nicolasLogMertensOscillation (N : Real))) := by
    dsimp [normalizedRatioWave, T, X]
    field_simp [law.nu_pos.ne', hrPos.ne', hLPos.ne'] <;> ring
  rw [hId, abs_mul, abs_neg, abs_of_pos hT]
  calc
    T * abs (law.densityRatio N r - law.referenceRatio r (law.referenceClock N) -
        ((r : Real) / (law.referenceClock N) ^ 2) *
          (law.nu * nicolasLogMertensOscillation (N : Real))) <=
        T * (K * (abs (law.nu * nicolasLogMertensOscillation (N : Real)) /
          (law.referenceClock N) ^ 2 + 1 / ((r : Real) * (N : Real)))) :=
      mul_le_mul_of_nonneg_left h.2.2 hT.le
    _ = K * (X * abs (nicolasLogMertensOscillation (N : Real)) / (r : Real) +
        (law.referenceClock N) ^ 2 / (law.nu * (r : Real) ^ 2) * (X / (N : Real))) := by
      rw [abs_mul, abs_of_pos law.nu_pos]
      dsimp [T]
      field_simp [law.nu_pos.ne', hrPos.ne', hLPos.ne', hNPos.ne'] <;> ring
    _ = _ := by
      have hRootSq : ((N : Real) ^ (1 / 2 : Real)) ^ (2 : Nat) = (N : Real) := by
        rw [<- Real.rpow_natCast, <- Real.rpow_mul hNPos.le]
        norm_num
      have hXdiv : X / (N : Real) = Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real) := by
        calc
          _ = ((N : Real) ^ (1 / 2 : Real) * Real.log (N : Real)) /
              ((N : Real) ^ (1 / 2 : Real)) ^ (2 : Nat) := by rw [hRootSq]
          _ = _ := by field_simp [hRoot.ne'] <;> ring
      rw [hXdiv]

def floorRank (law : QuadraticPrimeLaw) (alpha : Real) (N : Nat) : Nat :=
  Nat.floor (alpha * law.referenceClock N)

def normalizedFloorRatioWave (law : QuadraticPrimeLaw) (alpha : Real) (N : Nat) : Real :=
  law.normalizedRatioWave N (law.floorRank alpha N)

theorem tendsto_floorRank_atTop (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha) :
    Tendsto (law.floorRank alpha) atTop atTop := by
  apply tendsto_atTop.2
  intro m
  filter_upwards [law.tendsto_referenceClock_atTop.eventually_ge_atTop
    (((m : Real) + 1) / alpha)] with N hN
  have h := mul_le_mul_of_nonneg_left hN ha.le
  have hc : alpha * (((m : Real) + 1) / alpha) = (m : Real) + 1 := by
    field_simp [ha.ne']
  rw [hc] at h
  have hf := Nat.lt_floor_add_one (alpha * law.referenceClock N)
  have hm : (m : Real) <= (law.floorRank alpha N : Real) := by
    dsimp [floorRank]
    linarith only [h, hf]
  exact_mod_cast hm

/-- At the prescribed floor rank the relative error and additive tail both
have explicit vanishing coefficients. All actual denominators stay positive. -/
theorem exists_eventually_normalizedFloorRatioWave_error
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha) :
    exists K C : Real, 0 <= K /\ 0 <= C /\ Filter.Eventually (fun N : Nat =>
      0 < law.floorRank alpha N /\
      0 < law.prefixEsymm N (law.floorRank alpha N) /\
      0 < Nat.factorialConvolution law.realCoefficient (law.floorRank alpha N)
        (law.referenceClock N) /\
      abs (law.normalizedFloorRatioWave alpha N + 2 +
        (N : Real) ^ (1 / 2 : Real) * Real.log (N : Real) *
          nicolasLogMertensOscillation (N : Real)) <=
        (K / (law.floorRank alpha N : Real)) *
          abs ((N : Real) ^ (1 / 2 : Real) * Real.log (N : Real) *
            nicolasLogMertensOscillation (N : Real)) +
        C * (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real))) atTop := by
  choose r0 K hr0 hK hApprox using
    law.exists_eventually_normalizedRatioWave_error (2 * alpha) (by positivity)
  let C : Real := K * ((2 / alpha) ^ 2 / law.nu)
  refine Exists.intro K (Exists.intro C (And.intro hK (And.intro ?_ ?_)))
  . dsimp [C]
    exact mul_nonneg hK (div_nonneg (sq_nonneg _) law.nu_pos.le)
  . filter_upwards [hApprox, (law.tendsto_floorRank_atTop alpha ha).eventually_ge_atTop r0,
      law.tendsto_referenceClock_atTop.eventually_ge_atTop (2 / alpha),
      eventually_ge_atTop (2 : Nat)] with N hn hr hL hTwo
    let r := law.floorRank alpha N
    let L := law.referenceClock N
    let X : Real := (N : Real) ^ (1 / 2 : Real) * Real.log (N : Real)
    have hrNat : 0 < r := hr0.trans_le hr
    have hrPos : (0 : Real) < r := by exact_mod_cast hrNat
    have hLPos : 0 < L := by dsimp [L]; linarith only [hn.2.1]
    have hAlphaL : 2 <= alpha * L := by
      have h := mul_le_mul_of_nonneg_left hL ha.le
      have hc : alpha * (2 / alpha) = 2 := by field_simp [ha.ne']
      rw [hc] at h
      exact h
    have hFloorHi : (r : Real) <= alpha * L := Nat.floor_le (by linarith only [hAlphaL])
    have hFloorLo : alpha * L < (r : Real) + 1 := Nat.lt_floor_add_one _
    have hHalf : alpha * L / 2 <= (r : Real) := by linarith only [hFloorLo, hAlphaL]
    have hBand : (r : Real) / L <= 2 * alpha := by
      calc
        _ <= (alpha * L) / L := div_le_div_of_nonneg_right hFloorHi hLPos.le
        _ = alpha := by field_simp [hLPos.ne']
        _ <= _ := by linarith
    have hd := hn.2.2 r hr hBand
    refine And.intro hrNat (And.intro hd.1 (And.intro hd.2.1 ?_))
    have hInv := one_div_le_one_div_of_le (by positivity : 0 < alpha * L / 2) hHalf
    have hLR : L / (r : Real) <= 2 / alpha := by
      calc
        _ = L * (1 / (r : Real)) := by ring
        _ <= L * (1 / (alpha * L / 2)) :=
          mul_le_mul_of_nonneg_left hInv hLPos.le
        _ = _ := by field_simp [ha.ne', hLPos.ne']
    have hSquare : (L / (r : Real)) ^ (2 : Nat) <= (2 / alpha) ^ (2 : Nat) := by
      simpa only [pow_two] using
        mul_self_le_mul_self (div_nonneg hLPos.le hrPos.le) hLR
    have hRatio : L ^ 2 / (law.nu * (r : Real) ^ 2) <= (2 / alpha) ^ 2 / law.nu := by
      calc
        _ = (L / (r : Real)) ^ (2 : Nat) / law.nu := by
          field_simp [law.nu_pos.ne', hrPos.ne'] <;> ring
        _ <= _ := div_le_div_of_nonneg_right hSquare law.nu_pos.le
    have hNOne : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
    have hX : 0 < X := mul_pos
      (Real.rpow_pos_of_pos (zero_lt_one.trans hNOne) _) (Real.log_pos hNOne)
    have hTail : 0 <= Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real) := by positivity
    have hBudget := mul_le_mul_of_nonneg_right hRatio hTail
    have he := hd.2.2
    change abs (law.normalizedFloorRatioWave alpha N + 2 +
      X * nicolasLogMertensOscillation (N : Real)) <= _ at he
    apply he.trans
    change K * (X * abs (nicolasLogMertensOscillation (N : Real)) / (r : Real) +
      L ^ 2 / (law.nu * (r : Real) ^ 2) *
        (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real))) <= _
    dsimp [C]
    rw [abs_mul, abs_of_pos hX]
    change K * (X * abs (nicolasLogMertensOscillation (N : Real)) / (r : Real) +
      L ^ 2 / (law.nu * (r : Real) ^ 2) *
        (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real))) <=
      K / (r : Real) * (X * abs (nicolasLogMertensOscillation (N : Real))) +
        K * ((2 / alpha) ^ 2 / law.nu) *
          (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real))
    calc
      _ <= K * (X * abs (nicolasLogMertensOscillation (N : Real)) / (r : Real) +
        ((2 / alpha) ^ 2 / law.nu) *
          (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real))) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hBudget) hK
      _ = _ := by ring

/-- Under RH every qualifying local law has the same limiting zero wave. -/
theorem tendsto_normalizedFloorRatioWave_sub_zeroWave
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha) (hRH : RiemannHypothesis) :
    Tendsto (fun N : Nat =>
      law.normalizedFloorRatioWave alpha N - nicolasZeroWave (N : Real)) atTop (nhds 0) := by
  choose K C hK hC hApprox using law.exists_eventually_normalizedFloorRatioWave_error alpha ha
  let beta := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  let B := nicolasLogSpectralConstant + 2 + abs beta
  have ht : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hRank : Tendsto (fun N : Nat => (law.floorRank alpha N : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (law.tendsto_floorRank_atTop alpha ha)
  have hFirst : Tendsto (fun N : Nat => K * B / (law.floorRank alpha N : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hRank
  have hTail : Tendsto (fun N : Nat =>
      C * (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real))) atTop (nhds 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (((isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero).comp ht).const_mul C
  have hLast : Tendsto (fun N : Nat => nicolasLogSpectralConstant / Real.log (N : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp ht)
  have hZero : Tendsto (fun N : Nat =>
      K * B / (law.floorRank alpha N : Real) +
      C * (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real)) +
      nicolasLogSpectralConstant / Real.log (N : Real)) atTop (nhds 0) := by
    simpa only [zero_add, add_zero] using (hFirst.add hTail).add hLast
  apply squeeze_zero_norm' ?_ hZero
  filter_upwards [hApprox, ht.eventually (eventually_nicolasLog_normalized_wave_error hRH),
    ht.eventually_ge_atTop (Real.exp 1)] with N hA hS hExp
  let Y := (N : Real) ^ (1 / 2 : Real) * Real.log (N : Real) *
    nicolasLogMertensOscillation (N : Real)
  have hNOne : (1 : Real) < N :=
    lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hExp
  have hLog : 1 <= Real.log (N : Real) := by
    have h := Real.log_le_log (Real.exp_pos 1) hExp
    simpa only [Real.log_exp] using h
  have hDiv : nicolasLogSpectralConstant / Real.log (N : Real) <= nicolasLogSpectralConstant :=
    div_le_self nicolasLogSpectralConstant_pos.le hLog
  have hW := abs_nicolasZeroWave_le hRH hNOne
  change abs (nicolasZeroWave (N : Real)) <= beta at hW
  change abs (Y + 2 + nicolasZeroWave (N : Real)) <=
    nicolasLogSpectralConstant / Real.log (N : Real) at hS
  have hB : abs Y <= B := by
    apply abs_le.mpr
    dsimp [B]
    constructor <;> linarith only [(abs_le.mp hS).1, (abs_le.mp hS).2,
      (abs_le.mp hW).1, (abs_le.mp hW).2, hDiv, le_abs_self beta]
  have hr : (0 : Real) < law.floorRank alpha N := by exact_mod_cast hA.1
  have hScaled := mul_le_mul_of_nonneg_left hB
    (div_nonneg hK hr.le : 0 <= K / (law.floorRank alpha N : Real))
  have hFamily : abs (law.normalizedFloorRatioWave alpha N + 2 + Y) <=
      K * B / (law.floorRank alpha N : Real) +
        C * (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real)) := by
    have he := hA.2.2.2
    change abs (law.normalizedFloorRatioWave alpha N + 2 + Y) <=
      K / (law.floorRank alpha N : Real) * abs Y + _ at he
    apply he.trans
    calc
      _ <= K / (law.floorRank alpha N : Real) * B +
          C * (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real)) :=
        add_le_add hScaled (le_refl _)
      _ = _ := by ring
  have hTriangle := norm_sub_le
    (law.normalizedFloorRatioWave alpha N + 2 + Y)
    (Y + 2 + nicolasZeroWave (N : Real))
  have hCancel : (law.normalizedFloorRatioWave alpha N + 2 + Y) -
      (Y + 2 + nicolasZeroWave (N : Real)) =
      law.normalizedFloorRatioWave alpha N - nicolasZeroWave (N : Real) := by ring
  rw [hCancel] at hTriangle
  simp only [Real.norm_eq_abs] at hTriangle
  change abs (law.normalizedFloorRatioWave alpha N - nicolasZeroWave (N : Real)) <= _
  exact hTriangle.trans (add_le_add hFamily hS)

/-- Sparse lower boundedness of the actual normalized family profile detects RH. -/
theorem riemannHypothesis_iff_subpower_mesh_normalizedFloorRatioWave_bounded_below
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha)
    (u : Nat -> Nat) (hu : StrictMono u) (hmesh : Nat.SubpowerGapBound u (3 / 4)) :
    RiemannHypothesis <-> exists B : Real, Filter.Eventually (fun j : Nat =>
      B <= law.normalizedFloorRatioWave alpha (u j)) atTop := by
  have ht : Tendsto (fun j : Nat => (u j : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hu.tendsto_atTop
  constructor
  . intro hRH
    let beta := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
    refine Exists.intro (-beta - 1) ?_
    have hError := ((law.tendsto_normalizedFloorRatioWave_sub_zeroWave alpha ha hRH).abs).eventually
      (eventually_le_nhds (by norm_num : abs (0 : Real) < 1))
    filter_upwards [hu.tendsto_atTop.eventually hError,
      ht.eventually_gt_atTop (1 : Real)] with j he hj
    have hW := abs_nicolasZeroWave_le hRH hj
    change abs (nicolasZeroWave (u j : Real)) <= beta at hW
    linarith only [(abs_le.mp he).1, (abs_le.mp hW).1]
  . intro hBound
    choose B hBound using hBound
    choose K C hK hC hApprox using law.exists_eventually_normalizedFloorRatioWave_error alpha ha
    have hRank : Tendsto (fun N : Nat => (law.floorRank alpha N : Real)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (law.tendsto_floorRank_atTop alpha ha)
    have hDelta : Tendsto (fun N : Nat => K / (law.floorRank alpha N : Real))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hRank
    have hEpsilon : Tendsto (fun N : Nat =>
        C * (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real))) atTop (nhds 0) := by
      simpa only [mul_zero, Function.comp_def] using
        (((isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero).comp
          tendsto_natCast_atTop_atTop).const_mul C
    apply (riemannHypothesis_iff_nicolasLog_subpower_mesh_bounded u hu hmesh).mpr
    refine Exists.intro (max 0 (2 * (1 - B))) ?_
    filter_upwards [hBound, hu.tendsto_atTop.eventually hApprox,
      hu.tendsto_atTop.eventually (hDelta.eventually
        (eventually_le_nhds (by norm_num : (0 : Real) < 1 / 2))),
      hu.tendsto_atTop.eventually (hEpsilon.eventually
        (eventually_le_nhds (by norm_num : (0 : Real) < 1)))] with j hb hA hd he
    let Y := (u j : Real) ^ (1 / 2 : Real) * Real.log (u j : Real) *
      nicolasLogMertensOscillation (u j : Real)
    change Y <= _
    by_cases hY : Y <= 0
    . exact hY.trans (le_max_left _ _)
    . have hYPos : 0 <= Y := (lt_of_not_ge hY).le
      have h := hA.2.2.2
      change abs (law.normalizedFloorRatioWave alpha (u j) + 2 + Y) <=
        K / (law.floorRank alpha (u j) : Real) * abs Y + _ at h
      rw [abs_of_nonneg hYPos] at h
      have hScaled := mul_le_mul_of_nonneg_right hd hYPos
      linarith only [(abs_le.mp h).2, hScaled, he, hb, le_max_right 0 (2 * (1 - B))]

end PrimeFactorOscillations.QuadraticPrimeLaw
