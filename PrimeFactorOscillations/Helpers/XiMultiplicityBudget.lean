/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.XiWaveMoments

/-!
# Multiplicity excess-energy budgets

Under RH, zero excess energy is equivalent to simplicity of every indexed zero.
Finite packets and complete frequency fibers obey the same quadratic budget.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Topology

noncomputable section

namespace PrimeFactorOscillations

open Robin1984 Complex

def xiIndexedMultiplicity (p : RiemannXiDivisorZeroIndex) : Nat :=
  xiZeroMultiplicity ((1 / 2 : Complex) +
    ((riemannXiDivisorZeroValue p).im : Complex) * Complex.I)

theorem xiIndexedMultiplicity_pos (hRH : RiemannHypothesis)
    (p : RiemannXiDivisorZeroIndex) : 0 < xiIndexedMultiplicity p := by
  have hp : 0 < xiZeroMultiplicity (riemannXiDivisorZeroValue p) :=
    Nat.zero_lt_of_lt p.val.snd.isLt
  have he : riemannXiDivisorZeroValue p =
      (1 / 2 : Complex) + ((riemannXiDivisorZeroValue p).im : Complex) * Complex.I := by
    apply Complex.ext
    . simpa using Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p
    . simp
  rw [he] at hp
  exact hp

theorem tsum_xiWaveWeight_frequency_real (hRH : RiemannHypothesis) (w : Real) :
    tsum (fun p : RiemannXiDivisorZeroIndex =>
      if (riemannXiDivisorZeroValue p).im = w then xiWaveWeight p else 0) =
        (xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I) : Real) /
          (1 / 4 + w ^ 2) := by
  classical
  have hs : Summable (fun p : RiemannXiDivisorZeroIndex =>
      if (riemannXiDivisorZeroValue p).im = w then xiWaveWeight p else 0) :=
    (summable_xiWaveWeight hRH).norm.of_norm_bounded
      (fun p => by split_ifs <;> simp [norm_nonneg])
  have hc : ((tsum (fun p : RiemannXiDivisorZeroIndex =>
      if (riemannXiDivisorZeroValue p).im = w then xiWaveWeight p else 0) : Real) : Complex) =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        if (riemannXiDivisorZeroValue p).im = w then (xiWaveWeight p : Complex) else 0) := by
    calc
      _ = tsum (fun p : RiemannXiDivisorZeroIndex =>
          ((if (riemannXiDivisorZeroValue p).im = w then xiWaveWeight p else 0 : Real) :
            Complex)) := Complex.ofRealCLM.map_tsum hs
      _ = _ := by
        apply tsum_congr
        intro p
        split_ifs <;> rfl
  have h := tsum_xiWaveWeight_frequency hRH w
  rw [<- hc] at h
  have hh := congrArg Complex.re h
  simpa only [Complex.ofReal_re, Complex.div_ofReal_re, Complex.natCast_re] using hh

theorem summable_xiVarianceTerm (hRH : RiemannHypothesis) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      xiWaveWeight p * (xiIndexedMultiplicity p : Real) * xiWaveWeight p) := by
  classical
  have hw := summable_xiWaveWeight hRH
  have hp := summable_mul_of_summable_norm hw.norm hw.norm
  have hs : Summable (fun p : Prod RiemannXiDivisorZeroIndex RiemannXiDivisorZeroIndex =>
      if (riemannXiDivisorZeroValue p.2).im = (riemannXiDivisorZeroValue p.1).im
      then xiWaveWeight p.1 * xiWaveWeight p.2 else 0) :=
    hp.norm.of_norm_bounded (fun p => by split_ifs <;> simp <;> positivity)
  have hrow : forall p : RiemannXiDivisorZeroIndex,
      tsum (fun q : RiemannXiDivisorZeroIndex =>
        if (riemannXiDivisorZeroValue q).im = (riemannXiDivisorZeroValue p).im
        then xiWaveWeight p * xiWaveWeight q else 0) =
      xiWaveWeight p * (xiIndexedMultiplicity p : Real) * xiWaveWeight p := by
    intro p
    calc
      _ = xiWaveWeight p * tsum (fun q : RiemannXiDivisorZeroIndex =>
          if (riemannXiDivisorZeroValue q).im = (riemannXiDivisorZeroValue p).im
          then xiWaveWeight q else 0) := by
        rw [<- tsum_mul_left]
        apply tsum_congr
        intro q
        split_ifs <;> simp
      _ = _ := by
        rw [tsum_xiWaveWeight_frequency_real hRH]
        dsimp only [xiIndexedMultiplicity, xiWaveWeight]
        ring
  simpa only [hrow] using hs.prod

def xiSimpleBaseline : Real :=
  tsum (fun p : RiemannXiDivisorZeroIndex => (xiWaveWeight p) ^ 2)

def xiMultiplicityDefect : Real := xiVarianceBudget - xiSimpleBaseline

theorem summable_xiSimpleTerm (hRH : RiemannHypothesis) :
    Summable (fun p : RiemannXiDivisorZeroIndex => (xiWaveWeight p) ^ 2) := by
  apply (summable_xiVarianceTerm hRH).norm.of_norm_bounded
  intro p
  have hm : (1 : Real) <= xiIndexedMultiplicity p := by
    exact_mod_cast (xiIndexedMultiplicity_pos hRH p)
  have hw := xiWaveWeight_nonneg p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (mul_nonneg hw (Nat.cast_nonneg _)) hw)]
  nlinarith only [mul_le_mul_of_nonneg_right hm (sq_nonneg (xiWaveWeight p))]

theorem xiMultiplicityDefect_eq_tsum (hRH : RiemannHypothesis) :
    xiMultiplicityDefect =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        ((xiIndexedMultiplicity p : Real) - 1) * (xiWaveWeight p) ^ 2) := by
  unfold xiMultiplicityDefect xiVarianceBudget xiSimpleBaseline
  change tsum (fun p => xiWaveWeight p * (xiIndexedMultiplicity p : Real) * xiWaveWeight p) -
    tsum (fun p => (xiWaveWeight p) ^ 2) = _
  rw [<- (summable_xiVarianceTerm hRH).tsum_sub (summable_xiSimpleTerm hRH)]
  apply tsum_congr
  intro p
  dsimp only [xiIndexedMultiplicity]
  ring

theorem xiMultiplicityDefect_nonneg (hRH : RiemannHypothesis) :
    0 <= xiMultiplicityDefect := by
  rw [xiMultiplicityDefect_eq_tsum hRH]
  apply tsum_nonneg
  intro p
  have hm : (1 : Real) <= xiIndexedMultiplicity p := by
    exact_mod_cast (xiIndexedMultiplicity_pos hRH p)
  exact mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg _)

theorem xiMultiplicityDefect_le (hRH : RiemannHypothesis) :
    xiMultiplicityDefect <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) ^ 2 -
        xiSimpleBaseline := by
  exact sub_le_sub_right (xiVarianceBudget_le hRH) xiSimpleBaseline

theorem summable_xiDefectTerm (hRH : RiemannHypothesis) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      ((xiIndexedMultiplicity p : Real) - 1) * (xiWaveWeight p) ^ 2) := by
  convert (summable_xiVarianceTerm hRH).sub (summable_xiSimpleTerm hRH) using 1
  funext p
  ring

theorem xiDefectTerm_nonneg (hRH : RiemannHypothesis)
    (p : RiemannXiDivisorZeroIndex) :
    0 <= ((xiIndexedMultiplicity p : Real) - 1) * (xiWaveWeight p) ^ 2 := by
  have hm : (1 : Real) <= xiIndexedMultiplicity p := by
    exact_mod_cast (xiIndexedMultiplicity_pos hRH p)
  exact mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg _)

/-- Zero excess energy is equivalent to simplicity of every indexed zero. -/
theorem xiMultiplicityDefect_eq_zero_iff (hRH : RiemannHypothesis) :
    xiMultiplicityDefect = 0 <->
      forall p : RiemannXiDivisorZeroIndex, xiIndexedMultiplicity p = 1 := by
  constructor
  . intro hd p
    have hl := (summable_xiDefectTerm hRH).le_tsum p
      (fun q _ => xiDefectTerm_nonneg hRH q)
    rw [<- xiMultiplicityDefect_eq_tsum hRH, hd] at hl
    have hw : 0 < xiWaveWeight p := by
      unfold xiWaveWeight
      positivity
    have hu : (xiIndexedMultiplicity p : Real) <= 1 := by
      by_contra hn
      have hh : 1 < (xiIndexedMultiplicity p : Real) := lt_of_not_ge hn
      have hp := mul_pos (sub_pos.mpr hh) (pow_pos hw 2)
      linarith only [hl, hp]
    have hm : (1 : Real) <= xiIndexedMultiplicity p := by
      exact_mod_cast (xiIndexedMultiplicity_pos hRH p)
    have he : (xiIndexedMultiplicity p : Real) = 1 := le_antisymm hu hm
    exact_mod_cast he
  . intro hm
    rw [xiMultiplicityDefect_eq_tsum hRH]
    simp only [hm, Nat.cast_one, sub_self, zero_mul, tsum_zero]

/-- A simultaneous multiplicity budget over any finite supported zero packet. -/
theorem finite_multiplicity_defect_budget (hRH : RiemannHypothesis)
    (S : Finset RiemannXiDivisorZeroIndex) :
    Finset.sum S (fun p =>
      ((xiIndexedMultiplicity p : Real) - 1) * (xiWaveWeight p) ^ 2) <=
        (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) ^ 2 -
          xiSimpleBaseline := by
  have hl := (summable_xiDefectTerm hRH).sum_le_tsum S
    (fun p _ => xiDefectTerm_nonneg hRH p)
  rw [<- xiMultiplicityDefect_eq_tsum hRH] at hl
  exact hl.trans (xiMultiplicityDefect_le hRH)

/-- Each multiplicity is restricted by the same independent excess-energy budget. -/
theorem xiIndexedMultiplicity_le (hRH : RiemannHypothesis)
    (p : RiemannXiDivisorZeroIndex) :
    (xiIndexedMultiplicity p : Real) <= 1 +
      ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) ^ 2 -
        xiSimpleBaseline) / (xiWaveWeight p) ^ 2 := by
  have hl := (summable_xiDefectTerm hRH).le_tsum p
    (fun q _ => xiDefectTerm_nonneg hRH q)
  rw [<- xiMultiplicityDefect_eq_tsum hRH] at hl
  have he := hl.trans (xiMultiplicityDefect_le hRH)
  have hw : 0 < xiWaveWeight p := by
    unfold xiWaveWeight
    positivity
  have hh := div_le_div_of_nonneg_right he (pow_pos hw 2).le
  have heq : ((xiIndexedMultiplicity p : Real) - 1) *
      (xiWaveWeight p) ^ 2 / (xiWaveWeight p) ^ 2 =
        (xiIndexedMultiplicity p : Real) - 1 := by
    field_simp [hw.ne']
  rw [heq] at hh
  linarith only [hh]

/-- Aggregating the complete frequency fibre charges the full multiplicity. -/
theorem multiplicity_quadratic_budget (hRH : RiemannHypothesis) (w : Real) :
    let m := xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I)
    (m : Real) * ((m : Real) - 1) / (1 / 4 + w ^ 2) ^ 2 <=
      xiMultiplicityDefect := by
  classical
  let m := xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I)
  let e := xiZeroFrequencyFiberEquiv hRH w
  let S : Finset RiemannXiDivisorZeroIndex :=
    Finset.image (fun k : Fin m => (e.symm k).val) Finset.univ
  have hinj : Function.Injective (fun k : Fin m => (e.symm k).val) := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  have hterm : forall k : Fin m,
      ((xiIndexedMultiplicity (e.symm k).val : Real) - 1) *
          (xiWaveWeight (e.symm k).val) ^ 2 =
        ((m : Real) - 1) * (1 / (1 / 4 + w ^ 2)) ^ 2 := by
    intro k
    dsimp only [xiIndexedMultiplicity, xiWaveWeight, m]
    rw [(e.symm k).property]
  have heval : Finset.sum S (fun p =>
      ((xiIndexedMultiplicity p : Real) - 1) * (xiWaveWeight p) ^ 2) =
        (m : Real) * ((m : Real) - 1) / (1 / 4 + w ^ 2) ^ 2 := by
    dsimp only [S]
    rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
    simp_rw [hterm]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hd : Not ((1 / 4 : Real) + w ^ 2 = 0) := by positivity
    field_simp [hd]
  have hl := (summable_xiDefectTerm hRH).sum_le_tsum S
    (fun p _ => xiDefectTerm_nonneg hRH p)
  rw [heval, <- xiMultiplicityDefect_eq_tsum hRH] at hl
  exact hl

theorem multiplicity_quadratic_global_budget (hRH : RiemannHypothesis) (w : Real) :
    let m := xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I)
    (m : Real) * ((m : Real) - 1) / (1 / 4 + w ^ 2) ^ 2 <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) ^ 2 -
        xiSimpleBaseline :=
  (multiplicity_quadratic_budget hRH w).trans (xiMultiplicityDefect_le hRH)


end PrimeFactorOscillations
