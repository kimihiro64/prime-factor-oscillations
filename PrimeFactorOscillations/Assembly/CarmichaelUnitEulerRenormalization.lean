/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.ProbeEuler

/-!
# Renormalization of the unramified slice at w = v = 1

The angular phase A is retained. The exact rational factors are removed
before the remaining Euler defect is estimated. No estimate for the full
signed high packet or new zero-free boundary is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

noncomputable section
namespace PrimeFactorOscillations.CarmichaelUnitEulerRenormalization
open scoped Classical
open OAI OAI.SevenEighths ProbeEuler ProbeLocal

def localRemainder (Q : Real) (A eta s z : Complex) : Complex :=
  1 + (Inv.inv (Q : Complex) *
    (coordD Q eta 1 s - coordR Q A s z)) / (1 - coordD Q eta 1 s)

theorem rational_slice_factorization (t V D R : Complex)
    (hV : Not (1 - V = 0)) (hD : Not (1 - D = 0))
    (hR : Not (1 - R = 0)) :
    continuedCorrection V t D
      (markedFactor R V t ((1 - t) * D) (-D + t * R) 1) =
      (1 - t * V) / (1 - R) * (1 + t * (D - R) / (1 - D)) := by
  unfold continuedCorrection markedFactor
  simp only [pow_one]
  field_simp [hV, hD, hR]
  ring

private theorem coordinate_K_slice (Q : Real) (eta s : Complex) (hQ : 0 < Q) :
    coordK Q eta s 1 =
      (1 - Inv.inv (Q : Complex)) * coordD Q eta 1 s := by
  have hn : Not ((Q : Complex) = 0) := by exact_mod_cast hQ.ne'
  unfold coordK coordD
  simp only [star_one, mul_one]
  rw [show -s - (1 : Complex) = -s + (-1) by ring,
    Complex.cpow_add _ _ hn, Complex.cpow_neg_one]
  field_simp

theorem unramified_slice_factorization (Q : Real) (A eta s z : Complex)
    (hQ : 0 < Q)
    (hV : Not (1 - coordV Q z = 0))
    (hD : Not (1 - coordD Q eta 1 s = 0))
    (hR : Not (1 - coordR Q A s z = 0)) :
    unramifiedClosed Q A eta 1 s 1 z =
      (1 - Inv.inv (Q : Complex) * coordV Q z) /
        (1 - coordR Q A s z) * localRemainder Q A eta s z := by
  have hK := coordinate_K_slice Q eta s hQ
  have hW : coordW Q 1 1 = Inv.inv (Q : Complex) := by
    simp [coordW, Complex.cpow_neg_one]
  unfold unramifiedClosed
  rw [hW, hK]
  exact rational_slice_factorization _ _ _ _ hV hD hR

private theorem D_half (Q : Real) (eta s : Complex)
    (hQ : 4 <= Q) (heta : norm eta <= 1) (hs : (3 / 4 : Real) <= s.re) :
    norm (coordD Q eta 1 s) <= 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  exact (coordD_norm_le Q hQ0 eta 1 s heta (by simp)).trans
    (rpow_le_half Q _ hQ (by linarith))

private theorem inverse_Q_norm (Q : Real) (hQ : 0 < Q) :
    norm (Inv.inv (Q : Complex)) = Q ^ (-(1 : Real)) := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ,
    Real.rpow_neg_one]

private theorem weighted_coordinate_bounds (Q : Real) (A eta s z : Complex)
    (hQ : 4 <= Q) (hA : norm A <= 1) (heta : norm eta <= 1)
    (hs : (3 / 4 : Real) <= s.re)
    (hsz : (3 / 4 : Real) <= s.re + z.re) :
    norm (Inv.inv (Q : Complex) * coordD Q eta 1 s) <=
        Q ^ (-(3 / 2) : Real) /\
      norm (Inv.inv (Q : Complex) * coordR Q A s z) <=
        Q ^ (-(3 / 2) : Real) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 <= Q := by linarith
  have hnorm := inverse_Q_norm Q hQ0
  constructor
  . rw [norm_mul, hnorm]
    calc
      _ <= Q ^ (-(1 : Real)) * Q ^ (-s.re) :=
        mul_le_mul_of_nonneg_left
          (coordD_norm_le Q hQ0 eta 1 s heta (by simp))
          (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ (-1 - s.re) := by rw [<- Real.rpow_add hQ0]; congr 1
      _ <= _ := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  . rw [norm_mul, hnorm]
    calc
      _ <= Q ^ (-(1 : Real)) * Q ^ (4 - 6 * s.re - 6 * z.re) :=
        mul_le_mul_of_nonneg_left
          (coordR_norm_le Q hQ0 A s z hA) (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ (3 - 6 * s.re - 6 * z.re) := by
        rw [<- Real.rpow_add hQ0]; congr 1; ring
      _ <= _ := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)

theorem local_remainder_defect (Q : Real) (A eta s z : Complex)
    (hQ : 4 <= Q) (hA : norm A <= 1) (heta : norm eta <= 1)
    (hs : (3 / 4 : Real) <= s.re)
    (hsz : (3 / 4 : Real) <= s.re + z.re) :
    norm (localRemainder Q A eta s z - 1) <=
      4 * Q ^ (-(3 / 2) : Real) := by
  have hD := D_half Q eta s hQ heta hs
  have hi := inv_one_sub_norm_le_two (coordD Q eta 1 s) hD
  have hb := weighted_coordinate_bounds Q A eta s z hQ hA heta hs hsz
  have hn :
      norm (Inv.inv (Q : Complex) *
        (coordD Q eta 1 s - coordR Q A s z)) <=
          2 * Q ^ (-(3 / 2) : Real) := by
    rw [mul_sub]
    exact (norm_sub_le _ _).trans (by linarith [hb.1, hb.2])
  unfold localRemainder
  rw [add_sub_cancel_left, div_eq_mul_inv, norm_mul]
  calc
    _ <= (2 * Q ^ (-(3 / 2) : Real)) * 2 :=
      mul_le_mul hn hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem local_remainder_lower (Q : Real) (A eta s z : Complex)
    (hQ : 4 <= Q) (hA : norm A <= 1) (heta : norm eta <= 1)
    (hs : (3 / 4 : Real) <= s.re)
    (hsz : (3 / 4 : Real) <= s.re + z.re) :
    (1 / 2 : Real) <= norm (localRemainder Q A eta s z) := by
  have hQ0 : 0 < Q := by linarith
  have hbound : 4 * Q ^ (-(3 / 2) : Real) <= 1 / 2 := by
    calc
      _ <= Q * Q ^ (-(3 / 2) : Real) :=
        mul_le_mul_of_nonneg_right hQ (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ (-(1 / 2) : Real) := by
        conv_lhs => lhs; rw [<- Real.rpow_one Q]
        rw [<- Real.rpow_add hQ0]
        norm_num
      _ <= _ := rpow_le_half Q _ hQ (by norm_num)
  have hb := (local_remainder_defect Q A eta s z hQ hA heta hs hsz).trans hbound
  have hn := norm_sub_norm_le (1 : Complex) (localRemainder Q A eta s z)
  rw [norm_one, norm_sub_rev] at hn
  linarith


theorem local_remainder_analyticAt (Q : Real) (A eta : Complex)
    (s z : Complex -> Complex) (x : Complex) (hQ : 4 <= Q)
    (heta : norm eta <= 1) (hs : AnalyticAt Complex s x)
    (hz : AnalyticAt Complex z x) (hsRe : (3 / 4 : Real) <= (s x).re) :
    AnalyticAt Complex (fun y => localRemainder Q A eta (s y) (z y)) x := by
  have hQ0 : 0 < Q := by linarith
  have hpow (f : Complex -> Complex) (hf : AnalyticAt Complex f x) :
      AnalyticAt Complex (fun y => (Q : Complex) ^ (f y)) x := by
    have heq : (fun y => (Q : Complex) ^ (f y)) =
        (fun y => Complex.exp (f y * (Real.log Q : Complex))) := by
      funext y
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hQ0.ne'),
        <- Complex.ofReal_log hQ0.le, mul_comm]
    rw [heq]
    fun_prop
  have hD : AnalyticAt Complex (fun y => coordD Q eta 1 (s y)) x := by
    have h := hpow (fun y => -s y) (by fun_prop)
    simp only [coordD, star_one, mul_one]
    apply AnalyticAt.mul
    . fun_prop
    . exact h
  have hR : AnalyticAt Complex (fun y => coordR Q A (s y) (z y)) x := by
    have h := hpow (fun y => 4 - 6 * s y - 6 * z y) (by fun_prop)
    exact analyticAt_const.mul h
  have hden : Not (1 - coordD Q eta 1 (s x) = 0) :=
    one_sub_ne_zero_of_norm_le_half _ (D_half Q eta (s x) hQ heta hsRe)
  apply AnalyticAt.add analyticAt_const
  apply AnalyticAt.div
  . exact analyticAt_const.mul (hD.sub hR)
  . exact analyticAt_const.sub hD
  . exact hden

theorem remainderProduct_ne_zero {I : Type*}
    (Q : I -> Real) (A eta : I -> Complex) (s z : Complex)
    (hQ : forall i, 4 <= Q i) (hA : forall i, norm (A i) <= 1)
    (heta : forall i, norm (eta i) <= 1)
    (hs : (3 / 4 : Real) <= s.re)
    (hsz : (3 / 4 : Real) <= s.re + z.re)
    (hsum : Summable (fun i => Q i ^ (-(3 / 2) : Real))) :
    Not (tprod (fun i => localRemainder (Q i) (A i) (eta i) s z) = 0) := by
  let f := fun i => localRemainder (Q i) (A i) (eta i) s z
  have hlower (i : I) : (1 / 2 : Real) <= norm (f i) :=
    local_remainder_lower _ _ _ _ _ (hQ i) (hA i) (heta i) hs hsz
  have hzero (i : I) : Not (f i = 0) :=
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hlower i))
  have hf : Summable (fun i => norm (f i - 1)) :=
    (hsum.mul_left 4).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => local_remainder_defect _ _ _ _ _ (hQ i) (hA i) (heta i) hs hsz)
  have hmf : Multipliable f := by
    simpa only [add_sub_cancel] using multipliable_one_add_of_summable hf
  have hi (i : I) : norm (Inv.inv (f i) - 1) <= 2 * norm (f i - 1) := by
    have hn : norm (Inv.inv (f i)) <= 2 := by
      rw [norm_inv, inv_eq_one_div]
      exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (hlower i)).trans
        (by norm_num)
    have he : Inv.inv (f i) - 1 = -(f i - 1) * Inv.inv (f i) := by
      field_simp [hzero i]
      ring
    rw [he, norm_mul, norm_neg]
    have h := mul_le_mul_of_nonneg_left hn (norm_nonneg (f i - 1))
    linarith
  have hif : Summable (fun i => norm (Inv.inv (f i) - 1)) :=
    (hf.mul_left 2).of_nonneg_of_le (fun _ => norm_nonneg _) hi
  have hmif : Multipliable (fun i => Inv.inv (f i)) := by
    simpa only [add_sub_cancel] using multipliable_one_add_of_summable hif
  have hp := hmf.tprod_mul hmif
  have heq : (fun i => f i * Inv.inv (f i)) = (fun _ : I => (1 : Complex)) := by
    funext i
    field_simp [hzero i]
  rw [heq, tprod_one] at hp
  intro h
  change tprod f = 0 at h
  rw [h, zero_mul] at hp
  exact one_ne_zero hp

theorem analyticOnNhd_remainderProduct {I : Type*}
    (Q : I -> Real) (A eta : I -> Complex)
    (s z : Complex -> Complex) (U : Set Complex)
    (hQ : forall i, 4 <= Q i) (hA : forall i, norm (A i) <= 1)
    (heta : forall i, norm (eta i) <= 1)
    (hsum : Summable (fun i => Q i ^ (-(3 / 2) : Real)))
    (hU : IsOpen U) (hs : AnalyticOnNhd Complex s U)
    (hz : AnalyticOnNhd Complex z U)
    (hRe : forall x, Membership.mem U x ->
      (3 / 4 : Real) <= (s x).re /\
        (3 / 4 : Real) <= (s x).re + (z x).re) :
    AnalyticOnNhd Complex
      (fun x => tprod (fun i => localRemainder (Q i) (A i) (eta i) (s x) (z x))) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro x hx
  classical
  have hb := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let r0 : Real := Classical.choose hb
  have hr0 : 0 < r0 := (Classical.choose_spec hb).1
  have hball : Set.Subset (Metric.ball x r0) U := (Classical.choose_spec hb).2
  let r : Real := r0 / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let K0 : Set Complex := Metric.closedBall x r
  have hKU : Set.Subset K0 U := by
    intro y hy
    apply hball
    change dist y x < r0
    have hd : dist y x <= r := Metric.mem_closedBall.mp hy
    dsimp [r] at hd
    linarith
  let f : I -> Complex -> Complex :=
    fun i y => localRemainder (Q i) (A i) (eta i) (s y) (z y)
  have hana (i : I) (y : Complex) (hy : Membership.mem U y) :
      AnalyticAt Complex (f i) y :=
    local_remainder_analyticAt _ _ _ s z y (hQ i) (heta i)
      (hs y hy) (hz y hy) (hRe y hy).1
  have hbound : forall i, forall y, Membership.mem K0 y ->
      norm (f i y - 1) <= 4 * Q i ^ (-(3 / 2) : Real) := by
    intro i y hy
    have h := hRe y (hKU hy)
    exact local_remainder_defect _ _ _ _ _ (hQ i) (hA i) (heta i) h.1 h.2
  have hcts : forall i, ContinuousOn (fun y => f i y - 1) K0 := by
    intro i y hy
    exact ((hana i y (hKU hy)).continuousAt.sub continuousAt_const).continuousWithinAt
  have hp : HasProdUniformlyOn f (fun y => tprod (fun i => f i y)) K0 := by
    have h := Summable.hasProdUniformlyOn_one_add
      (f := fun i y => f i y - 1) (isCompact_closedBall x r)
      (hsum.mul_left 4) (Filter.Eventually.of_forall hbound) hcts
    simpa only [add_sub_cancel] using h
  have hlim : TendstoLocallyUniformlyOn
      (fun F : Finset I => fun y => F.prod (fun i => f i y))
      (fun y => tprod (fun i => f i y)) Filter.atTop (Metric.ball x r) :=
    (hp.mono Metric.ball_subset_closedBall).hasProdLocallyUniformlyOn
  have hfin : forall F : Finset I,
      DifferentiableOn Complex (fun y => F.prod (fun i => f i y)) (Metric.ball x r) := by
    intro F y hy
    have hyU : Membership.mem U y := hKU (Metric.ball_subset_closedBall hy)
    have hprod : DifferentiableAt Complex (fun a => F.prod (fun i => f i a)) y := by
      induction F using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        fun_prop
      | @insert i F hi ih =>
        simp only [Finset.prod_insert hi]
        exact (hana i y hyU).differentiableAt.mul ih
    exact hprod.differentiableWithinAt
  have hd := hlim.differentiableOn (Filter.Eventually.of_forall hfin) Metric.isOpen_ball
  have hcenter : Membership.mem (Metric.ball x r) x := by simpa using hr
  exact ((hd x hcenter).differentiableAt
    (Metric.isOpen_ball.mem_nhds hcenter)).differentiableWithinAt


theorem finite_slice_factorization {I : Type*} (F : Finset I)
    (Q : I -> Real) (A eta : I -> Complex) (s z : Complex)
    (hQ : forall i, Membership.mem F i -> 0 < Q i)
    (hV : forall i, Membership.mem F i -> Not (1 - coordV (Q i) z = 0))
    (hD : forall i, Membership.mem F i -> Not (1 - coordD (Q i) (eta i) 1 s = 0))
    (hR : forall i, Membership.mem F i -> Not (1 - coordR (Q i) (A i) s z = 0)) :
    F.prod (fun i => unramifiedClosed (Q i) (A i) (eta i) 1 s 1 z) =
      F.prod (fun i => (1 - Inv.inv (Q i : Complex) * coordV (Q i) z) /
        (1 - coordR (Q i) (A i) s z)) *
      F.prod (fun i => localRemainder (Q i) (A i) (eta i) s z) := by
  rw [<- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact unramified_slice_factorization _ _ _ _ _ (hQ i hi)
    (hV i hi) (hD i hi) (hR i hi)


open FullEulerContinuation

private theorem source_norm_four {S : Finset SourcePrime} (P : HighSourcePrime S) :
    4 <= sourceNorm P.val := by
  have he : 4 <= Real.exp 2 := by
    have h := Real.add_one_le_exp (1 : Real)
    rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [sq_nonneg (Real.exp 1 - 2)]
  exact he.trans P.property.1

private theorem source_summable (S : Finset SourcePrime) :
    Summable (fun P : HighSourcePrime S => sourceNorm P.val ^ (-(3 / 2) : Real)) := by
  have h := source_norm_majorant_summable.comp_injective
    (Subtype.val_injective : Function.Injective (Subtype.val : HighSourcePrime S -> SourcePrime))
  exact h.of_nonneg_of_le
    (fun P => Real.rpow_nonneg (by linarith [source_norm_four P]) _)
    (fun P => Real.rpow_le_rpow_of_exponent_le
      (by linarith [source_norm_four P]) (by norm_num))

def sourceRemainderProduct (S : Finset SourcePrime) (eta : SourceCharacter)
    (s z : Complex) : Complex :=
  tprod (fun P : HighSourcePrime S =>
    localRemainder (sourceNorm P.val)
      (actualAPhase eta (OAI.CompletedGauss.primaryGenerator P.val.val))
      (HeckeFamily.idealCoeff eta P.val.val) s z)

theorem source_remainderProduct_ne_zero (S : Finset SourcePrime) (eta : SourceCharacter)
    (s z : Complex) (hs : (3 / 4 : Real) <= s.re)
    (hsz : (3 / 4 : Real) <= s.re + z.re) :
    Not (sourceRemainderProduct S eta s z = 0) :=
  remainderProduct_ne_zero
    (fun P : HighSourcePrime S => sourceNorm P.val)
    (fun P => actualAPhase eta (OAI.CompletedGauss.primaryGenerator P.val.val))
    (fun P => HeckeFamily.idealCoeff eta P.val.val) s z
    source_norm_four
    (fun P => actualAPhase_norm_le_one eta
      (OAI.CompletedGauss.primaryGenerator P.val.val))
    (fun P => HeckeFamily.idealCoeff_norm_le_one eta P.val.val)
    hs hsz (source_summable S)

theorem analyticOnNhd_sourceRemainderProduct
    (S : Finset SourcePrime) (eta : SourceCharacter)
    (s z : Complex -> Complex) (U : Set Complex) (hU : IsOpen U)
    (hs : AnalyticOnNhd Complex s U) (hz : AnalyticOnNhd Complex z U)
    (hRe : forall x, Membership.mem U x ->
      (3 / 4 : Real) <= (s x).re /\
        (3 / 4 : Real) <= (s x).re + (z x).re) :
    AnalyticOnNhd Complex (fun x => sourceRemainderProduct S eta (s x) (z x)) U :=
  analyticOnNhd_remainderProduct
    (fun P : HighSourcePrime S => sourceNorm P.val)
    (fun P => actualAPhase eta (OAI.CompletedGauss.primaryGenerator P.val.val))
    (fun P => HeckeFamily.idealCoeff eta P.val.val) s z U
    source_norm_four
    (fun P => actualAPhase_norm_le_one eta
      (OAI.CompletedGauss.primaryGenerator P.val.val))
    (fun P => HeckeFamily.idealCoeff_norm_le_one eta P.val.val)
    (source_summable S) hU hs hz hRe

end PrimeFactorOscillations.CarmichaelUnitEulerRenormalization
