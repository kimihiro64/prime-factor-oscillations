/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistResonance
/-!
# Attainment of the quadratic-pair envelope

The positive local crest forces both retained character signs to be positive
when the odd field has at least thirteen elements. Thus the previously proved
pointwise envelope is attained. The scalar logarithmic lower bound supplies
the leading coefficient four for the integer product consumer.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticPairTwistExtrema
attribute [local instance] Classical.propDecidable

theorem exists_local_maximum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (hq : 13<=(Fintype.card F : Real)) :
    exists c : F, Not (c=0) /\ Not (c+h=0) /\
      traceFreePairWeight c h=((Fintype.card F : Real)+1)/((Fintype.card F : Real)-3) := by
  let q : Real := Fintype.card F
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have hq3 : 0<q-3 := by dsimp only [q]; linarith only [hq]
  have hex := QuadraticPairTwistResonance.exists_local_positive_crest
    hF h hh (by linarith only [hq])
  let c : F := Classical.choose hex
  have hcpos := Classical.choose_spec hex
  change 1/(4*q)<=QuadraticPairTwistLikelihood.localCorrection c h at hcpos
  have hc : Not (c=0) := by
    intro hz
    have hzcor : QuadraticPairTwistLikelihood.localCorrection c h=0 := by
      simp [hz,QuadraticPairTwistLikelihood.localCorrection,
        QuadraticPairTwistLikelihood.admissibilityMask,traceFreePairWeight_zero]
    rw [hzcor] at hcpos
    have hp : 0<1/(4*q) := by positivity
    linarith only [hcpos,hp]
  have hn : Not (c=-h) := by
    intro hz
    have hzcor : QuadraticPairTwistLikelihood.localCorrection c h=0 := by
      simp [hz,QuadraticPairTwistLikelihood.localCorrection,
        QuadraticPairTwistLikelihood.admissibilityMask,traceFreePairWeight_neg_shift]
    rw [hzcor] at hcpos
    have hp : 0<1/(4*q) := by positivity
    linarith only [hcpos,hp]
  have hch : Not (c+h=0) := by
    intro hz
    apply hn
    exact eq_neg_of_add_eq_zero_left hz
  have hcp : 1/(4*q)<=(1-2/q)*traceFreePairWeight c h-1 := by
    simpa only [QuadraticPairTwistLikelihood.localCorrection,
      QuadraticPairTwistLikelihood.admissibilityMask,if_neg hc,if_neg hn] using hcpos
  have hk : 0<1-2/q := by
    apply sub_pos.mpr
    apply (div_lt_one hq0).mpr
    dsimp only [q]
    linarith only [hq]
  have hmidid : (1-2/q)*((q-1)/(q-3))-1=2/(q*(q-3)) := by
    field_simp [ne_of_gt hq0,ne_of_gt hq3] <;> ring
  have hmid : (1-2/q)*((q-1)/(q-3))-1<1/(4*q) := by
    rw [hmidid]
    have hid : 1/(4*q)-2/(q*(q-3))=(q-11)/(4*q*(q-3)) := by
      field_simp [ne_of_gt hq0,ne_of_gt hq3] <;> ring
    apply sub_pos.mp
    rw [hid]
    apply div_pos
    . dsimp only [q]
      linarith only [hq]
    . positivity
  have hu : (q-1)/(q-3)<traceFreePairWeight c h := by
    by_contra hnlt
    have hule : traceFreePairWeight c h<=(q-1)/(q-3) := le_of_not_gt hnlt
    have hi := mul_le_mul_of_nonneg_left hule hk.le
    linarith only [hmid,hcp,hi]
  let A : Real := ((quadraticChar F) ((-h)*c) : Real)
  let B : Real := ((quadraticChar F) (h*(c+h)) : Real)
  have hval : traceFreePairWeight c h=(q-1+A+B)/(q-3) := by
    dsimp only [A,B,q]
    simp only [traceFreePairWeight,traceFreePairNumerator,if_neg hc,if_neg hn,
      twistPairNumerator,Int.cast_add,Int.cast_sub,Int.cast_natCast,Int.cast_one,
      Int.cast_mul,map_mul]
  have hsum : 0<A+B := by
    rw [hval] at hu
    have hid : ((q-1+A+B)/(q-3)-(q-1)/(q-3))*(q-3)=A+B := by
      field_simp [ne_of_gt hq3] <;> ring
    have hp := mul_pos (sub_pos.mpr hu) hq3
    rwa [hid] at hp
  have ha := QuadraticPairEuler.quadraticChar_real_signs ((-h)*c)
    (mul_ne_zero (neg_ne_zero.mpr hh) hc)
  have hb := QuadraticPairEuler.quadraticChar_real_signs (h*(c+h)) (mul_ne_zero hh hch)
  change A=1 \/ A=-1 at ha
  change B=1 \/ B=-1 at hb
  have hs : A+B=2 := by
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> linarith only [ha,hb,hsum]
  refine Exists.intro c (And.intro hc (And.intro hch ?_))
  rw [hval]
  change (q-1+A+B)/(q-3)=(q+1)/(q-3)
  congr 1
  linarith only [hs]

theorem log_envelope_lower (x : Real) (hx : 3<x) :
    4/x-4/x^2<=Real.log ((x+1)/(x-3)) := by
  have hx0 : 0<x := by linarith only [hx]
  have hx3 : 0<x-3 := by linarith only [hx]
  have hxp : 0<x+1 := by linarith only [hx]
  have hl := Real.one_sub_inv_le_log_of_pos
    (show 0<(x+1)/(x-3) from div_pos hxp hx3)
  have hi : 1-1/((x+1)/(x-3))=4/(x+1) := by
    field_simp [ne_of_gt hx3,ne_of_gt hxp] <;> ring
  simp only [<- one_div] at hl
  rw [hi] at hl
  have hd : 4/(x+1)-(4/x-4/x^2)=4/(x^2*(x+1)) := by
    field_simp [ne_of_gt hx0,ne_of_gt hxp] <;> ring
  have hn : 0<=4/(x^2*(x+1)) := by positivity
  linarith only [hl,hd,hn]

end FiniteField.QuadraticPairTwistExtrema
