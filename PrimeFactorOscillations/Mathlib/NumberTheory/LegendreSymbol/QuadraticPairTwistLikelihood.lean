/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistEuler
/-!
# Local likelihood corrections for integer quadratic-pair packets

The actual trace-free positive pair weight is compared with the flat
admissibility law. Its relative correction is extended by zero at the
two forbidden residues. It has exact mean zero, amplitude at most 3/q,
and variance at most 5/q^2 for q >= 7. The exact squared formula retains
all mask cross terms. These are local inputs to an integer-window
large-sieve consumer; no integer positivity theorem is asserted here.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticPairTwistLikelihood
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def admissibilityMask (c h : F) : Real :=
  if c=0 then 0 else if c=-h then 0 else 1

def localCorrection (c h : F) : Real :=
  (1-2/(Fintype.card F : Real))*traceFreePairWeight c h-admissibilityMask c h

theorem mask_indicator (c h : F) (hh : Not (h=0)) :
    admissibilityMask c h =
      1-(if c=0 then 1 else 0)-(if c=-h then 1 else 0) := by
  by_cases hc : c=0
  . have hn : Not ((0 : F)=-h) := fun hz => (neg_ne_zero.mpr hh) hz.symm
    simp [admissibilityMask,hc,hn]
  . by_cases hn : c=-h
    . simp [admissibilityMask,hc,hn,hh]
    . simp [admissibilityMask,hc,hn]

theorem mask_square (c h : F) :
    (admissibilityMask c h)^2=admissibilityMask c h := by
  unfold admissibilityMask
  split_ifs <;> norm_num

theorem sum_mask (h : F) (hh : Not (h=0)) :
    (Finset.univ.sum fun c : F => admissibilityMask c h) =
      (Fintype.card F : Real)-2 := by
  simp_rw [mask_indicator _ h hh]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  simp <;> ring

theorem weight_mul_mask (c h : F) :
    traceFreePairWeight c h*admissibilityMask c h=traceFreePairWeight c h := by
  by_cases hc : c=0
  . simp [hc,admissibilityMask,traceFreePairWeight_zero]
  . by_cases hn : c=-h
    . simp [hn,admissibilityMask,traceFreePairWeight_neg_shift]
    . simp [admissibilityMask,hc,hn]

theorem local_correction_mean_zero (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 7 <= (Fintype.card F : Real)) :
    (Finset.univ.sum fun c : F => localCorrection c h)=0 := by
  let q : Real := Fintype.card F
  have hq0 : Not (q=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  have hu := traceFreePairWeight_mean_one hF h hh (by linarith only [hq])
  change (1/q)*(Finset.univ.sum fun c : F => traceFreePairWeight c h)=1 at hu
  have hs : (Finset.univ.sum fun c : F => traceFreePairWeight c h)=q := by
    field_simp [hq0] at hu
    exact hu
  unfold localCorrection
  rw [Finset.sum_sub_distrib,<- Finset.mul_sum,sum_mask h hh,hs]
  change (1-2/q)*q-(q-2)=0
  field_simp [hq0] <;> ring

theorem local_correction_abs_le (c h : F) (hh : Not (h=0))
    (hq : 7 <= (Fintype.card F : Real)) :
    abs (localCorrection c h) <= 3/(Fintype.card F : Real) := by
  have hq0 : 0 < (Fintype.card F : Real) := by linarith only [hq]
  by_cases hc : c=0
  . simp [hc,localCorrection,admissibilityMask,traceFreePairWeight_zero]
    exact div_nonneg (by norm_num) hq0.le
  . by_cases hn : c=-h
    . simp [hn,localCorrection,admissibilityMask,traceFreePairWeight_neg_shift]
      exact div_nonneg (by norm_num) hq0.le
    . have hch : Not (c+h=0) := by
        intro hz
        apply hn
        calc
          c = (c+h)-h := by ring
          _ = -h := by rw [hz]; ring
      have hv := traceFreePairWeight_good_bounds c h hc hch hh
        (show 5 <= (Fintype.card F : Real) from by linarith only [hq])
      let q : Real := Fintype.card F
      have h0 : 0 < q := hq0
      have h3 : 0 < q-3 := by dsimp only [q]; linarith only [hq]
      have hq7 : 7 <= q := hq
      have hk : 0 <= 1-2/q := by
        apply sub_nonneg.mpr
        calc
          2/q <= q/q := div_le_div_of_nonneg_right (by linarith only [hq7]) h0.le
          _ = 1 := div_self (ne_of_gt h0)
      have he : (1-2/q)*((q+1)/(q-3))-(1+3/q) =
          (7-q)/(q*(q-3)) := by
        field_simp [ne_of_gt h0,ne_of_gt h3] <;> ring
      have hscalar : (1-2/q)*((q+1)/(q-3)) <= 1+3/q := by
        have hp : (7-q)/(q*(q-3)) <= 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith only [hq7]) (mul_pos h0 h3).le
        rw [<- he] at hp
        linarith only [hp]
      have hlo : 1-2/q <= (1-2/q)*traceFreePairWeight c h := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hv.1 hk
      have hup : (1-2/q)*traceFreePairWeight c h <= 1+3/q :=
        le_trans (mul_le_mul_of_nonneg_left hv.2 hk) hscalar
      have hi : 0 <= 1/q := one_div_nonneg.mpr h0.le
      unfold localCorrection
      simp only [admissibilityMask,if_neg hc,if_neg hn]
      change abs ((1-2/q)*traceFreePairWeight c h-1) <= 3/q
      apply abs_le.mpr
      constructor
      . have hdiv : 2/q <= 3/q :=
          div_le_div_of_nonneg_right (by norm_num) h0.le
        linarith only [hlo,hdiv]
      . linarith only [hup]

theorem local_correction_square (c h : F) :
    (localCorrection c h)^2 =
      (1-2/(Fintype.card F : Real))^2*(traceFreePairWeight c h)^2 -
        2*(1-2/(Fintype.card F : Real))*traceFreePairWeight c h+
          admissibilityMask c h := by
  unfold localCorrection
  calc
    _ = (1-2/(Fintype.card F : Real))^2*(traceFreePairWeight c h)^2 -
        2*(1-2/(Fintype.card F : Real))*
          (traceFreePairWeight c h*admissibilityMask c h)+
          (admissibilityMask c h)^2 := by ring
    _ = _ := by rw [weight_mul_mask,mask_square]

theorem local_correction_second_moment (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 7 <= (Fintype.card F : Real)) :
    (1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => (localCorrection c h)^2) =
      (1-2/(Fintype.card F : Real))*
        (QuadraticPairTwistEnergy.flatCorrection (Fintype.card F : Real)
          ((quadraticChar F) (-1) : Real)-1) := by
  let q : Real := Fintype.card F
  have hq0 : Not (q=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  have hu := traceFreePairWeight_mean_one hF h hh (by linarith only [hq])
  change (1/q)*(Finset.univ.sum fun c : F => traceFreePairWeight c h)=1 at hu
  have hs : (Finset.univ.sum fun c : F => traceFreePairWeight c h)=q := by
    field_simp [hq0] at hu
    exact hu
  have hM := traceFreePairWeight_second_moment hF h hh (by linarith only [hq])
  change (1/q)*(Finset.univ.sum fun c : F => (traceFreePairWeight c h)^2) =
    QuadraticPairTwistEnergy.moment q ((quadraticChar F) (-1) : Real) at hM
  have hsM : (Finset.univ.sum fun c : F => (traceFreePairWeight c h)^2) =
      q*QuadraticPairTwistEnergy.moment q ((quadraticChar F) (-1) : Real) := by
    field_simp [hq0] at hM
    exact hM
  simp_rw [local_correction_square]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,<- Finset.mul_sum,
    <- Finset.mul_sum,sum_mask h hh,hs,hsM]
  change (1/q)*((1-2/q)^2*(q*QuadraticPairTwistEnergy.moment q
    ((quadraticChar F) (-1) : Real))-2*(1-2/q)*q+(q-2)) = _
  unfold QuadraticPairTwistEnergy.flatCorrection
  change _ = (1-2/q)*(QuadraticPairTwistEnergy.moment q
    ((quadraticChar F) (-1) : Real)*(1-2/q)-1)
  field_simp [hq0] <;> ring

theorem local_correction_variance_le (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 7 <= (Fintype.card F : Real)) :
    (1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => (localCorrection c h)^2) <=
        5/(Fintype.card F : Real)^2 := by
  rw [local_correction_second_moment hF h hh hq]
  let q : Real := Fintype.card F
  have h0 : 0 < q := by dsimp only [q]; linarith only [hq]
  have he := QuadraticPairEuler.quadraticChar_real_signs (-1 : F)
    (neg_ne_zero.mpr one_ne_zero)
  have he0 : -1 <= ((quadraticChar F) (-1) : Real) := by rcases he with he | he <;> linarith
  have he1 : ((quadraticChar F) (-1) : Real) <= 1 := by rcases he with he | he <;> linarith
  have hd := QuadraticPairTwistEnergy.flatCorrection_bounds q
    ((quadraticChar F) (-1) : Real) (by dsimp only [q]; linarith only [hq]) he0 he1
  have hk : 0 <= 1-2/q := by
    apply sub_nonneg.mpr
    calc
      2/q <= q/q := div_le_div_of_nonneg_right
        (show 2 <= q from by dsimp only [q]; linarith only [hq]) h0.le
      _ = 1 := div_self (ne_of_gt h0)
  have hk1 : 1-2/q <= 1 := by
    have hp : 0 <= 2/q := div_nonneg (by norm_num) h0.le
    linarith only [hp]
  have hb : 0 <= 5/q^2 := div_nonneg (by norm_num) (sq_nonneg q)
  calc
    _ <= (1-2/q)*(5/q^2) := mul_le_mul_of_nonneg_left
      (show QuadraticPairTwistEnergy.flatCorrection q
        ((quadraticChar F) (-1) : Real)-1 <= 5/q^2 from by linarith only [hd.2]) hk
    _ <= 1*(5/q^2) := mul_le_mul_of_nonneg_right hk1 hb
    _ = _ := one_mul _

def flatPairWeight (c h : F) : Real :=
  ((Fintype.card F : Real)/((Fintype.card F : Real)-2))*admissibilityMask c h

theorem local_factorization (c h : F) (hq : 7 <= (Fintype.card F : Real)) :
    traceFreePairWeight c h=flatPairWeight c h*(1+localCorrection c h) := by
  let q : Real := Fintype.card F
  have h0 : Not (q=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  have h2 : Not (q-2=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  symm
  unfold flatPairWeight localCorrection
  change (q/(q-2)*admissibilityMask c h)*
    (1+((1-2/q)*traceFreePairWeight c h-admissibilityMask c h))=traceFreePairWeight c h
  calc
    _ = (q/(q-2))*((1-2/q)*
        (traceFreePairWeight c h*admissibilityMask c h)+
        (admissibilityMask c h-(admissibilityMask c h)^2)) := by ring
    _ = (q/(q-2))*((1-2/q)*traceFreePairWeight c h+
        (admissibilityMask c h-admissibilityMask c h)) := by
      rw [weight_mul_mask,mask_square]
    _ = _ := by field_simp [h0,h2] <;> ring

theorem likelihood_factor_bounds (c h : F) (hh : Not (h=0))
    (hq : 7 <= (Fintype.card F : Real)) :
    1/2 <= 1+localCorrection c h /\ 1+localCorrection c h <= 3/2 := by
  have ha := local_correction_abs_le c h hh hq
  have hd : 3/(Fintype.card F : Real) <= 1/2 := by
    calc
      _ <= (3 : Real)/7 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq
      _ <= _ := by norm_num
  have hb := abs_le.mp (le_trans ha hd)
  constructor <;> linarith only [hb.1,hb.2]

end FiniteField.QuadraticPairTwistLikelihood
