/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistLikelihood
/-!
# Nonvanishing variance and positive local pair-packet crests

The exact correction variance is at least 1/q^2 in every odd field of
cardinality q >= 7. Combining this with the proved centered mean and
3/q amplitude yields an admissible positive correction of size at least
1/(4*q). All mask terms in the source second moment are retained.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticPairTwistResonance
attribute [local instance] Classical.propDecidable

theorem variance_lower_scalar (q epsilon : Real) (hq : 7<=q) (he : epsilon<=1) :
    1/q^2 <= (1-2/q)*(QuadraticPairTwistEnergy.flatCorrection q epsilon-1) := by
  have h0 : 0<q := by linarith only [hq]
  have h3 : 0<q-3 := by linarith only [hq]
  have hid : (1-2/q)*(QuadraticPairTwistEnergy.flatCorrection q epsilon-1)-1/q^2 =
      ((q-7)^3+13*(q-7)^2+54*(q-7)+68+2*(1-epsilon)*(q-2)^2)/
        (q^3*(q-3)^2) := by
    unfold QuadraticPairTwistEnergy.flatCorrection QuadraticPairTwistEnergy.moment
    field_simp [ne_of_gt h0,ne_of_gt h3] <;> ring
  have h7 : 0<=q-7 := by linarith only [hq]
  have hE : 0<=1-epsilon := by linarith only [he]
  have hn : 0<=((q-7)^3+13*(q-7)^2+54*(q-7)+68+2*(1-epsilon)*(q-2)^2) := by positivity
  have hd : 0<=q^3*(q-3)^2 := mul_nonneg (pow_nonneg h0.le _) (sq_nonneg _)
  have hh := div_nonneg hn hd
  rw [<- hid] at hh
  linarith only [hh]

theorem local_correction_variance_lower {F : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (hq : 7<=(Fintype.card F : Real)) :
    1/(Fintype.card F : Real)^2 <=
      (1/(Fintype.card F : Real))*(Finset.univ.sum fun c : F =>
        (QuadraticPairTwistLikelihood.localCorrection c h)^2) := by
  rw [QuadraticPairTwistLikelihood.local_correction_second_moment hF h hh hq]
  have hs := QuadraticPairEuler.quadraticChar_real_signs (-1 : F)
    (neg_ne_zero.mpr one_ne_zero)
  have he : ((quadraticChar F) (-1) : Real)<=1 := by
    rcases hs with he | he <;> linarith only [he]
  exact variance_lower_scalar (Fintype.card F : Real)
    ((quadraticChar F) (-1) : Real) hq he

theorem centered_variance_positive_crest {I : Type*} [Fintype I]
    (w : I -> Real) (hq : 7<=(Fintype.card I : Real))
    (hmean : Finset.univ.sum w=0)
    (habs : forall c, abs (w c)<=3/(Fintype.card I : Real))
    (hvar : 1/(Fintype.card I : Real)^2 <=
      (1/(Fintype.card I : Real))*(Finset.univ.sum fun c : I => (w c)^2)) :
    exists c : I, 1/(4*(Fintype.card I : Real))<=w c := by
  let q : Real := Fintype.card I
  have h0 : 0<q := by dsimp only [q]; linarith only [hq]
  by_contra hn
  have hu : forall c : I, w c<=1/(4*q) := by
    intro c
    apply le_of_lt
    apply lt_of_not_ge
    intro hc
    apply hn
    exact Exists.intro c hc
  have hp : forall c : I,
      (w c)^2<=(1/(4*q)-3/q)*w c+(1/(4*q))*(3/q) := by
    intro c
    have hl := (abs_le.mp (habs c)).1
    change -(3/q)<=w c at hl
    have hc := mul_nonneg (sub_nonneg.mpr (hu c))
      (show 0<=w c+3/q from by linarith only [hl])
    nlinarith only [hc]
  have hs := Finset.sum_le_sum (fun c (_ : Membership.mem (Finset.univ : Finset I) c) => hp c)
  rw [Finset.sum_add_distrib,<- Finset.mul_sum,hmean] at hs
  simp only [mul_zero,zero_add,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  have he : (1/q)*(Finset.univ.sum fun c : I => (w c)^2)<=3/(4*q^2) := by
    calc
      _ <= (1/q)*((Fintype.card I : Real)*((1/(4*q))*(3/q))) :=
        mul_le_mul_of_nonneg_left hs (one_div_nonneg.mpr h0.le)
      _ = _ := by change (1/q)*(q*((1/(4*q))*(3/q)))=_; field_simp [ne_of_gt h0] <;> ring
  change 1/q^2<=(1/q)*(Finset.univ.sum fun c : I => (w c)^2) at hvar
  have hi : 0<1/q^2 := one_div_pos.mpr (sq_pos_of_pos h0)
  have hid : 3/(4*q^2)=(3/4)*(1/q^2) := by ring
  rw [hid] at he
  nlinarith only [hvar,he,hi]

theorem exists_local_positive_crest {F : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (hq : 7<=(Fintype.card F : Real)) :
    exists c : F, 1/(4*(Fintype.card F : Real))<=
      QuadraticPairTwistLikelihood.localCorrection c h := by
  exact centered_variance_positive_crest
    (fun c : F => QuadraticPairTwistLikelihood.localCorrection c h) hq
    (QuadraticPairTwistLikelihood.local_correction_mean_zero hF h hh hq)
    (fun c => QuadraticPairTwistLikelihood.local_correction_abs_le c h hh hq)
    (local_correction_variance_lower hF h hh hq)

end FiniteField.QuadraticPairTwistResonance
