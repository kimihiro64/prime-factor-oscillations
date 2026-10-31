/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTraceFreeKernel

/-!
# Exact covariance signs of the actual trace-free pair law

The complete count kernel is normalized only on q>=5. Off-overlap
covariances for chi(-1)=-1 are nonpositive before any magnitude estimate.
The positive endpoint rows are kept separately for a signed window.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def traceFreePairKernel (h k : F) : Real :=
  (1/(Fintype.card F : Real))*(Finset.univ.sum fun c : F =>
    traceFreePairWeight c h*traceFreePairWeight (c+k) h)

def traceFreePairCovariance (h k : F) : Real := traceFreePairKernel h k-1

theorem traceFreePairKernel_eq_model
    (hF : Not (ringChar F=2)) (h k : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) :
    traceFreePairKernel h k=(traceFreePairLagNumerator h k : Real)/
      ((Fintype.card F : Real)*((Fintype.card F : Real)-3)^2) := by
  let q : Real := Fintype.card F
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have hd : 0<q-3 := by dsimp only [q]; linarith only [hq]
  have hi : (Finset.univ.sum fun c : F =>
      ((traceFreePairNumerator c h*traceFreePairNumerator (c+k) h : Int) : Real))=
      (traceFreePairLagNumerator h k : Real) := by
    exact_mod_cast sum_traceFreePairNumerator_shift_correlation hF h k hh
  have he (c : F) :
      traceFreePairWeight c h*traceFreePairWeight (c+k) h=
      ((traceFreePairNumerator c h*traceFreePairNumerator (c+k) h : Int) : Real)/(q-3)^2 := by
    unfold traceFreePairWeight
    change ((traceFreePairNumerator c h : Real)/(q-3))*
      ((traceFreePairNumerator (c+k) h : Real)/(q-3))=_
    push_cast
    field_simp [ne_of_gt hd]
  unfold traceFreePairKernel
  simp_rw [he]
  rw [<- Finset.sum_div,hi]
  change (1/q)*((traceFreePairLagNumerator h k : Real)/(q-3)^2)=
    (traceFreePairLagNumerator h k : Real)/(q*(q-3)^2)
  field_simp [ne_of_gt hq0,ne_of_gt hd]

theorem traceFreePairCovariance_zero
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) :
    traceFreePairCovariance h 0=
      2/((Fintype.card F : Real)-3)-
      2*(1+((quadraticChar F) (-1) : Real))/
        ((Fintype.card F : Real)*((Fintype.card F : Real)-3)^2) := by
  unfold traceFreePairCovariance traceFreePairKernel
  simp only [add_zero,<- pow_two]
  rw [traceFreePairWeight_second_moment hF h hh hq]
  ring

theorem traceFreePairCovariance_nonoverlap
    (hF : Not (ringChar F=2)) (h k : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real))
    (hk0 : Not (k=0)) (hkh : Not (k=h)) (hkn : Not (k=-h)) :
    traceFreePairCovariance h k=
      -(4+2*((((quadraticChar F) h+(quadraticChar F) (-h))*(quadraticChar F) k+
        (quadraticChar F) (-h)*(quadraticChar F) (k-h)+
        (quadraticChar F) h*(quadraticChar F) (k+h) : Int) : Real)+
        2*(1+((quadraticChar F) (-1) : Real))/(Fintype.card F : Real))/
        ((Fintype.card F : Real)-3)^2 := by
  have hq0 : 0<(Fintype.card F : Real) := by linarith only [hq]
  have hd : 0<(Fintype.card F : Real)-3 := by linarith only [hq]
  unfold traceFreePairCovariance
  rw [traceFreePairKernel_eq_model hF h k hh hq]
  unfold traceFreePairLagNumerator
  dsimp only
  simp only [ite_eq_right hk0,ite_eq_right hkh,ite_eq_right hkn,mul_zero,add_zero]
  push_cast
  field_simp [ne_of_gt hq0,ne_of_gt hd]
  ring

theorem traceFreePairCovariance_neg (h k : F) :
    traceFreePairCovariance h (-k)=traceFreePairCovariance h k := by
  let e : Equiv F F :=
    { toFun := fun c => c-k
      invFun := fun c => c+k
      left_inv := by intro c; ring
      right_inv := by intro c; ring }
  have he := Equiv.sum_comp e (fun c : F => traceFreePairWeight c h*traceFreePairWeight (c+k) h)
  have hi (c : F) :
      traceFreePairWeight (c-k) h*traceFreePairWeight (c-k+k) h=
      traceFreePairWeight c h*traceFreePairWeight (c+(-k)) h := by
    rw [show c-k+k=c from by ring,show c-k=c+(-k) from by ring]
    ring
  change (Finset.univ.sum fun c : F =>
    traceFreePairWeight (c-k) h*traceFreePairWeight (c-k+k) h)=_ at he
  simp_rw [hi] at he
  unfold traceFreePairCovariance traceFreePairKernel
  rw [he]

theorem traceFreePairCovariance_nonpos_nonoverlap
    (hF : Not (ringChar F=2)) (h k : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) (ht : (quadraticChar F) (-1)=-1)
    (hk0 : Not (k=0)) (hkh : Not (k=h)) (hkn : Not (k=-h)) :
    traceFreePairCovariance h k<=0 := by
  have hkm : Not (k-h=0) := by intro he; apply hkh; linear_combination he
  have hkp : Not (k+h=0) := by intro he; apply hkn; linear_combination he
  have hA : And (-1<=((quadraticChar F) (h*(k+h)) : Real))
      (((quadraticChar F) (h*(k+h)) : Real)<=1) := by
    rcases QuadraticPairEuler.quadraticChar_real_signs (h*(k+h)) (mul_ne_zero hh hkp) with he | he <;>
      rw [he] <;> constructor <;> norm_num
  have hB : And (-1<=((quadraticChar F) (h*(k-h)) : Real))
      (((quadraticChar F) (h*(k-h)) : Real)<=1) := by
    rcases QuadraticPairEuler.quadraticChar_real_signs (h*(k-h)) (mul_ne_zero hh hkm) with he | he <;>
      rw [he] <;> constructor <;> norm_num
  have hf : (quadraticChar F) (-h)= -(quadraticChar F) h := by
    rw [show -h=(-1 : F)*h from by ring,map_mul,ht,neg_one_mul]
  have he :
      ((((quadraticChar F) h+(quadraticChar F) (-h))*(quadraticChar F) k+
        (quadraticChar F) (-h)*(quadraticChar F) (k-h)+
        (quadraticChar F) h*(quadraticChar F) (k+h) : Int) : Real)=
      ((quadraticChar F) (h*(k+h)) : Real)-((quadraticChar F) (h*(k-h)) : Real) := by
    rw [hf,map_mul,map_mul]
    push_cast
    ring
  have htR : ((quadraticChar F) (-1) : Real)=-1 := by exact_mod_cast ht
  rw [traceFreePairCovariance_nonoverlap hF h k hh hq hk0 hkh hkn,he,htR]
  simp only [add_neg_cancel,mul_zero,zero_div,add_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith only [hA.1,hB.2]) (sq_nonneg _)

theorem traceFreePairCovariance_adjacent_neg_one
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) (ht : (quadraticChar F) (-1)=-1) :
    traceFreePairCovariance h h=
      ((Fintype.card F : Real)-5-2*((quadraticChar F) (2 : F) : Real))/
        ((Fintype.card F : Real)-3)^2 := by
  have hq0 : 0<(Fintype.card F : Real) := by linarith only [hq]
  have hd : 0<(Fintype.card F : Real)-3 := by linarith only [hq]
  have hn : Not (h=-h) := by
    intro he
    have hz : (2 : F)*h=0 := by linear_combination he
    exact (mul_ne_zero (two_ne_zero_of_odd hF) hh) hz
  have hf : (quadraticChar F) (-h)= -(quadraticChar F) h := by
    rw [show -h=(-1 : F)*h from by ring,map_mul,ht,neg_one_mul]
  have h2 : (quadraticChar F) (h+h)=(quadraticChar F) (2 : F)*(quadraticChar F) h := by
    rw [show h+h=(2 : F)*h from by ring,map_mul]
  have hs : ((quadraticChar F) h : Real)^2=1 := by exact_mod_cast quadraticChar_sq_one hh
  unfold traceFreePairCovariance
  rw [traceFreePairKernel_eq_model hF h h hh hq]
  unfold traceFreePairLagNumerator
  dsimp only
  simp only [ite_eq_right hh,ite_true,ite_eq_right hn,sub_self,hf,h2,ht,
    add_neg_cancel,zero_mul,mul_zero,add_zero,zero_add]
  push_cast
  field_simp [ne_of_gt hq0,ne_of_gt hd]
  ring_nf
  rw [hs]
  simp

theorem traceFreePairCovariance_adjacent_le
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) (ht : (quadraticChar F) (-1)=-1) :
    traceFreePairCovariance h h<=1/((Fintype.card F : Real)-3) := by
  have hd : 0<(Fintype.card F : Real)-3 := by linarith only [hq]
  have hu : -1<=((quadraticChar F) (2 : F) : Real) := by
    rcases QuadraticPairEuler.quadraticChar_real_signs (2 : F)
      (two_ne_zero_of_odd hF) with he | he <;> linarith only [he]
  rw [traceFreePairCovariance_adjacent_neg_one hF h hh hq ht]
  calc
    _ <= ((Fintype.card F : Real)-3)/((Fintype.card F : Real)-3)^2 :=
      div_le_div_of_nonneg_right (by linarith only [hu]) (sq_nonneg _)
    _ = 1/((Fintype.card F : Real)-3) := by field_simp [ne_of_gt hd]

theorem traceFreePairCovariance_graph_upper
    (hF : Not (ringChar F=2)) (h k : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) (ht : (quadraticChar F) (-1)=-1) :
    traceFreePairCovariance h k<=
      ((if k=0 then (2 : Real) else 0)+(if k=h then 1 else 0)+
        (if k=-h then 1 else 0))/((Fintype.card F : Real)-3) := by
  have hn : Not (h=-h) := by
    intro he
    have hz : (2 : F)*h=0 := by linear_combination he
    exact (mul_ne_zero (two_ne_zero_of_odd hF) hh) hz
  by_cases hk0 : k=0
  . subst k
    rw [traceFreePairCovariance_zero hF h hh hq]
    norm_num [ht,Ne.symm hh,hh]
  . by_cases hkh : k=h
    . subst k
      simpa only [ite_eq_right hh,ite_true,ite_eq_right hn,zero_add,add_zero] using
        traceFreePairCovariance_adjacent_le hF h hh hq ht
    . by_cases hkn : k=-h
      . subst k
        rw [traceFreePairCovariance_neg]
        simpa only [ite_eq_right (neg_ne_zero.mpr hh),ite_eq_right (Ne.symm hn),ite_true,
          zero_add] using traceFreePairCovariance_adjacent_le hF h hh hq ht
      . simpa only [ite_eq_right hk0,ite_eq_right hkh,ite_eq_right hkn,zero_add,zero_div] using
          traceFreePairCovariance_nonpos_nonoverlap hF h k hh hq ht hk0 hkh hkn

theorem traceFreePairCovariance_positive_iff
    (hF : Not (ringChar F=2)) (h k : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) (ht : (quadraticChar F) (-1)=1)
    (hk0 : Not (k=0)) (hkh : Not (k=h)) (hkn : Not (k=-h)) :
    0<traceFreePairCovariance h k <->
      ((quadraticChar F) (h*k) : Real)=-1 /\
      ((quadraticChar F) (h*(k-h)) : Real)=-1 /\
      ((quadraticChar F) (h*(k+h)) : Real)=-1 := by
  have hkm : Not (k-h=0) := by intro he; apply hkh; linear_combination he
  have hkp : Not (k+h=0) := by intro he; apply hkn; linear_combination he
  have hA := QuadraticPairEuler.quadraticChar_real_signs (h*k) (mul_ne_zero hh hk0)
  have hB := QuadraticPairEuler.quadraticChar_real_signs (h*(k-h)) (mul_ne_zero hh hkm)
  have hC := QuadraticPairEuler.quadraticChar_real_signs (h*(k+h)) (mul_ne_zero hh hkp)
  have hf : (quadraticChar F) (-h)=(quadraticChar F) h := by
    rw [show -h=(-1 : F)*h from by ring,map_mul,ht,one_mul]
  have he :
      ((((quadraticChar F) h+(quadraticChar F) (-h))*(quadraticChar F) k+
        (quadraticChar F) (-h)*(quadraticChar F) (k-h)+
        (quadraticChar F) h*(quadraticChar F) (k+h) : Int) : Real)=
      2*((quadraticChar F) (h*k) : Real)+
        ((quadraticChar F) (h*(k-h)) : Real)+
        ((quadraticChar F) (h*(k+h)) : Real) := by
    rw [hf,map_mul,map_mul,map_mul]
    push_cast
    ring
  have hq0 : 0<(Fintype.card F : Real) := by linarith only [hq]
  have hd : 0<(Fintype.card F : Real)-3 := by linarith only [hq]
  have hd2 : 0<((Fintype.card F : Real)-3)^2 := sq_pos_of_pos hd
  have hp : 0<4/(Fintype.card F : Real) := div_pos (by norm_num) hq0
  have hu : 4/(Fintype.card F : Real)<=4/5 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq
  have htR : ((quadraticChar F) (-1) : Real)=1 := by exact_mod_cast ht
  rw [traceFreePairCovariance_nonoverlap hF h k hh hq hk0 hkh hkn,he,htR]
  norm_num only
  constructor
  . intro hpos
    by_contra hbad
    have hn : -(4+2*(2*((quadraticChar F) (h*k) : Real)+
        ((quadraticChar F) (h*(k-h)) : Real)+
        ((quadraticChar F) (h*(k+h)) : Real))+4/(Fintype.card F : Real))<=0 := by
      rcases hA with ha | ha <;> rcases hB with hb | hb <;> rcases hC with hc | hc <;>
        simp only [ha,hb,hc] at hbad <;> norm_num at hbad <;>
        rw [ha,hb,hc] <;> norm_num <;> linarith only [hp]
    have hnon := div_nonpos_of_nonpos_of_nonneg hn hd2.le
    linarith only [hpos,hnon]
  . intro hall
    rw [hall.1,hall.2.1,hall.2.2]
    apply div_pos _ hd2
    linarith only [hu]

end FiniteField
