/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairCovariance

/-!
# All-character raw pair covariance and exact linked-twist compensation

The full lag kernel retains every trace and singular-row correction over
all odd finite fields. At the shared-endpoint lag, a nonsquare gap dilation
cancels the remaining CM trace exactly in the sum of the two actual raw
correlations. No Hasse estimate or integer short-window mass is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem splitCubicPointTrace_reflection
    (hF : Not (ringChar F=2)) (h c : F) :
    splitCubicPointTrace (-h-c) (-c)=
      (quadraticChar F) (-1)*splitCubicPointTrace c (c+h) := by
  calc
    _ = splitCubicPointTrace ((-1 : F)*c) ((-1 : F)*(c+h)) := by
      rw [splitCubicPointTrace_comm hF]
      congr 1 <;> ring
    _ = _ := splitCubicPointTrace_scale hF (-1)
      (neg_ne_zero.mpr one_ne_zero) c (c+h)

theorem quadraticPairCorrelationKernel_adjacent_general
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0)) :
    quadraticPairCorrelationKernel h h=-1-(quadraticChar F) (-1) := by
  have hne : Not (h=-h) := by
    intro hz
    have he : (2 : F)*h=0 := by
      calc
        _=h+h := by ring
        _=h+(-h) := congrArg (fun x : F => h+x) hz
        _=0 := add_neg_cancel h
    exact (mul_ne_zero (two_ne_zero_of_odd hF) hh) he
  have hp (x : F) :
      (quadraticChar F) (x*(x-h))*(quadraticChar F) ((x+h)*(x+h-h))=
      (quadraticChar F) ((x-h)*(x+h))-
        (if x=0 then (quadraticChar F) ((-h)*h) else 0) := by
    by_cases hx : x=0
    . subst x
      simp
    . have he : (x*(x-h))*((x+h)*(x+h-h))=x^2*((x-h)*(x+h)) := by ring
      rw [<- map_mul,he,map_mul,map_pow,quadraticChar_sq_one hx,one_mul]
      simp only [ite_eq_right hx,sub_zero]
  have hs : (Finset.univ.sum fun x : F => (quadraticChar F) ((x-h)*(x+h)))=-1 := by
    simpa only [sub_neg_eq_add] using quadraticChar_sum_mul_sub hF h (-h) hne
  have hb : (quadraticChar F) ((-h)*h)=(quadraticChar F) (-1) := by
    rw [show (-h)*h=(-1 : F)*h^2 from by ring,map_mul,map_pow,
      quadraticChar_sq_one hh,mul_one]
  unfold quadraticPairCorrelationKernel
  simp_rw [hp]
  rw [Finset.sum_sub_distrib,hs,hb]
  simp

theorem completed_trace_numerator_shift_correlation
    (hF : Not (ringChar F=2)) (h k : F) (hh : Not (h=0))
    (A alpha beta : Int) :
    (Finset.univ.sum fun c : F =>
      (A-splitCubicPointTrace c (c+h)-
        alpha*(quadraticChar F) c-beta*(quadraticChar F) (c+h))*
      (A-splitCubicPointTrace (c+k) (c+k+h)-
        alpha*(quadraticChar F) (c+k)-beta*(quadraticChar F) (c+k+h)))=
      (Fintype.card F : Int)*A^2+
        (Fintype.card F : Int)*quadraticPairCorrelationKernel h k-1+
      (alpha^2+beta^2)*((Fintype.card F : Int)*(if k=0 then 1 else 0)-1)+
      alpha*beta*((Fintype.card F : Int)*
        ((if k=h then 1 else 0)+(if k=-h then 1 else 0))-2)-
      (alpha+beta)*((Fintype.card F : Int)*
        ((quadraticChar F) (k*(k-h))+(quadraticChar F) (k*(k+h)))+2) := by
  let e : Equiv F F :=
    { toFun := fun c => c+k
      invFun := fun c => c-k
      left_inv := by intro c; ring
      right_inv := by intro c; ring }
  have hts : (Finset.univ.sum fun c : F =>
      splitCubicPointTrace (c+k) (c+k+h))=0 :=
    (Equiv.sum_comp e (fun c : F => splitCubicPointTrace c (c+h))).trans
      (sum_splitCubicPointTrace hF h)
  have hk : (k+h=h) <-> k=0 := by
    constructor
    . intro ht
      exact add_right_cancel (ht.trans (zero_add h).symm)
    . intro ht
      rw [ht,zero_add]
  have hn : (k+h=0) <-> k=-h := by
    constructor
    . exact eq_neg_of_add_eq_zero_left
    . intro ht
      rw [ht,neg_add_cancel]
  have hxx := quadraticChar_translate_correlation hF (0 : F) k
  simp only [add_zero] at hxx
  have hyy := quadraticChar_translate_correlation hF h (k+h)
  simp only [hk] at hyy
  have hxy := quadraticChar_translate_correlation hF (0 : F) (k+h)
  simp only [add_zero,hn] at hxy
  have hyx := quadraticChar_translate_correlation hF h k
  have htx := sum_splitCubicPointTrace_mul_char hF h k hh
  have hty := sum_splitCubicPointTrace_mul_char hF h (k+h) hh
  rw [show (k+h)*(k+h-h)=k*(k+h) from by ring] at hty
  have hxt := sum_splitCubicPointTrace_shift_mul_char hF h k 0 hh
  simp only [add_zero] at hxt
  rw [show (0-k)*(0-k-h)=k*(k+h) from by ring] at hxt
  have hyt := sum_splitCubicPointTrace_shift_mul_char hF h k h hh
  rw [show (h-k)*(h-k-h)=k*(k-h) from by ring] at hyt
  have hp (c : F) :
      (A-splitCubicPointTrace c (c+h)-
        alpha*(quadraticChar F) c-beta*(quadraticChar F) (c+h))*
      (A-splitCubicPointTrace (c+k) (c+k+h)-
        alpha*(quadraticChar F) (c+k)-beta*(quadraticChar F) (c+k+h))=
      A^2+
      splitCubicPointTrace c (c+h)*splitCubicPointTrace (c+k) (c+k+h)+
      alpha^2*((quadraticChar F) c*(quadraticChar F) (c+k))+
      beta^2*((quadraticChar F) (c+h)*(quadraticChar F) (c+(k+h)))+
      (alpha*beta)*((quadraticChar F) c*(quadraticChar F) (c+(k+h)))+
      (alpha*beta)*((quadraticChar F) (c+h)*(quadraticChar F) (c+k))-
      A*splitCubicPointTrace c (c+h)-
      A*splitCubicPointTrace (c+k) (c+k+h)-
      (A*alpha)*(quadraticChar F) c-(A*alpha)*(quadraticChar F) (c+k)-
      (A*beta)*(quadraticChar F) (c+h)-(A*beta)*(quadraticChar F) (c+(k+h))+
      alpha*(splitCubicPointTrace c (c+h)*(quadraticChar F) (c+k))+
      alpha*(splitCubicPointTrace (c+k) (c+k+h)*(quadraticChar F) c)+
      beta*(splitCubicPointTrace c (c+h)*(quadraticChar F) (c+(k+h)))+
      beta*(splitCubicPointTrace (c+k) (c+k+h)*(quadraticChar F) (c+h)) := by
    simp only [add_assoc]
    ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,<- Finset.mul_sum]
  rw [splitCubicPointTrace_shift_correlation hF h k hh,hxx,hyy,hxy,hyx,
    sum_splitCubicPointTrace hF h,hts,quadraticChar_sum_zero hF,
    quadraticChar_translate_sum hF k,quadraticChar_translate_sum hF h,
    quadraticChar_translate_sum hF (k+h),htx,hxt,hty,hyt]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring


theorem completedQuadraticPairNumerator_shift_correlation_general
    (hF : Not (ringChar F=2)) (h k : F) (hh : Not (h=0)) :
    let q : Int := Fintype.card F
    let e := (quadraticChar F) h
    let f := (quadraticChar F) (-h)
    (Finset.univ.sum fun c : F =>
      completedQuadraticPairNumerator c h*completedQuadraticPairNumerator (c+k) h)=
      q*(q-1+e+f)^2+q*quadraticPairCorrelationKernel h k-1+
      ((1-f)^2+(1-e)^2)*(q*(if k=0 then 1 else 0)-1)+
      (1-f)*(1-e)*(q*((if k=h then 1 else 0)+(if k=-h then 1 else 0))-2)-
      (2-f-e)*(q*((quadraticChar F) (k*(k-h))+
        (quadraticChar F) (k*(k+h)))+2) := by
  dsimp only
  have ht := completed_trace_numerator_shift_correlation hF h k hh
    ((Fintype.card F : Int)-1+(quadraticChar F) h+(quadraticChar F) (-h))
    (1-(quadraticChar F) (-h)) (1-(quadraticChar F) h)
  have hs : (1-(quadraticChar F) (-h))+(1-(quadraticChar F) h)=
      2-(quadraticChar F) (-h)-(quadraticChar F) h := by ring
  rw [hs] at ht
  exact ht

theorem completedQuadraticPairNumerator_reflection_general
    (hF : Not (ringChar F=2)) (h c : F) :
    let q : Int := Fintype.card F
    let t := (quadraticChar F) (-1)
    let e := (quadraticChar F) h
    let f := (quadraticChar F) (-h)
    completedQuadraticPairNumerator c h+completedQuadraticPairNumerator (-h-c) h=
      2*(q-1+e+f)-(1+t)*splitCubicPointTrace c (c+h)-
      ((1-f)+t*(1-e))*(quadraticChar F) c-
      ((1-e)+t*(1-f))*(quadraticChar F) (c+h) := by
  dsimp only
  have hn (a : F) :
      (quadraticChar F) (-a)=(quadraticChar F) (-1)*(quadraticChar F) a := by
    rw [show -a=(-1 : F)*a from by ring,map_mul]
  have he : -h-c+h=-c := by ring
  have ht : splitCubicPointTrace (-h-c) (-h-c+h)=
      (quadraticChar F) (-1)*splitCubicPointTrace c (c+h) := by
    rw [he]
    exact splitCubicPointTrace_reflection hF h c
  unfold completedQuadraticPairNumerator
  rw [ht,he,show -h-c=-(c+h) from by ring,hn (c+h),hn c]
  ring

theorem completedQuadraticPairNumerator_boundary_correction_general
    (hF : Not (ringChar F=2)) (h k : F) :
    let q : Int := Fintype.card F
    let t := (quadraticChar F) (-1)
    let e := (quadraticChar F) h
    let f := (quadraticChar F) (-h)
    let A := q-1+e+f
    let alpha := 1-f
    let beta := 1-e
    completedQuadraticPairNumerator (-k) h+
      completedQuadraticPairNumerator (-h-k) h+
      completedQuadraticPairNumerator k h+
      completedQuadraticPairNumerator (k-h) h=
      4*A-(1+t)*(splitCubicPointTrace k (k+h)+splitCubicPointTrace (k-h) k)-
      (1+t)*(alpha+beta)*(quadraticChar F) k-
      (alpha+t*beta)*(quadraticChar F) (k-h)-
      (t*alpha+beta)*(quadraticChar F) (k+h) := by
  have ha := completedQuadraticPairNumerator_reflection_general hF h k
  have hb := completedQuadraticPairNumerator_reflection_general hF h (k-h)
  dsimp only at ha hb
  dsimp only
  have he : -h-(k-h)=-k := by ring
  have hf : k-h+h=k := by ring
  rw [he,hf] at hb
  calc
    _ = (completedQuadraticPairNumerator k h+completedQuadraticPairNumerator (-h-k) h)+
        (completedQuadraticPairNumerator (k-h) h+completedQuadraticPairNumerator (-k) h) := by ring
    _ = _ := by
      rw [ha,hb]
      ring

theorem monicQuadraticPairCount_shift_correlation_general
    (hF : Not (ringChar F=2)) (h k : F) (hh : Not (h=0)) :
    let q : Int := Fintype.card F
    let t := (quadraticChar F) (-1)
    let e := (quadraticChar F) h
    let f := (quadraticChar F) (-h)
    let A := q-1+e+f
    let alpha := 1-f
    let beta := 1-e
    16*(Finset.univ.sum fun c : F =>
      monicQuadraticPairCount c h*monicQuadraticPairCount (c+k) h)=
      q*A^2+q*quadraticPairCorrelationKernel h k-1+
      (alpha^2+beta^2)*(q*(if k=0 then 1 else 0)-1)+
      alpha*beta*(q*((if k=h then 1 else 0)+(if k=-h then 1 else 0))-2)-
      (alpha+beta)*(q*((quadraticChar F) (k*(k-h))+
        (quadraticChar F) (k*(k+h)))+2)-
      q*(4*A-(1+t)*(splitCubicPointTrace k (k+h)+splitCubicPointTrace (k-h) k)-
        (1+t)*(alpha+beta)*(quadraticChar F) k-
        (alpha+t*beta)*(quadraticChar F) (k-h)-
        (t*alpha+beta)*(quadraticChar F) (k+h))+
      q^2*(2*(if k=0 then 1 else 0)+(if k=h then 1 else 0)+(if k=-h then 1 else 0)) := by
  dsimp only
  rw [quadraticPairCount_shift_completion hF h k hh,
    completedQuadraticPairNumerator_shift_correlation_general hF h k hh,
    completedQuadraticPairNumerator_boundary_correction_general hF h k]
  ring


theorem monicQuadraticPairCount_adjacent_correlation_general
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0)) :
    let q : Int := Fintype.card F
    let t := (quadraticChar F) (-1)
    let e := (quadraticChar F) h
    16*(Finset.univ.sum fun c : F =>
      monicQuadraticPairCount c h*monicQuadraticPairCount (c+h) h)=
      q^3-5*q^2+(5-4*(quadraticChar F) (2 : F))*q-11-2*t+
      (1+t)*(e*(2*q^2+(2*(quadraticChar F) (2 : F)-4)*q+6)+
        q*splitCubicPointTrace h (h+h)) := by
  have he2 := quadraticChar_sq_one hh
  have ht2 : ((quadraticChar F) (-1))^2=1 :=
    quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  have hne : Not (h=-h) := by
    intro hz
    have he : (2 : F)*h=0 := by
      calc
        _=h+h := by ring
        _=h+(-h) := congrArg (fun x : F => h+x) hz
        _=0 := add_neg_cancel h
    exact (mul_ne_zero (two_ne_zero_of_odd hF) hh) he
  have hz : (quadraticChar F) (0 : F)=0 := by simp
  have hprod : (quadraticChar F) (h*(h+h))=(quadraticChar F) (2 : F) := by
    rw [show h*(h+h)=(2 : F)*h^2 from by ring,map_mul,map_pow,he2,mul_one]
  have hsum : (quadraticChar F) (h+h)=
      (quadraticChar F) (2 : F)*(quadraticChar F) h := by
    rw [show h+h=(2 : F)*h from by ring,map_mul]
  have hneg : (quadraticChar F) (-h)=
      (quadraticChar F) (-1)*(quadraticChar F) h := by
    rw [show -h=(-1 : F)*h from by ring,map_mul]
  have hi := monicQuadraticPairCount_shift_correlation_general hF h h hh
  dsimp only at hi
  dsimp only
  rw [quadraticPairCorrelationKernel_adjacent_general hF h hh] at hi
  simp only [ite_eq_right hh,ite_true,ite_eq_right hne,sub_self,mul_zero,
    zero_add,add_zero] at hi
  simp only [hz,hprod,hsum,splitCubicPointTrace_zero_left hF,hneg] at hi
  calc
    _ = _ := hi
    _ = _ := by
      ring_nf
      simp only [he2,ht2]
      ring

theorem monicQuadraticPairCount_twist_compensated_adjacent
    (hF : Not (ringChar F=2)) (h a : F) (hh : Not (h=0))
    (ha : (quadraticChar F) a=-1) :
    let q : Int := Fintype.card F
    8*(Finset.univ.sum fun c : F =>
      monicQuadraticPairCount c h*monicQuadraticPairCount (c+h) h+
      monicQuadraticPairCount c (a*h)*monicQuadraticPairCount (c+a*h) (a*h))=
      q^3-5*q^2+(5-4*(quadraticChar F) (2 : F))*q-11-
        2*(quadraticChar F) (-1) := by
  have ha0 : Not (a=0) := by
    intro hz
    subst a
    norm_num at ha
  have hah : Not (a*h=0) := mul_ne_zero ha0 hh
  have ht : splitCubicPointTrace (a*h) (a*h+a*h)=
      -splitCubicPointTrace h (h+h) := by
    rw [show a*h+a*h=a*(h+h) from by ring,
      splitCubicPointTrace_scale hF a ha0 h (h+h),ha,neg_one_mul]
  have he : (quadraticChar F) (a*h)=-(quadraticChar F) h := by
    rw [map_mul,ha,neg_one_mul]
  have hi := monicQuadraticPairCount_adjacent_correlation_general hF h hh
  have hj := monicQuadraticPairCount_adjacent_correlation_general hF (a*h) hah
  dsimp only at hi hj
  dsimp only
  rw [ht,he] at hj
  rw [Finset.sum_add_distrib]
  nlinarith only [hi,hj]

def compensatedQuadraticPairCrossMoment (q t u : Real) : Real :=
  (q^3-5*q^2+(5-4*u)*q-11-2*t)/
    (q*((q-3)^2+2*(1+t)))

theorem compensatedQuadraticPairCrossMoment_gt_one
    (q t u : Real) (hq : 16<=q)
    (ht : And (-1<=t) (t<=1)) (hu : And (-1<=u) (u<=1)) :
    1<compensatedQuadraticPairCrossMoment q t u := by
  let D : Real := (q-3)^2+2*(1+t)
  have hq0 : 0<q := by linarith only [hq]
  have hDlow : (q-3)^2<=D := by dsimp only [D]; linarith only [ht.1]
  have hD : 0<D := lt_of_lt_of_le
    (sq_pos_of_pos (by linarith only [hq])) hDlow
  have hmain : 0<(q-13)*(q+1) := mul_pos
    (by linarith only [hq]) (by linarith only [hq])
  have h1 : 0<=(1-u)*q := mul_nonneg
    (by linarith only [hu.2]) (le_of_lt hq0)
  have h2 : 0<=(1-t)*(q+1) := mul_nonneg
    (by linarith only [ht.2]) (by linarith only [hq])
  have hn : q*D<q^3-5*q^2+(5-4*u)*q-11-2*t := by
    dsimp only [D]
    nlinarith only [hmain,h1,h2]
  have hpositive : 0<(q^3-5*q^2+(5-4*u)*q-11-2*t-q*D)/(q*D) :=
    div_pos (sub_pos.mpr hn) (mul_pos hq0 hD)
  have he : compensatedQuadraticPairCrossMoment q t u-1=
      (q^3-5*q^2+(5-4*u)*q-11-2*t-q*D)/(q*D) := by
    unfold compensatedQuadraticPairCrossMoment
    change (q^3-5*q^2+(5-4*u)*q-11-2*t)/(q*D)-1=_
    field_simp [ne_of_gt hq0,ne_of_gt hD]
  rw [<- he] at hpositive
  linarith only [hpositive]

theorem compensatedQuadraticPairCrossMoment_error
    (q t u : Real) (hq : 16<=q)
    (ht : And (-1<=t) (t<=1)) (hu : And (-1<=u) (u<=1)) :
    abs (compensatedQuadraticPairCrossMoment q t u-(1+1/q))<=12/q^2 := by
  let D : Real := (q-3)^2+2*(1+t)
  let n : Real := -(4*u+2*t)*q-22-4*t
  have hq0 : 0<q := by linarith only [hq]
  have hDlow : (q-3)^2<=D := by dsimp only [D]; linarith only [ht.1]
  have hD : 0<D := lt_of_lt_of_le
    (sq_pos_of_pos (by linarith only [hq])) hDlow
  have h1 : 0<=(1-u)*q := mul_nonneg
    (by linarith only [hu.2]) (le_of_lt hq0)
  have h2 : 0<=(1-t)*(q+2) := mul_nonneg
    (by linarith only [ht.2]) (by linarith only [hq])
  have h3 : 0<=(1+u)*q := mul_nonneg
    (by linarith only [hu.1]) (le_of_lt hq0)
  have h4 : 0<=(1+t)*(q+2) := mul_nonneg
    (by linarith only [ht.1]) (by linarith only [hq])
  have hn : abs n<=6*q+26 := by
    apply abs_le.mpr
    constructor <;> dsimp only [n] <;> nlinarith only [h1,h2,h3,h4]
  have hquad : (6*q+26)*q<=12*D := by
    dsimp only [D]
    nlinarith only [hq,ht.1,sq_nonneg (q-16)]
  have hnq : abs n*q<=12*D :=
    (mul_le_mul_of_nonneg_right hn (le_of_lt hq0)).trans hquad
  have he : compensatedQuadraticPairCrossMoment q t u-(1+1/q)=n/(q*D) := by
    unfold compensatedQuadraticPairCrossMoment
    change (q^3-5*q^2+(5-4*u)*q-11-2*t)/(q*D)-(1+1/q)=n/(q*D)
    field_simp [ne_of_gt hq0,ne_of_gt hD]
    dsimp only [D,n]
    ring
  have hden : 0<q*D := mul_pos hq0 hD
  rw [he,abs_div,abs_of_pos hden]
  have hs : 0<=(12*D-abs n*q)/(q^2*D) :=
    div_nonneg (sub_nonneg.mpr hnq) (mul_nonneg (sq_nonneg q) (le_of_lt hD))
  have hidentity : 12/q^2-abs n/(q*D)=(12*D-abs n*q)/(q^2*D) := by
    field_simp [ne_of_gt hq0,ne_of_gt hD]
  rw [<- hidentity] at hs
  linarith only [hs]

end FiniteField
