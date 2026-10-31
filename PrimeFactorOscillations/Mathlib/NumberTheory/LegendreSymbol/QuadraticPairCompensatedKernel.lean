/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairGeneralCovariance

/-!
# The full compensated quadratic-pair correlation kernel

Nonsquare gap compensation cancels both cubic boundary traces at every lag.
The actual raw-count identity retains the quartic character kernel, every
signed character product, and all three boundary-intersection masks.
No Hasse bound or positive integer short-window mass is assumed.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem quadraticPairCorrelationKernel_scale (h k a : F) (ha : Not (a=0)) :
    quadraticPairCorrelationKernel (a*h) (a*k)=quadraticPairCorrelationKernel h k := by
  let e : Equiv F F :=
    { toFun := fun x => a*x
      invFun := fun x => x/a
      left_inv := by intro x; field_simp [ha]
      right_inv := by intro x; field_simp [ha] }
  unfold quadraticPairCorrelationKernel
  calc
    _=Finset.univ.sum (fun x : F =>
      (quadraticChar F) ((e x)*(e x-a*h))*
      (quadraticChar F) ((e x+a*k)*(e x+a*k-a*h))) :=
      (Equiv.sum_comp e (fun x : F =>
        (quadraticChar F) (x*(x-a*h))*
        (quadraticChar F) ((x+a*k)*(x+a*k-a*h)))).symm
    _=_ := by
      apply Finset.sum_congr rfl
      intro x _
      change (quadraticChar F) ((a*x)*(a*x-a*h))*
        (quadraticChar F) ((a*x+a*k)*(a*x+a*k-a*h))=_
      rw [show (a*x)*(a*x-a*h)=a^2*(x*(x-h)) from by ring,
        show (a*x+a*k)*(a*x+a*k-a*h)=a^2*((x+k)*(x+k-h)) from by ring]
      simp only [map_mul,map_pow,quadraticChar_sq_one ha,one_mul]

def twistCompensatedPairKernel (h k : F) : Int :=
  let q : Int := Fintype.card F
  let t := (quadraticChar F) (-1)
  let e := (quadraticChar F) h
  let f := (quadraticChar F) (-h)
  q^3-6*q^2+(7+2*t)*q-11-2*t+q*quadraticPairCorrelationKernel h k-
    2*q*((quadraticChar F) (k*(k-h))+(quadraticChar F) (k*(k+h))+
      (e+f)*(quadraticChar F) k+f*(quadraticChar F) (k-h)+
      e*(quadraticChar F) (k+h))+
    2*q*(q+2)*(if k=0 then 1 else 0)+
    q*(q+1+t)*((if k=h then 1 else 0)+(if k=-h then 1 else 0))

theorem monicQuadraticPairCount_twist_compensated_correlation
    (hF : Not (ringChar F=2)) (h k a : F) (hh : Not (h=0))
    (hchi : (quadraticChar F) a=-1) :
    8*(Finset.univ.sum fun c : F =>
      monicQuadraticPairCount c h*monicQuadraticPairCount (c+k) h+
      monicQuadraticPairCount c (a*h)*monicQuadraticPairCount (c+a*k) (a*h))=
        twistCompensatedPairKernel h k := by
  have ha : Not (a=0) := by
    intro hz
    subst a
    norm_num at hchi
  have hb := monicQuadraticPairCount_shift_correlation_general hF h k hh
  have ht := monicQuadraticPairCount_shift_correlation_general hF (a*h) (a*k)
    (mul_ne_zero ha hh)
  dsimp only at hb ht
  have hv (x : F) : (quadraticChar F) (a*x)=-(quadraticChar F) x := by
    rw [map_mul,hchi,neg_one_mul]
  have hinj (x y : F) (he : a*x=a*y) : x=y := by
    calc
      x=(a*x)/a := by field_simp [ha]
      _=(a*y)/a := congrArg (fun z : F => z/a) he
      _=y := by field_simp [ha]
  have hd0 :
      (if a*k=0 then (1 : Int) else 0)=(if k=0 then 1 else 0) := by
    by_cases hk : k=0
    . subst k
      simp
    . simp only [ite_eq_right (mul_ne_zero ha hk),ite_eq_right hk]
  have hdp :
      (if a*k=a*h then (1 : Int) else 0)=(if k=h then 1 else 0) := by
    by_cases hk : k=h
    . subst k
      simp
    . have hz : Not (a*k=a*h) := fun he => hk (hinj k h he)
      simp only [ite_eq_right hz,ite_eq_right hk]
  have hdm :
      (if a*k=-(a*h) then (1 : Int) else 0)=(if k=-h then 1 else 0) := by
    have hn : -(a*h)=a*(-h) := by ring
    rw [hn]
    by_cases hk : k=-h
    . rw [hk]
      simp
    . have hz : Not (a*k=a*(-h)) := fun he => hk (hinj k (-h) he)
      simp only [ite_eq_right hz,ite_eq_right hk]
  have hqm : (quadraticChar F) ((a*k)*(a*k-a*h))=
      (quadraticChar F) (k*(k-h)) := by
    rw [show (a*k)*(a*k-a*h)=a^2*(k*(k-h)) from by ring,
      map_mul,map_pow,quadraticChar_sq_one ha,one_mul]
  have hqp : (quadraticChar F) ((a*k)*(a*k+a*h))=
      (quadraticChar F) (k*(k+h)) := by
    rw [show (a*k)*(a*k+a*h)=a^2*(k*(k+h)) from by ring,
      map_mul,map_pow,quadraticChar_sq_one ha,one_mul]
  have htk : splitCubicPointTrace (a*k) (a*k+a*h)=
      -splitCubicPointTrace k (k+h) := by
    rw [show a*k+a*h=a*(k+h) from by ring,
      splitCubicPointTrace_scale hF a ha,hchi,neg_one_mul]
  have htm : splitCubicPointTrace (a*k-a*h) (a*k)=
      -splitCubicPointTrace (k-h) k := by
    rw [show a*k-a*h=a*(k-h) from by ring,
      splitCubicPointTrace_scale hF a ha,hchi,neg_one_mul]
  rw [hd0,hdp,hdm,quadraticPairCorrelationKernel_scale h k a ha,hqm,hqp,htk,htm] at ht
  rw [show -(a*h)=a*(-h) from by ring,hv h,hv (-h),hv k,
    show a*k-a*h=a*(k-h) from by ring,hv (k-h),
    show a*k+a*h=a*(k+h) from by ring,hv (k+h)] at ht
  have hn : (quadraticChar F) (-h)=(quadraticChar F) (-1)*(quadraticChar F) h := by
    rw [show -h=(-1 : F)*h from by ring,map_mul]
  have hc (x : F) (hx : Not (x=0)) :
      Or ((quadraticChar F) x=1) ((quadraticChar F) x=-1) := by
    have hp : ((quadraticChar F) x-1)*((quadraticChar F) x+1)=0 := by
      nlinarith only [quadraticChar_sq_one hx]
    rcases mul_eq_zero.mp hp with hl | hr
    . exact Or.inl (by linarith only [hl])
    . exact Or.inr (by linarith only [hr])
  unfold twistCompensatedPairKernel
  dsimp only
  rw [Finset.sum_add_distrib]
  rw [hn] at hb ht
  rw [hn]
  rcases hc h hh with he | he <;>
    rcases hc (-1) (neg_ne_zero.mpr one_ne_zero) with hs | hs
  all_goals
    rw [he,hs] at hb ht
    rw [he,hs]
    nlinarith only [hb,ht]

theorem twistCompensatedPairKernel_zero (h : F) (hh : Not (h=0)) :
    let q : Int := Fintype.card F
    let t := (quadraticChar F) (-1)
    twistCompensatedPairKernel h 0=q^3-3*q^2+(5+2*t)*q-11-2*t := by
  have he := quadraticChar_sq_one hh
  have hf := quadraticChar_sq_one (neg_ne_zero.mpr hh)
  have hz : (quadraticChar F) (0 : F)=0 := by simp
  have hn : Not ((0 : F)=h) := Ne.symm hh
  have hm : Not ((0 : F)=-h) := Ne.symm (neg_ne_zero.mpr hh)
  unfold twistCompensatedPairKernel
  dsimp only
  rw [quadraticPairCorrelationKernel_zero h hh]
  simp only [zero_mul,zero_sub,zero_add,hz,ite_true,ite_eq_right hn,ite_eq_right hm]
  ring_nf
  simp only [he,hf]
  ring

def compensatedQuadraticPairPersistence (q t u : Real) : Real :=
  (q^2-(6+4*u+2*t)*q-11-2*t)/(3*q^2-6*q-11-2*t)

theorem compensatedQuadraticPairPersistence_denominator_pos
    (q t : Real) (hq : 16<=q) (ht : t<=1) :
    0<3*q^2-6*q-11-2*t := by
  have hs : 0<=(q-16)*q := mul_nonneg
    (by linarith only [hq]) (by linarith only [hq])
  nlinarith only [hq,ht,hs]

theorem compensatedQuadraticPairPersistence_bounds
    (q t u : Real) (hq : 16<=q)
    (ht : And (-1<=t) (t<=1)) (hu : And (-1<=u) (u<=1)) :
    And (0<compensatedQuadraticPairPersistence q t u)
      (compensatedQuadraticPairPersistence q t u<1/2) := by
  let A : Real := q^2-(6+4*u+2*t)*q-11-2*t
  let B : Real := 3*q^2-6*q-11-2*t
  have hq0 : 0<q := by linarith only [hq]
  have hB : 0<B := compensatedQuadraticPairPersistence_denominator_pos q t hq ht.2
  have hmain : 0<(q-13)*(q+1) := mul_pos
    (by linarith only [hq]) (by linarith only [hq])
  have h1 : 0<=(1-u)*q := mul_nonneg
    (by linarith only [hu.2]) hq0.le
  have h2 : 0<=(1-t)*(q+1) := mul_nonneg
    (by linarith only [ht.2]) (by linarith only [hq])
  have hA : 0<A := by dsimp only [A]; nlinarith only [hmain,h1,h2]
  have h3 : 0<=(1+u)*q := mul_nonneg
    (by linarith only [hu.1]) hq0.le
  have h4 : 0<=(1+t)*(2*q+1) := mul_nonneg
    (by linarith only [ht.1]) (by linarith only [hq])
  have hsq : 0<(q-3)^2 := sq_pos_of_pos (by linarith only [hq])
  have hgap : 0<B-2*A := by
    dsimp only [A,B]
    nlinarith only [hsq,h3,h4]
  change And (0<A/B) (A/B<1/2)
  refine And.intro (div_pos hA hB) ?_
  have hp : 0<(B-2*A)/(2*B) := div_pos hgap (by linarith only [hB])
  have he : 1/2-A/B=(B-2*A)/(2*B) := by field_simp [ne_of_gt hB]
  rw [<- he] at hp
  linarith only [hp]

theorem compensatedQuadraticPairPersistence_error
    (q t u : Real) (hq : 16<=q)
    (ht : And (-1<=t) (t<=1)) (hu : And (-1<=u) (u<=1)) :
    abs (compensatedQuadraticPairPersistence q t u-1/3)<=5/q := by
  let B : Real := 3*q^2-6*q-11-2*t
  let n : Real := -(12+12*u+6*t)*q-22-4*t
  have hq0 : 0<q := by linarith only [hq]
  have hB : 0<B := compensatedQuadraticPairPersistence_denominator_pos q t hq ht.2
  have h1 : 0<=(1-u)*q := mul_nonneg
    (by linarith only [hu.2]) hq0.le
  have h2 : 0<=(1-t)*(3*q+2) := mul_nonneg
    (by linarith only [ht.2]) (by linarith only [hq])
  have h3 : 0<=(1+u)*q := mul_nonneg
    (by linarith only [hu.1]) hq0.le
  have h4 : 0<=(1+t)*(3*q+2) := mul_nonneg
    (by linarith only [ht.1]) (by linarith only [hq])
  have hn : abs n<=30*q+26 := by
    apply abs_le.mpr
    constructor <;> dsimp only [n] <;> nlinarith only [h1,h2,h3,h4,hq]
  have hs : 0<=(q-16)*q := mul_nonneg
    (by linarith only [hq]) hq0.le
  have hquad : (30*q+26)*q<=15*B := by
    dsimp only [B]
    nlinarith only [hq,ht.2,hs]
  have hnq : abs n*q<=15*B :=
    (mul_le_mul_of_nonneg_right hn hq0.le).trans hquad
  have he : compensatedQuadraticPairPersistence q t u-1/3=n/(3*B) := by
    unfold compensatedQuadraticPairPersistence
    change (q^2-(6+4*u+2*t)*q-11-2*t)/B-1/3=n/(3*B)
    field_simp [ne_of_gt hB]
    dsimp only [B,n]
    ring
  rw [he,abs_div,abs_of_pos (by linarith only [hB] : 0<3*B)]
  have hp : 0<=(15*B-abs n*q)/(3*q*B) :=
    div_nonneg (sub_nonneg.mpr hnq) (by positivity)
  have hi : 5/q-abs n/(3*B)=(15*B-abs n*q)/(3*q*B) := by
    field_simp [ne_of_gt hq0,ne_of_gt hB]
    ring
  rw [<- hi] at hp
  linarith only [hp]

end FiniteField
