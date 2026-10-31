/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.LinearCombination
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairGeneralCovariance

/-!
# The full trace-free actual-count lag kernel

The canonical trace-free observable is unchanged. All four products of
its two actual count classes are retained. Their combined correlation
has no cubic trace or quartic elliptic kernel, at any lag. Both endpoint
masks and all three singular displacements remain in the exact formula.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem linear_char_shift_sum (hF : Not (ringChar F=2)) (h k : F)
    (A alpha beta : Int) :
    (Finset.univ.sum fun c : F =>
      (A+alpha*(quadraticChar F) c+beta*(quadraticChar F) (c+h))*
      (A+alpha*(quadraticChar F) (c+k)+beta*(quadraticChar F) (c+k+h)))=
      (Fintype.card F : Int)*A^2+
      (alpha^2+beta^2)*((Fintype.card F : Int)*(if k=0 then 1 else 0)-1)+
      alpha*beta*((Fintype.card F : Int)*
        ((if k=h then 1 else 0)+(if k=-h then 1 else 0))-2) := by
  have hk : (k+h=h) <-> k=0 := by
    constructor
    . intro he; exact add_right_cancel (he.trans (zero_add h).symm)
    . intro he; rw [he,zero_add]
  have hn : (k+h=0) <-> k=-h := by
    constructor
    . exact eq_neg_of_add_eq_zero_left
    . intro he; rw [he,neg_add_cancel]
  have hxx := quadraticChar_translate_correlation hF (0 : F) k
  simp only [add_zero] at hxx
  have hyy := quadraticChar_translate_correlation hF h (k+h)
  simp only [hk] at hyy
  have hxy := quadraticChar_translate_correlation hF (0 : F) (k+h)
  simp only [add_zero,hn] at hxy
  have hyx := quadraticChar_translate_correlation hF h k
  have hp (c : F) :
      (A+alpha*(quadraticChar F) c+beta*(quadraticChar F) (c+h))*
      (A+alpha*(quadraticChar F) (c+k)+beta*(quadraticChar F) (c+k+h))=
      A^2+(A*alpha)*(quadraticChar F) c+(A*alpha)*(quadraticChar F) (c+k)+
      (A*beta)*(quadraticChar F) (c+h)+(A*beta)*(quadraticChar F) (c+(k+h))+
      alpha^2*((quadraticChar F) c*(quadraticChar F) (c+k))+
      beta^2*((quadraticChar F) (c+h)*(quadraticChar F) (c+(k+h)))+
      (alpha*beta)*((quadraticChar F) c*(quadraticChar F) (c+(k+h)))+
      (alpha*beta)*((quadraticChar F) (c+h)*(quadraticChar F) (c+k)) := by
    simp only [add_assoc]
    ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib,<- Finset.mul_sum]
  rw [quadraticChar_sum_zero hF,quadraticChar_translate_sum hF k,
    quadraticChar_translate_sum hF h,quadraticChar_translate_sum hF (k+h),
    hxx,hyy,hxy,hyx]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_zero,add_zero]
  ring

theorem sum_twistPairNumerator_shift_correlation
    (hF : Not (ringChar F=2)) (h k : F) (hh : Not (h=0)) :
    let q : Int := Fintype.card F
    let t := (quadraticChar F) (-1)
    (Finset.univ.sum fun c : F => twistPairNumerator c h*twistPairNumerator (c+k) h)=
      q*(q-1)^2+2*(q*(if k=0 then 1 else 0)-1)+
        t*(q*((if k=h then 1 else 0)+(if k=-h then 1 else 0))-2) := by
  dsimp only
  have he : (quadraticChar F) (-h)*(quadraticChar F) h=(quadraticChar F) (-1) := by
    rw [<- map_mul,show (-h)*h=(-1 : F)*h^2 from by ring,map_mul,map_pow,
      quadraticChar_sq_one hh,mul_one]
  have hi := linear_char_shift_sum hF h k ((Fintype.card F : Int)-1)
    ((quadraticChar F) (-h)) ((quadraticChar F) h)
  rw [quadraticChar_sq_one hh,quadraticChar_sq_one (neg_ne_zero.mpr hh),he] at hi
  simpa only [show (1 : Int)+1=2 from rfl,twistPairNumerator] using hi

theorem twistPairNumerator_boundary_sum (h k : F) :
    twistPairNumerator (-k) h+twistPairNumerator (-h-k) h+
      twistPairNumerator k h+twistPairNumerator (k-h) h=
      4*((Fintype.card F : Int)-1)+2*(
        ((quadraticChar F) h+(quadraticChar F) (-h))*(quadraticChar F) k+
        (quadraticChar F) (-h)*(quadraticChar F) (k-h)+
        (quadraticChar F) h*(quadraticChar F) (k+h)) := by
  have hn (x : F) : (quadraticChar F) (-x)=
      (quadraticChar F) (-1)*(quadraticChar F) x := by
    rw [show -x=(-1 : F)*x from by ring,map_mul]
  have he : (quadraticChar F) (-1)*(quadraticChar F) h=(quadraticChar F) (-h) :=
    (hn h).symm
  have hf : (quadraticChar F) (-1)*(quadraticChar F) (-h)=(quadraticChar F) h := by
    rw [<- map_mul,show (-1 : F)*(-h)=h from by ring]
  unfold twistPairNumerator
  rw [show -k+h=-(k-h) from by ring,show -h-k=-(k+h) from by ring,
    show -(k+h)+h=-k from by ring,show k-h+h=k from by ring,
    hn k,hn (k-h),hn (k+h)]
  linear_combination
    ((quadraticChar F) k+(quadraticChar F) (k+h))*hf+
    ((quadraticChar F) k+(quadraticChar F) (k-h))*he

private theorem two_boundary_shift_sum (h k : F) (q : Int) (f : F -> Int) :
    (Finset.univ.sum fun c : F =>
      (f c-(if c=0 then q else 0)-(if c=-h then q else 0))*
      (f (c+k)-(if c+k=0 then q else 0)-(if c+k=-h then q else 0)))=
      (Finset.univ.sum fun c : F => f c*f (c+k))-
      q*(f (-k)+f (-h-k)+f k+f (k-h))+
      q^2*(2*(if k=0 then 1 else 0)+(if k=h then 1 else 0)+(if k=-h then 1 else 0)) := by
  have e0 (c : F) : (c+k=0)=(c=-k) := propext (by
    constructor <;> intro he <;> linear_combination he)
  have e1 (c : F) : (c+k=-h)=(c=-h-k) := propext (by
    constructor <;> intro he <;> linear_combination he)
  have e20 : (-h-k=0)=(k=-h) := propext (by
    constructor <;> intro he <;> linear_combination -he)
  simp_rw [e0,e1]
  simp only [sub_mul,mul_sub,Finset.sum_sub_distrib,ite_mul,mul_ite,mul_zero,zero_mul]
  simp [show -h+k=k-h from by ring]
  simp only [add_comm]
  simp only [e20]
  simp only [<- pow_two]
  have hi (P : Prop) [Decidable P] :
      (if P then q^2 else 0)=q^2*(if P then 1 else 0) := by
    by_cases hp : P <;> simp [hp]
  have hd (P : Prop) [Decidable P] :
      (if P then (2 : Int) else 0)=2*(if P then 1 else 0) := by
    by_cases hp : P <;> simp [hp]
  simp_rw [hi,hd]
  ring

def traceFreePairLagNumerator (h k : F) : Int :=
  let q : Int := Fintype.card F
  let t := (quadraticChar F) (-1)
  let e := (quadraticChar F) h
  let f := (quadraticChar F) (-h)
  q*(q-1)*(q-5)-2*(1+t)-2*q*((e+f)*(quadraticChar F) k+
    f*(quadraticChar F) (k-h)+e*(quadraticChar F) (k+h))+
    2*q*(q+1)*(if k=0 then 1 else 0)+
    q*(q+t)*((if k=h then 1 else 0)+(if k=-h then 1 else 0))

theorem sum_traceFreePairNumerator_shift_correlation
    (hF : Not (ringChar F=2)) (h k : F) (hh : Not (h=0)) :
    (Finset.univ.sum fun c : F =>
      traceFreePairNumerator c h*traceFreePairNumerator (c+k) h)=traceFreePairLagNumerator h k := by
  simp_rw [traceFreePairNumerator_completion _ h hh]
  rw [two_boundary_shift_sum h k (Fintype.card F : Int) (fun c => twistPairNumerator c h),
    sum_twistPairNumerator_shift_correlation hF h k hh,twistPairNumerator_boundary_sum h k]
  unfold traceFreePairLagNumerator
  dsimp only
  ring

theorem monicQuadraticPairCount_full_twist_correlation
    (hF : Not (ringChar F=2)) (h k a : F) (hh : Not (h=0))
    (hchi : (quadraticChar F) a=-1) :
    4*(Finset.univ.sum fun c : F =>
      (monicQuadraticPairCount c h+monicQuadraticPairCount (a*c) (a*h))*
      (monicQuadraticPairCount (c+k) h+monicQuadraticPairCount (a*(c+k)) (a*h)))=
        traceFreePairLagNumerator h k := by
  have ha : Not (a=0) := by intro he; subst a; norm_num at hchi
  have hi := sum_traceFreePairNumerator_shift_correlation hF h k hh
  have he (c : F) :
      traceFreePairNumerator c h*traceFreePairNumerator (c+k) h=
      4*((monicQuadraticPairCount c h+monicQuadraticPairCount (a*c) (a*h))*
        (monicQuadraticPairCount (c+k) h+monicQuadraticPairCount (a*(c+k)) (a*h))) := by
    rw [traceFreePairNumerator_eq_twist_counts hF c h a hh ha hchi,
      traceFreePairNumerator_eq_twist_counts hF (c+k) h a hh ha hchi]
    ring
  simp_rw [he] at hi
  rw [<- Finset.mul_sum] at hi
  exact hi

end FiniteField
