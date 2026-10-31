/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairMoments
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistAverage

/-!
# Exact shifted covariance of irreducible quadratic-pair counts

Every lag retains the quartic character kernel, trace-character pairings
and both singular constants. Shared-endpoint correlation is an exact
polynomial depending only on field size and the quadratic character of 2.
The identities require no Hasse estimate or integer prime-pair hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def quadraticPairCorrelationKernel (h k : F) : Int :=
  Finset.univ.sum fun x : F =>
    (quadraticChar F) (x*(x-h))*
      (quadraticChar F) ((x+k)*(x+k-h))

theorem splitCubicPointTrace_reflection_neg_one
    (hF : Not (ringChar F=2)) (hm : (quadraticChar F) (-1)=-1) (h c : F) :
    splitCubicPointTrace (-h-c) (-c)=-splitCubicPointTrace c (c+h) := by
  calc
    _ = splitCubicPointTrace ((-1 : F)*c) ((-1 : F)*(c+h)) := by
      rw [splitCubicPointTrace_comm hF]
      congr 1 <;> ring
    _ = (quadraticChar F) (-1)*splitCubicPointTrace c (c+h) :=
      splitCubicPointTrace_scale hF (-1) (neg_ne_zero.mpr one_ne_zero) c (c+h)
    _ = _ := by rw [hm]; ring

theorem splitCubicPointTrace_arithmetic_progression_zero
    (hF : Not (ringChar F=2)) (hm : (quadraticChar F) (-1)=-1) (h : F) :
    splitCubicPointTrace h (h+h)=0 := by
  let e : Equiv F F :=
    { toFun := fun x => h+h-x
      invFun := fun x => h+h-x
      left_inv := by intro x; ring
      right_inv := by intro x; ring }
  have hp (x : F) :
      (quadraticChar F) ((e x)*(e x-h)*(e x-(h+h)))=
      -((quadraticChar F) (x*(x-h)*(x-(h+h)))) := by
    have he : (e x)*(e x-h)*(e x-(h+h))=(-1 : F)*(x*(x-h)*(x-(h+h))) := by
      change (h+h-x)*(h+h-x-h)*(h+h-x-(h+h))=_
      ring
    rw [he,map_mul,hm,neg_one_mul]
  have hs := Equiv.sum_comp e (fun x : F => (quadraticChar F) (x*(x-h)*(x-(h+h))))
  simp_rw [hp,Finset.sum_neg_distrib] at hs
  have hz : (Finset.univ.sum fun x : F => (quadraticChar F) (x*(x-h)*(x-(h+h))))=0 := by
    linarith only [hs]
  rw [splitCubicPointTrace_eq hF,hz,neg_zero]

theorem sum_splitCubicPointTrace_shift_mul_char
    (hF : Not (ringChar F=2)) (h k v : F) (hh : Not (h=0)) :
    (Finset.univ.sum fun c : F =>
      splitCubicPointTrace (c+k) (c+k+h)*(quadraticChar F) (c+v))=
      -(Fintype.card F : Int)*(quadraticChar F) ((v-k)*(v-k-h))-1 := by
  let e : Equiv F F :=
    { toFun := fun c => c+k
      invFun := fun c => c-k
      left_inv := by intro c; ring
      right_inv := by intro c; ring }
  calc
    _ = Finset.univ.sum (fun c : F =>
        splitCubicPointTrace (e c) (e c+h)*(quadraticChar F) (e c+(v-k))) := by
      apply Finset.sum_congr rfl
      intro c _
      change splitCubicPointTrace (c+k) (c+k+h)*(quadraticChar F) (c+v)=
        splitCubicPointTrace (c+k) (c+k+h)*(quadraticChar F) ((c+k)+(v-k))
      rw [show (c+k)+(v-k)=c+v from by ring]
    _ = Finset.univ.sum (fun c : F =>
        splitCubicPointTrace c (c+h)*(quadraticChar F) (c+(v-k))) :=
      Equiv.sum_comp e (fun c : F =>
        splitCubicPointTrace c (c+h)*(quadraticChar F) (c+(v-k)))
    _ = _ := sum_splitCubicPointTrace_mul_char hF h (v-k) hh

theorem splitCubicPointTrace_shift_correlation
    (hF : Not (ringChar F=2)) (h k : F) (hh : Not (h=0)) :
    (Finset.univ.sum fun c : F =>
      splitCubicPointTrace c (c+h)*splitCubicPointTrace (c+k) (c+k+h))=
      (Fintype.card F : Int)*quadraticPairCorrelationKernel h k-1 := by
  let w : F -> Int := fun x => (quadraticChar F) (x*(x-h))
  have ht (c : F) :
      splitCubicPointTrace (c+k) (c+k+h)=
        -(Finset.univ.sum fun x : F => w x*(quadraticChar F) (c+(k+x))) := by
    simpa only [w,add_assoc] using splitCubicPointTrace_convolution hF (c+k) h
  calc
    _ = Finset.univ.sum (fun c : F => Finset.univ.sum fun x : F =>
        (-w x)*(splitCubicPointTrace c (c+h)*(quadraticChar F) (c+(k+x)))) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [ht]
      simp only [mul_neg,Finset.mul_sum,neg_mul,Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = Finset.univ.sum (fun x : F => (-w x)*
        (Finset.univ.sum fun c : F =>
          splitCubicPointTrace c (c+h)*(quadraticChar F) (c+(k+x)))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ = Finset.univ.sum (fun x : F => (-w x)*
        (-(Fintype.card F : Int)*w (k+x)-1)) := by
      simp only [sum_splitCubicPointTrace_mul_char hF h _ hh,w]
    _ = _ := by
      have hp (x : F) : (-w x)*(-(Fintype.card F : Int)*w (k+x)-1)=
          (Fintype.card F : Int)*(w x*w (x+k))+w x := by
        rw [add_comm k x]
        ring
      simp_rw [hp]
      rw [Finset.sum_add_distrib,<- Finset.mul_sum,quadraticPairKernel_sum hF h hh]
      rfl

theorem quadraticPairCorrelationKernel_zero (h : F) (hh : Not (h=0)) :
    quadraticPairCorrelationKernel h 0=(Fintype.card F : Int)-2 := by
  simpa only [quadraticPairCorrelationKernel,add_zero,pow_two] using
    quadraticPairKernel_square_sum h hh

theorem quadraticPairCorrelationKernel_even (h k : F) :
    quadraticPairCorrelationKernel h k=quadraticPairCorrelationKernel h (-k) := by
  let w : F -> Int := fun x => (quadraticChar F) (x*(x-h))
  let e : Equiv F F :=
    { toFun := fun x => x+k
      invFun := fun x => x-k
      left_inv := by intro x; ring
      right_inv := by intro x; ring }
  have he := Equiv.sum_comp e (fun x : F => w x*w (x-k))
  change (Finset.univ.sum fun x : F => w (x+k)*w (x+k-k))=
    (Finset.univ.sum fun x : F => w x*w (x-k)) at he
  simp only [add_sub_cancel_right] at he
  calc
    _ = Finset.univ.sum (fun x : F => w (x+k)*w x) := by
      unfold quadraticPairCorrelationKernel
      apply Finset.sum_congr rfl
      intro x _
      dsimp only [w]
      ring
    _ = Finset.univ.sum (fun x : F => w x*w (x-k)) := he
    _ = _ := by simp only [quadraticPairCorrelationKernel,w,sub_eq_add_neg]

theorem quadraticPairCorrelationKernel_adjacent
    (hF : Not (ringChar F=2)) (hm : (quadraticChar F) (-1)=-1)
    (h : F) (hh : Not (h=0)) : quadraticPairCorrelationKernel h h=0 := by
  have hneg : (quadraticChar F) (-h)=-(quadraticChar F) h := by
    have he : -h=(-1 : F)*h := by ring
    rw [he,map_mul,hm,neg_one_mul]
  have hne : Not (h=-h) := by
    intro hz
    rw [<- hz] at hneg
    have he2 := quadraticChar_sq_one hh
    have he0 : (quadraticChar F) h=0 := by linarith only [hneg]
    rw [he0] at he2
    norm_num at he2
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
  have hb : (quadraticChar F) ((-h)*h)=-1 := by
    have he : (-h)*h=(-1 : F)*h^2 := by ring
    rw [he,map_mul,map_pow,hm,quadraticChar_sq_one hh]
    ring
  unfold quadraticPairCorrelationKernel
  simp_rw [hp]
  rw [Finset.sum_sub_distrib,hs]
  rw [hb]
  simp

theorem splitCubicPointTrace_adjacent_correlation
    (hF : Not (ringChar F=2)) (hm : (quadraticChar F) (-1)=-1)
    (h : F) (hh : Not (h=0)) :
    (Finset.univ.sum fun c : F =>
      splitCubicPointTrace c (c+h)*splitCubicPointTrace (c+h) (c+h+h))=-1 := by
  rw [splitCubicPointTrace_shift_correlation hF h h hh,
    quadraticPairCorrelationKernel_adjacent hF hm h hh,mul_zero,zero_sub]

theorem quadraticPairCount_first_order_completion
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0)) (c : F) :
    4*monicQuadraticPairCount c h=completedQuadraticPairNumerator c h-
      (if c=0 then (Fintype.card F : Int) else 0)-
      (if c=-h then (Fintype.card F : Int) else 0) := by
  by_cases hc : c=0
  . subst c
    rw [monicQuadraticPairCount_zero hF,completedQuadraticPairNumerator_zero hF h hh]
    have hn : Not ((0 : F)=-h) := Ne.symm (neg_ne_zero.mpr hh)
    simp only [ite_true,ite_eq_right hn]
    ring
  . by_cases hn : c=-h
    . subst c
      rw [monicQuadraticPairCount_neg_shift hF,
        completedQuadraticPairNumerator_neg_shift hF h hh]
      simp only [ite_eq_right (neg_ne_zero.mpr hh),ite_true]
      ring
    . have hch : Not (c+h=0) := fun hz => hn (eq_neg_of_add_eq_zero_left hz)
      have he : 4*monicQuadraticPairCount c h=completedQuadraticPairNumerator c h := by
        rw [monicQuadraticPairCount_eq_trace hF c h hc hch hh]
        unfold completedQuadraticPairNumerator
        ring
      simpa only [ite_eq_right hc,ite_eq_right hn,sub_zero] using he


theorem quadraticPair_linearized_shift_correlation
    (hF : Not (ringChar F=2)) (h k j : F) (hh : Not (h=0)) (A : Int) :
    (Finset.univ.sum fun c : F =>
      (A-2*(quadraticChar F) (c+j)-splitCubicPointTrace c (c+h))*
      (A-2*(quadraticChar F) (c+k+j)-splitCubicPointTrace (c+k) (c+k+h)))=
      (Fintype.card F : Int)*A^2+
        (Fintype.card F : Int)*quadraticPairCorrelationKernel h k-9-
        2*(Fintype.card F : Int)*
          ((quadraticChar F) ((k+j)*(k+j-h))+
            (quadraticChar F) ((j-k)*(j-k-h)))+
        4*(Fintype.card F : Int)*(if k=0 then 1 else 0) := by
  let e : Equiv F F :=
    { toFun := fun c => c+k
      invFun := fun c => c-k
      left_inv := by intro c; ring
      right_inv := by intro c; ring }
  have hts : (Finset.univ.sum fun c : F =>
      splitCubicPointTrace (c+k) (c+k+h))=0 :=
    (Equiv.sum_comp e (fun c : F => splitCubicPointTrace c (c+h))).trans
      (sum_splitCubicPointTrace hF h)
  have hk : (k+j=j) <-> k=0 := by
    constructor
    . intro ht
      exact add_right_cancel (ht.trans (zero_add j).symm)
    . intro ht
      rw [ht,zero_add]
  have hxx := quadraticChar_translate_correlation hF j (k+j)
  simp only [hk] at hxx
  have hp (c : F) :
      (A-2*(quadraticChar F) (c+j)-splitCubicPointTrace c (c+h))*
      (A-2*(quadraticChar F) (c+k+j)-splitCubicPointTrace (c+k) (c+k+h))=
      A^2+4*((quadraticChar F) (c+j)*(quadraticChar F) (c+(k+j)))+
        splitCubicPointTrace c (c+h)*splitCubicPointTrace (c+k) (c+k+h)-
        (2*A)*(quadraticChar F) (c+j)-
        (2*A)*(quadraticChar F) (c+(k+j))-
        A*splitCubicPointTrace c (c+h)-
        A*splitCubicPointTrace (c+k) (c+k+h)+
        2*(splitCubicPointTrace c (c+h)*(quadraticChar F) (c+(k+j)))+
        2*(splitCubicPointTrace (c+k) (c+k+h)*(quadraticChar F) (c+j)) := by
    rw [add_assoc c k j]
    ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,<- Finset.mul_sum]
  rw [hxx,splitCubicPointTrace_shift_correlation hF h k hh,
    quadraticChar_translate_sum hF j,quadraticChar_translate_sum hF (k+j),
    sum_splitCubicPointTrace hF h,hts,
    sum_splitCubicPointTrace_mul_char hF h (k+j) hh,
    sum_splitCubicPointTrace_shift_mul_char hF h k j hh]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

theorem completedQuadraticPairNumerator_shift_correlation
    (hF : Not (ringChar F=2)) (hm : (quadraticChar F) (-1)=-1)
    (h k : F) (hh : Not (h=0)) :
    (Finset.univ.sum fun c : F =>
      completedQuadraticPairNumerator c h*completedQuadraticPairNumerator (c+k) h)=
      (Fintype.card F : Int)*((Fintype.card F : Int)-1)^2+
        (Fintype.card F : Int)*quadraticPairCorrelationKernel h k-9-
        2*(Fintype.card F : Int)*
          ((quadraticChar F) (k*(k-h))+(quadraticChar F) (k*(k+h)))+
        4*(Fintype.card F : Int)*(if k=0 then 1 else 0) := by
  have hn : (quadraticChar F) (-h)=-(quadraticChar F) h := by
    rw [show -h=(-1 : F)*h from by ring,map_mul,hm,neg_one_mul]
  have hsign := QuadraticPairEuler.quadraticChar_real_signs h hh
  rcases hsign with hs | hs
  . have he : (quadraticChar F) h=1 := by exact_mod_cast hs
    have hb (c : F) :
        completedQuadraticPairNumerator c h=
          (Fintype.card F : Int)-1-2*(quadraticChar F) (c+0)-
            splitCubicPointTrace c (c+h) := by
      simp only [completedQuadraticPairNumerator,hn,he,add_zero]
      ring
    simp_rw [hb]
    have ht := quadraticPair_linearized_shift_correlation hF h k 0 hh
      ((Fintype.card F : Int)-1)
    have hw : (0-k)*(0-k-h)=k*(k+h) := by ring
    simpa only [add_zero,hw] using ht
  . have he : (quadraticChar F) h=-1 := by exact_mod_cast hs
    have hb (c : F) :
        completedQuadraticPairNumerator c h=
          (Fintype.card F : Int)-1-2*(quadraticChar F) (c+h)-
            splitCubicPointTrace c (c+h) := by
      simp only [completedQuadraticPairNumerator,hn,he]
      ring
    simp_rw [hb]
    have ht := quadraticPair_linearized_shift_correlation hF h k h hh
      ((Fintype.card F : Int)-1)
    have hw : (k+h)*(k+h-h)=k*(k+h) := by ring
    have hv : (h-k)*(h-k-h)=k*(k-h) := by ring
    rw [hw,hv] at ht
    simpa only [add_comm] using ht


theorem completedQuadraticPairNumerator_reflection
    (hF : Not (ringChar F=2)) (hm : (quadraticChar F) (-1)=-1) (h c : F) :
    completedQuadraticPairNumerator c h+completedQuadraticPairNumerator (-h-c) h=
      2*((Fintype.card F : Int)-1)+
        2*(quadraticChar F) h*((quadraticChar F) (c+h)-(quadraticChar F) c) := by
  have hn (a : F) : (quadraticChar F) (-a)=-(quadraticChar F) a := by
    rw [show -a=(-1 : F)*a from by ring,map_mul,hm,neg_one_mul]
  have he : -h-c+h=-c := by ring
  have ht : splitCubicPointTrace (-h-c) (-h-c+h)=
      -splitCubicPointTrace c (c+h) := by
    rw [he]
    exact splitCubicPointTrace_reflection_neg_one hF hm h c
  unfold completedQuadraticPairNumerator
  rw [ht,he,show -h-c=-(c+h) from by ring,hn (c+h),hn c,hn h]
  ring

theorem quadraticPairCount_shift_completion
    (hF : Not (ringChar F=2)) (h k : F) (hh : Not (h=0)) :
    16*(Finset.univ.sum fun c : F =>
      monicQuadraticPairCount c h*monicQuadraticPairCount (c+k) h)=
      (Finset.univ.sum fun c : F =>
        completedQuadraticPairNumerator c h*completedQuadraticPairNumerator (c+k) h)-
      (Fintype.card F : Int)*
        (completedQuadraticPairNumerator (-k) h+
          completedQuadraticPairNumerator (-h-k) h+
          completedQuadraticPairNumerator k h+
          completedQuadraticPairNumerator (k-h) h)+
      (Fintype.card F : Int)^2*
        (2*(if k=0 then 1 else 0)+(if k=h then 1 else 0)+
          (if k=-h then 1 else 0)) := by
  have hp (c : F) :
      16*(monicQuadraticPairCount c h*monicQuadraticPairCount (c+k) h)=
        (completedQuadraticPairNumerator c h-
          (if c=0 then (Fintype.card F : Int) else 0)-
          (if c=-h then (Fintype.card F : Int) else 0))*
        (completedQuadraticPairNumerator (c+k) h-
          (if c+k=0 then (Fintype.card F : Int) else 0)-
          (if c+k=-h then (Fintype.card F : Int) else 0)) := by
    rw [<- quadraticPairCount_first_order_completion hF h hh c,
      <- quadraticPairCount_first_order_completion hF h hh (c+k)]
    ring
  have hz (c : F) : (c+k=0) <-> c=-k := by
    constructor
    . exact eq_neg_of_add_eq_zero_left
    . intro hc
      rw [hc,neg_add_cancel]
  have hn (c : F) : (c+k=-h) <-> c=-h-k := by
    constructor
    . intro hc
      calc
        c=(c+k)-k := by ring
        _=-h-k := by rw [hc]
    . intro hc
      rw [hc,sub_add_cancel]
  calc
    _ = Finset.univ.sum (fun c : F =>
        (completedQuadraticPairNumerator c h-
          (if c=0 then (Fintype.card F : Int) else 0)-
          (if c=-h then (Fintype.card F : Int) else 0))*
        (completedQuadraticPairNumerator (c+k) h-
          (if c=-k then (Fintype.card F : Int) else 0)-
          (if c=-h-k then (Fintype.card F : Int) else 0))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      simpa only [hz,hn] using hp c
    _ = _ := by
      have heq : (-h-k=0) <-> k=-h := by
        rw [sub_eq_zero]
        exact eq_comm
      simp only [mul_sub,sub_mul,mul_ite,ite_mul,mul_zero,zero_mul,
        Finset.sum_sub_distrib]
      simp [heq,add_comm]
      split_ifs <;> ring

theorem completedQuadraticPairNumerator_boundary_correction
    (hF : Not (ringChar F=2)) (hm : (quadraticChar F) (-1)=-1) (h k : F) :
    completedQuadraticPairNumerator (-k) h+
      completedQuadraticPairNumerator (-h-k) h+
      completedQuadraticPairNumerator k h+
      completedQuadraticPairNumerator (k-h) h=
        4*((Fintype.card F : Int)-1)+
          2*(quadraticChar F) h*
            ((quadraticChar F) (k+h)-(quadraticChar F) (k-h)) := by
  have ha := completedQuadraticPairNumerator_reflection hF hm h k
  have hb := completedQuadraticPairNumerator_reflection hF hm h (k-h)
  have he : -h-(k-h)=-k := by ring
  have hf : k-h+h=k := by ring
  rw [he,hf] at hb
  linarith only [ha,hb]


theorem monicQuadraticPairCount_shift_correlation
    (hF : Not (ringChar F=2)) (hm : (quadraticChar F) (-1)=-1)
    (h k : F) (hh : Not (h=0)) :
    16*(Finset.univ.sum fun c : F =>
      monicQuadraticPairCount c h*monicQuadraticPairCount (c+k) h)=
      (Fintype.card F : Int)*((Fintype.card F : Int)-1)*((Fintype.card F : Int)-5)+
      (Fintype.card F : Int)*quadraticPairCorrelationKernel h k-9-
      2*(Fintype.card F : Int)*
        ((quadraticChar F) (k*(k-h))+(quadraticChar F) (k*(k+h)))+
      2*(Fintype.card F : Int)*(quadraticChar F) h*
        ((quadraticChar F) (k-h)-(quadraticChar F) (k+h))+
      4*(Fintype.card F : Int)*(if k=0 then 1 else 0)+
      (Fintype.card F : Int)^2*
        (2*(if k=0 then 1 else 0)+(if k=h then 1 else 0)+
          (if k=-h then 1 else 0)) := by
  rw [quadraticPairCount_shift_completion hF h k hh,
    completedQuadraticPairNumerator_shift_correlation hF hm h k hh,
    completedQuadraticPairNumerator_boundary_correction hF hm h k]
  ring

theorem monicQuadraticPairCount_adjacent_correlation
    (hF : Not (ringChar F=2)) (hm : (quadraticChar F) (-1)=-1)
    (h : F) (hh : Not (h=0)) :
    16*(Finset.univ.sum fun c : F =>
      monicQuadraticPairCount c h*monicQuadraticPairCount (c+h) h)=
      (Fintype.card F : Int)^3-5*(Fintype.card F : Int)^2+
        (5-4*(quadraticChar F) (2 : F))*(Fintype.card F : Int)-9 := by
  have he2 := quadraticChar_sq_one hh
  have hnchi : (quadraticChar F) (-h)=-(quadraticChar F) h := by
    rw [show -h=(-1 : F)*h from by ring,map_mul,hm,neg_one_mul]
  have hn : Not (h=-h) := by
    intro hx
    rw [<- hx] at hnchi
    have he0 : (quadraticChar F) h=0 := by linarith only [hnchi]
    rw [he0] at he2
    norm_num at he2
  have ht := monicQuadraticPairCount_shift_correlation hF hm h h hh
  rw [quadraticPairCorrelationKernel_adjacent hF hm h hh] at ht
  simp only [ite_eq_right hh,ite_true,ite_eq_right hn,sub_self,mul_zero,
    zero_add,add_zero] at ht
  have hw : h*(h+h)=(2 : F)*h^2 := by ring
  have hv : h+h=(2 : F)*h := by ring
  rw [hw,map_mul,map_pow,he2,hv,map_mul] at ht
  have hz : (quadraticChar F) (0 : F)=0 := by simp
  rw [hz] at ht
  calc
    _ = _ := ht
    _ = _ := by
      ring_nf
      rw [he2]
      ring

end FiniteField
