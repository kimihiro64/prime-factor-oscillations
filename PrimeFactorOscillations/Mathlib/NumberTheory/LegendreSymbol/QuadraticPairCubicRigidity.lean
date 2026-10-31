/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticCharacterOneException
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairSquareTransport

/-!
# Two-anchor rigidity for polynomial square transports of degree at most three

Compatibility is required at every input, with zero square multipliers
allowed. Both exceptional anchors and the five-element field are retained.
The coefficients are forced to those of the identity or the scaled cubic.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem linear_product_zero_sum (f : F -> F) (t : F)
    (ht : Not (f t=0)) :
    (Finset.univ.sum fun x : F => if (x-t)*f x=0 then (1 : Int) else 0)=
      1+(Finset.univ.sum fun x : F => if f x=0 then (1 : Int) else 0) := by
  have hp (x : F) :
      (if (x-t)*f x=0 then (1 : Int) else 0)=
        (if x=t then 1 else 0)+(if f x=0 then 1 else 0) := by
    by_cases hx : x=t
    . subst x
      simp [ht]
    . by_cases hf : f x=0
      . simp [hx,hf]
      . have hn := mul_ne_zero (sub_ne_zero.mpr hx) hf
        simp only [ite_eq_right hn,ite_eq_right hx,ite_eq_right hf,zero_add]
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

omit [Fintype F] [DecidableEq F] in
theorem cubic_squarePairReach_constant_zero (a b d e h : F)
    (hr : forall x : F, squarePairReach x (a*x^3+b*x^2+d*x+e) h) : e=0 := by
  have h := Classical.choose_spec (Classical.choose_spec (hr 0))
  simpa only [zero_pow (by decide : Not (3=0)),zero_pow (by decide : Not (2=0)),
    mul_zero,zero_mul,zero_add] using h.1

omit [Fintype F] [DecidableEq F] in
theorem cubic_squarePairReach_endpoint (a b d h : F) (hh : Not (h=0))
    (hr : forall x : F, squarePairReach x (a*x^3+b*x^2+d*x) h) :
    d=1-a*h^2+b*h := by
  have hv := Classical.choose_spec (Classical.choose_spec (hr (-h)))
  have he : a*(-h)^3+b*(-h)^2+d*(-h)+h=0 := by
    simpa only [neg_add_cancel,zero_mul] using hv.2
  have hz : h*(d-(1-a*h^2+b*h))=0 := by
    calc
      _ = -(a*(-h)^3+b*(-h)^2+d*(-h)+h) := by ring
      _ = 0 := by rw [he,neg_zero]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hh)

omit [Fintype F] [DecidableEq F] in
theorem cubic_squarePairReach_quotient_squares (a b d h : F)
    (hd : d=1-a*h^2+b*h)
    (hr : forall x : F, squarePairReach x (a*x^3+b*x^2+d*x) h) :
    (forall x : F, Not (x=0) -> IsSquare (a*x^2+b*x+d)) /\
      (forall x : F, Not (x= -h) -> IsSquare (a*x^2+(b-a*h)*x+1)) := by
  constructor
  . intro x hx
    let u : F := Classical.choose (hr x)
    have hu := (Classical.choose_spec (Classical.choose_spec (hr x))).1
    have hz : x*(a*x^2+b*x+d-u^2)=0 := by
      calc
        _ = (a*x^3+b*x^2+d*x)-x*u^2 := by ring
        _ = 0 := sub_eq_zero.mpr hu
    have he := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hx)
    exact Exists.intro u (by rw [he]; ring)
  . intro x hx
    let v : F := Classical.choose (Classical.choose_spec (hr x))
    have hv := (Classical.choose_spec (Classical.choose_spec (hr x))).2
    have hxh : Not (x+h=0) := fun he => hx (eq_neg_of_add_eq_zero_left he)
    have hz : (x+h)*(a*x^2+(b-a*h)*x+1-v^2)=0 := by
      calc
        _ = (a*x^3+b*x^2+d*x+h)-(x+h)*v^2 := by rw [hd]; ring
        _ = 0 := sub_eq_zero.mpr hv
    have he := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hxh)
    exact Exists.intro v (by rw [he]; ring)

theorem cubic_squarePairReach_rigidity (hF : Not (ringChar F=2))
    (hq : 5<=(Fintype.card F : Int)) (a b d e h : F) (hh : Not (h=0))
    (hr : forall x : F, squarePairReach x (a*x^3+b*x^2+d*x+e) h) :
    e=0 /\ ((a=0 /\ b=0 /\ d=1) \/
      (a*h^2=16 /\ b*h=24 /\ d=9)) := by
  have he := cubic_squarePairReach_constant_zero a b d e h hr
  subst e
  refine And.intro rfl ?_
  have hr0 : forall x : F, squarePairReach x (a*x^3+b*x^2+d*x) h := by
    intro x
    simpa only [add_zero] using hr x
  have hd := cubic_squarePairReach_endpoint a b d h hh hr0
  have hsquare := cubic_squarePairReach_quotient_squares a b d h hd hr0
  by_cases ha : a=0
  . apply Or.inl
    have hb : b=0 := affine_square_off_one_constant hF hq b d 0 (by
      intro x hx
      simpa only [ha,zero_mul,zero_add] using hsquare.1 x hx)
    refine And.intro ha (And.intro hb ?_)
    simpa only [ha,hb,zero_mul,sub_zero,add_zero] using hd
  . apply Or.inr
    have hR := quadratic_square_off_one_dichotomy hF hq a b d 0 ha hsquare.1
    have hS := quadratic_square_off_one_dichotomy hF hq a (b-a*h) 1 (-h) ha hsquare.2
    have hdiscs : b^2-4*a*d=0 /\ (b-a*h)^2-4*a=0 := by
      rcases hR with hR | hR
      . rcases hS with hS | hS
        . exact And.intro hR.1 (by simpa only [mul_one] using hS.1)
        . have hz : (1 : Int)= -1 := hR.2.symm.trans hS.2.1
          norm_num at hz
      . rcases hS with hS | hS
        . have hz : (1 : Int)= -1 := hS.2.symm.trans hR.2.1
          norm_num at hz
        . have hcharD : (quadraticChar F) d= -1 := by
            simpa only [zero_pow (by decide : Not (2=0)),mul_zero,zero_add] using hR.2.2.2
          have hd0 : Not (d=0) := by intro hz; rw [hz] at hcharD; norm_num at hcharD
          have hs0 : Not (a*(-h)^2+(b-a*h)*(-h)+1=0) := by
            intro hz
            have ht := hS.2.2.2
            rw [hz] at ht
            norm_num at ht
          have hcountR :
              (Finset.univ.sum fun x : F =>
                if a*x^3+b*x^2+d*x=0 then (1 : Int) else 0)=3 := by
            calc
              _ = Finset.univ.sum (fun x : F =>
                  if (x-0)*(a*x^2+b*x+d)=0 then (1 : Int) else 0) := by
                apply Finset.sum_congr rfl
                intro x _
                exact congrArg (fun z : F => if z=0 then (1 : Int) else 0) (by ring)
              _ = 3 := by
                rw [linear_product_zero_sum (fun x : F => a*x^2+b*x+d) 0
                  (by simpa only [zero_pow (by decide : Not (2=0)),mul_zero,zero_add] using hd0),
                  quadratic_zero_indicator_sum hF a b d ha,hR.2.2.1]
                norm_num
          have hcountS :
              (Finset.univ.sum fun x : F =>
                if a*x^3+b*x^2+d*x+h=0 then (1 : Int) else 0)=3 := by
            calc
              _ = Finset.univ.sum (fun x : F =>
                  if (x-(-h))*(a*x^2+(b-a*h)*x+1)=0 then (1 : Int) else 0) := by
                apply Finset.sum_congr rfl
                intro x _
                apply congrArg (fun z : F => if z=0 then (1 : Int) else 0)
                rw [hd]
                ring
              _ = 3 := by
                rw [linear_product_zero_sum (fun x : F => a*x^2+(b-a*h)*x+1) (-h) hs0,
                  quadratic_zero_indicator_sum hF a (b-a*h) 1 ha,hS.2.2.1]
                norm_num
          have hp (x : F) :
              (if a*x^3+b*x^2+d*x=0 then (1 : Int) else 0)+
                (if a*x^3+b*x^2+d*x+h=0 then 1 else 0)<=1 := by
            by_cases hx : a*x^3+b*x^2+d*x=0
            . have hxh : Not (a*x^3+b*x^2+d*x+h=0) := by simpa only [hx,zero_add] using hh
              rw [ite_eq_left hx,ite_eq_right hxh]
              norm_num
            . rw [ite_eq_right hx]
              split_ifs <;> norm_num
          have ht := Finset.sum_le_sum (s := (Finset.univ : Finset F)) (fun x _ => hp x)
          rw [Finset.sum_add_distrib,hcountR,hcountS] at ht
          simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at ht
          linarith only [ht,hR.1]
    have hrel : 2*b-3*a*h=0 := by
      have hz : a*h*(3*a*h-2*b)=0 := by
        calc
          _ = (b^2-4*a*d)-((b-a*h)^2-4*a) := by rw [hd]; ring
          _ = 0 := by rw [hdiscs.1,hdiscs.2,sub_self]
      have ht := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero ha hh)
      calc
        _ = -(3*a*h-2*b) := by ring
        _ = 0 := by rw [ht,neg_zero]
    have ha16 : a*h^2=16 := by
      have hz : a*(a*h^2-16)=0 := by
        calc
          _ = 4*((b-a*h)^2-4*a)-(2*b-3*a*h)*(2*b-a*h) := by ring
          _ = 0 := by rw [hdiscs.2,hrel]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha)
    have hb24 : b*h=24 := by
      have hz : (2 : F)*(b*h-24)=0 := by
        calc
          _ = (2*b-3*a*h)*h+3*(a*h^2-16) := by ring
          _ = 0 := by rw [hrel,ha16]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (two_ne_zero_of_odd hF))
    refine And.intro ha16 (And.intro hb24 ?_)
    rw [hd,ha16,hb24]
    norm_num

theorem cubic_squarePairReach_iff (hF : Not (ringChar F=2))
    (hq : 5<=(Fintype.card F : Int)) (a b d e h : F) (hh : Not (h=0)) :
    (forall x : F, squarePairReach x (a*x^3+b*x^2+d*x+e) h) <->
      e=0 /\ ((a=0 /\ b=0 /\ d=1) \/
        (a*h^2=16 /\ b*h=24 /\ d=9)) := by
  constructor
  . exact cubic_squarePairReach_rigidity hF hq a b d e h hh
  . intro hc x
    have he := hc.1
    subst e
    rcases hc.2 with hi | ht
    . have ha := hi.1
      have hb := hi.2.1
      have hd := hi.2.2
      simpa only [ha,hb,hd,zero_mul,zero_add,one_mul,add_zero] using
        squarePairReach_refl x h
    . have ha : a=16/h^2 := (eq_div_iff (pow_ne_zero 2 hh)).mpr ht.1
      have hb : b=24/h := (eq_div_iff hh).mpr ht.2.1
      rw [ha,hb,ht.2.2,add_zero]
      refine Exists.intro (4*x/h+3) (Exists.intro (4*x/h+1) (And.intro ?_ ?_))
      . field_simp [hh]
        ring
      . field_simp [hh]
        ring

end FiniteField
