/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairCubicLift

/-!
# An invariant probability sector for cubic pair transport

The quadratic-character sector opposite to the cubic exceptional roots
cannot be absorbed. Its exact signed numerator moment supplies a
uniform all-iterate lower bound for the actual compensated pair law.
The integer-origin prime-pair mass is a separate, unproved consumer.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem quadraticChar_cubic_root (hF : Not (ringChar F=2)) (c : F)
    (hr : (2*c+1)*(2*c+3)=0) :
    (quadraticChar F) (c*(c+2))=(quadraticChar F) (-(3 : F)) := by
  have h2 := two_ne_zero_of_odd hF
  have hd : (4 : F)*(c*(c+2))=-(3 : F) := by
    calc
      _ = (2*c+1)*(2*c+3)-3 := by ring
      _ = -(3 : F) := by rw [hr]; ring
  have h4 : (quadraticChar F) (4 : F)=1 := by
    rw [show (4 : F)=(2 : F)^2 from by ring,map_pow,quadraticChar_sq_one h2]
  have he := congrArg (quadraticChar F) hd
  simpa only [map_mul,h4,one_mul] using he

theorem cubicSafeSector_step (hF : Not (ringChar F=2)) (h3 : Not ((3 : F)=0))
    (c : F)
    (hs : (quadraticChar F) (c*(c+2))=-(quadraticChar F) (-(3 : F))) :
    (quadraticChar F) (cubicPairLift c*(cubicPairLift c+2))=
        -(quadraticChar F) (-(3 : F)) /\
      traceFreePairWeight (cubicPairLift c) 2=traceFreePairWeight c 2 := by
  have hu := quadraticChar_sq_one (neg_ne_zero.mpr h3)
  have hb : Not ((2*c+1)*(2*c+3)=0) := by
    intro hr
    have he := quadraticChar_cubic_root hF c hr
    have hz : (quadraticChar F) (-(3 : F))=0 := by linarith only [he,hs]
    rw [hz] at hu
    norm_num at hu
  have hd : cubicPairLift c*(cubicPairLift c+2)=
      (c*(c+2))*((2*c+1)*(2*c+3))^2 := by
    rw [cubicPairLift_add_two]
    unfold cubicPairLift
    ring
  apply And.intro
  . rw [hd,map_mul,map_pow,quadraticChar_sq_one hb,mul_one,hs]
  . simpa only [hb,ite_false] using traceFreePairWeight_cubic_lift c

theorem cubicSafeSector_iterate (hF : Not (ringChar F=2)) (h3 : Not ((3 : F)=0))
    (k : Nat) (c : F)
    (hs : (quadraticChar F) (c*(c+2))=-(quadraticChar F) (-(3 : F))) :
    (quadraticChar F) (((cubicPairLift^[k]) c)*((cubicPairLift^[k]) c+2))=
        -(quadraticChar F) (-(3 : F)) /\
      traceFreePairWeight ((cubicPairLift^[k]) c) 2=traceFreePairWeight c 2 := by
  induction k with
  | zero => exact And.intro hs rfl
  | succ k ih =>
    have ht := cubicSafeSector_step hF h3 ((cubicPairLift^[k]) c) ih.1
    rw [Function.iterate_succ_apply']
    exact And.intro ht.1 (ht.2.trans ih.2)

theorem sum_traceFreePairNumerator_quadratic_character (hF : Not (ringChar F=2)) :
    (Finset.univ.sum fun c : F =>
      traceFreePairNumerator c 2*(quadraticChar F) (c*(c+2)))=
      -(Fintype.card F : Int)+1-2*(quadraticChar F) (-1) := by
  have h2 := two_ne_zero_of_odd hF
  have hcorr := quadraticChar_translate_correlation hF (0 : F) (2 : F)
  simp only [add_zero,ite_eq_right h2,mul_zero,zero_sub] at hcorr
  have first (c : F) :
      ((quadraticChar F) c)^2*(quadraticChar F) (c+2)=
        (quadraticChar F) (c+2)-(if c=0 then (quadraticChar F) (2 : F) else 0) := by
    by_cases hc : c=0
    . simp [hc]
    . rw [quadraticChar_sq_one hc]
      simp only [ite_eq_right hc,sub_zero,one_mul]
  have second (c : F) :
      (quadraticChar F) c*((quadraticChar F) (c+2))^2=
        (quadraticChar F) c-(if c=-(2 : F) then (quadraticChar F) (-(2 : F)) else 0) := by
    by_cases hc : c=-(2 : F)
    . simp [hc]
    . have hn : Not (c+2=0) := fun he => hc (eq_neg_of_add_eq_zero_left he)
      rw [quadraticChar_sq_one hn]
      simp only [ite_eq_right hc,sub_zero,mul_one]
  have hfirst : (Finset.univ.sum fun c : F =>
      ((quadraticChar F) c)^2*(quadraticChar F) (c+2))=-(quadraticChar F) (2 : F) := by
    simp_rw [first]
    rw [Finset.sum_sub_distrib,quadraticChar_translate_sum hF]
    simp
  have hsecond : (Finset.univ.sum fun c : F =>
      (quadraticChar F) c*((quadraticChar F) (c+2))^2)=-(quadraticChar F) (-(2 : F)) := by
    simp_rw [second]
    rw [Finset.sum_sub_distrib,quadraticChar_sum_zero hF]
    simp
  have term (c : F) :
      traceFreePairNumerator c 2*(quadraticChar F) (c*(c+2))=
        ((Fintype.card F : Int)-1)*((quadraticChar F) c*(quadraticChar F) (c+2))+
        (quadraticChar F) (-(2 : F))*(((quadraticChar F) c)^2*(quadraticChar F) (c+2))+
        (quadraticChar F) (2 : F)*((quadraticChar F) c*((quadraticChar F) (c+2))^2) := by
    by_cases hc : c=0
    . simp [hc,traceFreePairNumerator]
    . by_cases hn : c=-(2 : F)
      . simp [hn,traceFreePairNumerator]
      . simp only [traceFreePairNumerator,ite_eq_right hc,ite_eq_right hn,
          twistPairNumerator,map_mul]
        ring
  simp_rw [term]
  simp only [Finset.sum_add_distrib,<- Finset.mul_sum]
  rw [hcorr,hfirst,hsecond]
  have ht := quadraticChar_shift_product (2 : F) h2
  calc
    _ = -(Fintype.card F : Int)+1-
        2*((quadraticChar F) (-(2 : F))*(quadraticChar F) (2 : F)) := by ring
    _ = _ := by rw [ht]


theorem sum_traceFreePairNumerator_safe_sector
    (hF : Not (ringChar F=2)) (h3 : Not ((3 : F)=0)) :
    2*(Finset.univ.sum fun c : F =>
      if (quadraticChar F) (c*(c+2))=-(quadraticChar F) (-(3 : F))
      then traceFreePairNumerator c 2 else 0)=
        (Fintype.card F : Int)*((Fintype.card F : Int)-3)+
          (quadraticChar F) (-(3 : F))*
            ((Fintype.card F : Int)-1+2*(quadraticChar F) (-1)) := by
  let u : Int := (quadraticChar F) (-(3 : F))
  have hu : u^2=1 := quadraticChar_sq_one (neg_ne_zero.mpr h3)
  have project (c : F) :
      2*(if (quadraticChar F) (c*(c+2))=-u then traceFreePairNumerator c 2 else 0)=
        traceFreePairNumerator c 2-u*(traceFreePairNumerator c 2*
          (quadraticChar F) (c*(c+2))) := by
    by_cases hc : c=0
    . simp [hc,traceFreePairNumerator]
    . by_cases hn : c=-(2 : F)
      . simp [hn,traceFreePairNumerator]
      . have hplus : Not (c+2=0) := fun he => hn (eq_neg_of_add_eq_zero_left he)
        let e : Int := (quadraticChar F) (c*(c+2))
        have he : e^2=1 := quadraticChar_sq_one (mul_ne_zero hc hplus)
        change 2*(if e=-u then traceFreePairNumerator c 2 else 0)=
          traceFreePairNumerator c 2-u*(traceFreePairNumerator c 2*e)
        by_cases hs : e=-u
        . rw [ite_eq_left hs,hs]
          calc
            2*traceFreePairNumerator c 2=
                traceFreePairNumerator c 2+u^2*traceFreePairNumerator c 2 := by rw [hu]; ring
            _ = _ := by ring
        . have hz : (e+u)*(e-u)=0 := by
            calc
              _ = e^2-u^2 := by ring
              _ = 0 := by rw [he,hu]; ring
          have hnot : Not (e+u=0) := fun hh => hs (eq_neg_of_add_eq_zero_left hh)
          have hv : e=u := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hnot)
          rw [ite_eq_right hs,hv]
          calc
            2*0=traceFreePairNumerator c 2-u^2*traceFreePairNumerator c 2 := by rw [hu]; ring
            _ = _ := by ring
  have hs :
      2*(Finset.univ.sum fun c : F =>
        if (quadraticChar F) (c*(c+2))=-u then traceFreePairNumerator c 2 else 0)=
      (Finset.univ.sum fun c : F => traceFreePairNumerator c 2)-
        u*(Finset.univ.sum fun c : F =>
          traceFreePairNumerator c 2*(quadraticChar F) (c*(c+2))) := by
    rw [Finset.mul_sum]
    simp_rw [project]
    rw [Finset.sum_sub_distrib,<- Finset.mul_sum]
  rw [sum_traceFreePairNumerator hF (2 : F) (two_ne_zero_of_odd hF),
    sum_traceFreePairNumerator_quadratic_character hF] at hs
  calc
    _ = (Fintype.card F : Int)*((Fintype.card F : Int)-3)-
        u*(-(Fintype.card F : Int)+1-2*(quadraticChar F) (-1)) := hs
    _ = _ := by dsimp [u]; ring

theorem traceFreePairWeight_safe_sector_mass
    (hF : Not (ringChar F=2)) (h3 : Not ((3 : F)=0))
    (hq : 5<=(Fintype.card F : Real)) :
    (1/(Fintype.card F : Real))*(Finset.univ.sum fun c : F =>
      if (quadraticChar F) (c*(c+2))=-(quadraticChar F) (-(3 : F))
      then traceFreePairWeight c 2 else 0)=
        1/2+((quadraticChar F) (-(3 : F)) : Real)*
          ((Fintype.card F : Real)-1+2*((quadraticChar F) (-1) : Real))/
          (2*(Fintype.card F : Real)*((Fintype.card F : Real)-3)) := by
  let q : Real := Fintype.card F
  let u : Real := (quadraticChar F) (-(3 : F))
  let t : Real := (quadraticChar F) (-1)
  let S : Real := Finset.univ.sum fun c : F =>
    if (quadraticChar F) (c*(c+2))=-(quadraticChar F) (-(3 : F))
    then (traceFreePairNumerator c 2 : Real) else 0
  have hi := sum_traceFreePairNumerator_safe_sector hF h3
  have hr : 2*S=q*(q-3)+u*(q-1+2*t) := by
    dsimp [S,q,u,t]
    exact_mod_cast hi
  have he : (Finset.univ.sum fun c : F =>
      if (quadraticChar F) (c*(c+2))=-(quadraticChar F) (-(3 : F))
      then traceFreePairWeight c 2 else 0)=S/(q-3) := by
    dsimp only [S,q]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hs : (quadraticChar F) (c*(c+2))=-(quadraticChar F) (-(3 : F))
    . simp only [ite_eq_left hs,traceFreePairWeight]
    . simp only [ite_eq_right hs,zero_div]
  change (1/q)*(Finset.univ.sum fun c : F =>
    if (quadraticChar F) (c*(c+2))=-(quadraticChar F) (-(3 : F))
    then traceFreePairWeight c 2 else 0)=1/2+u*(q-1+2*t)/(2*q*(q-3))
  rw [he]
  have hq0 : Not (q=0) := ne_of_gt (by dsimp [q]; linarith only [hq])
  have hq3 : Not (q-3=0) := ne_of_gt (by dsimp [q]; linarith only [hq])
  field_simp [hq0,hq3]
  nlinarith only [hr]

theorem traceFreePairWeight_cubic_iterate_mean_ge_safe_sector
    (hF : Not (ringChar F=2)) (h3 : Not ((3 : F)=0))
    (hq : 5<=(Fintype.card F : Real)) (k : Nat) :
    1/2+((quadraticChar F) (-(3 : F)) : Real)*
      ((Fintype.card F : Real)-1+2*((quadraticChar F) (-1) : Real))/
        (2*(Fintype.card F : Real)*((Fintype.card F : Real)-3)) <=
      (1/(Fintype.card F : Real))*
        (Finset.univ.sum fun c : F => traceFreePairWeight ((cubicPairLift^[k]) c) 2) := by
  have h2 := two_ne_zero_of_odd hF
  have nonnegative (x : F) : 0<=traceFreePairWeight x 2 := by
    by_cases hx : x=0
    . simp [hx,traceFreePairWeight_zero]
    . by_cases hn : x=-(2 : F)
      . simp [hn,traceFreePairWeight_neg_shift]
      . have hplus : Not (x+2=0) := fun he => hn (eq_neg_of_add_eq_zero_left he)
        exact le_trans (by norm_num) (traceFreePairWeight_good_bounds x 2 hx hplus h2 hq).1
  have point (c : F) :
      (if (quadraticChar F) (c*(c+2))=-(quadraticChar F) (-(3 : F))
      then traceFreePairWeight c 2 else 0)<=traceFreePairWeight ((cubicPairLift^[k]) c) 2 := by
    by_cases hs : (quadraticChar F) (c*(c+2))=-(quadraticChar F) (-(3 : F))
    . rw [ite_eq_left hs,(cubicSafeSector_iterate hF h3 k c hs).2]
    . rw [ite_eq_right hs]
      exact nonnegative _
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset F)) (fun c _ => point c)
  have hm := mul_le_mul_of_nonneg_left hs
    (div_nonneg (by norm_num : (0 : Real)<=1) (Nat.cast_nonneg (Fintype.card F)))
  rw [traceFreePairWeight_safe_sector_mass hF h3 hq] at hm
  exact hm

theorem traceFreePairWeight_cubic_iterate_mean_lower
    (hF : Not (ringChar F=2)) (hq : 5<=(Fintype.card F : Real)) (k : Nat) :
    ((Fintype.card F : Real)-3)/(2*(Fintype.card F : Real)) <=
      (1/(Fintype.card F : Real))*
        (Finset.univ.sum fun c : F => traceFreePairWeight ((cubicPairLift^[k]) c) 2) := by
  let q : Real := Fintype.card F
  have hqp : 0<q := by dsimp [q]; linarith only [hq]
  have hq3p : 0<q-3 := by dsimp [q]; linarith only [hq]
  by_cases h3 : (3 : F)=0
  . rw [traceFreePairWeight_cubic_iterate_mean_char_three hF h3 hq k]
    have hden : 0<2*q := by positivity
    have hm := div_le_div_of_nonneg_right
      (show q-3<=2*q from by dsimp [q]; linarith only [hq]) hden.le
    simpa only [div_self (ne_of_gt hden)] using hm
  . let u : Real := (quadraticChar F) (-(3 : F))
    let t : Real := (quadraticChar F) (-1)
    have hui := quadraticChar_sq_one (neg_ne_zero.mpr h3)
    have hti := quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero : Not ((1 : F)=0)))
    have hu : u^2=1 := by dsimp [u]; exact_mod_cast hui
    have ht : t^2=1 := by dsimp [t]; exact_mod_cast hti
    have hulow : -1<=u := by nlinarith only [hu,sq_nonneg (u+1)]
    have htlow : -1<=t := by nlinarith only [ht,sq_nonneg (t+1)]
    have htup : t<=1 := by nlinarith only [ht,sq_nonneg (t-1)]
    have hA : 0<=q-1+2*t := by dsimp [q]; linarith only [hq,htlow]
    have hj := mul_nonneg (show 0<=u+1 from by linarith only [hulow]) hA
    have hp : -(q+1)<=u*(q-1+2*t) := by nlinarith only [hj,htup]
    have hn : 0<=3*(q-3)+u*(q-1+2*t) := by dsimp [q] at *; linarith only [hp,hq]
    have hden : 0<2*q*(q-3) := by positivity
    have he : (1/2+u*(q-1+2*t)/(2*q*(q-3)))-(q-3)/(2*q)=
        (3*(q-3)+u*(q-1+2*t))/(2*q*(q-3)) := by
      field_simp [ne_of_gt hqp,ne_of_gt hq3p]
      ring
    have hscalar : (q-3)/(2*q)<=1/2+u*(q-1+2*t)/(2*q*(q-3)) :=
      sub_nonneg.mp (by rw [he]; exact div_nonneg hn hden.le)
    exact le_trans hscalar (traceFreePairWeight_cubic_iterate_mean_ge_safe_sector hF h3 hq k)

end FiniteField
