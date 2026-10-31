/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldRawHellinger
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistAverage

/-!
# Exact character projection of the original quadratic-pair law

The singular-row-completed elliptic trace is orthogonal to every function
of the two quadratic-character signs when the character of -1 is -1.
The arithmetic identities retain both singular rows. They use exact
previously proved signed trace moments, not Hasse or an RH hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldCharacterProjection
attribute [local instance] Classical.propDecidable
open _root_.FiniteField
open _root_.FiniteField.QuadraticPairEuler
open FiniteFieldRawHellinger
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev trace (h c : F) : Int := splitCubicPointTrace c (c+h)

def maskedTrace (h c : F) : Int :=
  trace h c-(if c=0 then (quadraticChar F) (-h) else 0)-
    (if c=-h then (quadraticChar F) h else 0)

theorem masked_trace_good (h c : F) (hc : Not (c=0)) (hn : Not (c=-h)) :
    maskedTrace h c=trace h c := by
  simp only [maskedTrace,ite_eq_right hc,ite_eq_right hn,sub_zero]

theorem masked_trace_zero (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0)) :
    maskedTrace h 0=0 := by
  have hn : Not ((0 : F)=-h) := Ne.symm (neg_ne_zero.mpr hh)
  simp [maskedTrace,trace,hn,splitCubicPointTrace_zero_left hF]

theorem masked_trace_neg_shift (hF : Not (ringChar F=2)) (h : F)
    (hh : Not (h=0)) : maskedTrace h (-h)=0 := by
  have ht : trace h (-h)=(quadraticChar F) h := by
    unfold trace
    rw [neg_add_cancel,splitCubicPointTrace_comm hF,
      splitCubicPointTrace_zero_left hF]
    simp
  simp [maskedTrace,neg_ne_zero.mpr hh,ht]

theorem masked_trace_pairing (h : F) (f : F -> Int) :
    (Finset.univ.sum fun c : F => maskedTrace h c*f c)=
      (Finset.univ.sum fun c : F => trace h c*f c)-
        (quadraticChar F) (-h)*f 0-(quadraticChar F) h*f (-h) := by
  have hp (c : F) :
      maskedTrace h c*f c=trace h c*f c-
        (if c=0 then (quadraticChar F) (-h)*f 0 else 0)-
        (if c=-h then (quadraticChar F) h*f (-h) else 0) := by
    by_cases hc : c=0
    . subst c
      simp only [maskedTrace,ite_true,sub_mul]
      split_ifs <;> simp_all <;> ring
    . by_cases hn : c=-h
      . subst c
        simp only [maskedTrace,ite_eq_right hc,ite_true,zero_mul,sub_zero,sub_mul]
      . simp only [maskedTrace,ite_eq_right hc,ite_eq_right hn,zero_mul,sub_zero]
  simp_rw [hp]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  simp

theorem trace_reflection (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h c : F) :
    trace h (-h-c) = -trace h c := by
  calc
    _ = splitCubicPointTrace ((-1 : F)*c) ((-1 : F)*(c+h)) := by
      unfold trace
      rw [splitCubicPointTrace_comm hF]
      congr 1 <;> ring
    _ = (quadraticChar F) (-1)*trace h c :=
      splitCubicPointTrace_scale hF (-1) (neg_ne_zero.mpr one_ne_zero) c (c+h)
    _ = _ := by rw [hm]; ring

theorem trace_two_character_sum (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) :
    (Finset.univ.sum fun c : F =>
      trace h c*((quadraticChar F) c*(quadraticChar F) (c+h)))=0 := by
  let e : Equiv F F :=
    { toFun := fun c => -h-c
      invFun := fun c => -h-c
      left_inv := by intro c; ring
      right_inv := by intro c; ring }
  have ht (c : F) : trace h (e c) = -trace h c := trace_reflection hF hm h c
  have hc (c : F) :
      (quadraticChar F) (e c)*(quadraticChar F) (e c+h)=
        (quadraticChar F) c*(quadraticChar F) (c+h) := by
    have he1 : e c=(-1 : F)*(c+h) := by change -h-c=(-1 : F)*(c+h); ring
    have he2 : e c+h=(-1 : F)*c := by change -h-c+h=(-1 : F)*c; ring
    rw [he2,he1,map_mul,map_mul,hm]
    ring
  have he := Equiv.sum_comp e (fun c : F =>
    trace h c*((quadraticChar F) c*(quadraticChar F) (c+h)))
  simp_rw [ht,hc,neg_mul,Finset.sum_neg_distrib] at he
  linarith only [he]

theorem masked_trace_sum (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) :
    (Finset.univ.sum fun c : F => maskedTrace h c)=0 := by
  have hp := masked_trace_pairing h (fun _ => (1 : Int))
  have hn : (quadraticChar F) (-h)=-(quadraticChar F) h := by
    have he : -h=(-1 : F)*h := by ring
    rw [he,map_mul,hm,neg_one_mul]
  simp only [mul_one] at hp
  rw [sum_splitCubicPointTrace hF,hn] at hp
  linarith only [hp]

theorem masked_trace_left_character_sum (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0)) :
    (Finset.univ.sum fun c : F => maskedTrace h c*(quadraticChar F) c)=0 := by
  have hs : (Finset.univ.sum fun c : F => trace h c*(quadraticChar F) c)=-1 := by
    simpa using sum_splitCubicPointTrace_mul_char hF h (0 : F) hh
  have hp := masked_trace_pairing h (quadraticChar F)
  have hc := quadraticChar_shift_product h hh
  rw [hm] at hc
  have hc' : (quadraticChar F) h*(quadraticChar F) (-h)=-1 := by
    nlinarith only [hc]
  have hz : (quadraticChar F) (0 : F)=0 := by simp
  simpa only [hz,mul_zero,sub_zero,hs,hc',sub_self] using hp

theorem masked_trace_right_character_sum (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0)) :
    (Finset.univ.sum fun c : F => maskedTrace h c*(quadraticChar F) (c+h))=0 := by
  have hs : (Finset.univ.sum fun c : F => trace h c*(quadraticChar F) (c+h))=-1 := by
    simpa using sum_splitCubicPointTrace_mul_char hF h h hh
  have hp := masked_trace_pairing h (fun c => (quadraticChar F) (c+h))
  have hc := quadraticChar_shift_product h hh
  rw [hm] at hc
  have hz : (quadraticChar F) (0 : F)=0 := by simp
  simpa only [zero_add,neg_add_cancel,hz,mul_zero,sub_zero,hs,hc,sub_self] using hp

theorem masked_trace_two_character_sum (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) :
    (Finset.univ.sum fun c : F =>
      maskedTrace h c*((quadraticChar F) c*(quadraticChar F) (c+h)))=0 := by
  have hp := masked_trace_pairing h
    (fun c => (quadraticChar F) c*(quadraticChar F) (c+h))
  have hz : (quadraticChar F) (0 : F)=0 := by simp
  simpa only [zero_add,neg_add_cancel,hz,mul_zero,zero_mul,sub_zero,
    trace_two_character_sum hF hm h] using hp

theorem masked_trace_square_sum (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) :
    (Finset.univ.sum fun c : F => (maskedTrace h c)^2)=
      ((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1) := by
  have hp (c : F) :
      (maskedTrace h c)^2=(trace h c)^2-
        (if c=0 then 1 else 0)-(if c=-h then 1 else 0) := by
    by_cases hc : c=0
    . subst c
      have hn : Not ((0 : F)=-h) := Ne.symm (neg_ne_zero.mpr hh)
      rw [masked_trace_zero hF h hh]
      simp only [trace,zero_add,splitCubicPointTrace_zero_left hF,
        quadraticChar_sq_one (neg_ne_zero.mpr hh),ite_true,ite_eq_right hn]
      ring
    . by_cases hn : c=-h
      . subst c
        have ht : trace h (-h)=(quadraticChar F) h := by
          unfold trace
          rw [neg_add_cancel,splitCubicPointTrace_comm hF,
            splitCubicPointTrace_zero_left hF]
          simp
        rw [masked_trace_neg_shift hF h hh,ht,quadraticChar_sq_one hh]
        simp only [ite_eq_right hc,ite_true]
        ring
      . rw [masked_trace_good h c hc hn]
        simp only [ite_eq_right hc,ite_eq_right hn,sub_zero]
  simp_rw [hp]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,sum_splitCubicPointTrace_square hF h hh]
  simp
  ring


theorem masked_trace_polynomial_sum (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (a b d e : Real) :
    (Finset.univ.sum fun c : F => (maskedTrace h c : Real)*
      (a+b*((quadraticChar F) c : Real)+d*((quadraticChar F) (c+h) : Real)+
        e*(((quadraticChar F) c : Real)*((quadraticChar F) (c+h) : Real))))=0 := by
  have h0 : (Finset.univ.sum fun c : F => (maskedTrace h c : Real))=0 := by
    exact_mod_cast masked_trace_sum hF hm h
  have hx : (Finset.univ.sum fun c : F =>
      (maskedTrace h c : Real)*((quadraticChar F) c : Real))=0 := by
    exact_mod_cast masked_trace_left_character_sum hF hm h hh
  have hy : (Finset.univ.sum fun c : F =>
      (maskedTrace h c : Real)*((quadraticChar F) (c+h) : Real))=0 := by
    exact_mod_cast masked_trace_right_character_sum hF hm h hh
  have hxy : (Finset.univ.sum fun c : F => (maskedTrace h c : Real)*
      (((quadraticChar F) c : Real)*((quadraticChar F) (c+h) : Real)))=0 := by
    exact_mod_cast masked_trace_two_character_sum hF hm h
  have hp (c : F) : (maskedTrace h c : Real)*
      (a+b*((quadraticChar F) c : Real)+d*((quadraticChar F) (c+h) : Real)+
        e*(((quadraticChar F) c : Real)*((quadraticChar F) (c+h) : Real)))=
      a*(maskedTrace h c : Real)+
        b*((maskedTrace h c : Real)*((quadraticChar F) c : Real))+
        d*((maskedTrace h c : Real)*((quadraticChar F) (c+h) : Real))+
        e*((maskedTrace h c : Real)*
          (((quadraticChar F) c : Real)*((quadraticChar F) (c+h) : Real))) := by ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib,<- Finset.mul_sum,h0,hx,hy,hxy,mul_zero,add_zero]

theorem masked_trace_table_sum (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (g : Int -> Int -> Real) :
    (Finset.univ.sum fun c : F =>
      (maskedTrace h c : Real)*g ((quadraticChar F) c) ((quadraticChar F) (c+h)))=0 := by
  let a : Real := (g 1 1+g 1 (-1)+g (-1) 1+g (-1) (-1))/4
  let b : Real := (g 1 1+g 1 (-1)-g (-1) 1-g (-1) (-1))/4
  let d : Real := (g 1 1-g 1 (-1)+g (-1) 1-g (-1) (-1))/4
  let e : Real := (g 1 1-g 1 (-1)-g (-1) 1+g (-1) (-1))/4
  have signs (z : F) (hz : Not (z=0)) :
      (quadraticChar F) z=1 \/ (quadraticChar F) z=-1 := by
    rcases quadraticChar_real_signs z hz with hp | hn
    . exact Or.inl (by exact_mod_cast hp)
    . exact Or.inr (by exact_mod_cast hn)
  have hp (c : F) :
      (maskedTrace h c : Real)*g ((quadraticChar F) c) ((quadraticChar F) (c+h))=
      (maskedTrace h c : Real)*
        (a+b*((quadraticChar F) c : Real)+d*((quadraticChar F) (c+h) : Real)+
          e*(((quadraticChar F) c : Real)*((quadraticChar F) (c+h) : Real))) := by
    by_cases hc : c=0
    . subst c
      rw [masked_trace_zero hF h hh]
      simp
    . by_cases hn : c=-h
      . subst c
        rw [masked_trace_neg_shift hF h hh]
        simp
      . have hch : Not (c+h=0) := by
          intro hz
          exact hn (eq_neg_of_add_eq_zero_left hz)
        rcases signs c hc with hx | hx <;>
          rcases signs (c+h) hch with hy | hy <;>
          simp only [hx,hy,Int.cast_one,Int.cast_neg] <;>
          dsimp only [a,b,d,e] <;> ring
  calc
    _ = Finset.univ.sum (fun c : F => (maskedTrace h c : Real)*
        (a+b*((quadraticChar F) c : Real)+d*((quadraticChar F) (c+h) : Real)+
          e*(((quadraticChar F) c : Real)*((quadraticChar F) (c+h) : Real)))) :=
      Finset.sum_congr rfl (fun c _ => hp c)
    _ = 0 := masked_trace_polynomial_sum hF hm h hh a b d e

def optimalTable (h : F) (x y : Int) : Real :=
  if x=0 then 0 else if y=0 then 0 else
    ((Fintype.card F : Real)-1-
      (1+((quadraticChar F) h : Real))*(x : Real)-
      (1-((quadraticChar F) h : Real))*(y : Real))/
        ((Fintype.card F : Real)-3)

def optimalDensity (h c : F) : Real :=
  optimalTable h ((quadraticChar F) c) ((quadraticChar F) (c+h))

theorem raw_density_decomposition (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) (c : F) :
    rawDensity h c=optimalDensity h c-
      (maskedTrace h c : Real)/((Fintype.card F : Real)-3) := by
  by_cases hc : c=0
  . subst c
    rw [masked_trace_zero hF h hh]
    simp [rawDensity,normalizedPairCount,monicQuadraticPairCount_zero hF,
      optimalDensity,optimalTable]
  . by_cases hn : c=-h
    . subst c
      rw [masked_trace_neg_shift hF h hh]
      simp [rawDensity,normalizedPairCount,monicQuadraticPairCount_neg_shift hF,
        optimalDensity,optimalTable]
    . have hch : Not (c+h=0) := by
        intro hz
        exact hn (eq_neg_of_add_eq_zero_left hz)
      have hx : Not ((quadraticChar F) c=0) := by
        intro hz
        have hs := quadraticChar_sq_one hc
        rw [hz] at hs
        norm_num at hs
      have hy : Not ((quadraticChar F) (c+h)=0) := by
        intro hz
        have hs := quadraticChar_sq_one hch
        rw [hz] at hs
        norm_num at hs
      have hm' : (quadraticChar F) (-h)=-(quadraticChar F) h := by
        have he : -h=(-1 : F)*h := by ring
        rw [he,map_mul,hm,neg_one_mul]
      have hd : offset ((quadraticChar F) h : Real)
          ((quadraticChar F) (-h) : Real)=3 := by
        unfold offset
        rw [hm',Int.cast_neg]
        ring
      unfold rawDensity
      rw [normalizedPairCount_eq_rational hF c h hc hch hh hq,hd,
        masked_trace_good h c hc hn]
      simp only [optimalDensity,optimalTable,ite_eq_right hx,ite_eq_right hy,
        correction,hm',Int.cast_neg,trace]
      ring

theorem raw_projection_pythagoras (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) (g : Int -> Int -> Real) :
    FiniteFieldPairAffinity.squareDistance (Fintype.card F : Real)
      (rawDensity h) (fun c => g ((quadraticChar F) c) ((quadraticChar F) (c+h))) =
      ((Fintype.card F : Real)+1)/
        ((Fintype.card F : Real)*((Fintype.card F : Real)-3))+
      FiniteFieldPairAffinity.squareDistance (Fintype.card F : Real)
        (optimalDensity h) (fun c => g ((quadraticChar F) c) ((quadraticChar F) (c+h))) := by
  let q : Real := Fintype.card F
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have hq3 : 0<q-3 := by dsimp only [q]; linarith only [hq]
  have hs : (Finset.univ.sum fun c : F => (maskedTrace h c : Real)^2)=(q-3)*(q+1) := by
    dsimp only [q]
    exact_mod_cast masked_trace_square_sum hF h hh
  have hc : (Finset.univ.sum fun c : F => (maskedTrace h c : Real)*
      (optimalDensity h c-g ((quadraticChar F) c) ((quadraticChar F) (c+h))))=0 := by
    simpa only [optimalDensity] using masked_trace_table_sum hF hm h hh
      (fun x y => optimalTable h x y-g x y)
  have hp (c : F) :
      (rawDensity h c-g ((quadraticChar F) c) ((quadraticChar F) (c+h)))^2 =
      (1/(q-3)^2)*(maskedTrace h c : Real)^2+
        (optimalDensity h c-g ((quadraticChar F) c) ((quadraticChar F) (c+h)))^2-
        (2/(q-3))*((maskedTrace h c : Real)*
          (optimalDensity h c-g ((quadraticChar F) c) ((quadraticChar F) (c+h)))) := by
    rw [raw_density_decomposition hF hm h hh hq c]
    change (optimalDensity h c-(maskedTrace h c : Real)/(q-3)-
      g ((quadraticChar F) c) ((quadraticChar F) (c+h)))^2 = _
    field_simp [ne_of_gt hq3]
    <;> ring
  unfold FiniteFieldPairAffinity.squareDistance
  simp_rw [hp]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,<- Finset.mul_sum,
    hs,hc,mul_zero,sub_zero]
  change (1/q)*((1/(q-3)^2)*((q-3)*(q+1))+
      (Finset.univ.sum fun c : F =>
        (optimalDensity h c-g ((quadraticChar F) c) ((quadraticChar F) (c+h)))^2))=
    (q+1)/(q*(q-3))+(1/q)*(Finset.univ.sum fun c : F =>
      (optimalDensity h c-g ((quadraticChar F) c) ((quadraticChar F) (c+h)))^2)
  field_simp [ne_of_gt hq0,ne_of_gt hq3]
  <;> ring

theorem character_only_error_lower (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) (g : Int -> Int -> Real) :
    ((Fintype.card F : Real)+1)/
        ((Fintype.card F : Real)*((Fintype.card F : Real)-3)) <=
      FiniteFieldPairAffinity.squareDistance (Fintype.card F : Real)
        (rawDensity h) (fun c => g ((quadraticChar F) c) ((quadraticChar F) (c+h))) := by
  rw [raw_projection_pythagoras hF hm h hh hq g]
  have hn : 0<=FiniteFieldPairAffinity.squareDistance (Fintype.card F : Real)
      (optimalDensity h) (fun c => g ((quadraticChar F) c) ((quadraticChar F) (c+h))) := by
    unfold FiniteFieldPairAffinity.squareDistance
    positivity
  linarith only [hn]

theorem optimal_density_error (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) :
    FiniteFieldPairAffinity.squareDistance (Fintype.card F : Real)
      (rawDensity h) (optimalDensity h)=
      ((Fintype.card F : Real)+1)/
        ((Fintype.card F : Real)*((Fintype.card F : Real)-3)) := by
  have hp := raw_projection_pythagoras hF hm h hh hq (optimalTable h)
  simpa only [optimalDensity,FiniteFieldPairAffinity.squareDistance,sub_self,
    zero_pow (by norm_num : Not (2=0)),Finset.sum_const_zero,mul_zero,add_zero] using hp


end PrimeFactorOscillations.FiniteFieldCharacterProjection
