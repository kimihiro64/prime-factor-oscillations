/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairSquareTransport

/-!
# Exact attainable profiles and sharp mass of square transports

All pullbacks of the canonical actual two-class law are precisely its
masks that retain the double-negative core. The least mean is
(q-chi(-1))/(4*q), attained by a compatible idempotent map; the greatest
mean is one, attained by the identity. The quantifiers include every
nonzero shift in every odd finite field of cardinal at least five.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem squarePairCollapse_zero (h : F) (hh : Not (h=0)) :
    squarePairCollapse 0 h=0 := by
  have hi : (quadraticChar F) (h*(0+h))=1 := by
    rw [zero_add,map_mul]
    nlinarith only [quadraticChar_sq_one hh]
  simp only [squarePairCollapse,hi,ite_true]

theorem squarePairCollapse_neg_shift (h : F) (hh : Not (h=0)) :
    squarePairCollapse (-h) h= -h := by
  have hi : (quadraticChar F) ((-h)*(-h))=1 := by
    rw [map_mul]
    nlinarith only [quadraticChar_sq_one (neg_ne_zero.mpr hh)]
  simp only [squarePairCollapse,neg_add_cancel,mul_zero,hi]
  norm_num

theorem squarePairCollapse_idempotent (c h : F) (hh : Not (h=0)) :
    squarePairCollapse (squarePairCollapse c h) h=squarePairCollapse c h := by
  by_cases hb : (quadraticChar F) (h*(c+h))=1
  . have he : squarePairCollapse c h=0 := by simp only [squarePairCollapse,ite_eq_left hb]
    rw [he,squarePairCollapse_zero h hh]
  . by_cases ha : (quadraticChar F) ((-h)*c)=1
    . have he : squarePairCollapse c h= -h := by
        simp only [squarePairCollapse,ite_eq_right hb,ite_eq_left ha]
      rw [he,squarePairCollapse_neg_shift h hh]
    . have he : squarePairCollapse c h=c := by
        simp only [squarePairCollapse,ite_eq_right hb,ite_eq_right ha]
      rw [he]
      exact he

theorem squarePair_mask_attainment (h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) (A : F -> Prop)
    (hA : forall c : F, squarePairCore c h -> A c) :
    Exists (fun Phi : F -> F =>
      (forall c : F, squarePairReach c (Phi c) h) /\
      (forall c : F, traceFreePairWeight (Phi c) h=
        if A c then traceFreePairWeight c h else 0)) := by
  let Phi : F -> F := fun c => if A c then c else squarePairCollapse c h
  refine Exists.intro Phi (And.intro ?_ ?_)
  . intro c
    by_cases ha : A c
    . simpa only [Phi,ite_eq_left ha] using squarePairReach_refl c h
    . simpa only [Phi,ite_eq_right ha] using squarePairCollapse_reachable c h hh
  . intro c
    by_cases ha : A c
    . simp only [Phi,ite_eq_left ha]
    . have hc : Not (squarePairCore c h) := by intro hc; exact ha (hA c hc)
      simp only [Phi,ite_eq_right ha,squarePairCollapse_profile c h hh hq,ite_eq_right hc]

theorem squarePair_profiles_iff (h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) (f : F -> Real) :
    (Exists (fun Phi : F -> F =>
      (forall c : F, squarePairReach c (Phi c) h) /\
      (forall c : F, traceFreePairWeight (Phi c) h=f c))) <->
    Exists (fun A : F -> Prop =>
      (forall c : F, squarePairCore c h -> A c) /\
      (forall c : F, f c=if A c then traceFreePairWeight c h else 0)) := by
  constructor
  . intro hex
    let Phi : F -> F := Classical.choose hex
    have hPhi := Classical.choose_spec hex
    let A : F -> Prop := fun c => f c=traceFreePairWeight c h
    refine Exists.intro A (And.intro ?_ ?_)
    . intro c hc
      change f c=traceFreePairWeight c h
      rw [<- hPhi.2 c,traceFreePairWeight_square_core c (Phi c) h hh hq hc (hPhi.1 c),
        traceFreePairWeight_core c h hc hq]
    . intro c
      by_cases ha : A c
      . rw [ite_eq_left ha]
        exact ha
      . rw [ite_eq_right ha]
        rcases traceFreePairWeight_square_reach_cases c (Phi c) h (hPhi.1 c) with hz | he
        . rw [<- hPhi.2 c,hz]
        . exact False.elim (ha (by change f c=traceFreePairWeight c h; rw [<- hPhi.2 c,he]))
  . intro hex
    let A : F -> Prop := Classical.choose hex
    have hA := Classical.choose_spec hex
    have hatt := squarePair_mask_attainment h hh hq A hA.1
    let Phi : F -> F := Classical.choose hatt
    have hPhi := Classical.choose_spec hatt
    refine Exists.intro Phi (And.intro hPhi.1 ?_)
    intro c
    rw [hPhi.2 c,hA.2 c]

theorem squarePairCore_indicator (c h : F) (hh : Not (h=0)) :
    4*(if squarePairCore c h then (1 : Int) else 0)=
      (1-(quadraticChar F) ((-h)*c))*(1-(quadraticChar F) (h*(c+h))) := by
  by_cases hc : c=0
  . subst c
    have hb : (quadraticChar F) (h*(0+h))=1 := by
      rw [zero_add,map_mul]
      nlinarith only [quadraticChar_sq_one hh]
    simp only [squarePairCore,hb,mul_zero]
    norm_num
  . by_cases hn : c=-h
    . subst c
      have ha : (quadraticChar F) ((-h)*(-h))=1 := by
        rw [map_mul]
        nlinarith only [quadraticChar_sq_one (neg_ne_zero.mpr hh)]
      simp only [squarePairCore,ha,neg_add_cancel,mul_zero]
      norm_num
    . have hch : Not (c+h=0) := by intro he; exact hn (eq_neg_of_add_eq_zero_left he)
      have ha : (quadraticChar F) ((-h)*c)=1 \/ (quadraticChar F) ((-h)*c)= -1 := by
        rcases QuadraticPairEuler.quadraticChar_real_signs ((-h)*c)
          (mul_ne_zero (neg_ne_zero.mpr hh) hc) with hs | hs
        . exact Or.inl (by exact_mod_cast hs)
        . exact Or.inr (by exact_mod_cast hs)
      have hb : (quadraticChar F) (h*(c+h))=1 \/ (quadraticChar F) (h*(c+h))= -1 := by
        rcases QuadraticPairEuler.quadraticChar_real_signs (h*(c+h))
          (mul_ne_zero hh hch) with hs | hs
        . exact Or.inl (by exact_mod_cast hs)
        . exact Or.inr (by exact_mod_cast hs)
      rcases ha with ha | ha <;> rcases hb with hb | hb <;>
        simp only [squarePairCore,ha,hb] <;> norm_num

theorem sum_squarePairCore_indicator (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) :
    4*(Finset.univ.sum fun c : F => if squarePairCore c h then (1 : Int) else 0)=
      (Fintype.card F : Int)-(quadraticChar F) (-1) := by
  have ha : (Finset.univ.sum fun c : F => (quadraticChar F) ((-h)*c))=0 := by
    simp only [map_mul,<- Finset.mul_sum,quadraticChar_sum_zero hF,mul_zero]
  have hb : (Finset.univ.sum fun c : F => (quadraticChar F) (h*(c+h)))=0 := by
    simp only [map_mul,<- Finset.mul_sum,quadraticChar_translate_sum hF h,mul_zero]
  have hc := quadraticChar_translate_correlation hF (0 : F) h
  simp only [add_zero,ite_eq_right hh,mul_zero,zero_sub] at hc
  have hp (c : F) :
      (quadraticChar F) ((-h)*c)*(quadraticChar F) (h*(c+h))=
        ((quadraticChar F) (-h)*(quadraticChar F) h)*
          ((quadraticChar F) c*(quadraticChar F) (c+h)) := by
    simp only [map_mul]
    ring
  have hab : (Finset.univ.sum fun c : F =>
      (quadraticChar F) ((-h)*c)*(quadraticChar F) (h*(c+h)))=
        -(quadraticChar F) (-1) := by
    simp_rw [hp]
    rw [<- Finset.mul_sum,hc,quadraticChar_shift_product h hh]
    ring
  have hi (c : F) :
      4*(if squarePairCore c h then (1 : Int) else 0)=
        1-(quadraticChar F) ((-h)*c)-(quadraticChar F) (h*(c+h))+
          (quadraticChar F) ((-h)*c)*(quadraticChar F) (h*(c+h)) := by
    rw [squarePairCore_indicator c h hh]
    ring
  calc
    _=Finset.univ.sum (fun c : F =>
        4*(if squarePairCore c h then (1 : Int) else 0)) := Finset.mul_sum _ _ _
    _=Finset.univ.sum (fun c : F =>
        1-(quadraticChar F) ((-h)*c)-(quadraticChar F) (h*(c+h))+
          (quadraticChar F) ((-h)*c)*(quadraticChar F) (h*(c+h))) := by
      apply Finset.sum_congr rfl
      intro c _
      exact hi c
    _=_ := by
      simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,ha,hb,hab,
        Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
      ring

theorem squarePairCore_mass (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 5<=(Fintype.card F : Real)) :
    (1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => if squarePairCore c h then (1 : Real) else 0)=
        ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))/
          (4*(Fintype.card F : Real)) := by
  have hi := sum_squarePairCore_indicator hF h hh
  have hs : 4*(Finset.univ.sum fun c : F =>
      if squarePairCore c h then (1 : Real) else 0)=
        (Fintype.card F : Real)-((quadraticChar F) (-1) : Real) := by
    exact_mod_cast hi
  have hq0 : Not ((Fintype.card F : Real)=0) := ne_of_gt (by linarith only [hq])
  have he : (Finset.univ.sum fun c : F =>
      if squarePairCore c h then (1 : Real) else 0)=
        ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))/4 := by
    linarith only [hs]
  rw [he]
  field_simp [hq0]

theorem traceFreePairWeight_square_extremal (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 5<=(Fintype.card F : Real))
    (Phi : F -> F) (hPhi : forall c : F, squarePairReach c (Phi c) h) :
    ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))/
        (4*(Fintype.card F : Real)) <=
      (1/(Fintype.card F : Real))*
        (Finset.univ.sum fun c : F => traceFreePairWeight (Phi c) h) /\
    (1/(Fintype.card F : Real))*
        (Finset.univ.sum fun c : F => traceFreePairWeight (Phi c) h)<=1 := by
  have hl (c : F) : (if squarePairCore c h then (1 : Real) else 0)<=
      traceFreePairWeight (Phi c) h := by
    by_cases hc : squarePairCore c h
    . rw [ite_eq_left hc,traceFreePairWeight_square_core c (Phi c) h hh hq hc (hPhi c)]
    . rw [ite_eq_right hc]
      exact traceFreePairWeight_nonneg_all (Phi c) h hh hq
  have hu (c : F) : traceFreePairWeight (Phi c) h<=traceFreePairWeight c h := by
    rcases traceFreePairWeight_square_reach_cases c (Phi c) h (hPhi c) with hz | he
    . rw [hz]
      exact traceFreePairWeight_nonneg_all c h hh hq
    . exact le_of_eq he
  have hscale : 0<=1/(Fintype.card F : Real) := by positivity
  have hlo := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun c (_ : Membership.mem Finset.univ c) => hl c)) hscale
  have hup := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun c (_ : Membership.mem Finset.univ c) => hu c)) hscale
  rw [squarePairCore_mass hF h hh hq] at hlo
  rw [traceFreePairWeight_mean_one hF h hh hq] at hup
  exact And.intro hlo hup

theorem traceFreePairWeight_square_minimum_attained
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) :
    (forall c : F, squarePairReach c (squarePairCollapse c h) h) /\
    (forall c : F, squarePairCollapse (squarePairCollapse c h) h=squarePairCollapse c h) /\
    (1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => traceFreePairWeight (squarePairCollapse c h) h)=
        ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))/
          (4*(Fintype.card F : Real)) := by
  refine And.intro (fun c => squarePairCollapse_reachable c h hh)
    (And.intro (fun c => squarePairCollapse_idempotent c h hh) ?_)
  simp_rw [squarePairCollapse_profile (h := h) (hh := hh) (hq := hq)]
  exact squarePairCore_mass hF h hh hq

end FiniteField
