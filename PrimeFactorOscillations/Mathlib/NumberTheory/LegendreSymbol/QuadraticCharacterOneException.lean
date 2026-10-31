/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticCharacterPolynomial

/-!
# Polynomial square values with one exceptional input

An affine polynomial cannot be nonconstant. A genuinely quadratic
polynomial is a square polynomial, apart from an explicitly characterized
five-element-field exception. The exceptional character and both roots
are retained for the coupled two-anchor classification.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem character_lower (x : F) : -1<=(quadraticChar F) x := by
  by_cases hx : x=0
  . simp [hx]
  . nlinarith only [quadraticChar_sq_one hx]

private theorem character_upper (x : F) : (quadraticChar F) x<=1 := by
  by_cases hx : x=0
  . simp [hx]
  . nlinarith only [quadraticChar_sq_one hx]

theorem square_off_one_character_sum (f : F -> F) (t : F)
    (hsquare : forall x : F, Not (x=t) -> IsSquare (f x)) :
    (Finset.univ.sum fun x : F => (quadraticChar F) (f x))=
      (Fintype.card F : Int)-
        (Finset.univ.sum fun x : F => if f x=0 then (1 : Int) else 0)-1+
        (quadraticChar F) (f t)+(if f t=0 then 1 else 0) := by
  have hp (x : F) :
      (quadraticChar F) (f x)=
        (1-(if f x=0 then (1 : Int) else 0))+
          (if x=t then (quadraticChar F) (f t)-1+(if f t=0 then 1 else 0) else 0) := by
    by_cases hxt : x=t
    . subst x
      rw [ite_eq_left rfl]
      ring
    . rw [ite_eq_right hxt]
      by_cases hz : f x=0
      . simp [hz]
      . rw [(quadraticChar_one_iff_isSquare hz).mpr (hsquare x hxt),ite_eq_right hz]
        ring
  calc
    _ = Finset.univ.sum (fun x : F =>
        (1-(if f x=0 then (1 : Int) else 0))+
          (if x=t then (quadraticChar F) (f t)-1+(if f t=0 then 1 else 0) else 0)) :=
      Finset.sum_congr rfl (fun x _ => hp x)
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
        Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      ring

theorem affine_square_off_one_constant (hF : Not (ringChar F=2))
    (hq : 5<=(Fintype.card F : Int)) (a b t : F)
    (hsquare : forall x : F, Not (x=t) -> IsSquare (a*x+b)) : a=0 := by
  by_contra ha
  have hs := square_off_one_character_sum (fun x : F => a*x+b) t hsquare
  rw [quadraticChar_affine_sum hF a b ha,affine_zero_indicator_sum a b ha] at hs
  have hl := character_lower (a*t+b)
  have hz : (0 : Int)<=(if a*t+b=0 then 1 else 0) := by split_ifs <;> norm_num
  linarith only [hq,hs,hl,hz]

theorem quadratic_square_off_one_dichotomy (hF : Not (ringChar F=2))
    (hq : 5<=(Fintype.card F : Int)) (a b c t : F) (ha : Not (a=0))
    (hsquare : forall x : F, Not (x=t) -> IsSquare (a*x^2+b*x+c)) :
    (b^2-4*a*c=0 /\ (quadraticChar F) a=1) \/
      ((Fintype.card F : Int)=5 /\ (quadraticChar F) a= -1 /\
        (quadraticChar F) (b^2-4*a*c)=1 /\
          (quadraticChar F) (a*t^2+b*t+c)= -1) := by
  have hs := square_off_one_character_sum (fun x : F => a*x^2+b*x+c) t hsquare
  rw [quadraticChar_quadratic_sum hF a b c ha,
    quadratic_zero_indicator_sum hF a b c ha] at hs
  have hlo := character_lower (a*t^2+b*t+c)
  have hz : (0 : Int)<=(if a*t^2+b*t+c=0 then 1 else 0) := by
    split_ifs <;> norm_num
  by_cases hd : b^2-4*a*c=0
  . apply Or.inl
    refine And.intro hd ?_
    rw [ite_eq_left hd,hd] at hs
    have hzchar : (quadraticChar F) (0 : F)=0 := by simp
    rw [hzchar] at hs
    rcases quadraticChar_dichotomy ha with hp | hn
    . exact hp
    . rw [hn] at hs
      linarith only [hq,hs,hlo,hz]
  . apply Or.inr
    rw [ite_eq_right hd] at hs
    have haLow := character_lower a
    have hdHigh := character_upper (b^2-4*a*c)
    have hfive : (Fintype.card F : Int)=5 := by
      linarith only [hq,hs,haLow,hdHigh,hlo,hz]
    have hminus : (quadraticChar F) a= -1 := by
      linarith only [hs,hfive,haLow,hdHigh,hlo,hz]
    have hdelta : (quadraticChar F) (b^2-4*a*c)=1 := by
      linarith only [hs,hfive,haLow,hdHigh,hlo,hz]
    have ht : (quadraticChar F) (a*t^2+b*t+c)= -1 := by
      linarith only [hs,hfive,haLow,hdHigh,hlo,hz]
    exact And.intro hfive (And.intro hminus (And.intro hdelta ht))

end FiniteField
