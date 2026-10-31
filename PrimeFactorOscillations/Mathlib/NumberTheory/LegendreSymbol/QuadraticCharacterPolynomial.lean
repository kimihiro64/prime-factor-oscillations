/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairMoments

/-!
# Character sums and zero counts for quadratic polynomials

The discriminant formulas include the repeated-root case. These classical
identities feed the two-anchor low-degree square-transport classification.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem quadraticChar_affine_sum (hF : Not (ringChar F=2))
    (a b : F) (ha : Not (a=0)) :
    (Finset.univ.sum fun x : F => (quadraticChar F) (a*x+b))=0 := by
  let e : Equiv F F :=
    { toFun := fun x => a*x+b
      invFun := fun y => (y-b)/a
      left_inv := by intro x; field_simp [ha]; ring
      right_inv := by intro y; field_simp [ha]; ring }
  calc
    _ = Finset.univ.sum (quadraticChar F) := Equiv.sum_comp e _
    _ = 0 := quadraticChar_sum_zero hF

theorem affine_zero_indicator_sum (a b : F) (ha : Not (a=0)) :
    (Finset.univ.sum fun x : F => if a*x+b=0 then (1 : Int) else 0)=1 := by
  let e : Equiv F F :=
    { toFun := fun x => a*x+b
      invFun := fun y => (y-b)/a
      left_inv := by intro x; field_simp [ha]; ring
      right_inv := by intro y; field_simp [ha]; ring }
  calc
    _ = Finset.univ.sum (fun y : F => if y=0 then (1 : Int) else 0) :=
      Equiv.sum_comp e _
    _ = 1 := by simp

theorem quadraticChar_quadratic_sum (hF : Not (ringChar F=2))
    (a b c : F) (ha : Not (a=0)) :
    (Finset.univ.sum fun x : F => (quadraticChar F) (a*x^2+b*x+c))=
      if b^2-4*a*c=0 then (quadraticChar F) a*((Fintype.card F : Int)-1)
      else -(quadraticChar F) a := by
  have htwo := two_ne_zero_of_odd hF
  have hscale : Not (2*a=0) := mul_ne_zero htwo ha
  let e : Equiv F F :=
    { toFun := fun x => 2*a*x+b
      invFun := fun y => (y-b)/(2*a)
      left_inv := by intro x; field_simp [hscale]; ring
      right_inv := by intro y; field_simp [hscale]; ring }
  have hp (x : F) :
      (quadraticChar F) (a*x^2+b*x+c)=
        (quadraticChar F) a*(quadraticChar F) ((e x)^2-(b^2-4*a*c)) := by
    have he : (2*a)^2*(a*x^2+b*x+c)=a*((e x)^2-(b^2-4*a*c)) := by
      change (2*a)^2*(a*x^2+b*x+c)=a*((2*a*x+b)^2-(b^2-4*a*c))
      ring
    have ht := congrArg (fun z : F => (quadraticChar F) z) he
    have hsq : (quadraticChar F) ((2*a)^2)=1 := by
      rw [map_pow,quadraticChar_sq_one hscale]
    rw [map_mul,hsq,one_mul,map_mul] at ht
    exact ht
  have hs :
      (Finset.univ.sum fun x : F => (quadraticChar F) (a*x^2+b*x+c))=
        (quadraticChar F) a*
          (Finset.univ.sum fun y : F => (quadraticChar F) (y^2-(b^2-4*a*c))) := by
    simp_rw [hp]
    rw [<- Finset.mul_sum]
    exact congrArg (fun z : Int => (quadraticChar F) a*z)
      (Equiv.sum_comp e (fun y : F => (quadraticChar F) (y^2-(b^2-4*a*c))))
  rw [hs]
  by_cases hd : b^2-4*a*c=0
  . rw [ite_eq_left hd,hd]
    simp only [sub_zero,map_pow,quadraticChar_translate_square_sum hF]
  . rw [ite_eq_right hd,quadraticChar_sum_square_sub hF _ hd]
    ring

theorem quadratic_zero_indicator_sum (hF : Not (ringChar F=2))
    (a b c : F) (ha : Not (a=0)) :
    (Finset.univ.sum fun x : F => if a*x^2+b*x+c=0 then (1 : Int) else 0)=
      1+(quadraticChar F) (b^2-4*a*c) := by
  have htwo := two_ne_zero_of_odd hF
  have hscale : Not (2*a=0) := mul_ne_zero htwo ha
  let e : Equiv F F :=
    { toFun := fun x => 2*a*x+b
      invFun := fun y => (y-b)/(2*a)
      left_inv := by intro x; field_simp [hscale]; ring
      right_inv := by intro y; field_simp [hscale]; ring }
  have hp (x : F) : a*x^2+b*x+c=0 <-> (e x)^2=b^2-4*a*c := by
    have he : (2*a)^2*(a*x^2+b*x+c)=a*((e x)^2-(b^2-4*a*c)) := by
      change (2*a)^2*(a*x^2+b*x+c)=a*((2*a*x+b)^2-(b^2-4*a*c))
      ring
    constructor
    . intro hz
      rw [hz,mul_zero] at he
      have ht : (e x)^2-(b^2-4*a*c)=0 :=
        (mul_eq_zero.mp he.symm).resolve_left ha
      exact sub_eq_zero.mp ht
    . intro hz
      rw [hz,sub_self,mul_zero] at he
      exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hscale)
  have hs :
      (Finset.univ.sum fun x : F => if a*x^2+b*x+c=0 then (1 : Int) else 0)=
        Finset.univ.sum (fun y : F => if y^2=b^2-4*a*c then (1 : Int) else 0) := by
    calc
      _ = Finset.univ.sum (fun x : F =>
          if (e x)^2=b^2-4*a*c then (1 : Int) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hz : a*x^2+b*x+c=0
        . rw [ite_eq_left hz,ite_eq_left ((hp x).mp hz)]
        . rw [ite_eq_right hz,ite_eq_right (fun ht => hz ((hp x).mpr ht))]
      _ = _ := Equiv.sum_comp e
        (fun y : F => if y^2=b^2-4*a*c then (1 : Int) else 0)
  rw [hs]
  have ht := quadraticChar_card_sqrts hF (b^2-4*a*c)
  rw [<- Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  have hf : (Finset.univ.filter fun y : F => y^2=b^2-4*a*c)=
      Set.toFinset {y : F | y^2=b^2-4*a*c} := by
    ext y
    simp
  rw [hf]
  simpa only [add_comm] using ht

end FiniteField
