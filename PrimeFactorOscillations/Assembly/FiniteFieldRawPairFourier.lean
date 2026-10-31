/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerTail
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPolynomialPairs

/-!
# The original elliptic pair packet in additive Fourier coordinates

The Fourier transform of the actual monic-quadratic irreducibility count
factors into a quadratic phase sum and a twisted nonsquare-pair sum.
The discriminant substitution retains both forbidden constant terms and
every zero-discriminant correction. No trace-free averaging, prime-pair
supply, or incomplete integer mass estimate is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace PrimeFactorOscillations.FiniteFieldRawPairFourier
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def nonsquarePairIndicator (u h : F) : Complex :=
  if Not (IsSquare u) /\ Not (IsSquare (u-4*h)) then 1 else 0

def nonsquarePairTransform (psi : AddChar F Complex) (a h : F) : Complex :=
  Finset.univ.sum fun u : F => nonsquarePairIndicator u h*psi (a*u)

def quadraticPhase (psi : AddChar F Complex) (a : F) : Complex :=
  Finset.univ.sum fun b : F => psi (a*b^2)

def rawCountTransform (psi : AddChar F Complex) (a h : F) : Complex :=
  Finset.univ.sum fun c : F =>
    (_root_.FiniteField.monicQuadraticPairCount c h : Complex)*psi (-4*a*c)

theorem count_eq_discriminant_indicator
    (hF : Not (ringChar F=2)) (c h : F) :
    (_root_.FiniteField.monicQuadraticPairCount c h : Complex) =
      Finset.univ.sum (fun b : F => nonsquarePairIndicator (b^2-4*c) h) := by
  have he (b : F) : b^2-4*(c+h)=(b^2-4*c)-4*h := by ring
  simp only [_root_.FiniteField.monicQuadraticPairCount,Int.cast_sum,
    _root_.FiniteField.monicQuadratic_irreducible_iff_nonsquare hF,he,
    nonsquarePairIndicator]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> norm_num

theorem discriminant_column_transform
    (psi : AddChar F Complex) (a h b : F)
    (hfour : Not ((4 : F)=0)) :
    (Finset.univ.sum fun c : F =>
      nonsquarePairIndicator (b^2-4*c) h*psi (-4*a*c)) =
        psi ((-a)*b^2)*nonsquarePairTransform psi a h := by
  let e : Equiv F F :=
    { toFun := fun c => b^2-4*c
      invFun := fun u => (b^2-u)/4
      left_inv := by intro c; field_simp [hfour] <;> ring
      right_inv := by intro u; field_simp [hfour] <;> ring }
  calc
    _ = Finset.univ.sum (fun c : F =>
        nonsquarePairIndicator (e c) h*psi ((-a)*b^2+a*e c)) := by
      apply Finset.sum_congr rfl
      intro c _
      have he : -4*a*c=(-a)*b^2+a*(e c) := by
        change -4*a*c=(-a)*b^2+a*(b^2-4*c)
        ring
      rw [he]
      rfl
    _ = Finset.univ.sum (fun u : F =>
        nonsquarePairIndicator u h*psi ((-a)*b^2+a*u)) :=
      Equiv.sum_comp e (fun u : F =>
        nonsquarePairIndicator u h*psi ((-a)*b^2+a*u))
    _ = _ := by
      unfold nonsquarePairTransform
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [AddChar.map_add_eq_mul]
      ring

theorem raw_count_transform_factorization
    (hF : Not (ringChar F=2)) (psi : AddChar F Complex) (a h : F) :
    rawCountTransform psi a h =
      quadraticPhase psi (-a)*nonsquarePairTransform psi a h := by
  have htwo := _root_.FiniteField.two_ne_zero_of_odd hF
  have hfour : Not ((4 : F)=0) := by
    have he : (4 : F)=2^2 := by ring
    rw [he]
    exact pow_ne_zero 2 htwo
  unfold rawCountTransform
  simp_rw [count_eq_discriminant_indicator hF,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [discriminant_column_transform psi a h _ hfour]
  rw [<- Finset.sum_mul]
  rfl

def characterTransform (psi : AddChar F Complex) (a : F) : Complex :=
  Finset.univ.sum fun u : F => ((quadraticChar F) u : Complex)*psi (a*u)

def conicTransform (psi : AddChar F Complex) (a h : F) : Complex :=
  Finset.univ.sum fun u : F =>
    ((quadraticChar F) (u*(u-4*h)) : Complex)*psi (a*u)

def constantTransform (psi : AddChar F Complex) (a : F) : Complex :=
  Finset.univ.sum fun u : F => psi (a*u)

def boundaryTransform (psi : AddChar F Complex) (a h : F) : Complex :=
  (1-((quadraticChar F) (-4*h) : Complex))+
    (1-((quadraticChar F) (4*h) : Complex))*psi (4*a*h)

theorem shifted_character_transform
    (psi : AddChar F Complex) (a h : F) :
    (Finset.univ.sum fun u : F =>
      ((quadraticChar F) (u-4*h) : Complex)*psi (a*u)) =
        psi (4*a*h)*characterTransform psi a := by
  let e : Equiv F F := Equiv.addRight (4*h)
  calc
    _ = Finset.univ.sum (fun u : F =>
        ((quadraticChar F) (e u-4*h) : Complex)*psi (a*e u)) :=
      (Equiv.sum_comp e (fun u : F =>
        ((quadraticChar F) (u-4*h) : Complex)*psi (a*u))).symm
    _ = _ := by
      unfold characterTransform
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      change ((quadraticChar F) ((u+4*h)-4*h) : Complex)*psi (a*(u+4*h)) = _
      have he : a*(u+4*h)=4*a*h+a*u := by ring
      rw [add_sub_cancel_right,he,AddChar.map_add_eq_mul]
      ring

theorem nonsquare_pair_transform_expansion
    (psi : AddChar F Complex) (a h : F) (hfour : Not ((4 : F)=0))
    (hh : Not (h=0)) :
    4*nonsquarePairTransform psi a h =
      constantTransform psi a-
        (1+psi (4*a*h))*characterTransform psi a+
          conicTransform psi a h-boundaryTransform psi a h := by
  have ht : Not (4*h=0) := mul_ne_zero hfour hh
  have hj (u : F) : Not (u=0 /\ u-4*h=0) := by
    intro hu
    apply ht
    have he := sub_eq_zero.mp hu.2
    exact he.symm.trans hu.1
  have hi (u : F) :
      4*nonsquarePairIndicator u h =
        (1-((quadraticChar F) u : Complex))*
          (1-((quadraticChar F) (u-4*h) : Complex))-
        (if u=0 then 1-((quadraticChar F) (u-4*h) : Complex) else 0)-
        (if u-4*h=0 then 1-((quadraticChar F) u : Complex) else 0) := by
    have he := congrArg (fun z : Int => (z : Complex))
      (_root_.FiniteField.four_nonsquare_pair_indicator u (u-4*h))
    simpa only [Int.cast_mul,Int.cast_ofNat,Int.cast_sub,Int.cast_add,Int.cast_ite,
      Int.cast_one,Int.cast_zero,hj u,ite_false,add_zero,nonsquarePairIndicator] using he
  have hp (u : F) :
      4*nonsquarePairIndicator u h*psi (a*u) =
        psi (a*u)-((quadraticChar F) u : Complex)*psi (a*u)-
          ((quadraticChar F) (u-4*h) : Complex)*psi (a*u)+
            ((quadraticChar F) (u*(u-4*h)) : Complex)*psi (a*u)-
        (if u=0 then (1-((quadraticChar F) (u-4*h) : Complex))*psi (a*u) else 0)-
        (if u-4*h=0 then (1-((quadraticChar F) u : Complex))*psi (a*u) else 0) := by
    rw [hi]
    simp only [map_mul,Int.cast_mul]
    split_ifs <;> ring
  have hr0 :
      (Finset.univ.sum fun u : F =>
        if u=0 then (1-((quadraticChar F) (u-4*h) : Complex))*psi (a*u) else 0) =
          1-((quadraticChar F) (-4*h) : Complex) := by
    simp
  have hrt :
      (Finset.univ.sum fun u : F =>
        if u-4*h=0 then (1-((quadraticChar F) u : Complex))*psi (a*u) else 0) =
          (1-((quadraticChar F) (4*h) : Complex))*psi (4*a*h) := by
    simp only [sub_eq_zero]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    congr 2
    ring
  calc
    _ = Finset.univ.sum (fun u : F =>
        4*nonsquarePairIndicator u h*psi (a*u)) := by
      unfold nonsquarePairTransform
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = _ := by
      simp_rw [hp]
      simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
      rw [shifted_character_transform,hr0,hrt]
      unfold constantTransform characterTransform conicTransform boundaryTransform
      ring

theorem raw_count_transform_full_signed
    (hF : Not (ringChar F=2)) (psi : AddChar F Complex) (a h : F)
    (hh : Not (h=0)) :
    4*rawCountTransform psi a h =
      quadraticPhase psi (-a)*
        (constantTransform psi a-
          (1+psi (4*a*h))*characterTransform psi a+
            conicTransform psi a h-boundaryTransform psi a h) := by
  have htwo := _root_.FiniteField.two_ne_zero_of_odd hF
  have hfour : Not ((4 : F)=0) := by
    have he : (4 : F)=2^2 := by ring
    rw [he]
    exact pow_ne_zero 2 htwo
  rw [raw_count_transform_factorization hF]
  calc
    _ = quadraticPhase psi (-a)*(4*nonsquarePairTransform psi a h) := by ring
    _ = _ := by rw [nonsquare_pair_transform_expansion psi a h hfour hh]

end PrimeFactorOscillations.FiniteFieldRawPairFourier
