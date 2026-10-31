/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldRawPairKloosterman
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.QuadraticPhase

/-!
# Nonzero frequencies of the original elliptic pair packet

The quadratic and linear Gauss factors multiply to the field size.
The full nonzero-frequency formula therefore keeps a signed residue
exclusion term coupled to a Gauss-Kloosterman term and both boundary
corrections. The Kloosterman argument is exactly a square. These are
identities, not an estimate for the coupled incomplete integer sum.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace PrimeFactorOscillations.FiniteFieldRawPairFourier
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem addchar_shift_ne_one
    (psi : AddChar F Complex) (hpsi : Not (psi=1))
    (a : F) (ha : Not (a=0)) :
    Not (psi.mulShift a=1) := by
  intro he
  apply hpsi
  ext x
  have hx := congrArg (fun p : AddChar F Complex => p (x/a)) he
  have heq : a*(x/a)=x := by field_simp [ha]
  simpa [AddChar.mulShift_apply,heq] using hx

theorem quadratic_linear_phase_product
    (hF : Not (ringChar F=2)) (psi : AddChar F Complex)
    (hpsi : Not (psi=1)) (a : F) (ha : Not (a=0)) :
    quadraticPhase psi (-a)*characterTransform psi a=(Fintype.card F : Complex) := by
  let chi : MulChar F Complex :=
    (quadraticChar F).ringHomComp (Int.castRingHom Complex)
  have hchi : Not (chi=1) :=
    (MulChar.ringHomComp_ne_one_iff (Int.cast_injective)).mpr
      (quadraticChar_ne_one hF)
  have hquad : MulChar.IsQuadratic chi :=
    (quadraticChar_isQuadratic F).comp (Int.castRingHom Complex)
  have hInv : Inv.inv chi=chi := hquad.inv
  have hshift := addchar_shift_ne_one psi hpsi a ha
  have hneg := addchar_shift_ne_one psi hpsi (-a) (neg_ne_zero.mpr ha)
  have hphase : quadraticPhase psi (-a)=gaussSum chi (psi.mulShift (-a)) := by
    exact MulChar.sum_quadraticPhase_eq_gaussSum hF (psi.mulShift (-a)) hneg
  have hinvpsi : Inv.inv (psi.mulShift a)=psi.mulShift (-a) := by
    ext x
    simp only [AddChar.inv_apply,AddChar.mulShift_apply,neg_mul,mul_neg]
  have hg := gaussSum_mul_gaussSum_eq_card hchi
    (AddChar.IsPrimitive.of_ne_one hshift)
  rw [hInv,hinvpsi] at hg
  rw [hphase,mul_comm]
  exact hg

theorem kloosterman_square_argument
    (hF : Not (ringChar F=2)) (psi : AddChar F Complex)
    (a h : F) (ha : Not (a=0)) :
    kloostermanPhase psi (a/2) (2*a*h^2)=
      kloostermanPhase psi 1 (a^2*h^2) := by
  have htwo := _root_.FiniteField.two_ne_zero_of_odd hF
  have hA : Not (a/2=0) := div_ne_zero ha htwo
  let v : Units F := Units.mk0 (a/2) hA
  let e : Equiv (Units F) (Units F) := Equiv.mulLeft v
  calc
    _ = Finset.univ.sum (fun t : Units F =>
        psi ((e t : F)+(a^2*h^2)/(e t : F))) := by
      unfold kloostermanPhase
      apply Finset.sum_congr rfl
      intro t _
      apply congrArg psi
      change (a/2)*(t : F)+(2*a*h^2)/(t : F)=
        (a/2)*(t : F)+(a^2*h^2)/((a/2)*(t : F))
      field_simp [ha,htwo,Units.ne_zero t] <;> ring
    _ = _ := by
      simpa only [kloostermanPhase,one_mul] using
        Equiv.sum_comp e (fun t : Units F =>
          psi ((t : F)+(a^2*h^2)/(t : F)))

theorem raw_count_transform_nonzero
    (hF : Not (ringChar F=2)) (psi : AddChar F Complex)
    (hpsi : Not (psi=1)) (a h : F) (ha : Not (a=0))
    (hh : Not (h=0)) :
    4*rawCountTransform psi a h =
      quadraticPhase psi (-a)*psi (2*a*h)*kloostermanPhase psi 1 (a^2*h^2)-
        (Fintype.card F : Complex)*(1+psi (4*a*h))-
          quadraticPhase psi (-a)*boundaryTransform psi a h := by
  rw [raw_count_transform_kloosterman hF psi a h hh,
    kloosterman_square_argument hF psi a h ha]
  have hg := quadratic_linear_phase_product hF psi hpsi a ha
  calc
    _ = quadraticPhase psi (-a)*psi (2*a*h)*kloostermanPhase psi 1 (a^2*h^2)-
        (1+psi (4*a*h))*(quadraticPhase psi (-a)*characterTransform psi a)-
          quadraticPhase psi (-a)*boundaryTransform psi a h := by ring
    _ = _ := by rw [hg]; ring

def rawNormalization (h : F) : Complex :=
  (Fintype.card F : Complex)-3+
    ((quadraticChar F) h : Complex)+((quadraticChar F) (-h) : Complex)

def rawNormalizedWeight (c h : F) : Complex :=
  4*(_root_.FiniteField.monicQuadraticPairCount c h : Complex)/rawNormalization h

def rawFourierCoeff (psi : AddChar F Complex) (a h : F) : Complex :=
  (1/(Fintype.card F : Complex))*
    (Finset.univ.sum fun c : F => rawNormalizedWeight c h*psi (-4*a*c))

theorem raw_fourier_count_transport (psi : AddChar F Complex) (a h : F) :
    rawFourierCoeff psi a h =
      (4*rawCountTransform psi a h)/
        ((Fintype.card F : Complex)*rawNormalization h) := by
  have hs :
      (Finset.univ.sum fun c : F => rawNormalizedWeight c h*psi (-4*a*c)) =
        (4/rawNormalization h)*rawCountTransform psi a h := by
    unfold rawNormalizedWeight rawCountTransform
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  unfold rawFourierCoeff
  rw [hs]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem raw_normalization_ne_zero (h : F) (hh : Not (h=0))
    (hq : 7<=Fintype.card F) : Not (rawNormalization h=0) := by
  have he := quadraticChar_sq_one hh
  have hf := quadraticChar_sq_one (neg_ne_zero.mpr hh)
  have he0 : (-1 : Int)<=(quadraticChar F) h := by nlinarith only [he]
  have hf0 : (-1 : Int)<=(quadraticChar F) (-h) := by nlinarith only [hf]
  have hqi : (7 : Int)<=(Fintype.card F : Int) := by exact_mod_cast hq
  have hp : (0 : Int)<(Fintype.card F : Int)-3+
      (quadraticChar F) h+(quadraticChar F) (-h) := by omega
  intro hz
  apply ne_of_gt hp
  unfold rawNormalization at hz
  exact_mod_cast hz

theorem raw_fourier_zero (hF : Not (ringChar F=2))
    (psi : AddChar F Complex) (h : F) (hh : Not (h=0))
    (hq : 7<=Fintype.card F) :
    rawFourierCoeff psi 0 h=1 := by
  have he := congrArg (fun z : Int => (z : Complex))
    (_root_.FiniteField.sum_monicQuadraticPairCount_eq hF h hh)
  have hc : 4*rawCountTransform psi 0 h =
      (Fintype.card F : Complex)*rawNormalization h := by
    unfold rawCountTransform rawNormalization
    simp only [mul_zero,zero_mul,neg_zero,AddChar.map_zero_eq_one,mul_one]
    simpa only [Int.cast_mul,Int.cast_ofNat,Int.cast_sum,Int.cast_natCast,
      Int.cast_add,Int.cast_sub] using he
  have hcard : Not ((Fintype.card F : Complex)=0) := by
    exact_mod_cast Fintype.card_ne_zero
  rw [raw_fourier_count_transport,hc]
  exact div_self (mul_ne_zero hcard (raw_normalization_ne_zero h hh hq))

theorem raw_fourier_nonzero (hF : Not (ringChar F=2))
    (psi : AddChar F Complex) (hpsi : Not (psi=1)) (a h : F)
    (ha : Not (a=0)) (hh : Not (h=0)) (hq : 7<=Fintype.card F) :
    rawFourierCoeff psi a h =
      -(1+psi (4*a*h))/rawNormalization h+
        (quadraticPhase psi (-a)/
          ((Fintype.card F : Complex)*rawNormalization h))*
            (psi (2*a*h)*kloostermanPhase psi 1 (a^2*h^2)-
              boundaryTransform psi a h) := by
  have hcard : Not ((Fintype.card F : Complex)=0) := by
    exact_mod_cast Fintype.card_ne_zero
  have hd := raw_normalization_ne_zero h hh hq
  rw [raw_fourier_count_transport,raw_count_transform_nonzero hF psi hpsi a h ha hh]
  field_simp [hcard,hd]
  <;> ring

end PrimeFactorOscillations.FiniteFieldRawPairFourier
