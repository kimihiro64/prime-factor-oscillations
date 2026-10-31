/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldRawPairFourier

/-!
# The conic and Kloosterman terms of the original pair packet

The conic character transform is evaluated by a complete parametrization
of its affine points by nonzero field elements. Its constant transform is
retained, including zero frequency. Substitution in the original pair
count keeps the quadratic phase, residue exclusions and both boundary
compensations in one exact expression. No incomplete mass bound is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace PrimeFactorOscillations.FiniteFieldRawPairFourier
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev ConicPoint (h : F) :=
  Subtype (fun z : Prod F F => z.2^2=z.1*(z.1-4*h))

theorem conic_product (h : F) (p : ConicPoint h) :
    (p.val.1-2*h+p.val.2)*(p.val.1-2*h-p.val.2)=4*h^2 := by
  calc
    _ = p.val.1*(p.val.1-4*h)-p.val.2^2+4*h^2 := by ring
    _ = _ := by rw [p.property]; ring

def conicToUnit (h : F) (htwo : Not ((2 : F)=0)) (hh : Not (h=0))
    (p : ConicPoint h) : Units F :=
  Units.mk0 (p.val.1-2*h+p.val.2) (by
    intro hz
    have hd := conic_product h p
    rw [hz,zero_mul] at hd
    have hfour : Not ((4 : F)=0) := by
      rw [show (4 : F)=2^2 by ring]
      exact pow_ne_zero 2 htwo
    exact mul_ne_zero hfour (pow_ne_zero 2 hh) hd.symm)

def conicFromUnit (h : F) (htwo : Not ((2 : F)=0)) (t : Units F) :
    ConicPoint h :=
  Subtype.mk
    (2*h+((t : F)+4*h^2/(t : F))/2,
      ((t : F)-4*h^2/(t : F))/2)
    (by
      change (((t : F)-4*h^2/(t : F))/2)^2=
        (2*h+((t : F)+4*h^2/(t : F))/2)*
          ((2*h+((t : F)+4*h^2/(t : F))/2)-4*h)
      field_simp [htwo,Units.ne_zero t]
      ring)

def conicEquivUnits (h : F) (htwo : Not ((2 : F)=0)) (hh : Not (h=0)) :
    Equiv (ConicPoint h) (Units F) :=
  { toFun := conicToUnit h htwo hh
    invFun := conicFromUnit h htwo
    left_inv := by
      intro p
      let t : F := p.val.1-2*h+p.val.2
      have ht : Not (t=0) := Units.ne_zero (conicToUnit h htwo hh p)
      have hd : 4*h^2/t=p.val.1-2*h-p.val.2 := by
        apply (div_eq_iff ht).mpr
        dsimp only [t]
        calc
          _ = (p.val.1-2*h+p.val.2)*(p.val.1-2*h-p.val.2) :=
            (conic_product h p).symm
          _ = _ := mul_comm _ _
      apply Subtype.ext
      apply Prod.ext
      . change 2*h+(t+4*h^2/t)/2=p.val.1
        rw [hd]
        dsimp only [t]
        field_simp [htwo]
        ring
      . change (t-4*h^2/t)/2=p.val.2
        rw [hd]
        dsimp only [t]
        field_simp [htwo]
        ring
    right_inv := by
      intro t
      apply Units.ext
      change
        (2*h+((t : F)+4*h^2/(t : F))/2)-2*h+
          ((t : F)-4*h^2/(t : F))/2=(t : F)
      field_simp [htwo,Units.ne_zero t]
      ring }

theorem conic_sum_fiber
    (hF : Not (ringChar F=2)) (psi : AddChar F Complex) (a h : F) :
    (Finset.univ.sum fun p : ConicPoint h => psi (a*p.val.1)) =
      conicTransform psi a h+constantTransform psi a := by
  have hb :
      (Finset.univ.sum fun p : ConicPoint h => psi (a*p.val.1)) =
      ((Finset.univ : Finset (Prod F F)).filter
        (fun z => z.2^2=z.1*(z.1-4*h))).sum (fun z => psi (a*z.1)) := by
    refine Finset.sum_bij (fun p _ => p.val) ?_ ?_ ?_ ?_
    . intro p _
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) p.property)
    . intro p _ q _ hpq
      exact Subtype.ext hpq
    . intro z hz
      exact Exists.intro (Subtype.mk z (Finset.mem_filter.mp hz).2)
        (Exists.intro (Finset.mem_univ _) rfl)
    . intro p _
      rfl
  have hr (u : F) :
      (Finset.univ.sum fun y : F =>
        if y^2=u*(u-4*h) then psi (a*u) else 0) =
          (((quadraticChar F) (u*(u-4*h)) : Complex)+1)*psi (a*u) := by
    rw [<- Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    have hc := congrArg (fun z : Int => (z : Complex))
      (quadraticChar_card_sqrts hF (u*(u-4*h)))
    simpa only [Int.cast_natCast,Int.cast_add,Int.cast_one,Set.toFinset_ofPred]
      using congrArg (fun z : Complex => z*psi (a*u)) hc
  rw [hb,Finset.sum_filter,Fintype.sum_prod_type]
  simp_rw [hr,add_mul,one_mul]
  rw [Finset.sum_add_distrib]
  rfl

def kloostermanPhase (psi : AddChar F Complex) (A B : F) : Complex :=
  Finset.univ.sum fun t : Units F => psi (A*(t : F)+B/(t : F))

theorem conic_transform_kloosterman
    (hF : Not (ringChar F=2)) (psi : AddChar F Complex) (a h : F)
    (hh : Not (h=0)) :
    conicTransform psi a h+constantTransform psi a =
      psi (2*a*h)*kloostermanPhase psi (a/2) (2*a*h^2) := by
  have htwo := _root_.FiniteField.two_ne_zero_of_odd hF
  let e := conicEquivUnits h htwo hh
  rw [<- conic_sum_fiber hF]
  calc
    _ = Finset.univ.sum (fun t : Units F =>
        psi (a*(conicFromUnit h htwo t).val.1)) :=
      (Equiv.sum_comp e.symm (fun p : ConicPoint h => psi (a*p.val.1))).symm
    _ = _ := by
      unfold kloostermanPhase
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      change psi (a*(2*h+((t : F)+4*h^2/(t : F))/2))=_
      have he : a*(2*h+((t : F)+4*h^2/(t : F))/2)=
          2*a*h+((a/2)*(t : F)+(2*a*h^2)/(t : F)) := by
        field_simp [htwo,Units.ne_zero t]
        ring
      rw [he,AddChar.map_add_eq_mul]

theorem raw_count_transform_kloosterman
    (hF : Not (ringChar F=2)) (psi : AddChar F Complex) (a h : F)
    (hh : Not (h=0)) :
    4*rawCountTransform psi a h =
      quadraticPhase psi (-a)*
        (psi (2*a*h)*kloostermanPhase psi (a/2) (2*a*h^2)-
          (1+psi (4*a*h))*characterTransform psi a-
            boundaryTransform psi a h) := by
  rw [raw_count_transform_full_signed hF psi a h hh]
  rw [<- conic_transform_kloosterman hF psi a h hh]
  ring

end PrimeFactorOscillations.FiniteFieldRawPairFourier
