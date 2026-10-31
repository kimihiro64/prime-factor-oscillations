/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistLikelihood

/-!
# Shared-endpoint overlap of exact local prime-pair masks

The same mask is used in both slots. Nonzero gaps in odd characteristic
exclude three distinct residues. Zero gaps retain one forbidden residue.
The field of three elements is the exact shared-endpoint obstruction.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticPairTwistLikelihood
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
theorem mask_nonneg (c h : F) : 0<=admissibilityMask c h := by
  unfold admissibilityMask
  split_ifs <;> norm_num

theorem mask_adjacent_indicator (hF : Not (ringChar F=2)) (c h : F) (hh : Not (h=0)) :
    admissibilityMask c h*admissibilityMask (c+h) h=
      1-(if c=0 then 1 else 0)-(if c=-h then 1 else 0)-
        (if c=-(h+h) then 1 else 0) := by
  have h2 : Not (h+h=0) := by
    rw [show h+h=(2 : F)*h from by ring]
    exact mul_ne_zero (two_ne_zero_of_odd hF) hh
  have hn : Not ((0 : F)=-h) := fun he => hh (neg_eq_zero.mp he.symm)
  have hn2 : Not ((0 : F)=-(h+h)) := fun he => h2 (neg_eq_zero.mp he.symm)
  have hdist : Not (-h=-(h+h)) := by
    intro he
    have he' : h=h+h := neg_injective he
    have hz : 0=h := add_left_cancel (show h+0=h+h from by simpa using he')
    exact hh hz.symm
  have e0 : (c+h=0)=(c=-h) := propext
    (by constructor
        . exact eq_neg_of_add_eq_zero_left
        . intro he; rw [he]; ring)
  have e1 : (c+h=-h)=(c=-(h+h)) := propext (by
    constructor
    . intro he
      calc
        c=(c+h)-h := by ring
        _= -h-h := by rw [he]
        _= -(h+h) := by ring
    . intro he; rw [he]; ring)
  simp only [admissibilityMask,e0,e1]
  by_cases h0 : c=0 <;> by_cases h1 : c=-h <;> by_cases h3 : c=-(h+h) <;>
    simp_all

theorem sum_mask_adjacent (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0)) :
    (Finset.univ.sum fun c : F => admissibilityMask c h*admissibilityMask (c+h) h)=
      (Fintype.card F : Real)-3 := by
  simp_rw [mask_adjacent_indicator hF _ h hh]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  simp; ring

theorem sum_mask_zero :
    (Finset.univ.sum fun c : F => admissibilityMask c (0 : F))=
      (Fintype.card F : Real)-1 := by
  have he (c : F) : admissibilityMask c (0 : F)=1-(if c=0 then 1 else 0) := by
    unfold admissibilityMask
    by_cases hc : c=0 <;> simp [hc]
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  simp

def maskDiagonalMoment (h : F) : Real :=
  (Fintype.card F : Real)*(Finset.univ.sum fun c : F => (admissibilityMask c h)^2)/
    (Finset.univ.sum fun c : F => admissibilityMask c h)^2

def maskSharedMoment (h : F) : Real :=
  (Fintype.card F : Real)*
    (Finset.univ.sum fun c : F => admissibilityMask c h*admissibilityMask (c+h) h)/
    (Finset.univ.sum fun c : F => admissibilityMask c h)^2

theorem maskMoments_zero (hq : 2<=(Fintype.card F : Real)) :
    And (maskDiagonalMoment (0 : F)=(Fintype.card F : Real)/((Fintype.card F : Real)-1))
      (maskSharedMoment (0 : F)=(Fintype.card F : Real)/((Fintype.card F : Real)-1)) := by
  have h1 : Not ((Fintype.card F : Real)-1=0) := ne_of_gt (by linarith only [hq])
  have hd : maskDiagonalMoment (0 : F)=
      (Fintype.card F : Real)/((Fintype.card F : Real)-1) := by
    unfold maskDiagonalMoment
    simp_rw [mask_square]
    rw [sum_mask_zero]
    field_simp [h1]
  refine And.intro hd ?_
  unfold maskSharedMoment
  simp_rw [add_zero,<- pow_two,mask_square]
  rw [sum_mask_zero]
  field_simp [h1]

theorem maskMoments_nonzero (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (hq : 3<=(Fintype.card F : Real)) :
    And (maskDiagonalMoment h=(Fintype.card F : Real)/((Fintype.card F : Real)-2))
      (maskSharedMoment h=(Fintype.card F : Real)*((Fintype.card F : Real)-3)/
        ((Fintype.card F : Real)-2)^2) := by
  have h2 : Not ((Fintype.card F : Real)-2=0) := ne_of_gt (by linarith only [hq])
  constructor
  . unfold maskDiagonalMoment
    simp_rw [mask_square]
    rw [sum_mask h hh]
    field_simp [h2]
  . unfold maskSharedMoment
    rw [sum_mask_adjacent hF h hh,sum_mask h hh]

theorem maskSharedMoment_card_three (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : Fintype.card F=3) : maskSharedMoment h=0 := by
  rw [(maskMoments_nonzero hF h hh (by rw [hq]; norm_num)).2,hq]
  norm_num

theorem mask_adjacent_vanish_card_three (hF : Not (ringChar F=2))
    (c h : F) (hh : Not (h=0)) (hq : Fintype.card F=3) :
    admissibilityMask c h*admissibilityMask (c+h) h=0 := by
  have hsum := sum_mask_adjacent hF h hh
  rw [hq] at hsum
  norm_num only [Nat.cast_ofNat,sub_self] at hsum
  have hle := Finset.single_le_sum
    (fun (x : F) (_ : Membership.mem Finset.univ x) =>
      mul_nonneg (mask_nonneg x h) (mask_nonneg (x+h) h))
    (Finset.mem_univ c)
  rw [hsum] at hle
  exact le_antisymm hle (mul_nonneg (mask_nonneg c h) (mask_nonneg (c+h) h))

theorem maskMoments_compatible (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) :
    And (1<=maskSharedMoment h) (maskSharedMoment h<=maskDiagonalMoment h) := by
  let q : Real := Fintype.card F
  have h2 : 0<q-2 := by dsimp only [q]; linarith only [hq]
  have he := maskMoments_nonzero hF h hh (by linarith only [hq])
  rw [he.1,he.2]
  change And (1<=q*(q-3)/(q-2)^2) (q*(q-3)/(q-2)^2<=q/(q-2))
  have elo : q*(q-3)/(q-2)^2-1=(q-4)/(q-2)^2 := by
    field_simp [ne_of_gt h2]; ring
  have eup : q/(q-2)-q*(q-3)/(q-2)^2=q/(q-2)^2 := by
    field_simp [ne_of_gt h2]; ring
  have hp : 0<=(q-4)/(q-2)^2 := div_nonneg
    (by dsimp only [q]; linarith only [hq]) (sq_nonneg _)
  have hr : 0<=q/(q-2)^2 := div_nonneg (by dsimp only [q]; positivity) (sq_nonneg _)
  rw [<- elo] at hp
  rw [<- eup] at hr
  exact And.intro (by linarith only [hp]) (by linarith only [hr])

end FiniteField.QuadraticPairTwistLikelihood
