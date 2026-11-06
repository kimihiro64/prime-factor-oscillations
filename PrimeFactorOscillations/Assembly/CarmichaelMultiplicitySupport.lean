/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelMultiplicityCarrier

/-!
# Reflection budgets retaining multiplicity support

The charged weight is real and may vanish. It is not a new positive-natural
multiplicity spectrum. Both half charges, including fixed reflection points,
remain in the symmetric weight.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

open DirichletCompensatedProbe CarmichaelWeightedSignal

variable {I : Type*} {sigma : Real}

def repeatedUnitAt (S : ReflectedSpectrum I sigma) (i : I) : Real :=
  if 2 <= S.mult i then S.unitMass i else 0

def multiplicitySupportCost (S : ReflectedSpectrum I sigma) (i : I) : Real :=
  if 2 <= S.mult i then S.mass i else 0

theorem repeatedUnitAt_nonneg (S : ReflectedSpectrum I sigma) (i : I) :
    0 <= S.repeatedUnitAt i := by
  unfold repeatedUnitAt
  split_ifs
  . exact S.unitMass_nonneg i
  . exact le_refl 0

theorem repeatedUnitAt_le_unitMass (S : ReflectedSpectrum I sigma) (i : I) :
    S.repeatedUnitAt i <= S.unitMass i := by
  unfold repeatedUnitAt
  split_ifs
  . exact le_refl _
  . exact S.unitMass_nonneg i

theorem multiplicitySupportCost_eq (S : ReflectedSpectrum I sigma) (i : I) :
    S.multiplicitySupportCost i = S.excessMassAt i + S.repeatedUnitAt i := by
  by_cases h : 2 <= S.mult i
  . simp only [multiplicitySupportCost, repeatedUnitAt, if_pos h]
    rw [S.mass_eq_unit_add_excess i]
    ring
  . have hm : S.mult i = 1 := by
      have hp := S.mult_pos i
      omega
    simp [multiplicitySupportCost, repeatedUnitAt, h, excessMassAt, hm]

theorem multiplicitySupportCost_nonneg (S : ReflectedSpectrum I sigma) (i : I) :
    0 <= S.multiplicitySupportCost i := by
  unfold multiplicitySupportCost
  split_ifs
  . exact S.mass_nonneg i
  . exact le_refl 0

theorem multiplicitySupportCost_le_mass (S : ReflectedSpectrum I sigma) (i : I) :
    S.multiplicitySupportCost i <= S.mass i := by
  unfold multiplicitySupportCost
  split_ifs
  . exact le_refl _
  . exact S.mass_nonneg i

theorem multiplicitySupportCost_le_twice_excess
    (S : ReflectedSpectrum I sigma) (i : I) :
    S.multiplicitySupportCost i <= 2 * S.excessMassAt i := by
  by_cases h : 2 <= S.mult i
  . have hm : (2 : Real) <= (S.mult i : Real) := by exact_mod_cast h
    have hu : S.unitMass i <= S.excessMassAt i := by
      unfold unitMass excessMassAt
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith
    rw [S.multiplicitySupportCost_eq i]
    simp only [repeatedUnitAt, if_pos h]
    linarith
  . simp only [multiplicitySupportCost, if_neg h]
    exact mul_nonneg (by norm_num) (S.excessMassAt_nonneg i)

theorem multiplicitySupportCost_mirror (S : ReflectedSpectrum I sigma) (i : I) :
    S.multiplicitySupportCost (S.mirror i) = S.multiplicitySupportCost i := by
  simp only [multiplicitySupportCost, S.mult_mirror i, S.mass_mirror i]

variable [Fintype I]

def weakRepeatedUnitMass (S : ReflectedSpectrum I sigma) : Real :=
  S.weakIndices.sum S.repeatedUnitAt

def multiplicitySupportCharge (S : ReflectedSpectrum I sigma) (i : I) : Real := by
  classical
  exact if Membership.mem S.weakIndices i then S.multiplicitySupportCost i / 2 else 0

def multiplicitySupportWeight (S : ReflectedSpectrum I sigma) (i : I) : Real :=
  S.mass i - S.multiplicitySupportCharge i -
    S.multiplicitySupportCharge (S.mirror i)

theorem weakRepeatedUnitMass_nonneg (S : ReflectedSpectrum I sigma) :
    0 <= S.weakRepeatedUnitMass :=
  Finset.sum_nonneg (fun i _ => S.repeatedUnitAt_nonneg i)

theorem weakRepeatedUnitMass_le_unit (S : ReflectedSpectrum I sigma) :
    S.weakRepeatedUnitMass <= S.weakUnitMass :=
  Finset.sum_le_sum (fun i _ => S.repeatedUnitAt_le_unitMass i)

theorem multiplicitySupportCharge_le (S : ReflectedSpectrum I sigma) (i : I) :
    S.multiplicitySupportCharge i <= S.multiplicitySupportCost i / 2 := by
  classical
  unfold multiplicitySupportCharge
  split_ifs
  . exact le_refl _
  . exact div_nonneg (S.multiplicitySupportCost_nonneg i) (by norm_num)

theorem multiplicitySupportWeight_nonneg (S : ReflectedSpectrum I sigma) (i : I) :
    0 <= S.multiplicitySupportWeight i := by
  have hi := S.multiplicitySupportCharge_le i
  have hj := S.multiplicitySupportCharge_le (S.mirror i)
  have hc := S.multiplicitySupportCost_le_mass i
  rw [S.multiplicitySupportCost_mirror i] at hj
  unfold multiplicitySupportWeight
  linarith

theorem multiplicitySupportWeight_mirror (S : ReflectedSpectrum I sigma) (i : I) :
    S.multiplicitySupportWeight (S.mirror i) = S.multiplicitySupportWeight i := by
  simp only [multiplicitySupportWeight, S.mass_mirror i, S.mirror_involutive i]
  ring

theorem reflected_right_weight_le (S : ReflectedSpectrum I (7 / 8))
    (f : I -> Real) (hNonneg : forall i, 0 <= f i)
    (hMirror : forall i, f (S.mirror i) = f i)
    (B : Finset I) (hRight : forall i, Membership.mem B i -> 1 / 2 < (S.point i).re) :
    2 * B.sum f <= Finset.univ.sum f := by
  classical
  have hDisjoint : Disjoint B (B.image S.mirror) := by
    apply Finset.disjoint_left.mpr
    intro k hk hm
    choose j hj he using Finset.mem_image.mp hm
    have hK := hRight k hk
    have hJ := hRight j hj
    have hPoint := S.point_mirror j
    rw [he] at hPoint
    have hRe := congrArg Complex.re hPoint
    rw [zeroReflection_re] at hRe
    linarith
  have hImage : (B.image S.mirror).sum f = B.sum f := by
    rw [Finset.sum_image (fun i _ j _ h => S.mirror_injective h)]
    apply Finset.sum_congr rfl
    intro i hi
    exact hMirror i
  have hSum := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (Union.union B (B.image S.mirror)))
    (fun i _ _ => hNonneg i)
  rw [Finset.sum_union hDisjoint, hImage] at hSum
  linarith

theorem multiplicitySupportWeight_right (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hRight : 1 / 2 < (S.point i).re) :
    S.unitMass i <= S.multiplicitySupportWeight i := by
  classical
  have hNot : Not (Membership.mem S.weakIndices i) := by
    intro hi
    exact (not_lt_of_ge (S.weak_re_le_half i hi)) hRight
  have hCharge : S.multiplicitySupportCharge i = 0 := by
    simp only [multiplicitySupportCharge, if_neg hNot]
  have hj := S.multiplicitySupportCharge_le (S.mirror i)
  rw [S.multiplicitySupportCost_mirror i] at hj
  have hc := S.multiplicitySupportCost_le_twice_excess i
  have hm := S.mass_eq_unit_add_excess i
  unfold multiplicitySupportWeight
  rw [hCharge]
  linarith

theorem sum_multiplicitySupportCharge (S : ReflectedSpectrum I sigma) :
    Finset.univ.sum S.multiplicitySupportCharge =
      (S.weakExcessMass + S.weakRepeatedUnitMass) / 2 := by
  classical
  calc
    Finset.univ.sum S.multiplicitySupportCharge =
        S.weakIndices.sum S.multiplicitySupportCharge := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i hi hn
      simp only [multiplicitySupportCharge, if_neg hn]
    _ = S.weakIndices.sum (fun i => S.multiplicitySupportCost i / 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [multiplicitySupportCharge, if_pos hi]
    _ = (S.weakExcessMass + S.weakRepeatedUnitMass) / 2 := by
      simp_rw [S.multiplicitySupportCost_eq]
      rw [<- Finset.sum_div, Finset.sum_add_distrib]
      rfl

theorem sum_multiplicitySupportWeight (S : ReflectedSpectrum I sigma) :
    Finset.univ.sum S.multiplicitySupportWeight =
      S.totalMass - S.weakExcessMass - S.weakRepeatedUnitMass := by
  classical
  have hUniv : Finset.univ.image S.mirror = (Finset.univ : Finset I) := by
    apply Finset.ext
    intro i
    constructor
    . intro hi
      exact Finset.mem_univ i
    . intro hi
      exact Finset.mem_image.mpr (Exists.intro (S.mirror i)
        (And.intro (Finset.mem_univ _) (S.mirror_involutive i)))
  have hPerm : Finset.univ.sum (fun i => S.multiplicitySupportCharge (S.mirror i)) =
      Finset.univ.sum S.multiplicitySupportCharge := by
    calc
      _ = (Finset.univ.image S.mirror).sum S.multiplicitySupportCharge := by
        rw [Finset.sum_image (fun i _ j _ h => S.mirror_injective h)]
      _ = _ := by rw [hUniv]
  change Finset.univ.sum (fun i => S.mass i - S.multiplicitySupportCharge i -
    S.multiplicitySupportCharge (S.mirror i)) = _
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hPerm,
    S.sum_multiplicitySupportCharge]
  unfold totalMass
  ring

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum
