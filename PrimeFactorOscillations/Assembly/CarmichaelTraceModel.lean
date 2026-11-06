/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelTraceAtoms
import PrimeFactorOscillations.Assembly.CarmichaelTraceGrid

/-!
# Integer-weighted affine grid models with complete reference support

The reflected grid carries positive natural multiplicities proportional to
height. Both affine-reference supports and the joint strict-sign carrier are
classified exactly. Every full complex residue remains nonzero.
This is a finite-spectrum construction, not an arithmetic L-function model.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelTraceSharpness

open DirichletCompensatedProbe
open PrimeFactorOscillations.CarmichaelWeightedSignal

abbrev GridIndex (n : Nat) :=
  {t : Prod Bool (Prod Nat Nat) // Membership.mem (gridIndices n) t}

def modelPoint (d e n : Nat) (t : GridIndex n) : Complex :=
  gridPoint d e n t.val

def modelMultiplicity (d e n : Nat) (t : GridIndex n) : Nat :=
  e ^ (t.val.2.1 + t.val.2.2) * d ^ (n - t.val.2.1)

def modelReflection {n : Nat} (t : GridIndex n) : GridIndex n :=
  Subtype.mk (Prod.mk (Bool.not t.val.1) t.val.2)
    (by
      apply (mem_gridIndices n _).mpr
      exact (mem_gridIndices n t.val).mp t.property)

theorem modelPoint_injective (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (hcop : Nat.Coprime d e) : Function.Injective (modelPoint d e n) := by
  intro x y hxy
  apply Subtype.ext
  exact gridPoint_injective d e n hd hde hcop x.val y.val x.property y.property hxy

theorem modelPoint_im (d e n : Nat) (t : GridIndex n) :
    (modelPoint d e n t).im = gridHeight d e t.val.2.1 t.val.2.2 := by
  exact gridPoint_im d e n t.val

theorem modelPoint_im_pos (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (t : GridIndex n) : 0 < (modelPoint d e n t).im := by
  rw [modelPoint_im]
  exact gridHeight_pos d e _ _ (zero_lt_one.trans hd) (zero_lt_one.trans (hd.trans hde))

theorem modelPoint_strip (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (t : GridIndex n) : 0 < (modelPoint d e n t).re /\ (modelPoint d e n t).re < 1 := by
  exact gridPoint_strip d e n hd hde t.val t.property

theorem modelReflection_point (d e n : Nat) (t : GridIndex n) :
    modelPoint d e n (modelReflection t) = zeroReflection (modelPoint d e n t) := by
  apply Complex.ext
  all_goals
    cases h : t.val.1 <;>
      simp [modelPoint, modelReflection, gridPoint, h, gridRight, gridLeft, zeroReflection]

theorem modelReflection_involutive (n : Nat) (t : GridIndex n) :
    modelReflection (modelReflection t) = t := by
  apply Subtype.ext
  apply Prod.ext
  . simp [modelReflection]
  . rfl

theorem modelReflection_multiplicity (d e n : Nat) (t : GridIndex n) :
    modelMultiplicity d e n (modelReflection t) = modelMultiplicity d e n t := by
  rfl

theorem modelMultiplicity_pos (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (t : GridIndex n) : 0 < modelMultiplicity d e n t := by
  exact mul_pos (pow_pos (zero_lt_one.trans (hd.trans hde)) _)
    (pow_pos (zero_lt_one.trans hd) _)

theorem modelMultiplicity_eq_height (d e n : Nat) (hd : 1 < d)
    (t : GridIndex n) :
    (modelMultiplicity d e n t : Real) =
      (d : Real) ^ n * (modelPoint d e n t).im := by
  have hi := ((mem_gridIndices n t.val).mp t.property).1
  have hdR : Not ((d : Real) = 0) := by exact_mod_cast (Nat.ne_of_gt (zero_lt_one.trans hd))
  have hp : (d : Real) ^ (n - t.val.2.1) * (d : Real) ^ t.val.2.1 = (d : Real) ^ n := by
    rw [<- pow_add, Nat.sub_add_cancel hi]
  rw [modelPoint_im, gridHeight_formula]
  simp only [modelMultiplicity, Nat.cast_mul, Nat.cast_pow]
  calc
    (e : Real) ^ (t.val.2.1 + t.val.2.2) * (d : Real) ^ (n - t.val.2.1) =
        ((e : Real) ^ (t.val.2.1 + t.val.2.2) *
          ((d : Real) ^ (n - t.val.2.1) * (d : Real) ^ t.val.2.1)) /
            (d : Real) ^ t.val.2.1 := by
      field_simp [hdR]
    _ = (d : Real) ^ n *
        ((e : Real) ^ (t.val.2.1 + t.val.2.2) / (d : Real) ^ t.val.2.1) := by
      rw [hp]
      ring

theorem modelOrder_at (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (hcop : Nat.Coprime d e) (t : GridIndex n) :
    atomicOrder (modelPoint d e n) (modelMultiplicity d e n) (modelPoint d e n t) =
      modelMultiplicity d e n t := by
  exact atomicOrder_at _ _ (modelPoint_injective d e n hd hde hcop) t

theorem model_den_ne (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (t : GridIndex n) (a : Real) :
    Not (modelPoint d e n t + (a : Complex) - 1 = 0) := by
  intro h
  have hi : (modelPoint d e n t).im = 0 := by
    simpa using congrArg Complex.im h
  exact (ne_of_gt (modelPoint_im_pos d e n hd hde t)) hi

theorem model_reference_balanced (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (hcop : Nat.Coprime d e) (t u : GridIndex n) (a : Real) (ha : 0 < a)
    (hPoint : modelPoint d e n u = powerMap a (modelPoint d e n t)) :
    a * (atomicOrder (modelPoint d e n) (modelMultiplicity d e n)
      (powerMap a (modelPoint d e n t)) : Real) =
        (modelMultiplicity d e n t : Real) := by
  rw [<- hPoint, modelOrder_at d e n hd hde hcop u]
  have hIm := powerMap_im_identity a ha (modelPoint d e n t)
  rw [<- hPoint] at hIm
  calc
    a * (modelMultiplicity d e n u : Real) =
        (d : Real) ^ n * ((modelPoint d e n u).im * a) := by
      rw [modelMultiplicity_eq_height d e n hd u]
      ring
    _ = (d : Real) ^ n * (modelPoint d e n t).im := by rw [hIm]
    _ = (modelMultiplicity d e n t : Real) := (modelMultiplicity_eq_height d e n hd t).symm

def modelProjection (d e n : Nat) (a : Real) (t : GridIndex n) : Real :=
  (atomicPowerResidue (modelPoint d e n) (modelMultiplicity d e n) a
    (modelPoint d e n t) * (modelPoint d e n t + (a : Complex) - 1)).im

theorem modelProjection_eq (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (hcop : Nat.Coprime d e) (t : GridIndex n) (a : Real) (ha : 0 < a) :
    modelProjection d e n a t =
      if Exists (fun u : GridIndex n =>
        modelPoint d e n u = powerMap a (modelPoint d e n t))
      then 0 else -(modelMultiplicity d e n t : Real) * (modelPoint d e n t).im := by
  classical
  unfold modelProjection
  rw [atomicPower_projection _ _ a _ (model_den_ne d e n hd hde t a),
    modelOrder_at d e n hd hde hcop t]
  by_cases h : Exists (fun u : GridIndex n =>
      modelPoint d e n u = powerMap a (modelPoint d e n t))
  . rw [if_pos h]
    choose u hu using h
    rw [model_reference_balanced d e n hd hde hcop t u a ha hu, sub_self, zero_mul]
  . rw [if_neg h, atomicOrder_zero _ _ _ (not_exists.mp h)]
    simp

theorem modelProjection_neg_iff (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (hcop : Nat.Coprime d e) (t : GridIndex n) (a : Real) (ha : 0 < a) :
    modelProjection d e n a t < 0 <->
      Not (Exists (fun u : GridIndex n =>
        modelPoint d e n u = powerMap a (modelPoint d e n t))) := by
  classical
  rw [modelProjection_eq d e n hd hde hcop t a ha]
  have hm : (0 : Real) < (modelMultiplicity d e n t : Real) := by
    exact_mod_cast modelMultiplicity_pos d e n hd hde t
  have hp := mul_pos hm (modelPoint_im_pos d e n hd hde t)
  by_cases h : Exists (fun u : GridIndex n =>
      modelPoint d e n u = powerMap a (modelPoint d e n t)) <;> simp [h, hp]

theorem model_full_residue_ne_zero (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (hcop : Nat.Coprime d e) (t : GridIndex n) (a : Real) (ha : 1 < a) :
    Not (atomicPowerResidue (modelPoint d e n) (modelMultiplicity d e n)
      a (modelPoint d e n t) = 0) := by
  apply atomicPowerResidue_ne_zero _ _ a ha _ (ne_of_gt (modelPoint_im_pos d e n hd hde t))
    (model_den_ne d e n hd hde t a)
  rw [modelOrder_at d e n hd hde hcop t]
  exact modelMultiplicity_pos d e n hd hde t


theorem modelReference_right (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (t u : GridIndex n) (a : Real) (ha : 2 <= a)
    (h : modelPoint d e n u = powerMap a (modelPoint d e n t)) :
    t.val.1 = true /\ u.val.1 = true := by
  have ht := (mem_gridIndices n t.val).mp t.property
  have hT : t.val.1 = true := by
    cases hs : t.val.1
    . have hNo := powerMap_gridLeft_ne_point d e n t.val.2.1 t.val.2.2
        hd hde ht.1 ht.2 a ha u.val
      apply False.elim
      apply hNo
      simpa [modelPoint, gridPoint, hs] using h.symm
    . rfl
  refine And.intro hT ?_
  cases hs : u.val.1
  . have hNo := powerMap_gridRight_ne_left d e n t.val.2.1 t.val.2.2
      u.val.2.1 u.val.2.2 hd hde ht.1 ht.2 a ha
    apply False.elim
    apply hNo
    simpa [modelPoint, gridPoint, hT, hs] using h.symm
  . rfl

theorem modelReference_e_iff (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (hcop : Nat.Coprime d e) (t : GridIndex n) :
    Exists (fun u : GridIndex n =>
      modelPoint d e n u = powerMap (e : Real) (modelPoint d e n t)) <->
        t.val.1 = true /\ 0 < t.val.2.2 := by
  have he : 1 < e := hd.trans hde
  have heR : (2 : Real) <= (e : Real) := by exact_mod_cast (show 2 <= e by omega)
  have ht := (mem_gridIndices n t.val).mp t.property
  constructor
  . intro h
    choose u hu using h
    have hr := modelReference_right d e n hd hde t u (e : Real) heR hu
    have hp : powerMap (e : Real) (gridRight d e n t.val.2.1 t.val.2.2) =
        gridRight d e n u.val.2.1 u.val.2.2 := by
      simpa [modelPoint, gridPoint, hr.1, hr.2] using hu.symm
    have hi := (powerMap_gridRight_e_iff d e n _ _ _ _ hd he hcop).mp hp
    exact And.intro hr.1 (by omega)
  . intro h
    let u : GridIndex n := Subtype.mk
      (Prod.mk true (Prod.mk t.val.2.1 (t.val.2.2 - 1)))
      (by
        apply (mem_gridIndices n _).mpr
        exact And.intro ht.1 ((Nat.sub_le _ _).trans ht.2))
    refine Exists.intro u ?_
    have hp : powerMap (e : Real) (gridRight d e n t.val.2.1 t.val.2.2) =
        gridRight d e n t.val.2.1 (t.val.2.2 - 1) :=
      (powerMap_gridRight_e_iff d e n _ _ _ _ hd he hcop).mpr
        (And.intro rfl (by omega))
    simpa [modelPoint, gridPoint, u, h.1] using hp.symm

theorem modelReference_d_iff (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (hcop : Nat.Coprime d e) (t : GridIndex n) :
    Exists (fun u : GridIndex n =>
      modelPoint d e n u = powerMap (d : Real) (modelPoint d e n t)) <->
        t.val.1 = true /\ t.val.2.1 < n /\ 0 < t.val.2.2 := by
  have he : 1 < e := hd.trans hde
  have hdR : (2 : Real) <= (d : Real) := by exact_mod_cast (show 2 <= d by omega)
  have ht := (mem_gridIndices n t.val).mp t.property
  constructor
  . intro h
    choose u hu using h
    have hr := modelReference_right d e n hd hde t u (d : Real) hdR hu
    have hp : powerMap (d : Real) (gridRight d e n t.val.2.1 t.val.2.2) =
        gridRight d e n u.val.2.1 u.val.2.2 := by
      simpa [modelPoint, gridPoint, hr.1, hr.2] using hu.symm
    have hi := (powerMap_gridRight_d_iff d e n _ _ _ _ hd he hcop).mp hp
    have huI := (mem_gridIndices n u.val).mp u.property
    exact And.intro hr.1 (And.intro (by omega) (by omega))
  . intro h
    let u : GridIndex n := Subtype.mk
      (Prod.mk true (Prod.mk (t.val.2.1 + 1) (t.val.2.2 - 1)))
      (by
        apply (mem_gridIndices n _).mpr
        change t.val.2.1 + 1 <= n /\ t.val.2.2 - 1 <= n
        exact And.intro (by omega) ((Nat.sub_le _ _).trans ht.2))
    refine Exists.intro u ?_
    have hp : powerMap (d : Real) (gridRight d e n t.val.2.1 t.val.2.2) =
        gridRight d e n (t.val.2.1 + 1) (t.val.2.2 - 1) :=
      (powerMap_gridRight_d_iff d e n _ _ _ _ hd he hcop).mpr
        (And.intro rfl (by omega))
    simpa [modelPoint, gridPoint, u, h.1] using hp.symm

theorem model_joint_carrier_iff (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (hcop : Nat.Coprime d e) (t : GridIndex n) :
    (modelProjection d e n (d : Real) t < 0 \/ modelProjection d e n (e : Real) t < 0) <->
      Not (t.val.1 = true /\ t.val.2.1 < n /\ 0 < t.val.2.2) := by
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast (zero_lt_one.trans hd)
  have heR : (0 : Real) < (e : Real) := by exact_mod_cast (zero_lt_one.trans (hd.trans hde))
  rw [modelProjection_neg_iff d e n hd hde hcop t (d : Real) hdR,
    modelProjection_neg_iff d e n hd hde hcop t (e : Real) heR,
    modelReference_d_iff d e n hd hde hcop t,
    modelReference_e_iff d e n hd hde hcop t]
  constructor
  . intro h hi
    apply Or.elim h
    . intro hD
      exact hD hi
    . intro hE
      exact hE (And.intro hi.1 hi.2.2)
  . intro h
    exact Or.inl h

end PrimeFactorOscillations.CarmichaelTraceSharpness
