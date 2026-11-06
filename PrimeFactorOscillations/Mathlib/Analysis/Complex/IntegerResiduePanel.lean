/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Data.Nat.GCD.BigOperators
import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResiduePanelGeometry

/-!
# Exact spacing of finite compensated-residue panels

The target integer is shared, while every reference integer is retained.
The least common multiple amplifies the common resonance. Degree two is
included, with its exceptional nonresonant rows handled explicitly.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

def residuePanelPeriod (D : Finset Nat) : Nat := D.lcm id

def residuePanelRadius (D : Finset Nat) (hD : D.Nonempty) (z : Complex) : Real :=
  let K := D.max' hD
  min 1 ((residuePanelPeriod D : Real) * ((K : Real) - 1) /
    norm (z + (K : Complex) - 1))

def residuePanelNorm (D : Finset Nat) (hD : D.Nonempty) (z : Complex)
    (a : Int) (b : Nat -> Int) : Real :=
  D.sup' hD (fun d => norm (integerResidueCode d z a (b d)))

def residuePanelNonzero (D : Finset Nat) (a : Int) (b : Nat -> Int) : Prop :=
  Not (And (a = 0) (forall d : Nat, Membership.mem D d -> b d = 0))

theorem residuePanelPeriod_pos (D : Finset Nat)
    (hPow : forall d : Nat, Membership.mem D d -> 2 <= d) :
    0 < residuePanelPeriod D := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro d hd
  have h := hPow d hd
  exact ne_of_gt (lt_of_lt_of_le (by decide : 0 < (2 : Nat)) h)

theorem residuePanelPeriod_dvd_target (D : Finset Nat) (a : Int) (b : Nat -> Int)
    (hRes : forall d : Nat, Membership.mem D d -> (d : Int) * b d = a) :
    Dvd.dvd (residuePanelPeriod D : Int) a := by
  apply Int.natCast_dvd.mpr
  apply Finset.lcm_dvd
  intro d hd
  exact Int.natCast_dvd.mp (Exists.intro (b d) (hRes d hd).symm)

theorem residuePanelPeriod_le_abs (D : Finset Nat) (a : Int) (b : Nat -> Int)
    (ha : Not (a = 0))
    (hRes : forall d : Nat, Membership.mem D d -> (d : Int) * b d = a) :
    (residuePanelPeriod D : Real) <= abs (a : Real) := by
  choose q hq using residuePanelPeriod_dvd_target D a b hRes
  have hq0 : Not (q = 0) := by
    intro h
    rw [h, mul_zero] at hq
    exact ha hq
  have hi : (1 : Int) <= abs q := by
    rcases lt_or_gt_of_ne hq0 with hn | hp
    . rw [abs_of_neg hn]
      omega
    . rw [abs_of_pos hp]
      omega
  have hqr : (1 : Real) <= abs (q : Real) := by exact_mod_cast hi
  have he : (a : Real) = (residuePanelPeriod D : Real) * (q : Real) := by exact_mod_cast hq
  have hL0 : (0 : Real) <= residuePanelPeriod D := by positivity
  rw [he, abs_mul, abs_of_nonneg hL0]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hqr hL0

private theorem panel_unit_target_nonresonant (d : Nat) (hd : 2 <= d)
    (a b : Int) (hUnit : Or (a = 1) (a = -1)) : Not ((d : Int) * b - a = 0) := by
  intro h
  have hDiv : Dvd.dvd d a.natAbs :=
    Int.natCast_dvd.mp (Exists.intro b (sub_eq_zero.mp h).symm)
  have hAbs : a.natAbs = 1 := by
    rcases hUnit with hp | hn
    . simp [hp]
    . simp [hn]
  rw [hAbs] at hDiv
  have hLe := Nat.le_of_dvd (by decide : 0 < (1 : Nat)) hDiv
  omega

private theorem panel_spacing_witness (D : Finset Nat) (hD : D.Nonempty)
    (hPow : forall d : Nat, Membership.mem D d -> 2 <= d)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (a : Int) (b : Nat -> Int) (hab : residuePanelNonzero D a b) :
    Exists (fun d : Nat => And (Membership.mem D d)
      (residuePanelRadius D hD z <= norm (integerResidueCode d z a (b d)))) := by
  classical
  let K := D.max' hD
  have hK : Membership.mem D K := Finset.max'_mem D hD
  have hK2 : 2 <= K := hPow K hK
  by_cases hK3 : 3 <= K
  . by_cases hRes : forall d : Nat, Membership.mem D d -> (d : Int) * b d = a
    . have ha : Not (a = 0) := by
        intro ha
        apply hab
        refine And.intro ha ?_
        intro d hd
        have hr := hRes d hd
        rw [ha] at hr
        have hd0 : Not ((d : Int) = 0) := by
          have hd2 := hPow d hd
          omega
        exact (mul_eq_zero.mp hr).resolve_left hd0
      have hL := residuePanelPeriod_le_abs D a b ha hRes
      have hNorm := integerResidueCode_resonant_norm K hK2 z hH a (b K) (hRes K hK)
      have hKReal : (2 : Real) <= K := by exact_mod_cast hK2
      have hm := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hL (by linarith : 0 <= (K : Real) - 1))
        (norm_nonneg (z + (K : Complex) - 1))
      rw [<- hNorm] at hm
      exact Exists.intro K (And.intro hK ((min_le_right _ _).trans hm))
    . have hEx : Exists (fun d : Nat => And (Membership.mem D d)
          (Not ((d : Int) * b d = a))) := by
        by_contra hn
        apply hRes
        intro d hd
        by_contra he
        exact hn (Exists.intro d (And.intro hd he))
      choose d hdt using hEx
      have hd2 := hPow d hdt.1
      have hk : Not ((d : Int) * b d - a = 0) :=
        fun h => hdt.2 (sub_eq_zero.mp h)
      by_cases hd3 : 3 <= d
      . have hn := integerResidueCode_nonresonant_unit d hd3 z hRe hH a (b d) hk
        exact Exists.intro d (And.intro hdt.1 ((min_le_left _ _).trans hn))
      . have hdEq : d = 2 := by omega
        subst d
        by_cases hUnit : Or (a = 1) (a = -1)
        . have hkK := panel_unit_target_nonresonant K hK2 a (b K) hUnit
          have hn := integerResidueCode_nonresonant_unit K hK3 z hRe hH a (b K) hkK
          exact Exists.intro K (And.intro hK ((min_le_left _ _).trans hn))
        . have haPos : Not (a = 1) := fun h => hUnit (Or.inl h)
          have haNeg : Not (a = -1) := fun h => hUnit (Or.inr h)
          have hn := integerResidueCode_two_nonresonant_unit z hRe hH a (b 2) hk haPos haNeg
          exact Exists.intro 2 (And.intro hdt.1 ((min_le_left _ _).trans hn))
  . have hKTwo : K = 2 := by omega
    have hDs : D = {2} := by
      apply Finset.ext
      intro d
      constructor
      . intro hd
        have hlo := hPow d hd
        have hhi := Finset.le_max' D d hd
        change d <= K at hhi
        exact Finset.mem_singleton.mpr (by omega)
      . intro hd
        have he : d = 2 := Finset.mem_singleton.mp hd
        rw [he]
        simpa only [hKTwo] using hK
    subst D
    have hab2 : Not (And (a = 0) (b 2 = 0)) := by
      intro h
      apply hab
      refine And.intro h.1 ?_
      intro d hd
      have he : d = 2 := Finset.mem_singleton.mp hd
      simpa only [he] using h.2
    refine Exists.intro 2 (And.intro (Finset.mem_singleton_self 2) ?_)
    simpa [residuePanelRadius, residuePanelPeriod] using
      integerResidueCode_strip_separation 2 (by decide) z hRe hH a (b 2) hab2

theorem residuePanelNorm_separation (D : Finset Nat) (hD : D.Nonempty)
    (hPow : forall d : Nat, Membership.mem D d -> 2 <= d)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (a : Int) (b : Nat -> Int) (hab : residuePanelNonzero D a b) :
    residuePanelRadius D hD z <= residuePanelNorm D hD z a b := by
  choose d hdt using panel_spacing_witness D hD hPow z hRe hH a b hab
  exact hdt.2.trans (Finset.le_sup' (fun e => norm (integerResidueCode e z a (b e))) hdt.1)

theorem residuePanel_resonant_profile (D : Finset Nat)
    (hPow : forall d : Nat, Membership.mem D d -> 2 <= d)
    (z : Complex) (hH : 2 <= abs z.im) (d : Nat) (hd : Membership.mem D d) :
    norm (integerResidueCode d z (residuePanelPeriod D : Int)
      ((residuePanelPeriod D / d : Nat) : Int)) =
        (residuePanelPeriod D : Real) * ((d : Real) - 1) /
          norm (z + (d : Complex) - 1) := by
  have hdL : Dvd.dvd d (residuePanelPeriod D) := Finset.dvd_lcm hd
  have hm : d * (residuePanelPeriod D / d) = residuePanelPeriod D := Nat.mul_div_cancel' hdL
  have he : (d : Int) * ((residuePanelPeriod D / d : Nat) : Int) =
      (residuePanelPeriod D : Int) := by exact_mod_cast hm
  rw [integerResidueCode_resonant_norm d (hPow d hd) z hH _ _ he]
  simp

theorem residuePanelNorm_attains (D : Finset Nat) (hD : D.Nonempty)
    (hPow : forall d : Nat, Membership.mem D d -> 2 <= d)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im) :
    Exists (fun a : Int => Exists (fun b : Nat -> Int =>
      And (residuePanelNonzero D a b)
        (residuePanelNorm D hD z a b = residuePanelRadius D hD z))) := by
  classical
  let K := D.max' hD
  have hK : Membership.mem D K := Finset.max'_mem D hD
  have hK2 : 2 <= K := hPow K hK
  let S := (residuePanelPeriod D : Real) * ((K : Real) - 1) /
    norm (z + (K : Complex) - 1)
  by_cases hS : 1 <= S
  . refine Exists.intro 1 (Exists.intro (fun _ => 0) (And.intro ?_ ?_))
    . intro h
      norm_num at h
    . have hR : residuePanelRadius D hD z = 1 := min_eq_left hS
      rw [hR]
      apply le_antisymm
      . exact Finset.sup'_le hD _ (fun d _ => by simp [integerResidueCode])
      . have h := Finset.le_sup' (fun d => norm (integerResidueCode d z 1 0)) hK
        simpa [integerResidueCode, residuePanelNorm] using h
  . have hSL : S <= 1 := le_of_lt (lt_of_not_ge hS)
    have hR : residuePanelRadius D hD z = S := min_eq_right hSL
    refine Exists.intro (residuePanelPeriod D : Int)
      (Exists.intro (fun d => ((residuePanelPeriod D / d : Nat) : Int)) (And.intro ?_ ?_))
    . intro h
      have hL := residuePanelPeriod_pos D hPow
      have hLInt : (0 : Int) < residuePanelPeriod D := by exact_mod_cast hL
      exact (ne_of_gt hLInt) h.1
    . rw [hR]
      apply le_antisymm
      . apply Finset.sup'_le hD
        intro d hd
        rw [residuePanel_resonant_profile D hPow z hH d hd]
        have hm := residueReferenceFraction_mono d K (hPow d hd)
          (Finset.le_max' D d hd) z hRe.1 hH
        have hMul := mul_le_mul_of_nonneg_left hm
          (show (0 : Real) <= residuePanelPeriod D by positivity)
        simpa only [S, mul_div_assoc] using hMul
      . have h := Finset.le_sup'
          (fun d => norm (integerResidueCode d z (residuePanelPeriod D : Int)
            ((residuePanelPeriod D / d : Nat) : Int))) hK
        rw [residuePanel_resonant_profile D hPow z hH K hK] at h
        exact h

theorem residuePanel_unique (D : Finset Nat) (hD : D.Nonempty)
    (hPow : forall d : Nat, Membership.mem D d -> 2 <= d)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (a a' : Int) (b b' : Nat -> Int) (observation : Nat -> Complex)
    (hErr : forall d : Nat, Membership.mem D d ->
      norm (integerResidueCode d z a (b d) - observation d) +
        norm (integerResidueCode d z a' (b' d) - observation d) < residuePanelRadius D hD z) :
    And (a = a') (forall d : Nat, Membership.mem D d -> b d = b' d) := by
  classical
  by_contra hNe
  have hNZ : residuePanelNonzero D (a - a') (fun d => b d - b' d) := by
    intro h
    apply hNe
    refine And.intro (sub_eq_zero.mp h.1) ?_
    intro d hd
    exact sub_eq_zero.mp (h.2 d hd)
  choose d hdt using panel_spacing_witness D hD hPow z hRe hH (a - a')
    (fun d => b d - b' d) hNZ
  have hLow := hdt.2
  change residuePanelRadius D hD z <= norm (integerResidueCode d z (a - a') (b d - b' d)) at hLow
  rw [<- integerResidueCode_sub d z a (b d) a' (b' d)] at hLow
  have hTri := norm_sub_le (integerResidueCode d z a (b d) - observation d)
    (integerResidueCode d z a' (b' d) - observation d)
  have he : integerResidueCode d z a (b d) - observation d -
      (integerResidueCode d z a' (b' d) - observation d) =
      integerResidueCode d z a (b d) - integerResidueCode d z a' (b' d) := by ring
  rw [he] at hTri
  have hE := hErr d hdt.1
  linarith

private theorem panel_radius_den_pos (d : Nat) (z : Complex) (hH : 2 <= abs z.im) :
    0 < norm (z + (d : Complex) - 1) := by
  have h := Complex.abs_im_le_norm (z + (d : Complex) - 1)
  simp at h
  linarith

theorem residuePanelRadius_pos (D : Finset Nat) (hD : D.Nonempty)
    (hPow : forall d : Nat, Membership.mem D d -> 2 <= d)
    (z : Complex) (hH : 2 <= abs z.im) : 0 < residuePanelRadius D hD z := by
  let K := D.max' hD
  have hK : Membership.mem D K := Finset.max'_mem D hD
  have hK2 : (2 : Real) <= K := by exact_mod_cast hPow K hK
  have hL : (0 : Real) < residuePanelPeriod D := by exact_mod_cast residuePanelPeriod_pos D hPow
  have hDen := panel_radius_den_pos K z hH
  have hAmp : 0 < (residuePanelPeriod D : Real) * ((K : Real) - 1) /
      norm (z + (K : Complex) - 1) :=
    div_pos (mul_pos hL (by linarith)) hDen
  by_cases hOne : 1 <= (residuePanelPeriod D : Real) * ((K : Real) - 1) /
      norm (z + (K : Complex) - 1)
  . change 0 < min 1 _
    rw [min_eq_left hOne]
    norm_num
  . change 0 < min 1 _
    rw [min_eq_right (le_of_lt (lt_of_not_ge hOne))]
    exact hAmp

theorem residuePanel_unit_iff (D : Finset Nat) (hD : D.Nonempty)
    (hPow : forall d : Nat, Membership.mem D d -> 2 <= d)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im) :
    (forall a : Int, forall b : Nat -> Int, residuePanelNonzero D a b ->
      1 <= residuePanelNorm D hD z a b) <->
      norm (z + (D.max' hD : Complex) - 1) <=
        (residuePanelPeriod D : Real) * ((D.max' hD : Real) - 1) := by
  let K := D.max' hD
  let S := (residuePanelPeriod D : Real) * ((K : Real) - 1) /
    norm (z + (K : Complex) - 1)
  have hDen := panel_radius_den_pos K z hH
  have he : S * norm (z + (K : Complex) - 1) =
      (residuePanelPeriod D : Real) * ((K : Real) - 1) := by dsimp [S]; field_simp
  constructor
  . intro hUnit
    choose a b hab using residuePanelNorm_attains D hD hPow z hRe hH
    have hOne := hUnit a b hab.1
    rw [hab.2] at hOne
    have hRad : residuePanelRadius D hD z <= S := min_le_right 1 S
    have hm := mul_le_mul_of_nonneg_right (hOne.trans hRad) hDen.le
    simpa only [one_mul, he] using hm
  . intro hDisk a b hab
    have hRatio : 1 <= S :=
      le_of_mul_le_mul_right (by rw [one_mul, he]; exact hDisk) hDen
    have hRad : residuePanelRadius D hD z = 1 := min_eq_left hRatio
    simpa only [hRad] using residuePanelNorm_separation D hD hPow z hRe hH a b hab

theorem residuePanelRadius_three_four (z : Complex) :
    residuePanelRadius ({3, 4} : Finset Nat) (by simp) z =
      min 1 (36 / norm (z + 3)) := by
  have hK : ({3, 4} : Finset Nat).max' (by simp) = 4 := by decide
  have hL : residuePanelPeriod ({3, 4} : Finset Nat) = 12 := by decide
  simp only [residuePanelRadius, hK, hL]
  norm_num only [Nat.cast_ofNat]
  have he : z + (4 : Complex) - 1 = z + 3 := by ring
  rw [he]

theorem residuePanelNorm_three_four (z : Complex) (a : Int) (b : Nat -> Int) :
    residuePanelNorm ({3, 4} : Finset Nat) (by simp) z a b =
      max (norm (integerResidueCode 3 z a (b 3)))
        (norm (integerResidueCode 4 z a (b 4))) := by
  apply le_antisymm
  . apply Finset.sup'_le
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with he | he
    . subst d
      exact le_max_left _ _
    . subst d
      exact le_max_right _ _
  . exact max_le
      (Finset.le_sup' (fun d => norm (integerResidueCode d z a (b d))) (by simp))
      (Finset.le_sup' (fun d => norm (integerResidueCode d z a (b d))) (by simp))

theorem residuePanel_three_four_separation (z : Complex)
    (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (a : Int) (b : Nat -> Int) (hab : residuePanelNonzero {3, 4} a b) :
    min 1 (36 / norm (z + 3)) <=
      max (norm (integerResidueCode 3 z a (b 3)))
        (norm (integerResidueCode 4 z a (b 4))) := by
  have hPow : forall d : Nat, Membership.mem ({3, 4} : Finset Nat) d -> 2 <= d := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    omega
  have h := residuePanelNorm_separation {3, 4} (by simp) hPow z hRe hH a b hab
  rw [residuePanelRadius_three_four, residuePanelNorm_three_four] at h
  exact h

end Complex

end
