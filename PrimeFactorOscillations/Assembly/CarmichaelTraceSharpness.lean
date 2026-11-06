/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelTraceModel
import PrimeFactorOscillations.Helpers.CarmichaelTraceRatios

/-!
# Sharp joint sign carriers for coprime affine powers

The integer-weighted reflected grid has an exact total mass and common
zero-projection mass. Its joint carrier ratio approaches 1-1/(2*e)
with a uniform geometric error, while all full compensated residues survive.
The matching actual-zeta union bound reuses the larger power's proved bound.
No Euler-product realization, upper multiplicity bound or QRH gain is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelTraceSharpness

open DirichletCompensatedProbe
open PrimeFactorOscillations.CarmichaelWeightedSignal

def modelAtomMass (d e n : Nat) (t : GridIndex n) : Real :=
  (modelMultiplicity d e n t : Real) / (modelPoint d e n t).im ^ 2

def modelTotalMass (d e n : Nat) : Real :=
  Finset.univ.sum (modelAtomMass d e n)

def modelWeakMass (d e n : Nat) : Real := by
  classical
  exact Finset.univ.sum (fun t : GridIndex n =>
    if t.val.1 = true /\ t.val.2.1 < n /\ 0 < t.val.2.2 then modelAtomMass d e n t else 0)

def modelJointCarrierMass (d e n : Nat) : Real := by
  classical
  exact Finset.univ.sum (fun t : GridIndex n =>
    if modelProjection d e n (d : Real) t < 0 \/ modelProjection d e n (e : Real) t < 0
    then modelAtomMass d e n t else 0)

theorem modelAtomMass_eq (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (t : GridIndex n) :
    modelAtomMass d e n t =
      (d : Real) ^ n * ((d : Real) / (e : Real)) ^ t.val.2.1 *
        (1 / (e : Real)) ^ t.val.2.2 := by
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast (zero_lt_one.trans hd)
  have heR : (0 : Real) < (e : Real) := by exact_mod_cast (zero_lt_one.trans (hd.trans hde))
  have hHeight := modelPoint_im_pos d e n hd hde t
  unfold modelAtomMass
  calc
    (modelMultiplicity d e n t : Real) / (modelPoint d e n t).im ^ 2 =
        (d : Real) ^ n / (modelPoint d e n t).im := by
      rw [modelMultiplicity_eq_height d e n hd t]
      field_simp [hHeight.ne']
      <;> ring
    _ = (d : Real) ^ n * ((d : Real) / (e : Real)) ^ t.val.2.1 *
        (1 / (e : Real)) ^ t.val.2.2 := by
      rw [modelPoint_im]
      simp only [gridHeight, div_pow, one_div_pow]
      field_simp [hdR.ne', heR.ne']
      <;> ring

private theorem grid_sum_product (n : Nat)
    (f : Prod Bool (Prod Nat Nat) -> Real) :
    (gridIndices n).sum f =
      Finset.univ.sum (fun b : Bool =>
        (Finset.range (n + 1)).sum (fun i =>
          (Finset.range (n + 1)).sum (fun j => f (Prod.mk b (Prod.mk i j))))) := by
  unfold gridIndices
  have hOuter :
      ((Finset.univ : Finset Bool).product
        ((Finset.range (n + 1)).product (Finset.range (n + 1)))).sum f =
      Finset.univ.sum (fun b : Bool =>
        ((Finset.range (n + 1)).product (Finset.range (n + 1))).sum
          (fun p => f (Prod.mk b p))) := by
    simpa only [SProd.sprod, Finset.instSProd] using
      Finset.sum_product (Finset.univ : Finset Bool)
        ((Finset.range (n + 1)).product (Finset.range (n + 1))) f
  rw [hOuter]
  apply Finset.sum_congr rfl
  intro b hb
  simpa only [SProd.sprod, Finset.instSProd] using
    Finset.sum_product (Finset.range (n + 1)) (Finset.range (n + 1))
      (fun p => f (Prod.mk b p))

theorem modelTotalMass_eq (d e n : Nat) (hd : 1 < d) (hde : d < e) :
    modelTotalMass d e n =
      2 * (d : Real) ^ n * geomBlock ((d : Real) / (e : Real)) n *
        geomBlock (1 / (e : Real)) n := by
  classical
  let D : Real := (d : Real) ^ n
  let a : Real := (d : Real) / (e : Real)
  let b : Real := 1 / (e : Real)
  have hRect :
      (Finset.range (n + 1)).sum (fun i =>
        (Finset.range (n + 1)).sum (fun j => D * a ^ i * b ^ j)) =
          D * geomBlock a n * geomBlock b n := by
    simp only [geomBlock, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  unfold modelTotalMass
  simp_rw [modelAtomMass_eq d e n hd hde]
  rw [Finset.sum_coe_sort (gridIndices n)
    (fun t => D * a ^ t.2.1 * b ^ t.2.2)]
  rw [grid_sum_product n (fun t => D * a ^ t.2.1 * b ^ t.2.2)]
  simp only [Fintype.sum_bool]
  change
    (Finset.range (n + 1)).sum (fun i =>
      (Finset.range (n + 1)).sum (fun j => D * a ^ i * b ^ j)) +
    (Finset.range (n + 1)).sum (fun i =>
      (Finset.range (n + 1)).sum (fun j => D * a ^ i * b ^ j)) =
        2 * D * geomBlock a n * geomBlock b n
  simp only [hRect]
  ring

private theorem positive_row_sum (b : Real) (n : Nat) :
    (Finset.range (n + 1)).sum (fun j => if 0 < j then b ^ j else 0) =
      geomBlock b n - 1 := by
  have hTerm (j : Nat) :
      (if 0 < j then b ^ j else 0) = b ^ j - (if j = 0 then 1 else 0) := by
    cases j <;> simp
  simp_rw [hTerm]
  rw [Finset.sum_sub_distrib]
  simp [geomBlock]

private theorem strict_column_sum (D a : Real) (n : Nat) :
    (Finset.range (n + 1)).sum (fun i => if i < n then D * a ^ i else 0) =
      D * (Finset.range n).sum (fun i => a ^ i) := by
  rw [Finset.sum_range_succ]
  have hSum : (Finset.range n).sum (fun i => if i < n then D * a ^ i else 0) =
      (Finset.range n).sum (fun i => D * a ^ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi)]
  rw [hSum]
  simp [Finset.mul_sum]

theorem modelWeakMass_eq (d e n : Nat) (hd : 1 < d) (hde : d < e) :
    modelWeakMass d e n =
      (d : Real) ^ n * (Finset.range n).sum (fun i => ((d : Real) / (e : Real)) ^ i) *
        (geomBlock (1 / (e : Real)) n - 1) := by
  classical
  let D : Real := (d : Real) ^ n
  let a : Real := (d : Real) / (e : Real)
  let b : Real := 1 / (e : Real)
  have hSplit (i j : Nat) :
      (if i < n /\ 0 < j then D * a ^ i * b ^ j else 0) =
        (if i < n then D * a ^ i else 0) * (if 0 < j then b ^ j else 0) := by
    by_cases hi : i < n <;> by_cases hj : 0 < j <;> simp [hi, hj]
  have hRect :
      (Finset.range (n + 1)).sum (fun i =>
        (Finset.range (n + 1)).sum (fun j =>
          if i < n /\ 0 < j then D * a ^ i * b ^ j else 0)) =
            D * (Finset.range n).sum (fun i => a ^ i) * (geomBlock b n - 1) := by
    simp_rw [hSplit, <- Finset.mul_sum]
    rw [<- Finset.sum_mul, strict_column_sum, positive_row_sum]
  unfold modelWeakMass
  simp_rw [modelAtomMass_eq d e n hd hde]
  rw [Finset.sum_coe_sort (gridIndices n)
    (fun t => if t.1 = true /\ t.2.1 < n /\ 0 < t.2.2
      then D * a ^ t.2.1 * b ^ t.2.2 else 0)]
  simpa [D, a, b, gridIndices, Finset.sum_product, Fintype.sum_bool] using hRect

theorem model_carrier_add_weak (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (hcop : Nat.Coprime d e) :
    modelJointCarrierMass d e n + modelWeakMass d e n = modelTotalMass d e n := by
  classical
  unfold modelJointCarrierMass modelWeakMass modelTotalMass
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hCarrier := model_joint_carrier_iff d e n hd hde hcop t
  by_cases h : t.val.1 = true /\ t.val.2.1 < n /\ 0 < t.val.2.2
  . have hn : Not (modelProjection d e n (d : Real) t < 0 \/
        modelProjection d e n (e : Real) t < 0) := by
      intro hc
      exact (hCarrier.mp hc) h
    simp [h, hn]
  . have hc := hCarrier.mpr h
    simp [h, hc]

private theorem model_bases (d e : Nat) (hd : 1 < d) (hde : d < e) :
    0 <= (d : Real) / (e : Real) /\ 0 <= 1 / (e : Real) /\
      1 / (e : Real) <= (d : Real) / (e : Real) /\ (d : Real) / (e : Real) < 1 := by
  have hdR : (1 : Real) < (d : Real) := by exact_mod_cast hd
  have heR : (d : Real) < (e : Real) := by exact_mod_cast hde
  have hePos : (0 : Real) < (e : Real) := by linarith
  refine And.intro (div_nonneg (by linarith) hePos.le)
    (And.intro (one_div_nonneg.mpr hePos.le) (And.intro ?_ ?_))
  . have hp : 0 <= ((d : Real) - 1) / (e : Real) := div_nonneg (by linarith) hePos.le
    have heq : (d : Real) / (e : Real) - 1 / (e : Real) =
        ((d : Real) - 1) / (e : Real) := by ring
    linarith
  . have hp : 0 < ((e : Real) - (d : Real)) / (e : Real) :=
      div_pos (sub_pos.mpr heR) hePos
    have heq : 1 - (d : Real) / (e : Real) =
        ((e : Real) - (d : Real)) / (e : Real) := by
      field_simp [hePos.ne']
      <;> ring
    linarith

theorem modelTotalMass_pos (d e n : Nat) (hd : 1 < d) (hde : d < e) :
    0 < modelTotalMass d e n := by
  rw [modelTotalMass_eq d e n hd hde]
  have hb := model_bases d e hd hde
  have haG : 0 < geomBlock ((d : Real) / (e : Real)) n :=
    lt_of_lt_of_le (by norm_num) (geomBlock_ge_one _ hb.1 n)
  have hbG : 0 < geomBlock (1 / (e : Real)) n :=
    lt_of_lt_of_le (by norm_num) (geomBlock_ge_one _ hb.2.1 n)
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast (zero_lt_one.trans hd)
  exact mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hdR n)) haG) hbG


theorem model_carrier_ratio_eq (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (hcop : Nat.Coprime d e) :
    modelJointCarrierMass d e n / modelTotalMass d e n =
      rectangularCarrierRatio ((d : Real) / (e : Real)) (1 / (e : Real)) n := by
  have hb := model_bases d e hd hde
  have hGa : 0 < geomBlock ((d : Real) / (e : Real)) n :=
    lt_of_lt_of_le (by norm_num) (geomBlock_ge_one _ hb.1 n)
  have hGb : 0 < geomBlock (1 / (e : Real)) n :=
    lt_of_lt_of_le (by norm_num) (geomBlock_ge_one _ hb.2.1 n)
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast (zero_lt_one.trans hd)
  have hC : modelJointCarrierMass d e n = modelTotalMass d e n - modelWeakMass d e n := by
    linarith only [model_carrier_add_weak d e n hd hde hcop]
  rw [hC]
  simp only [rectangularCarrierRatio, modelTotalMass_eq d e n hd hde,
    modelWeakMass_eq d e n hd hde]
  field_simp [hdR.ne', hGa.ne', hGb.ne']
  <;> ring

theorem model_carrier_ratio_gap_bounds (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (hcop : Nat.Coprime d e) :
    0 <= modelJointCarrierMass d e n / modelTotalMass d e n - (1 - 1 / (2 * (e : Real))) /\
      modelJointCarrierMass d e n / modelTotalMass d e n - (1 - 1 / (2 * (e : Real))) <=
        (1 / (e : Real)) * ((d : Real) / (e : Real)) ^ n := by
  have hb := model_bases d e hd hde
  have h := rectangularCarrierRatio_gap_bounds ((d : Real) / (e : Real))
    (1 / (e : Real)) n hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
  have hCenter : (1 / (e : Real)) / 2 = 1 / (2 * (e : Real)) := by
    rw [div_div, mul_comm (e : Real) 2]
  rw [model_carrier_ratio_eq d e n hd hde hcop]
  simpa only [hCenter] using h

theorem coprime_power_carrier_sharpness (d e : Nat) (hd : 1 < d) (hde : d < e)
    (hcop : Nat.Coprime d e) (epsilon : Real) (hepsilon : 0 < epsilon) :
    exists n : Nat, 0 < modelTotalMass d e n /\
      modelJointCarrierMass d e n / modelTotalMass d e n <
        1 - 1 / (2 * (e : Real)) + epsilon /\
      (forall (t : GridIndex n) (a : Real), 1 < a ->
        Filter.Tendsto
          (fun s => (s - modelPoint d e n t) *
            affinePowerReadout (atomicReadout (modelPoint d e n) (modelMultiplicity d e n)) a s)
          (nhdsWithin (modelPoint d e n t) (Set.compl {modelPoint d e n t}))
          (nhds (atomicPowerResidue (modelPoint d e n) (modelMultiplicity d e n)
            a (modelPoint d e n t))) /\
        Not (atomicPowerResidue (modelPoint d e n) (modelMultiplicity d e n)
          a (modelPoint d e n t) = 0)) := by
  have hb := model_bases d e hd hde
  choose n hn using rectangularCarrierRatio_near_limit
    ((d : Real) / (e : Real)) (1 / (e : Real))
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 epsilon hepsilon
  have hCenter : (1 / (e : Real)) / 2 = 1 / (2 * (e : Real)) := by
    rw [div_div, mul_comm (e : Real) 2]
  refine Exists.intro n (And.intro (modelTotalMass_pos d e n hd hde) (And.intro ?_ ?_))
  . rw [model_carrier_ratio_eq d e n hd hde hcop]
    simpa only [hCenter] using hn
  . intro t a ha
    refine And.intro ?_ (model_full_residue_ne_zero d e n hd hde hcop t a ha)
    exact atomicPower_scaled_limit (modelPoint d e n) (modelMultiplicity d e n)
      a (zero_lt_one.trans ha) (modelPoint d e n t) (model_den_ne d e n hd hde t a)

theorem zeta_two_power_carrier_lower (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (d e T : Real) (hd : 2 <= d) (he : 2 <= e) (rD rE : Complex -> Complex)
    (hrD : forall rho : Complex, Membership.mem (upperZeroValues T) rho ->
      Filter.Tendsto
        (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) d s)
        (nhdsWithin rho (Set.compl {rho})) (nhds (rD rho)))
    (hrE : forall rho : Complex, Membership.mem (upperZeroValues T) rho ->
      Filter.Tendsto
        (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) e s)
        (nhdsWithin rho (Set.compl {rho})) (nhds (rE rho))) :
    (2 - 1 / e) *
      (upperZeroValues T).sum (zetaWeightedMultiplicity (fun t => 1 / t ^ 2)) <=
      2 * ((upperZeroValues T).filter (fun rho =>
        (rD rho * (rho + (d : Complex) - 1)).im < 0 \/
          (rE rho * (rho + (e : Complex) - 1)).im < 0)).sum
            (zetaWeightedMultiplicity (fun t => 1 / t ^ 2)) := by
  classical
  have hSingle := zeta_power_inverse_square_height_carrier_lower G hG e T he rE hrE
  have hSubset : (upperZeroValues T).filter (fun rho =>
      (rE rho * (rho + (e : Complex) - 1)).im < 0) <=
      (upperZeroValues T).filter (fun rho =>
        (rD rho * (rho + (d : Complex) - 1)).im < 0 \/
          (rE rho * (rho + (e : Complex) - 1)).im < 0) := by
    intro rho hr
    exact Finset.mem_filter.mpr
      (And.intro (Finset.mem_filter.mp hr).1 (Or.inr (Finset.mem_filter.mp hr).2))
  have hSum := Finset.sum_le_sum_of_subset_of_nonneg hSubset
    (fun rho _ _ => show 0 <= zetaWeightedMultiplicity (fun t => 1 / t ^ 2) rho from
      mul_nonneg (Nat.cast_nonneg _) (one_div_nonneg.mpr (sq_nonneg _)))
  exact hSingle.trans (mul_le_mul_of_nonneg_left hSum (by norm_num))

end PrimeFactorOscillations.CarmichaelTraceSharpness
