/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasZeroMassBudget
import PrimeFactorOscillations.Helpers.XiDistinctZeroSums
import PrimeFactorOscillations.Mathlib.Analysis.Complex.RealResiduePacket

/-!
# A single global zero budget for any finite set of strip points

The existing unconditional distinct-zero regrouping retains every analytic
multiplicity. Filtering out regular points then compares one finite subset
with the complete positive series, without a cardinality factor.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations
open Complex Robin1984 PrimeClassDeletion

private theorem finite_budget_zero_strip {rho : Complex} (hXi : Complex.riemannXi rho = 0) :
    And (1 - (7 / 8 : Real) <= rho.re) (rho.re <= (7 / 8 : Real)) := by
  exact xi_zero_strip_of_zeta_nonvanishing (by norm_num)
    (fun s hs _ => QRH.zeta_ne_zero s hs) hXi

private theorem finite_budget_ne_one (w : Complex) (hw : w.re < 1) : Not (w = 1) := by
  intro h
  have hr := congrArg Complex.re h
  change w.re = 1 at hr
  linarith

/-- The complete real zero sum is regrouped exactly by distinct complex value. -/
theorem nicolas_distinct_product_real_hasSum :
    HasSum (fun z : XiDistinctZero => (xiZeroMultiplicity z.val : Real) *
      ((z.val * (1 - z.val)) ^ (-1 : Int)).re)
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) := by
  have hs := summable_inverse_zero_product_strip
    (by norm_num : (0 : Real) < 7 / 8) (by norm_num : (7 / 8 : Real) < 1)
    (fun p => finite_budget_zero_strip (riemannXiDivisorZeroValue_eq_zero p))
  have hg := xiDistinctZero_weighted_hasSum
    (fun z : Complex => (z * (1 - z)) ^ (-1 : Int)) hs
  rw [nicolas_inverse_zero_product_sum] at hg
  have hr := Complex.reCLM.hasSum hg
  change HasSum (fun z : XiDistinctZero =>
    ((xiZeroMultiplicity z.val : Complex) *
      (z.val * (1 - z.val)) ^ (-1 : Int)).re)
    ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) : Real) : Complex).re at hr
  simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Complex.ofReal_re] using hr

/-- A finite set pays for each complete multiplicity fiber exactly once. -/
theorem zeta_finite_product_mass_le (S : Finset Complex)
    (hStrip : forall w : Complex, Membership.mem S w -> And (0 < w.re) (w.re < 1)) :
    S.sum (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      ((w * (1 - w)) ^ (-1 : Int)).re) <=
        Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) := by
  classical
  let P : Complex -> Prop := fun w => Complex.riemannXi w = 0
  let T : Finset XiDistinctZero := Finset.subtype P S
  have hs := nicolas_distinct_product_real_hasSum
  calc
    _ = (S.filter P).sum (fun w => (analyticOrderNatAt riemannZeta w : Real) *
        ((w * (1 - w)) ^ (-1 : Int)).re) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro w hw hNot
      have hnXi : Not (Complex.riemannXi w = 0) := by
        intro h
        exact hNot (Finset.mem_filter.mpr (And.intro hw h))
      have hXiOrder : analyticOrderNatAt Complex.riemannXi w = 0 := by
        change (analyticOrderAt Complex.riemannXi w).toNat = 0
        rw [analyticOrderAt_eq_zero.mpr (Or.inr hnXi)]
        rfl
      have hOrder : analyticOrderNatAt riemannZeta w = 0 := by
        rw [<- xiZeroMultiplicity_eq_zetaOrder (hStrip w hw).1
          (finite_budget_ne_one w (hStrip w hw).2), xiZeroMultiplicity_eq_analyticOrderNatAt,
          hXiOrder]
      simp only [hOrder, Nat.cast_zero, zero_mul]
    _ = T.sum (fun z => (xiZeroMultiplicity z.val : Real) *
        ((z.val * (1 - z.val)) ^ (-1 : Int)).re) := by
      apply Finset.sum_bij (fun w hw =>
        (Subtype.mk w ((Finset.mem_filter.mp hw).2) : XiDistinctZero))
      . intro w hw
        exact Finset.mem_subtype.mpr (Finset.mem_filter.mp hw).1
      . intro a ha b hb h
        exact congrArg Subtype.val h
      . intro z hz
        refine Exists.intro z.val (Exists.intro ?_ ?_)
        . exact Finset.mem_filter.mpr (And.intro (Finset.mem_subtype.mp hz) z.property)
        . rfl
      . intro w hw
        change (analyticOrderNatAt riemannZeta w : Real) *
          ((w * (1 - w)) ^ (-1 : Int)).re =
          (xiZeroMultiplicity w : Real) * ((w * (1 - w)) ^ (-1 : Int)).re
        rw [xiZeroMultiplicity_eq_zetaOrder (hStrip w (Finset.mem_filter.mp hw).1).1
          (finite_budget_ne_one w (hStrip w (Finset.mem_filter.mp hw).1).2)]
    _ <= _ := by
      rw [<- hs.tsum_eq]
      apply hs.summable.sum_le_tsum T
      intro z _
      have hz := finite_budget_zero_strip z.property
      exact mul_nonneg (Nat.cast_nonneg _)
        (inverse_product_re_nonneg z.val (by linarith only [hz.1]) (by linarith only [hz.2]))

/-- The finite inverse mass has one twentieth as a global, not per-point, budget. -/
theorem zeta_finite_inverse_mass_le (S : Finset Complex)
    (hStrip : forall w : Complex, Membership.mem S w -> And (0 < w.re) (w.re < 1)) :
    S.sum (fun w => (analyticOrderNatAt riemannZeta w : Real) * (Inv.inv w).re) <=
      (1 / 20 : Real) := by
  calc
    _ <= S.sum (fun w => (analyticOrderNatAt riemannZeta w : Real) *
        ((w * (1 - w)) ^ (-1 : Int)).re) := by
      apply Finset.sum_le_sum
      intro w hw
      exact mul_le_mul_of_nonneg_left
        (inverse_re_le_inverse_product_re w (hStrip w hw).1 (hStrip w hw).2)
        (Nat.cast_nonneg _)
    _ <= Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) :=
      zeta_finite_product_mass_le S hStrip
    _ <= 1 / 20 := robin_zero_constant_le_one_twentieth

end PrimeFactorOscillations
