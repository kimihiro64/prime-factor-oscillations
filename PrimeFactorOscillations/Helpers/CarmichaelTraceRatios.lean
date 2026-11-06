/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantitative rectangular carrier ratios

The exact finite geometric packet has a uniform exponential error bound and
an epsilon witness for its limiting carrier coefficient. This is the scalar
consumer for the coprime affine-grid sharpness construction; the ratio formulas
alone do not assert that a finite grid realizes a zeta zero spectrum.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelTraceSharpness

def geomBlock (x : Real) (n : Nat) : Real :=
  (Finset.range (n + 1)).sum (fun i => x ^ i)

def rectangularCarrierRatio (a b : Real) (n : Nat) : Real :=
  1 - (Finset.range n).sum (fun i => a ^ i) * (geomBlock b n - 1) /
    (2 * geomBlock a n * geomBlock b n)

theorem geomBlock_ge_one (x : Real) (hx : 0 <= x) (n : Nat) :
    1 <= geomBlock x n := by
  have h := Finset.single_le_sum
    (fun i (_hi : Membership.mem (Finset.range (n + 1)) i) => pow_nonneg hx i)
    (Finset.mem_range.mpr (Nat.zero_lt_succ n))
  simpa only [pow_zero, geomBlock] using h

theorem rectangularCarrierRatio_gap (a b : Real) (n : Nat)
    (ha : 0 <= a) (hb : 0 <= b) (hba : b <= a) (ha1 : a < 1) :
    rectangularCarrierRatio a b n - (1 - b / 2) =
      (b * (a ^ n / geomBlock a n) +
        (1 - a ^ n / geomBlock a n) * (b ^ (n + 1) / geomBlock b n)) / 2 := by
  have hA : 0 < geomBlock a n := lt_of_lt_of_le (by norm_num) (geomBlock_ge_one a ha n)
  have hB : 0 < geomBlock b n := lt_of_lt_of_le (by norm_num) (geomBlock_ge_one b hb n)
  have hGA : geomBlock a n =
      (Finset.range n).sum (fun i => a ^ i) + a ^ n := by
    exact Finset.sum_range_succ (fun i => a ^ i) n
  have hGB : geomBlock b n * (1 - b) = 1 - b ^ (n + 1) :=
    geom_sum_mul_of_le_one (hba.trans ha1.le) (n + 1)
  unfold rectangularCarrierRatio
  field_simp [hA.ne', hB.ne']
  linear_combination (geomBlock b n - 1) * hGA -
    (geomBlock a n - a ^ n) * hGB

theorem rectangularCarrierRatio_gap_bounds (a b : Real) (n : Nat)
    (ha : 0 <= a) (hb : 0 <= b) (hba : b <= a) (ha1 : a < 1) :
    0 <= rectangularCarrierRatio a b n - (1 - b / 2) /\
      rectangularCarrierRatio a b n - (1 - b / 2) <= b * a ^ n := by
  let A := geomBlock a n
  let B := geomBlock b n
  let P := a ^ n
  let Q := b ^ (n + 1)
  let x := P / A
  let y := Q / B
  have hA : 1 <= A := geomBlock_ge_one a ha n
  have hB : 1 <= B := geomBlock_ge_one b hb n
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hP : 0 <= P := pow_nonneg ha n
  have hQ : 0 <= Q := pow_nonneg hb (n + 1)
  have hPre : 0 <= (Finset.range n).sum (fun i => a ^ i) :=
    Finset.sum_nonneg (fun i _ => pow_nonneg ha i)
  have hGA : A = (Finset.range n).sum (fun i => a ^ i) + P :=
    Finset.sum_range_succ (fun i => a ^ i) n
  have hPA : P <= A := by linarith
  have hx0 : 0 <= x := div_nonneg hP hA0.le
  have hx1 : x <= 1 := by
    have h := div_le_div_of_nonneg_right hPA hA0.le
    simpa only [div_self hA0.ne'] using h
  have hxP : x <= P := div_le_self hP hA
  have hy0 : 0 <= y := div_nonneg hQ hB0.le
  have hPow : forall k : Nat, b ^ k <= a ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k hk =>
      simp only [pow_succ]
      exact mul_le_mul hk hba hb (pow_nonneg ha k)
  have hQP : Q <= b * P := by
    have h := mul_le_mul_of_nonneg_left (hPow n) hb
    change b ^ (n + 1) <= b * a ^ n
    rw [pow_succ]
    nlinarith only [h]
  have hyP : y <= b * P :=
    (div_le_div_of_nonneg_right hQP hB0.le).trans
      (div_le_self (mul_nonneg hb hP) hB)
  have hbx : b * x <= b * P := mul_le_mul_of_nonneg_left hxP hb
  have hxy : (1 - x) * y <= y := by
    nlinarith only [mul_nonneg hx0 hy0]
  have hGap := rectangularCarrierRatio_gap a b n ha hb hba ha1
  change rectangularCarrierRatio a b n - (1 - b / 2) =
    (b * x + (1 - x) * y) / 2 at hGap
  rw [hGap]
  constructor
  . exact div_nonneg
      (add_nonneg (mul_nonneg hb hx0) (mul_nonneg (sub_nonneg.mpr hx1) hy0))
      (by norm_num)
  . nlinarith only [hbx, hxy, hyP]

theorem rectangularCarrierRatio_near_limit (a b : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hba : b <= a) (ha1 : a < 1)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    exists n : Nat, rectangularCarrierRatio a b n < 1 - b / 2 + epsilon := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one ha ha1
  have hev : Filter.Eventually (fun n : Nat => a ^ n < epsilon) Filter.atTop :=
    hp.eventually (gt_mem_nhds hepsilon)
  choose N hN using Filter.eventually_atTop.mp hev
  have hGap := rectangularCarrierRatio_gap_bounds a b N ha hb hba ha1
  have hSmall := hN N (le_refl N)
  have hb1 : b <= 1 := hba.trans ha1.le
  have hPow0 : 0 <= a ^ N := pow_nonneg ha N
  have hMult : b * a ^ N <= a ^ N := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hb1) hPow0]
  exact Exists.intro N (by linarith)

end PrimeFactorOscillations.CarmichaelTraceSharpness
