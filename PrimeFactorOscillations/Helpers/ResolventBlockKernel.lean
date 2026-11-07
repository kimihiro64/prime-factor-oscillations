/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ResolventBlockPolynomial

/-! # The sharp response of the compensated resolvent on a full-strip block -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

open Complex

def unitResolventKernel (x y : Real) : Real := (18 / 5) * pairedResolventDifference 2 3 x y

def unitResolventBlockCharge (H : Real) : Real := 36 / ((4 + H ^ 2) * (9 + H ^ 2))

theorem unitBlockDenTwo_eq_resolvent (x y : Real) :
    pairedResolventDen 2 x y = unitBlockDenTwo (x ^ 2) (y ^ 2) := by
  unfold pairedResolventDen unitBlockDenTwo
  ring

theorem unitBlockDenThree_eq_resolvent (x y : Real) :
    pairedResolventDen 3 x y = unitBlockDenThree (x ^ 2) (y ^ 2) := by
  unfold pairedResolventDen unitBlockDenThree
  ring

theorem unitBlockGram_eq_resolvent (x y : Real) :
    pairedResolventGram 2 3 x y = unitBlockGram (x ^ 2) (y ^ 2) := by
  unfold pairedResolventGram unitBlockGram
  ring

theorem unitResolventKernel_formula (x y : Real) (hx : abs x < 2) :
    unitResolventKernel x y = 36 * unitBlockGram (x ^ 2) (y ^ 2) /
      (unitBlockDenTwo (x ^ 2) (y ^ 2) * unitBlockDenThree (x ^ 2) (y ^ 2)) := by
  unfold unitResolventKernel
  rw [pairedResolventDifference_formula 2 3 x y hx (by norm_num),
    unitBlockDenTwo_eq_resolvent, unitBlockDenThree_eq_resolvent, unitBlockGram_eq_resolvent]
  norm_num <;> ring

theorem unitResolventBlockCharge_pos (H : Real) : 0 < unitResolventBlockCharge H := by
  unfold unitResolventBlockCharge
  exact div_pos (by norm_num) (mul_pos (by nlinarith only [sq_nonneg H])
    (by nlinarith only [sq_nonneg H]))

theorem unitResolventKernel_center (y : Real) :
    unitResolventKernel 0 y = unitResolventBlockCharge y := by
  have hA : Not (4 + y ^ 2 = 0) := ne_of_gt (by nlinarith only [sq_nonneg y])
  have hB : Not (9 + y ^ 2 = 0) := ne_of_gt (by nlinarith only [sq_nonneg y])
  rw [unitResolventKernel_formula 0 y (by norm_num)]
  norm_num [unitBlockGram, unitBlockDenTwo, unitBlockDenThree, unitResolventBlockCharge] <;>
    field_simp [hA, hB] <;> ring

theorem unitResolventKernel_horizontal_lower (x y : Real)
    (hx : abs x <= 1 / 2) (hy : abs y <= 1) :
    unitResolventBlockCharge y <= unitResolventKernel x y := by
  have hx2 : abs x < 2 := by linarith only [hx]
  have hx3 : abs x < 3 := by linarith only [hx]
  have hxBounds := abs_le.mp hx
  have hyBounds := abs_le.mp hy
  have hxProd := mul_nonneg (show 0 <= x + 1 / 2 by linarith only [hxBounds.1])
    (show 0 <= 1 / 2 - x by linarith only [hxBounds.2])
  have hyProd := mul_nonneg (show 0 <= y + 1 by linarith only [hyBounds.1])
    (show 0 <= 1 - y by linarith only [hyBounds.2])
  have hv : And (0 <= x ^ 2) (x ^ 2 <= 1 / 4) :=
    And.intro (sq_nonneg x) (by nlinarith only [hxProd])
  have hw : And (0 <= y ^ 2) (y ^ 2 <= 1) :=
    And.intro (sq_nonneg y) (by nlinarith only [hyProd])
  have hPoly := unitBlockDefect_lower (x ^ 2) (y ^ 2) hv hw
  have hNonneg : 0 <= unitBlockDefect (x ^ 2) (y ^ 2) :=
    (mul_nonneg (by norm_num : (0 : Real) <= 7 / 64) (sq_nonneg x)).trans hPoly
  have hDTwo : 0 < unitBlockDenTwo (x ^ 2) (y ^ 2) := by
    rw [<- unitBlockDenTwo_eq_resolvent]
    exact pairedResolventDen_pos 2 x y hx2
  have hDThree : 0 < unitBlockDenThree (x ^ 2) (y ^ 2) := by
    rw [<- unitBlockDenThree_eq_resolvent]
    exact pairedResolventDen_pos 3 x y hx3
  have hAB : 0 < (4 + y ^ 2) * (9 + y ^ 2) :=
    mul_pos (by nlinarith only [sq_nonneg y]) (by nlinarith only [sq_nonneg y])
  rw [unitResolventKernel_formula x y hx2]
  unfold unitResolventBlockCharge
  unfold unitBlockDefect at hNonneg
  have hCross : 36 * (unitBlockDenTwo (x ^ 2) (y ^ 2) * unitBlockDenThree (x ^ 2) (y ^ 2)) <=
      36 * unitBlockGram (x ^ 2) (y ^ 2) * ((4 + y ^ 2) * (9 + y ^ 2)) := by
    nlinarith only [hNonneg]
  have hScale := div_le_div_of_nonneg_right hCross (mul_pos hAB (mul_pos hDTwo hDThree)).le
  convert hScale using 1 <;> field_simp [hAB.ne', hDTwo.ne', hDThree.ne'] <;> ring

theorem unitResolventBlockCharge_le (H y : Real) (hH : 0 <= H) (hy : abs y <= H) :
    unitResolventBlockCharge H <= unitResolventBlockCharge y := by
  have hb := abs_le.mp hy
  have hp := mul_nonneg (show 0 <= y + H by linarith only [hb.1])
    (show 0 <= H - y by linarith only [hb.2])
  have hSq : y ^ 2 <= H ^ 2 := by nlinarith only [hp]
  have hFactor : 0 <= 13 + H ^ 2 + y ^ 2 := by nlinarith only [sq_nonneg H, sq_nonneg y]
  have hProd := mul_nonneg (sub_nonneg.mpr hSq) hFactor
  have hDen : (4 + y ^ 2) * (9 + y ^ 2) <= (4 + H ^ 2) * (9 + H ^ 2) := by
    nlinarith only [hProd]
  have hDH : 0 < (4 + H ^ 2) * (9 + H ^ 2) :=
    mul_pos (by nlinarith only [sq_nonneg H]) (by nlinarith only [sq_nonneg H])
  have hDY : 0 < (4 + y ^ 2) * (9 + y ^ 2) :=
    mul_pos (by nlinarith only [sq_nonneg y]) (by nlinarith only [sq_nonneg y])
  unfold unitResolventBlockCharge
  have hCross : 36 * ((4 + y ^ 2) * (9 + y ^ 2)) <= 36 * ((4 + H ^ 2) * (9 + H ^ 2)) := by
    nlinarith only [hDen]
  have hScale := div_le_div_of_nonneg_right hCross (mul_pos hDH hDY).le
  convert hScale using 1 <;> field_simp [hDH.ne', hDY.ne'] <;> ring

theorem unitResolventKernel_block_lower (H x y : Real)
    (hH : And (0 <= H) (H <= 1)) (hx : abs x <= 1 / 2) (hy : abs y <= H) :
    unitResolventBlockCharge H <= unitResolventKernel x y :=
  (unitResolventBlockCharge_le H y hH.1 hy).trans
    (unitResolventKernel_horizontal_lower x y hx (hy.trans hH.2))

theorem unitResolventKernel_block_sharp (H q : Real) (hH : And (0 <= H) (H <= 1)) :
    (forall x y : Real, abs x <= 1 / 2 -> abs y <= H -> q <= unitResolventKernel x y) <->
      q <= unitResolventBlockCharge H := by
  constructor
  case mp =>
    intro h
    have hc := h 0 H (by norm_num) (by rw [abs_of_nonneg hH.1])
    rw [unitResolventKernel_center] at hc
    exact hc
  case mpr =>
    intro h x y hx hy
    exact h.trans (unitResolventKernel_block_lower H x y hH hx hy)

theorem unitResolventBlockCharge_one : unitResolventBlockCharge 1 = 18 / 25 := by
  norm_num [unitResolventBlockCharge]

end PrimeFactorOscillations
