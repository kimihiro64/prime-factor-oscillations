/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasZetaStrip
import PrimeFactorOscillations.Helpers.QRHSevenEighths
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.ZeroConstantBound
import PrimeFactorOscillations.Helpers.XiZetaMultiplicity

/-!
# A multiplicity-weighted budget for an individual zeta zero

The full positive real reciprocal-product sum pays for every copy in a zero
fiber. The only zero-free input is the installed unconditional QRH theorem.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations
open Complex Robin1984

private theorem budget_xi_strip (p : RiemannXiDivisorZeroIndex) :
    And (1 - (7 / 8 : Real) <= (riemannXiDivisorZeroValue p).re)
      ((riemannXiDivisorZeroValue p).re <= (7 / 8 : Real)) := by
  exact canonical_xi_strip_of_zeta_nonvanishing (by norm_num)
    (fun s hs _ => QRH.zeta_ne_zero s hs) p

private theorem budget_atom_nonneg (p : RiemannXiDivisorZeroIndex) :
    0 <= ((riemannXiDivisorZeroValue p *
      (1 - riemannXiDivisorZeroValue p)) ^ (-1 : Int)).re := by
  have hp := budget_xi_strip p
  rw [zpow_neg_one, Complex.inv_re]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  have h := mul_nonneg (by linarith : 0 <= (riemannXiDivisorZeroValue p).re)
    (by linarith : 0 <= 1 - (riemannXiDivisorZeroValue p).re)
  nlinarith only [h, sq_nonneg (riemannXiDivisorZeroValue p).im]

/-- Every multiplicity copy of one zero is charged to the complete zero sum. -/
theorem zeta_zero_product_mass_le {w : Complex}
    (hw : And (0 < w.re) (w.re < 1)) :
    (analyticOrderNatAt riemannZeta w : Real) *
      ((w * (1 - w)) ^ (-1 : Int)).re <=
        Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) := by
  classical
  have hw0 : Not (w = 0) := by
    intro h
    simp [h] at hw
  have hw1 : Not (w = 1) := by
    intro h
    simp [h] at hw
  let f : RiemannXiDivisorZeroIndex -> Real := fun p =>
    ((riemannXiDivisorZeroValue p *
      (1 - riemannXiDivisorZeroValue p)) ^ (-1 : Int)).re
  have hsInv := summable_inverse_zero_product_strip (by norm_num : (0 : Real) < 7 / 8)
    (by norm_num : (7 / 8 : Real) < 1) budget_xi_strip
  have hs : Summable f := by
    apply hsInv.norm.of_norm_bounded
    intro p
    simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm
      ((riemannXiDivisorZeroValue p *
        (1 - riemannXiDivisorZeroValue p)) ^ (-1 : Int))
  have hTotal : tsum f =
      Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) := by
    have hMap := Complex.reCLM.map_tsum hsInv
    rw [nicolas_inverse_zero_product_sum] at hMap
    simpa [f] using hMap.symm
  let e := xiZeroFiberEquiv w hw0
  let j : Fin (xiZeroMultiplicity w) -> RiemannXiDivisorZeroIndex :=
    fun k => (e.symm k).val
  have hj : Function.Injective j := by
    intro a b h
    apply e.symm.injective
    exact Subtype.ext h
  have hv (k : Fin (xiZeroMultiplicity w)) :
      riemannXiDivisorZeroValue (j k) = w := (e.symm k).property
  let s : Finset RiemannXiDivisorZeroIndex := Finset.univ.image j
  have hFinite : (Finset.sum s f) =
      (xiZeroMultiplicity w : Real) * ((w * (1 - w)) ^ (-1 : Int)).re := by
    dsimp only [s]
    rw [Finset.sum_image (fun a _ b _ h => hj h)]
    simp only [hv]
    simp <;> ring
  rw [<- xiZeroMultiplicity_eq_zetaOrder hw.1 hw1, <- hFinite, <- hTotal]
  exact hs.sum_le_tsum s (fun p _ => budget_atom_nonneg p)

/-- The one-sided reciprocal mass is bounded independently of multiplicity. -/
theorem zeta_inverse_zero_mass_le {w : Complex}
    (hw : And (0 < w.re) (w.re < 1)) :
    (analyticOrderNatAt riemannZeta w : Real) * (Inv.inv w).re <= (1 / 20 : Real) := by
  have hw0 : Not (w = 0) := by intro h; simp [h] at hw
  have hw1 : Not (1 - w = 0) := by
    intro h
    have hOne := sub_eq_zero.mp h
    have hRe := congrArg Complex.re hOne
    simp only [Complex.one_re] at hRe
    linarith only [hw.2, hRe]
  have hId : (w * (1 - w)) ^ (-1 : Int) = Inv.inv w + Inv.inv (1 - w) := by
    rw [zpow_neg_one]
    field_simp
    ring
  have hPos : 0 <= (Inv.inv (1 - w)).re := by
    rw [Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [hw.2]
  have hComp : (Inv.inv w).re <= ((w * (1 - w)) ^ (-1 : Int)).re := by
    rw [hId, Complex.add_re]
    linarith only [hPos]
  exact (mul_le_mul_of_nonneg_left hComp (Nat.cast_nonneg _)).trans
    ((zeta_zero_product_mass_le hw).trans robin_zero_constant_le_one_twentieth)

end PrimeFactorOscillations
