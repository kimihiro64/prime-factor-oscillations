/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelScalarErasure
import PrimeFactorOscillations.Helpers.NicolasZeroMassBudget
import PrimeFactorOscillations.Mathlib.Analysis.Complex.ScalarBudgetDecode

/-!
# One original real residue recovers both actual zeta multiplicities

The complete positive zero budget bounds the one-sided defect by three tenths.
The original real coordinate therefore cannot erase actual zero mass. Two
rounding steps recover both orders, without a multiplicity cap or RH. The
fine error tolerance depends on the point; no sampling-error rate is claimed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CarmichaelWeightedSignal
open DirichletCompensatedProbe

private theorem single_real_reference_strip (d : Nat) (hd : 2 <= d)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1)) :
    And (0 < (powerMap (d : Real) rho).re) ((powerMap (d : Real) rho).re < 1) := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have h := powerMap_real_identity (d : Real) (by linarith) rho
  constructor <;> nlinarith [hRe.1, hRe.2]

private theorem single_real_order_iff (w : Complex) (hw : w.re < 1) :
    0 < analyticOrderNatAt riemannZeta w <-> riemannZeta w = 0 := by
  have hOne : Not (w = 1) := by
    intro h
    have hh := congrArg Complex.re h
    change w.re = 1 at hh
    linarith
  simpa only [DirichletCharacter.LFunction_modOne_eq] using
    LFunction_order_pos_iff_zero (1 : DirichletCharacter Complex 1) w hOne

/-- Exact affine geometry of the one-sided real defect. -/
theorem zeta_scalar_defect_reference_identity (d : Nat) (hd : 2 <= d)
    (rho : Complex) (hRe : 0 < rho.re) :
    Complex.scalarResidueDefect d rho =
      ((d : Real) - 1) * (Inv.inv (powerMap (d : Real) rho)).re := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hdC : Not ((d : Complex) = 0) := by
    intro h
    have hh := congrArg Complex.re h
    change (d : Real) = 0 at hh
    linarith
  have hDen : Not (rho + (d : Complex) - 1 = 0) := by
    intro h
    have hh := congrArg Complex.re h
    change rho.re + (d : Real) - 1 = 0 at hh
    linarith
  have hId : (d : Complex) * rho / (rho + (d : Complex) - 1) =
      (d : Complex) - ((d : Complex) - 1) * Inv.inv (powerMap (d : Real) rho) := by
    change (d : Complex) * rho / (rho + (d : Complex) - 1) =
      (d : Complex) - ((d : Complex) - 1) *
        Inv.inv ((rho + (d : Complex) - 1) / (d : Complex))
    field_simp
    ring
  unfold Complex.scalarResidueDefect
  rw [hId]
  simp only [Complex.sub_re, Complex.natCast_re, Complex.mul_re,
    Complex.sub_im, Complex.natCast_im, Complex.one_re, Complex.one_im]
  ring

/-- A positive reference order can occur only for degrees two through seven. -/
theorem zeta_scalar_reference_degree_le (d : Nat) (hd : 2 <= d)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1))
    (hB : 0 < analyticOrderNatAt riemannZeta (powerMap (d : Real) rho)) : d <= 7 := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hStrip := single_real_reference_strip d hd rho hRe
  have hZero := (single_real_order_iff _ hStrip.2).mp hB
  have hBound : (powerMap (d : Real) rho).re <= (7 / 8 : Real) := by
    by_contra h
    exact QRH.zeta_ne_zero _ (lt_of_not_ge h) hZero
  have hId := powerMap_real_identity (d : Real) (by linarith) rho
  have hD : (d : Real) < 8 := by nlinarith [hRe.1]
  have hNat : d < 8 := by exact_mod_cast hD
  omega

/-- The actual reference defect occupies at most three tenths of one unit. -/
theorem zeta_scalar_defect_mass_bound (d : Nat) (hd : 2 <= d)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1)) :
    And (0 <= Complex.scalarResidueDefect d rho *
      (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) : Real))
      (Complex.scalarResidueDefect d rho *
        (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) : Real) <= 3 / 10) := by
  constructor
  . exact mul_nonneg (Complex.scalarResidueDefect_pos d hd rho hRe.1.le).le
      (Nat.cast_nonneg _)
  . by_cases hB : analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) = 0
    . norm_num [hB]
    . have hD := zeta_scalar_reference_degree_le d hd rho hRe (Nat.pos_of_ne_zero hB)
      have hdR : (2 : Real) <= d := by exact_mod_cast hd
      have hd7 : (d : Real) <= 7 := by exact_mod_cast hD
      have hCap := zeta_inverse_zero_mass_le (single_real_reference_strip d hd rho hRe)
      have hMul := mul_le_mul_of_nonneg_left hCap
        (show 0 <= (d : Real) - 1 by linarith)
      rw [zeta_scalar_defect_reference_identity d hd rho hRe.1]
      nlinarith only [hMul, hd7]

private theorem single_real_residue_value (d : Nat) (rho : Complex) :
    (zetaCanonicalPowerResidue (d : Real) rho).re =
      (d : Real) * (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) : Real) -
        (analyticOrderNatAt riemannZeta rho : Real) - Complex.scalarResidueDefect d rho *
          (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) : Real) := by
  rw [zetaCanonicalPowerResidue_eq_integerCode]
  simpa only [Int.cast_natCast] using Complex.integerResidueCode_real_decomposition d rho
    (analyticOrderNatAt riemannZeta rho : Int)
    (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) : Int)

/-- No cancellation of actual zero mass is possible in the original real coordinate. -/
theorem zeta_single_real_residue_zero_iff (d : Nat) (hd : 2 <= d)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1)) :
    (zetaCanonicalPowerResidue (d : Real) rho).re = 0 <->
      And (analyticOrderNatAt riemannZeta rho = 0)
        (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) = 0) := by
  constructor
  . intro hErase
    by_contra h
    have hMass : 0 < analyticOrderNatAt riemannZeta rho +
        analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) := by omega
    rw [zetaCanonicalPowerResidue_eq_integerCode] at hErase
    have hCost := Complex.scalar_erasure_cost d hd rho hRe.1.le
      (analyticOrderNatAt riemannZeta rho)
      (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho)) hMass hErase
    have hBound := zeta_scalar_defect_mass_bound d hd rho hRe
    linarith only [hCost.2, hBound.2]
  . intro h
    simp [zetaCanonicalPowerResidue, h.1, h.2]

/-- A target or reference zero forces a nonzero original real residue. -/
theorem zeta_single_real_residue_nonzero (d : Nat) (hd : 2 <= d)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1))
    (hZero : Or (riemannZeta rho = 0) (riemannZeta (powerMap (d : Real) rho) = 0)) :
    Not ((zetaCanonicalPowerResidue (d : Real) rho).re = 0) := by
  intro h
  have hOrders := (zeta_single_real_residue_zero_iff d hd rho hRe).mp h
  cases hZero with
  | inl hA =>
    have hPos := (single_real_order_iff rho hRe.2).mpr hA
    omega
  | inr hB =>
    have hPos := (single_real_order_iff _ (single_real_reference_strip d hd rho hRe).2).mpr hB
    omega

/-- One real observation recovers both orders, with explicit coarse and fine errors. -/
theorem zeta_single_real_decode (d : Nat) (hd : 2 <= d)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1)) (y : Real)
    (hNoise : abs ((zetaCanonicalPowerResidue (d : Real) rho).re - y) < 7 / 20)
    (hFine : abs ((zetaCanonicalPowerResidue (d : Real) rho).re - y) <
      Complex.scalarResidueDefect d rho / 2) :
    Real.scalarBudgetDecode d (3 / 10) (Complex.scalarResidueDefect d rho) y =
      Prod.mk (analyticOrderNatAt riemannZeta rho : Int)
        (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) : Int) := by
  rw [single_real_residue_value] at hNoise hFine
  apply Real.scalarBudgetDecode_eq
  . exact Complex.scalarResidueDefect_pos d hd rho hRe.1.le
  . simpa only [Int.cast_natCast] using zeta_scalar_defect_mass_bound d hd rho hRe
  . simpa only [Int.cast_natCast,
      show (1 - (3 / 10 : Real)) / 2 = 7 / 20 by norm_num] using hNoise
  . simpa only [Int.cast_natCast] using hFine

/-- The single real residue is the actual readout limit, also at real strip points. -/
theorem zeta_single_real_limit (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | And (0 < s.re) (s.re < 1)})
    (d : Nat) (hd : 2 <= d) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) :
    Filter.Tendsto (fun s => ((s - rho) *
      affinePowerReadout (zetaMultiplicityReadout G) (d : Real) s).re)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (zetaCanonicalPowerResidue (d : Real) rho).re) := by
  have hdR : (1 : Real) < d := by exact_mod_cast (by omega : 1 < d)
  have h := dirichlet_power_readout_scaled_limit
    (1 : DirichletCharacter Complex 1) G hG (d : Real) hdR rho hRe
  have hL : DirichletCharacter.LFunction (1 : DirichletCharacter Complex 1) = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq
  have hReadout : DirichletZeroReadout.readout (1 : DirichletCharacter Complex 1) G =
      zetaMultiplicityReadout G := by
    funext s
    simp only [DirichletZeroReadout.readout, zetaMultiplicityReadout, hL]
  rw [hReadout] at h
  have hz : Filter.Tendsto (fun s => (s - rho) *
      affinePowerReadout (zetaMultiplicityReadout G) (d : Real) s)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (zetaCanonicalPowerResidue (d : Real) rho)) := by
    simpa [dirichletCanonicalPowerResidue, zetaCanonicalPowerResidue,
      DirichletCharacter.LFunction_modOne_eq] using h
  exact (Complex.continuous_re.tendsto _).comp hz

end PrimeFactorOscillations.CarmichaelWeightedSignal
