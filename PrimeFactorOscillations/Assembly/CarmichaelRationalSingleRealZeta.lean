/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelSingleRealZeta
import PrimeFactorOscillations.Mathlib.Analysis.Complex.RationalResidueBudget

/-!
# Rational powers approaching one retain one-coordinate zeta recovery

For d=1+k/n, scaling the original real residue by n restores an integer
level. The actual zero budget gives a defect at most k/20. Every positive
n and1<=k<=19 is allowed, with all multiplicities and real strip points.
No polynomial input substitution, sampling-error rate, or RH is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CarmichaelWeightedSignal
open Complex DirichletCompensatedProbe

def zetaRationalReferenceOrder (n k : Nat) (rho : Complex) : Nat :=
  analyticOrderNatAt riemannZeta (powerMap (rationalPowerDegree n k) rho)

private theorem rational_reference_strip (n k : Nat) (hn : 0 < n) (hk : 0 < k)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1)) :
    And (0 < (powerMap (rationalPowerDegree n k) rho).re)
      ((powerMap (rationalPowerDegree n k) rho).re < 1) := by
  have hd := rationalPowerDegree_gt_one n k hn hk
  have he := powerMap_real_identity (rationalPowerDegree n k) (by linarith) rho
  constructor <;> nlinarith [hRe.1, hRe.2]

private theorem rational_zeta_code (n k : Nat) (rho : Complex) :
    zetaCanonicalPowerResidue (rationalPowerDegree n k) rho =
      realPowerResidueCode (rationalPowerDegree n k) rho
        (analyticOrderNatAt riemannZeta rho : Int) (zetaRationalReferenceOrder n k rho : Int) := by
  simp [zetaCanonicalPowerResidue, realPowerResidueCode, zetaRationalReferenceOrder]

private theorem rational_zeta_order_iff (w : Complex) (hw : w.re < 1) :
    0 < analyticOrderNatAt riemannZeta w <-> riemannZeta w = 0 := by
  have hOne : Not (w = 1) := by
    intro h
    have hh := congrArg Complex.re h
    change w.re = 1 at hh
    linarith
  simpa only [DirichletCharacter.LFunction_modOne_eq] using
    LFunction_order_pos_iff_zero (1 : DirichletCharacter Complex 1) w hOne

/-- The integer-scaled defect has the numerator gap k, not the degree d. -/
theorem zeta_rational_scaled_defect_identity (n k : Nat) (hn : 0 < n) (hk : 0 < k)
    (rho : Complex) (hRe : 0 <= rho.re) :
    (n : Real) * realPowerResidueDefect (rationalPowerDegree n k) rho =
      (k : Real) * (Inv.inv (powerMap (rationalPowerDegree n k) rho)).re := by
  have hd := rationalPowerDegree_mul_den n k hn
  push_cast at hd
  have hFactor : (n : Real) * (rationalPowerDegree n k - 1) = (k : Real) := by
    linarith only [hd]
  rw [realPowerResidueDefect_reference_identity _ (rationalPowerDegree_gt_one n k hn hk) rho hRe]
  change (n : Real) * ((rationalPowerDegree n k - 1) *
    (Inv.inv (powerMap (rationalPowerDegree n k) rho)).re) = _
  rw [<- mul_assoc, hFactor]

/-- Every multiplicity copy is retained in the rational one-sided budget. -/
theorem zeta_rational_defect_mass_bound (n k : Nat) (hn : 0 < n) (hk : 0 < k)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1)) :
    And (0 <= ((n : Real) * realPowerResidueDefect (rationalPowerDegree n k) rho) *
      (zetaRationalReferenceOrder n k rho : Real))
      (((n : Real) * realPowerResidueDefect (rationalPowerDegree n k) rho) *
        (zetaRationalReferenceOrder n k rho : Real) <= (k : Real) / 20) := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hDelta := realPowerResidueDefect_pos _ (rationalPowerDegree_gt_one n k hn hk)
    rho hRe.1.le
  constructor
  . exact mul_nonneg (mul_pos hnR hDelta).le (Nat.cast_nonneg _)
  . have hCap := zeta_inverse_zero_mass_le (rational_reference_strip n k hn hk rho hRe)
    change (zetaRationalReferenceOrder n k rho : Real) *
      (Inv.inv (powerMap (rationalPowerDegree n k) rho)).re <= 1 / 20 at hCap
    rw [zeta_rational_scaled_defect_identity n k hn hk rho hRe.1.le]
    calc
      _ = (k : Real) * ((zetaRationalReferenceOrder n k rho : Real) *
          (Inv.inv (powerMap (rationalPowerDegree n k) rho)).re) := by ring
      _ <= (k : Real) * (1 / 20) := mul_le_mul_of_nonneg_left hCap (Nat.cast_nonneg k)
      _ = _ := by ring

/-- A numerator gap at most nineteen prevents erasure in the original real coordinate. -/
theorem zeta_rational_single_real_zero_iff (n k : Nat) (hn : 0 < n)
    (hk : 0 < k) (hkSmall : k <= 19) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) :
    (zetaCanonicalPowerResidue (rationalPowerDegree n k) rho).re = 0 <->
      And (analyticOrderNatAt riemannZeta rho = 0) (zetaRationalReferenceOrder n k rho = 0) := by
  constructor
  . intro hZero
    by_contra h
    have hMass : 0 < analyticOrderNatAt riemannZeta rho + zetaRationalReferenceOrder n k rho := by
      omega
    rw [rational_zeta_code] at hZero
    have hCost := rationalPowerResidue_zero_cost n k hn hk rho hRe.1.le
      (analyticOrderNatAt riemannZeta rho) (zetaRationalReferenceOrder n k rho) hMass hZero
    have hBound := zeta_rational_defect_mass_bound n k hn hk rho hRe
    have hkR : (k : Real) <= 19 := by exact_mod_cast hkSmall
    linarith only [hCost.2, hBound.2, hkR]
  . intro h
    have hb := h.2
    change analyticOrderNatAt riemannZeta (powerMap (rationalPowerDegree n k) rho) = 0 at hb
    simp [zetaCanonicalPowerResidue, h.1, hb]

/-- Either actual zero gives a nonzero real signal, uniformly in the denominator n. -/
theorem zeta_rational_single_real_nonzero (n k : Nat) (hn : 0 < n)
    (hk : 0 < k) (hkSmall : k <= 19) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1))
    (hZero : Or (riemannZeta rho = 0)
      (riemannZeta (powerMap (rationalPowerDegree n k) rho) = 0)) :
    Not ((zetaCanonicalPowerResidue (rationalPowerDegree n k) rho).re = 0) := by
  intro h
  have hOrders := (zeta_rational_single_real_zero_iff n k hn hk hkSmall rho hRe).mp h
  cases hZero with
  | inl ha =>
    have hPos := (rational_zeta_order_iff rho hRe.2).mpr ha
    omega
  | inr hb =>
    have hPos : 0 < zetaRationalReferenceOrder n k rho :=
      (rational_zeta_order_iff _ (rational_reference_strip n k hn hk rho hRe).2).mpr hb
    omega

/-- Both orders are recovered with the exact scaled coarse and fine observation errors. -/
theorem zeta_rational_single_real_decode (n k : Nat) (hn : 0 < n) (hk : 0 < k)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1)) (y : Real)
    (hNoise : abs ((n : Real) *
      ((zetaCanonicalPowerResidue (rationalPowerDegree n k) rho).re - y)) < (1 - (k : Real) / 20) / 2)
    (hFine : abs ((n : Real) *
      ((zetaCanonicalPowerResidue (rationalPowerDegree n k) rho).re - y)) <
      ((n : Real) * realPowerResidueDefect (rationalPowerDegree n k) rho) / 2) :
    rationalPowerDecode n k ((k : Real) / 20)
      (realPowerResidueDefect (rationalPowerDegree n k) rho) y =
        Prod.mk (analyticOrderNatAt riemannZeta rho : Int) (zetaRationalReferenceOrder n k rho : Int) := by
  rw [rational_zeta_code] at hNoise hFine
  apply rationalPowerDecode_eq n k hn hk rho hRe.1.le
  . simpa only [Int.cast_natCast] using zeta_rational_defect_mass_bound n k hn hk rho hRe
  . exact hNoise
  . exact hFine

/-- The rational scalar observation is the actual analytic residue limit, including real points. -/
theorem zeta_rational_single_real_limit (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | And (0 < s.re) (s.re < 1)})
    (n k : Nat) (hn : 0 < n) (hk : 0 < k) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) :
    Filter.Tendsto (fun s => ((s - rho) *
      affinePowerReadout (zetaMultiplicityReadout G) (rationalPowerDegree n k) s).re)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (zetaCanonicalPowerResidue (rationalPowerDegree n k) rho).re) := by
  have h := dirichlet_power_readout_scaled_limit
    (1 : DirichletCharacter Complex 1) G hG (rationalPowerDegree n k)
    (rationalPowerDegree_gt_one n k hn hk) rho hRe
  have hL : DirichletCharacter.LFunction (1 : DirichletCharacter Complex 1) = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq
  have hReadout : DirichletZeroReadout.readout (1 : DirichletCharacter Complex 1) G =
      zetaMultiplicityReadout G := by
    funext s
    simp only [DirichletZeroReadout.readout, zetaMultiplicityReadout, hL]
  rw [hReadout] at h
  have hz : Filter.Tendsto (fun s => (s - rho) *
      affinePowerReadout (zetaMultiplicityReadout G) (rationalPowerDegree n k) s)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (zetaCanonicalPowerResidue (rationalPowerDegree n k) rho)) := by
    simpa [dirichletCanonicalPowerResidue, zetaCanonicalPowerResidue,
      DirichletCharacter.LFunction_modOne_eq] using h
  exact (Complex.continuous_re.tendsto _).comp hz

end PrimeFactorOscillations.CarmichaelWeightedSignal
