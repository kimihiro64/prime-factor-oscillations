/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.CarmichaelDirichletScalarOrbit
import PrimeFactorOscillations.Mathlib.Analysis.Complex.AnchoredScalarChain

/-!
# Three quadratic-only scalar observations of actual Dirichlet zeros

The third quadratic iterate lies in the installed unconditional zero-free
strip. The first three real residue limits recover all preceding orders
with strict half-unit errors, including real strip points and every character.
The two-row collision is an order-model obstruction, not an actual L-example.
No new zero-free exponent or observation-error rate is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

open DirichletCompensatedProbe

def quadraticOrbitPoint (rho : Complex) : Nat -> Complex
  | 0 => rho
  | n + 1 => powerMap 2 (quadraticOrbitPoint rho n)

theorem quadraticOrbitPoint_closed_form (rho : Complex) (j : Nat) :
    quadraticOrbitPoint rho j = 1 + (rho - 1) / (2 : Complex) ^ j := by
  induction j with
  | zero =>
    simp only [quadraticOrbitPoint, pow_zero, div_one]
    ring
  | succ j ih =>
    rw [quadraticOrbitPoint, ih]
    have hPow : Not ((2 : Complex) ^ j = 0) := pow_ne_zero j (by norm_num)
    change (1 + (rho - 1) / (2 : Complex) ^ j + 2 - 1) / 2 =
      1 + (rho - 1) / (2 : Complex) ^ (j + 1)
    rw [pow_succ]
    field_simp [hPow] <;> ring

def quadraticOrbitOrder {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (rho : Complex) (j : Nat) : Nat :=
  analyticOrderNatAt (DirichletCharacter.LFunction chi) (quadraticOrbitPoint rho j)

def quadraticOrbitCoefficient (rho : Complex) (j : Nat) : Real :=
  ((2 : Complex) * quadraticOrbitPoint rho j / (quadraticOrbitPoint rho j + 1)).re

private theorem quadratic_orbit_strip (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) (j : Nat) :
    And (0 < (quadraticOrbitPoint rho j).re) ((quadraticOrbitPoint rho j).re < 1) := by
  induction j with
  | zero => exact hRe
  | succ j ih =>
    have h := powerMap_real_identity 2 (by norm_num) (quadraticOrbitPoint rho j)
    change And (0 < (powerMap 2 (quadraticOrbitPoint rho j)).re)
      ((powerMap 2 (quadraticOrbitPoint rho j)).re < 1)
    exact And.intro (by linarith [ih.1]) (by linarith [ih.2])

private theorem quadratic_orbit_order_pos_iff_zero {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) (j : Nat) :
    0 < quadraticOrbitOrder chi rho j <->
      DirichletCharacter.LFunction chi (quadraticOrbitPoint rho j) = 0 := by
  apply LFunction_order_pos_iff_zero
  intro he
  have hh := congrArg Complex.re he
  change (quadraticOrbitPoint rho j).re = 1 at hh
  linarith [(quadratic_orbit_strip rho hRe j).2]

theorem dirichlet_quadratic_chain_terminal_order {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) : quadraticOrbitOrder chi rho 3 = 0 := by
  have h0 := powerMap_real_identity 2 (by norm_num) rho
  have h1 := powerMap_real_identity 2 (by norm_num) (powerMap 2 rho)
  have h2 := powerMap_real_identity 2 (by norm_num) (powerMap 2 (powerMap 2 rho))
  have hBound : (7 / 8 : Real) < (quadraticOrbitPoint rho 3).re := by
    change (7 / 8 : Real) < (powerMap 2 (powerMap 2 (powerMap 2 rho))).re
    linarith [hRe.1]
  have hNZ := QRH.dirichletL_ne_zero q chi (quadraticOrbitPoint rho 3) hBound (by
    intro hPole
    have hh := congrArg Complex.re hPole.2
    change (quadraticOrbitPoint rho 3).re = 1 at hh
    linarith [(quadratic_orbit_strip rho hRe 3).2])
  have hOrd : analyticOrderAt (DirichletCharacter.LFunction chi)
      (quadraticOrbitPoint rho 3) = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hNZ)
  change (analyticOrderAt (DirichletCharacter.LFunction chi)
    (quadraticOrbitPoint rho 3)).toNat = 0
  rw [hOrd]
  rfl

theorem dirichlet_quadratic_chain_scalar_values {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex) (j : Nat) :
    (dirichletCanonicalPowerResidue chi 2 (quadraticOrbitPoint rho j)).re =
      -(quadraticOrbitOrder chi rho j : Real) + quadraticOrbitCoefficient rho j *
        (quadraticOrbitOrder chi rho (j + 1) : Real) := by
  have he : dirichletCanonicalPowerResidue chi 2 (quadraticOrbitPoint rho j) =
      Complex.integerResidueCode 2 (quadraticOrbitPoint rho j)
        (quadraticOrbitOrder chi rho j : Int) (quadraticOrbitOrder chi rho (j + 1) : Int) := by
    simp [dirichletCanonicalPowerResidue, Complex.integerResidueCode,
      quadraticOrbitOrder, quadraticOrbitPoint]
  rw [he]
  have hden : quadraticOrbitPoint rho j + (2 : Complex) - 1 =
      quadraticOrbitPoint rho j + 1 := by ring
  simpa [Complex.anchoredScalarFirst, quadraticOrbitCoefficient, hden] using
    Complex.integerResidueCode_re_scalar 2 (quadraticOrbitPoint rho j)
      (quadraticOrbitOrder chi rho j : Int) (quadraticOrbitOrder chi rho (j + 1) : Int)

theorem dirichlet_quadratic_chain_real_limits {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | And (0 < s.re) (s.re < 1)})
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1)) (j : Nat) :
    Filter.Tendsto
      (fun s => ((s - quadraticOrbitPoint rho j) *
        affinePowerReadout (DirichletZeroReadout.readout chi G) 2 s).re)
      (nhdsWithin (quadraticOrbitPoint rho j) (Set.compl {quadraticOrbitPoint rho j}))
      (nhds (-(quadraticOrbitOrder chi rho j : Real) + quadraticOrbitCoefficient rho j *
        (quadraticOrbitOrder chi rho (j + 1) : Real))) := by
  have h := dirichlet_power_readout_scaled_limit chi G hG 2 (by norm_num)
    (quadraticOrbitPoint rho j) (quadratic_orbit_strip rho hRe j)
  have hh := (Complex.continuous_re.tendsto _).comp h
  have he : Function.comp Complex.re
      (fun s : Complex => (s - quadraticOrbitPoint rho j) *
        affinePowerReadout (DirichletZeroReadout.readout chi G) 2 s) =
      (fun s : Complex => ((s - quadraticOrbitPoint rho j) *
        affinePowerReadout (DirichletZeroReadout.readout chi G) 2 s).re) := by
    funext s
    exact Function.comp_apply
  rw [he] at hh
  simpa only [dirichlet_quadratic_chain_scalar_values chi rho j] using hh

theorem dirichlet_quadratic_chain_decode {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) (y : Nat -> Real)
    (hObs : forall j, j < 3 ->
      abs ((dirichletCanonicalPowerResidue chi 2 (quadraticOrbitPoint rho j)).re - y j) < 1 / 2) :
    forall j, j <= 3 ->
      Complex.scalarChainDecode (quadraticOrbitCoefficient rho) y (3 - j) j =
        (quadraticOrbitOrder chi rho j : Int) := by
  apply Complex.scalarChainDecode_all (quadraticOrbitCoefficient rho) y
    (fun j => (quadraticOrbitOrder chi rho j : Int)) 3
  . rw [dirichlet_quadratic_chain_terminal_order chi rho hRe]
    rfl
  . intro i hi
    have h := hObs i hi
    rw [dirichlet_quadratic_chain_scalar_values chi rho i] at h
    simpa only [Int.cast_natCast] using h

theorem dirichlet_quadratic_chain_zero_iff {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) :
    (Exists (fun j => And (j < 3)
      (DirichletCharacter.LFunction chi (quadraticOrbitPoint rho j) = 0))) <->
    Exists (fun j => And (j < 3)
      ((dirichletCanonicalPowerResidue chi 2 (quadraticOrbitPoint rho j)).re <= -1)) := by
  have h := Complex.scalarChain_negative_iff (quadraticOrbitCoefficient rho)
    (quadraticOrbitOrder chi rho) 3 (dirichlet_quadratic_chain_terminal_order chi rho hRe)
  simpa only [dirichlet_quadratic_chain_scalar_values,
    quadratic_orbit_order_pos_iff_zero chi rho hRe] using h

theorem dirichlet_quadratic_chain_noisy_zero_iff {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) (y : Nat -> Real)
    (hObs : forall j, j < 3 ->
      abs ((dirichletCanonicalPowerResidue chi 2 (quadraticOrbitPoint rho j)).re - y j) < 1 / 2) :
    (Exists (fun j => And (j < 3)
      (DirichletCharacter.LFunction chi (quadraticOrbitPoint rho j) = 0))) <->
    Exists (fun j => And (j < 3) (y j < -1 / 2)) := by
  have hRows : forall j, j < 3 ->
      abs (-(quadraticOrbitOrder chi rho j : Real) + quadraticOrbitCoefficient rho j *
        (quadraticOrbitOrder chi rho (j + 1) : Real) - y j) < 1 / 2 := by
    intro j hj
    simpa only [dirichlet_quadratic_chain_scalar_values] using hObs j hj
  have h := Complex.scalarChain_noisy_negative_iff (quadraticOrbitCoefficient rho) y
    (quadraticOrbitOrder chi rho) 3 (dirichlet_quadratic_chain_terminal_order chi rho hRe) hRows
  simpa only [quadratic_orbit_order_pos_iff_zero chi rho hRe] using h

end PrimeFactorOscillations.CarmichaelWeightedSignal
