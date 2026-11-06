/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.CarmichaelPowerSignal

/-!
# Exact Dirichlet multiplicity residues, including real strip points

Finite local factorization gives the actual multiplicity without an assumed
limit. Affine power compensation retains both target and reference orders.
Every character of every nonzero modulus is allowed, including principal
characters. No RH or nonreal-point hypothesis is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

open DirichletCompensatedProbe

private theorem dirichlet_factor_order {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex) (hOne : Not (rho = 1))
    (n : Nat) (g : Complex -> Complex) (hg : AnalyticAt Complex g rho)
    (hgn : Not (g rho = 0))
    (hEq : Filter.Eventually (fun s => DirichletCharacter.LFunction chi s =
      (s - rho) ^ n * g s) (nhds rho)) :
    analyticOrderNatAt (DirichletCharacter.LFunction chi) rho = n := by
  have ha := DirichletZeroReadout.analyticOnNhd_LFunction_off_one chi rho
    (Set.mem_compl_singleton_iff.mpr hOne)
  have hOrder : analyticOrderAt (DirichletCharacter.LFunction chi) rho = (n : ENat) := by
    apply ha.analyticOrderAt_eq_natCast.mpr
    exact Exists.intro g (And.intro hg (And.intro hgn
      (by simpa only [smul_eq_mul] using hEq)))
  exact congrArg ENat.toNat hOrder

theorem LFunction_order_pos_iff_zero {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex) (hOne : Not (rho = 1)) :
    0 < analyticOrderNatAt (DirichletCharacter.LFunction chi) rho <->
      DirichletCharacter.LFunction chi rho = 0 := by
  constructor
  . intro hPos
    by_contra hNZ
    have hOrder : analyticOrderAt (DirichletCharacter.LFunction chi) rho = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hNZ)
    change 0 < (analyticOrderAt (DirichletCharacter.LFunction chi) rho).toNat at hPos
    rw [hOrder] at hPos
    exact (Nat.lt_irrefl 0) hPos
  . intro hZero
    choose n g hg hgn hEq hPos using L_factor_exists chi rho hOne
    rw [dirichlet_factor_order chi rho hOne n g hg hgn hEq]
    exact hPos hZero

theorem dirichlet_readout_scaled_limit {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (G : Complex -> Complex)
    (rho : Complex) (hOne : Not (rho = 1)) (hG : AnalyticAt Complex G rho) :
    Filter.Tendsto (fun s => (s - rho) * DirichletZeroReadout.readout chi G s)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (-((analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : Real) : Complex))) := by
  classical
  choose n g hg hgn hEq _hPos using L_factor_exists chi rho hOne
  have hn := dirichlet_factor_order chi rho hOne n g hg hgn hEq
  have hW := weighted_limit (fun _ : Unit => DirichletCharacter.LFunction chi)
    (fun _ : Unit => g) (fun _ : Unit => (1 : Complex)) (fun _ : Unit => n) rho
    (fun _ => hg) (fun _ => hgn) (fun _ => hEq) G hG
  simpa [readout, DirichletZeroReadout.readout, <- hn] using hW

def dirichletCanonicalPowerResidue {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (d : Real) (rho : Complex) : Complex :=
  -(analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : Complex) +
    (d : Complex) * rho / (rho + (d : Complex) - 1) *
      (analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap d rho) : Complex)

theorem dirichlet_power_readout_scaled_limit {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | And (0 < s.re) (s.re < 1)})
    (d : Real) (hd : 1 < d) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) :
    Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (DirichletZeroReadout.readout chi G) d s)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (dirichletCanonicalPowerResidue chi d rho)) := by
  have hq := powerMap_real_identity d (by linarith) rho
  have hqRe : And (0 < (powerMap d rho).re) ((powerMap d rho).re < 1) := by
    constructor <;> nlinarith [hRe.1, hRe.2]
  have hOne : Not (rho = 1) := by
    intro he
    have hh := congrArg Complex.re he
    change rho.re = 1 at hh
    linarith [hRe.2]
  have hqOne : Not (powerMap d rho = 1) := by
    intro he
    have hh := congrArg Complex.re he
    change (powerMap d rho).re = 1 at hh
    linarith [hqRe.2]
  have hden : Not (rho + (d : Complex) - 1 = 0) := by
    intro he
    have hh := congrArg Complex.re he
    change rho.re + d - 1 = 0 at hh
    linarith [hRe.1]
  have hA := dirichlet_readout_scaled_limit chi G rho hOne (hG rho hRe)
  have hB := dirichlet_readout_scaled_limit chi G (powerMap d rho) hqOne
    (hG (powerMap d rho) hqRe)
  simpa only [dirichletCanonicalPowerResidue, Complex.ofReal_natCast] using
    affinePowerReadout_scaled_limit (DirichletZeroReadout.readout chi G) d (by linarith)
      rho hden (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : Real)
      (analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap d rho) : Real) hA hB

end PrimeFactorOscillations.CarmichaelWeightedSignal
