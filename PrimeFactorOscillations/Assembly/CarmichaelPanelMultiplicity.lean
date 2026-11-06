/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.CarmichaelOptimalMultiplicity
import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResiduePanel

/-!
# Simultaneous finite-panel certification of actual zeta orders

All power references are retained, with no RH or multiplicity-cap hypothesis.
The error budget is a hypothesis, rather than an achieved arithmetic estimate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

open DirichletCompensatedProbe

theorem zeta_panel_readout_certifies_orders
    (D : Finset Nat) (hD : D.Nonempty)
    (hPow : forall d : Nat, Membership.mem D d -> 2 <= d)
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | And (0 < s.re) (s.re < 1)})
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1))
    (hHeight : 2 <= abs rho.im) (r observation : Nat -> Complex)
    (hr : forall d : Nat, Membership.mem D d -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) (d : Real) s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (r d)))
    (A : Nat) (B : Nat -> Nat)
    (hErr : forall d : Nat, Membership.mem D d ->
      norm (r d - observation d) +
        norm (Complex.integerResidueCode d rho (A : Int) (B d : Int) - observation d) <
          Complex.residuePanelRadius D hD rho) :
    And (analyticOrderNatAt riemannZeta rho = A)
      (forall d : Nat, Membership.mem D d ->
        analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) = B d) := by
  have hIm : Not (rho.im = 0) := by
    intro h
    rw [h, abs_zero] at hHeight
    linarith
  have hCodes : forall d : Nat, Membership.mem D d ->
      r d = Complex.integerResidueCode d rho
        (analyticOrderNatAt riemannZeta rho : Int)
        (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) : Int) := by
    intro d hd
    have hd2 := hPow d hd
    have hdR : (1 : Real) < d := by exact_mod_cast (show 1 < d by omega)
    have hEq := zeta_power_readout_residue_eq G hG (d : Real) hdR rho hRe hIm
      (r d) (hr d hd)
    rw [zetaCanonicalPowerResidue_eq_integerCode] at hEq
    exact hEq
  have h := Complex.residuePanel_unique D hD hPow rho
    (And.intro hRe.1.le hRe.2.le) hHeight
    (analyticOrderNatAt riemannZeta rho : Int) (A : Int)
    (fun d => (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) : Int))
    (fun d => (B d : Int)) observation (by
      intro d hd
      rw [<- hCodes d hd]
      exact hErr d hd)
  refine And.intro (by exact_mod_cast h.1) ?_
  intro d hd
  exact_mod_cast h.2 d hd

end PrimeFactorOscillations.CarmichaelWeightedSignal

end
