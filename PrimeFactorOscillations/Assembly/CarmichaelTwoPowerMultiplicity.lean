/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.CarmichaelPanelMultiplicity
import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResidueTwoPower

/-!
# Actual zeta multiplicity decoding at cube-root-sized power degrees

The two consecutive powers retain both reference multiplicities.
Their total true-plus-candidate error budget is one in each row.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

open DirichletCompensatedProbe

theorem zeta_two_power_cube_root_certifies_orders
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | And (0 < s.re) (s.re < 1)})
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1))
    (hHeight : 2 <= abs rho.im) (R : Real) (hR0 : 0 <= R)
    (hCube : R ^ 3 = abs rho.im) (r observation : Nat -> Complex)
    (hr : forall d : Nat, Membership.mem ({Nat.ceil R, Nat.ceil R + 1} : Finset Nat) d ->
      Filter.Tendsto
        (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) (d : Real) s)
        (nhdsWithin rho (Set.compl {rho})) (nhds (r d)))
    (A : Nat) (B : Nat -> Nat)
    (hErr : forall d : Nat, Membership.mem ({Nat.ceil R, Nat.ceil R + 1} : Finset Nat) d ->
      norm (r d - observation d) +
        norm (Complex.integerResidueCode d rho (A : Int) (B d : Int) - observation d) < 1) :
    And (analyticOrderNatAt riemannZeta rho = A)
      (forall d : Nat, Membership.mem ({Nat.ceil R, Nat.ceil R + 1} : Finset Nat) d ->
        analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) = B d) := by
  have hSel := Complex.twoPowerBudget_ceil_cube_root rho
    (And.intro hRe.1.le hRe.2.le) hHeight R hR0 hCube
  have hPow : forall d : Nat,
      Membership.mem ({Nat.ceil R, Nat.ceil R + 1} : Finset Nat) d -> 2 <= d := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h | h
    . rw [h]
      omega
    . rw [h]
      omega
  have hEq : Complex.residuePanelRadius ({Nat.ceil R, Nat.ceil R + 1} : Finset Nat)
      (by simp) rho = Complex.twoPowerBudgetRadius (Nat.ceil R + 1) rho := by
    simpa using Complex.residuePanelRadius_consecutive (Nat.ceil R + 1) hSel.1 rho
  have hOne : 1 <= Complex.residuePanelRadius
      ({Nat.ceil R, Nat.ceil R + 1} : Finset Nat) (by simp) rho := by
    rw [hEq]
    exact hSel.2
  apply zeta_panel_readout_certifies_orders ({Nat.ceil R, Nat.ceil R + 1} : Finset Nat)
    (by simp) hPow G hG rho hRe hHeight r observation hr A B
  intro d hd
  exact lt_of_lt_of_le (hErr d hd) hOne

end PrimeFactorOscillations.CarmichaelWeightedSignal

end
