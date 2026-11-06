/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.CarmichaelMultiplicityDecoding
import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResidueAdaptive

/-!
# Optimal constant-accuracy certification of actual zeta orders

Changing the compensation power preserves every reference contribution and
gives unit residue-lattice spacing. Half-unit accuracy certifies both actual
analytic orders without RH or an upper multiplicity bound.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

open DirichletCompensatedProbe

theorem zeta_large_power_readout_certifies_orders
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (d : Nat) (rho : Complex)
    (hRe : 0 < rho.re /\ rho.re < 1)
    (hHeight : 2 <= abs rho.im)
    (hd : 2 * abs rho.im <= (d : Real))
    (r observation : Complex)
    (hr : Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) (d : Real) s)
      (nhdsWithin rho (Set.compl {rho})) (nhds r))
    (A B : Nat)
    (hActual : norm (r - observation) < 1 / 2)
    (hCandidate : norm (Complex.integerResidueCode d rho (A : Int) (B : Int) - observation) <
      1 / 2) :
    analyticOrderNatAt riemannZeta rho = A /\
      analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) = B := by
  have hdR : (1 : Real) < d := by linarith
  have hIm : Not (rho.im = 0) := by
    intro h
    rw [h, abs_zero] at hHeight
    linarith
  have hEq := zeta_power_readout_residue_eq G hG (d : Real) hdR rho hRe hIm r hr
  rw [zetaCanonicalPowerResidue_eq_integerCode] at hEq
  rw [hEq] at hActual
  have h := Complex.integerResidueCode_large_power_unique d rho
    (And.intro hRe.1.le hRe.2.le) hHeight hd
    (analyticOrderNatAt riemannZeta rho : Int)
    (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) : Int)
    (A : Int) (B : Int) observation hActual hCandidate
  exact And.intro (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem zeta_adaptive_readout_certifies_orders
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (rho : Complex)
    (hRe : 0 < rho.re /\ rho.re < 1)
    (hHeight : 2 <= abs rho.im)
    (r observation : Complex)
    (hr : Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G)
        (Complex.adaptiveResidueDegree rho : Real) s)
      (nhdsWithin rho (Set.compl {rho})) (nhds r))
    (A B : Nat)
    (hActual : norm (r - observation) < 1 / 2)
    (hCandidate : norm (Complex.integerResidueCode (Complex.adaptiveResidueDegree rho) rho
      (A : Int) (B : Int) - observation) < 1 / 2) :
    analyticOrderNatAt riemannZeta rho = A /\
      analyticOrderNatAt riemannZeta
        (powerMap (Complex.adaptiveResidueDegree rho : Real) rho) = B :=
  zeta_large_power_readout_certifies_orders G hG (Complex.adaptiveResidueDegree rho) rho
    hRe hHeight (Complex.adaptiveResidueDegree_ge_height rho)
    r observation hr A B hActual hCandidate

end PrimeFactorOscillations.CarmichaelWeightedSignal

end
