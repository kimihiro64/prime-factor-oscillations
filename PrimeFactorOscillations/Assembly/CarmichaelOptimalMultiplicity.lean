/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.CarmichaelStripMultiplicity
import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResidueOptimalDegree

/-!
# Actual zeta multiplicity certification at the minimum unit-spacing degree

The degree is chosen by one exact disk test. Target and reference orders
are retained, and the achieved observation error remains explicit.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

open DirichletCompensatedProbe

theorem zeta_minimal_degree_readout_certifies_orders
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | And (0 < s.re) (s.re < 1)})
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1))
    (hHeight : 2 <= abs rho.im) (r observation : Complex)
    (hr : Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G)
        (Complex.optimalUnitResidueDegree rho : Real) s)
      (nhdsWithin rho (Set.compl {rho})) (nhds r))
    (A B : Nat)
    (hErr : norm (r - observation) + norm (Complex.integerResidueCode
      (Complex.optimalUnitResidueDegree rho) rho (A : Int) (B : Int) - observation) < 1) :
    And (analyticOrderNatAt riemannZeta rho = A)
      (analyticOrderNatAt riemannZeta
        (powerMap (Complex.optimalUnitResidueDegree rho : Real) rho) = B) := by
  let d := Complex.optimalUnitResidueDegree rho
  have hd : 2 <= d := Complex.optimalUnitResidueDegree_ge_two rho hHeight
  have hSpace := Complex.integerResidueCode_optimal_spacing rho
    (And.intro hRe.1.le hRe.2.le) hHeight
  have hErr' : norm (r - observation) +
      norm (Complex.integerResidueCode d rho (A : Int) (B : Int) - observation) <
        min 1 ((d : Real) * ((d : Real) - 1) / norm (rho + (d : Complex) - 1)) := by
    change norm (r - observation) + norm (Complex.integerResidueCode
      (Complex.optimalUnitResidueDegree rho) rho (A : Int) (B : Int) - observation) < _
    rw [hSpace]
    exact hErr
  exact zeta_strip_readout_certifies_orders G hG d hd rho hRe hHeight
    r observation hr A B hErr'

end PrimeFactorOscillations.CarmichaelWeightedSignal

end
