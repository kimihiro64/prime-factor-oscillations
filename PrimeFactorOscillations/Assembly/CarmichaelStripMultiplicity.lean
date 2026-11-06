/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.CarmichaelAdaptiveMultiplicity
import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResidueStrip

/-!
# Strip-wide joint certification of actual zeta multiplicities

The exact minimum spacing is consumed with every reference order retained.
No RH, reference nonvanishing, or multiplicity bound is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

open DirichletCompensatedProbe

theorem zeta_strip_readout_certifies_orders
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | And (0 < s.re) (s.re < 1)})
    (d : Nat) (hd : 2 <= d) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) (hHeight : 2 <= abs rho.im)
    (r observation : Complex)
    (hr : Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) (d : Real) s)
      (nhdsWithin rho (Set.compl {rho})) (nhds r))
    (A B : Nat)
    (hErr : norm (r - observation) +
      norm (Complex.integerResidueCode d rho (A : Int) (B : Int) - observation) <
        min 1 ((d : Real) * ((d : Real) - 1) / norm (rho + (d : Complex) - 1))) :
    And (analyticOrderNatAt riemannZeta rho = A)
      (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) = B) := by
  have hdR : (1 : Real) < d := by exact_mod_cast (show 1 < d by omega)
  have hIm : Not (rho.im = 0) := by
    intro h
    rw [h, abs_zero] at hHeight
    linarith
  have hEq := zeta_power_readout_residue_eq G hG (d : Real) hdR rho hRe hIm r hr
  rw [zetaCanonicalPowerResidue_eq_integerCode] at hEq
  rw [hEq] at hErr
  have h := Complex.integerResidueCode_strip_unique d hd rho
    (And.intro hRe.1.le hRe.2.le) hHeight
    (analyticOrderNatAt riemannZeta rho : Int)
    (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) : Int)
    (A : Int) (B : Int) observation hErr
  exact And.intro (by exact_mod_cast h.1) (by exact_mod_cast h.2)

end PrimeFactorOscillations.CarmichaelWeightedSignal

end
