/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
import PrimeFactorOscillations.Helpers.NicolasZetaStrip
import PrimeFactorOscillations.Helpers.QRHSevenEighths
import PrimeFactorOscillations.Helpers.XiSharpMultiplicity

/-!
# Optimized multiplicity bound from the actual seven-eighths theorem

For each positive epsilon the radii are fixed before the zero height varies.
The additive constant is allowed to depend on epsilon. No endpoint constant
uniform as the inner radius tends to one half is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Complex Robin1984

theorem xi_seven_eighths_centered_strip (p : RiemannXiDivisorZeroIndex) :
    abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 3 / 8 := by
  have hp := canonical_xi_strip_of_zeta_nonvanishing
    (by norm_num : (0 : Real) <= 7 / 8)
    (fun s hs _ => QRH.zeta_ne_zero s hs) p
  apply abs_le.mpr
  constructor <;> linarith only [hp.1, hp.2]

theorem zeta_multiplicity_seven_eighths_sharp_log_bound
    (eps : Real) (heps : 0 < eps) :
    Exists (fun C : Real => And (0 < C)
      (forall w : Complex, And (0 < w.re) (w.re < 1) -> 2 <= abs w.im ->
        (analyticOrderNatAt riemannZeta w : Real) <=
          (Real.sharpResolventCoefficient + eps) * Real.log (abs w.im) + C)) := by
  choose r R hr hR hPos hCoefficient using
    Real.sharpResolvent_admissible_approximation eps heps
  choose C hC hBound using zeta_multiplicity_log_bound_of_positive_strip
    (3 / 8) r R (by norm_num) (by linarith only [hr]) hr hR hPos
    xi_seven_eighths_centered_strip
  refine Exists.intro (C + 1) (And.intro (by linarith only [hC]) ?_)
  intro w hw ht
  have hLog : 0 <= Real.log (abs w.im) := Real.log_nonneg (by linarith only [ht])
  have h0 := hBound w hw ht
  have h1 := mul_le_mul_of_nonneg_right (le_of_lt hCoefficient) hLog
  linarith only [h0, h1]

end PrimeFactorOscillations
