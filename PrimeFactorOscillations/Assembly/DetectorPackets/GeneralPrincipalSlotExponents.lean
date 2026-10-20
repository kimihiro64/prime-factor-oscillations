/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.DetectorPackets.GeneralPrincipalExponents

/-!
# GeneralPrincipalSlotExponents

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Relative slot-error exponents

Exact scalar preflight for the marked error before and after the compensating
factor of norm Q^Re(s). The residue has a distinct endpoint.
-/


namespace PrimeFactorOscillations.GeneralPrincipalRegion

theorem principal_relative_exponent_caps (x w z : Real)
    (hx : (3/4:Real)<=x) (hw : (19/20:Real)<=w) (hz : (33/200:Real)<=z) :
    4-6*x-6*z<=-(37/50:Real) /\
    1-x-w-6*z<=-(37/50:Real) /\
    4-5*x-6*z<=-(37/50:Real) /\
    1-w-6*z<=-(37/50:Real) /\
    -6*z<=-(37/50:Real) /\
    -x<=-(37/50:Real) := by
  exact And.intro (by linarith) (And.intro (by linarith)
    (And.intro (by linarith) (And.intro (by linarith)
      (And.intro (by linarith) (by linarith)))))

theorem principal_residue_relative_exponent_caps (x : Real) (hx : (3/4:Real)<=x) :
    4-6*x-6*(1/6:Real)<=-(3/4:Real) /\
    1-x-1-6*(1/6:Real)<=-(3/4:Real) /\
    4-5*x-6*(1/6:Real)<=-(3/4:Real) /\
    1-1-6*(1/6:Real)<=-(3/4:Real) /\
    -6*(1/6:Real)<=-(3/4:Real) /\
    -x<=-(3/4:Real) := by
  exact And.intro (by linarith) (And.intro (by linarith)
    (And.intro (by linarith) (And.intro (by linarith)
      (And.intro (by linarith) (by linarith)))))

end PrimeFactorOscillations.GeneralPrincipalRegion

