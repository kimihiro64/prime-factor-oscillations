/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# GeneralPrincipalExponents

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
# Exact endpoint checks for the principal correction

Scalar preflight for the actual exponents of V,R,W,D,K and every term
retained in the rational correction defect. This alone is not an analytic gain.
-/


namespace PrimeFactorOscillations.GeneralPrincipalRegion

theorem principal_coordinate_exponent_caps (x w z : Real)
    (hx : (3/4:Real)<=x) (hw : (9/10:Real)<=w) (hz : (4/25:Real)<=z) :
    -6*z<=-(24/25:Real) /\
    4-6*x-6*z<=-(73/50:Real) /\
    -w<=-(9/10:Real) /\
    -x<=-(3/4:Real) /\
    1-x-w<=-(13/20:Real) := by
  exact And.intro (by linarith) (And.intro (by linarith)
    (And.intro (by linarith) (And.intro (by linarith) (by linarith))))

theorem principal_defect_exponent_caps (x w z : Real)
    (hx : (3/4:Real)<=x) (hw : (9/10:Real)<=w) (hz : (4/25:Real)<=z) :
    4-6*x-6*z<=-(7/5:Real) /\
    (1-x-w)+(-6*z)<=-(7/5:Real) /\
    (-x)+(-6*z)<=-(7/5:Real) /\
    (-x)+(-w)<=-(7/5:Real) /\
    (-6*z)+(-w)<=-(7/5:Real) := by
  exact And.intro (by linarith) (And.intro (by linarith)
    (And.intro (by linarith) (And.intro (by linarith) (by linarith))))

end PrimeFactorOscillations.GeneralPrincipalRegion

