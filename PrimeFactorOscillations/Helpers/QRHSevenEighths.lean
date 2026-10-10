/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import OAI.NumberTheory.DirichletL.Nonvanishing
import PrimeFactorOscillations.Helpers.LcmCutoffWindow

/-!
# The verified seven-eighths input and its modified-LCM consequences

The zeta and Dirichlet assertions below reuse the OAI source proof at commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, ported to the pinned Windows
Lean 4.34.0 environment. The source and artifact provenance is recorded in
data/analytic-artifacts-qrh-port.json. This is an attributed source port,
not a new proof of the seven-eighths zero-free region.

The two modified-LCM applications discharge the explicit strip hypothesis
of our signed-margin theorems. Their eventual cutoff is uniform in k;
both endpoint conventions retain the positive margin 1/200.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

theorem zeta_ne_zero (s : _root_.Complex) (hs : (7 / 8 : _root_.Real) < s.re) :
    Not (_root_.riemannZeta s = 0) :=
  OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs

theorem dirichletL_ne_zero (q : _root_.Nat) [_root_.NeZero q]
    (chi : _root_.DirichletCharacter _root_.Complex q) (s : _root_.Complex)
    (hs : (7 / 8 : _root_.Real) < s.re) (hpole : Not (chi = 1 /\ s = 1)) :
    Not (_root_.DirichletCharacter.LFunction chi s = 0) :=
  OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re chi hs hpole

theorem modifiedLcm_height_margin :
    Filter.Eventually (fun N : _root_.Nat => forall k : _root_.Real, forall hk : 1 < k,
      k <= lcmStripMovingExponent (7 / 8) 4 N ->
        1 / (200 * (N : Real) ^ (1 / 8 : Real) * Real.log (N : Real)) <
          Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N)))
      Filter.atTop :=
  eventually_modifiedLcm_seven_eighths_window
    (fun s hs _ => zeta_ne_zero s hs)

theorem modifiedLcm_cutoff_margin :
    Filter.Eventually (fun N : _root_.Nat => forall k : _root_.Real, forall hk : 1 < k,
      k <= (9 / 8 : Real) + 4 / Real.log (N : Real) ->
        1 / (200 * (N : Real) ^ (1 / 8 : Real) * Real.log (N : Real)) <
          Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N)))
      Filter.atTop :=
  eventually_modifiedLcm_seven_eighths_cutoff
    (fun s hs _ => zeta_ne_zero s hs)

end PrimeFactorOscillations.QRH
