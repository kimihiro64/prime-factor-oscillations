/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Proof.DetectorPackets.QuarticCompensatedLocal

/-!
# QuarticPrincipalResidue

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
# Exact principal residue probabilities for quartic compensation

These are real algebraic identities for the pole coordinates.
The Gaussian analytic residue formulas supplying the coordinates are
separate source inputs, not constructed by this module.
-/


noncomputable section
namespace PrimeFactorOscillations.QuarticPrincipalResidue

theorem pole_denominator_nonzero (P : Real) (hP : 1 < P) :
    Not (1-(1/P)^2 = 0) := by
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hi0 : 0 < 1/P := one_div_pos.mpr hP0
  have hi1 : 1/P < 1 := (div_lt_one hP0).mpr hP
  nlinarith

theorem marked_probability (P : Real) (hP : 1 < P) :
    (1/P-(1/P)^2)/(1-(1/P)^2) = 1/(P+1) := by
  have hP0 : Not (P = 0) := ne_of_gt (lt_trans zero_lt_one hP)
  have hP1 : Not (P+1 = 0) := by linarith
  have hd := pole_denominator_nonzero P hP
  apply (div_eq_iff hd).mpr
  field_simp [hP0, hP1]
  ring

theorem corrected_probability (P : Real) (hP : 1 < P) :
    (1-(1/P)^2)/(P+1)+(1/P)^2 = 1/P := by
  have hP0 : Not (P = 0) := ne_of_gt (lt_trans zero_lt_one hP)
  have hP1 : Not (P+1 = 0) := by linarith
  field_simp [hP0, hP1]
  ring

theorem corrected_product {I : Type} (S : Finset I) (P : I -> Real)
    (hP : forall i, Membership.mem S i -> 1 < P i) :
    S.prod (fun i => (1-(1/P i)^2)/(P i+1)+(1/P i)^2) =
      1/(S.prod P) := by
  calc
    _ = S.prod (fun i => 1/P i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact corrected_probability (P i) (hP i hi)
    _ = _ := by simp only [one_div, Finset.prod_inv_distrib]

theorem corrected_product_pos {I : Type} (S : Finset I) (P : I -> Real)
    (hP : forall i, Membership.mem S i -> 1 < P i) :
    0 < S.prod (fun i => (1-(1/P i)^2)/(P i+1)+(1/P i)^2) := by
  rw [corrected_product S P hP]
  exact one_div_pos.mpr (Finset.prod_pos (fun i hi =>
    lt_trans zero_lt_one (hP i hi)))

end PrimeFactorOscillations.QuarticPrincipalResidue

