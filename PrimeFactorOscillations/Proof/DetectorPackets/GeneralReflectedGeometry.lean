/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Reflection.LowRetainedBudget

/-!
# GeneralLowEnergyExponent

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
# The complete reflected exponent with a variable slot budget

Generalizes the source's fixed one-sixth calculation while keeping every
retained-frequency and extraction term. The second theorem inserts the
actual tuple-count and compensation powers before drawing a conclusion.
Its consumer is the generalized physical low estimate, not a zero-free
theorem by itself.
-/


noncomputable section
namespace PrimeFactorOscillations.GeneralLowGeometry
open OAI.SevenEighths.InverseTerminalWidths
open OAI.SevenEighths.ProbeLowReflected

theorem compensated_reflected_exponent_general
    (Lambda d ell0 O0 H A0 N0 S0 B0 za v ell el theta eps : Real)
    (hd : 0<=d) (heps : 0<=eps)
    (hO : -eps<=O0) (hH : H<=(1-Lambda-2*d)-O0+eps)
    (hA : 2*A0<=O0+eps) (hN : 0<=N0) (hNA : N0<=A0)
    (hS : 0<=S0) (hB : 0<=B0) (hell : ell0<=Lambda-d+eps)
    (hz : za<=ell0+eps) (hv : -eps<=v) (hl : -eps<=ell)
    (he : -eps<=el) (htheta : abs theta<=eps)
    (hret : v+3*ell+el<=2*H+2*A0+2*za-1-ell0-theta-N0-3*B0+eps) :
    OAI.SevenEighths.InverseTerminalWidths.reflectedExponent O0 H S0 B0 za v ell el
      (2*H+2*A0+2*za-1-ell0-theta-N0-3*B0)<=
      (1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+40*eps := by
  let Td := 2*H+2*A0+2*za-1-ell0-theta-N0-3*B0
  have hthetaLo : -eps<=theta := (abs_le.mp htheta).1
  have hthetaHi : theta<=eps := (abs_le.mp htheta).2
  have hTd : Td<=H-3*d+6*eps := by dsimp [Td];linarith
  have hcol : v+ell<=H+10*eps := by dsimp [Td] at hTd;linarith
  have hmax : max H (v+ell)<=H+10*eps := max_le (by linarith) hcol
  have hk := le_max_left 0 (Td-v-3*ell-el)
  have hExtra0 : 0<=max 0 ((5*Lambda+d-1)/4) := le_max_left _ _
  have hExtra : (5*Lambda+d-1)/4<=max 0 ((5*Lambda+d-1)/4) :=
    le_max_right _ _
  by_cases hu : hybridSaving v za=za
  . unfold OAI.SevenEighths.InverseTerminalWidths.reflectedExponent
    rw [hu]
    change O0/2+max H (v+ell)-S0-B0+za-za-ell-2*el/3-
      max 0 (Td-v-3*ell-el)/2<=_
    linarith
  . have hhalf := hybrid_half_with_error hv heps hu
    have hquarter := retained_kernel_quarter Td (v+3*ell+el)
    have hcharge : Td/4-17*eps/12<=
        hybridSaving v za+ell+2*el/3+max 0 (Td-v-3*ell-el)/2 := by
      have heq : Td-(v+3*ell+el)=Td-v-3*ell-el := by ring
      rw [heq] at hquarter
      linarith
    have hbound : OAI.SevenEighths.InverseTerminalWidths.reflectedExponent O0 H S0 B0 za v ell el Td<=
        O0/2+H-S0-B0+za-Td/4+(10+17/12)*eps := by
      unfold OAI.SevenEighths.InverseTerminalWidths.reflectedExponent
      linarith
    change OAI.SevenEighths.InverseTerminalWidths.reflectedExponent O0 H S0 B0 za v ell el Td<=_
    apply hbound.trans
    dsimp [Td]
    linarith

theorem complete_compensation_reflected_cost
    (Lambda d ell0 O0 H A0 N0 S0 B0 za v ell el theta eps : Real)
    (hLambda : Lambda<=1/5) (hd : 0<=d) (heps : 0<=eps)
    (hO : -eps<=O0) (hH : H<=(1-Lambda-2*d)-O0+eps)
    (hA : 2*A0<=O0+eps) (hN : 0<=N0) (hNA : N0<=A0)
    (hS : 0<=S0) (hB : 0<=B0) (hell : ell0<=Lambda-d+eps)
    (hz : za<=ell0+eps) (hv : -eps<=v) (hl : -eps<=ell)
    (he : -eps<=el) (htheta : abs theta<=eps)
    (hret : v+3*ell+el<=2*H+2*A0+2*za-1-ell0-theta-N0-3*B0+eps) :
    -d+(OAI.SevenEighths.InverseTerminalWidths.reflectedExponent O0 H S0 B0 za v ell el
      (2*H+2*A0+2*za-1-ell0-theta-N0-3*B0)-(1-Lambda-2*d))/2<=
      -7*d/8+20*eps := by
  have hb := compensated_reflected_exponent_general
    Lambda d ell0 O0 H A0 N0 S0 B0 za v ell el theta eps
    hd heps hO hH hA hN hNA hS hB hell hz hv hl he htheta hret
  have hx : max 0 ((5*Lambda+d-1)/4)<=d/4 := max_le
    (by linarith) (by linarith)
  linarith

end PrimeFactorOscillations.GeneralLowGeometry
