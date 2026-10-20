/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.DirichletPowerProbe

/-!
# PowerCompensationPoleCheck

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


namespace PrimeFactorOscillations.PowerCompensationPoleCheck

theorem main_identity (s d k : Complex)
    (hd : Not (d = 0)) (hOne : Not (s = 1))
    (hden : Not (s + d - 1 = 0)) :
    k / (s - 1) -
      s / (s + d - 1) * (k / ((s + d - 1) / d - 1)) =
        -k * (d - 1) / (s + d - 1) := by
  have hs : Not (s - 1 = 0) := sub_ne_zero.mpr hOne
  have hm : Not ((s + d - 1) / d - 1 = 0) := by
    intro h
    have heq : (s + d - 1) / d = 1 := sub_eq_zero.mp h
    have hmul := (div_eq_iff hd).mp heq
    apply hOne
    linear_combination hmul
  have hmap : (s + d - 1) / d - 1 = (s - 1) / d := by
    field_simp [hd] <;> ring
  have hinner : k / ((s + d - 1) / d - 1) = k * d / (s - 1) := by
    apply (div_eq_iff hm).mpr
    rw [hmap]
    field_simp [hd, hs] <;> ring
  rw [hinner]
  field_simp [hs, hden] <;> ring

theorem quadratic_identity (s k : Complex)
    (hOne : Not (s = 1)) (hden : Not (s + 1 = 0)) :
    k / (s - 1) - s / (s + 1) * (k / ((s + 1) / 2 - 1)) =
      -k / (s + 1) := by
  have heq : s + (2 : Complex) - 1 = s + 1 := by ring
  have hden' : Not (s + (2 : Complex) - 1 = 0) := by simpa only [heq] using hden
  simpa only [heq, show (2 : Complex) - 1 = 1 by norm_num, mul_one] using
    main_identity s 2 k (by norm_num) hOne hden'

theorem quartic_identity (s k : Complex)
    (hOne : Not (s = 1)) (hden : Not (s + 3 = 0)) :
    k / (s - 1) - s / (s + 3) * (k / ((s + 3) / 4 - 1)) =
      -k * 3 / (s + 3) := by
  have heq : s + (4 : Complex) - 1 = s + 3 := by ring
  have hden' : Not (s + (4 : Complex) - 1 = 0) := by simpa only [heq] using hden
  simpa only [heq, show (4 : Complex) - 1 = 3 by norm_num] using
    main_identity s 4 k (by norm_num) hOne hden'

end PrimeFactorOscillations.PowerCompensationPoleCheck
