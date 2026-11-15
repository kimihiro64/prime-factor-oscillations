/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianScalingLogRemainder

/-! # The complete signed difference of the normalized permanent corrections

Only the analytic remainders are bounded separately. The actual difference
of the two first corrections retains its two-power saving.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_log_half_lipschitz (x y : Real) (hx : 1 / 2 <= x) (hy : 1 / 2 <= y) :
    abs (Real.log x - Real.log y) <= 2 * abs (x - y) := by
  let a := min x y
  let b := max x y
  have ha : (1 / 2 : Real) <= a := le_min hx hy
  have hPositive (t : Real) (ht : Membership.mem (Set.Icc a b) t) : 0 < t := by
    linarith only [ha, ht.1]
  have hDeriv (t : Real) (ht : Membership.mem (Set.Icc a b) t) :
      HasDerivAt Real.log (Inv.inv t) t :=
    Real.hasDerivAt_log (ne_of_gt (hPositive t ht))
  have hBound (t : Real) (ht : Membership.mem (Set.Icc a b) t) :
      norm (Inv.inv t) <= 2 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hPositive t ht))]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1 / 2) (le_trans ha ht.1)
    norm_num at h
    exact h
  have hxI : Membership.mem (Set.Icc a b) x :=
    And.intro (min_le_left x y) (le_max_left x y)
  have hyI : Membership.mem (Set.Icc a b) y :=
    And.intro (min_le_right x y) (le_max_right x y)
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hDeriv t ht).hasDerivWithinAt) hBound hyI hxI
  simpa only [Real.norm_eq_abs] using h

theorem hamiltonian_signed_correction_log_difference
    (qOld qNew eOld eNew c bOld bNew : Real)
    (hOld : 1 / 2 <= 1 + qOld + eOld) (hNew : 1 / 2 <= 1 + qNew + eNew)
    (hDifference : abs (qNew - qOld) <= c)
    (hErrorOld : abs eOld <= bOld) (hErrorNew : abs eNew <= bNew) :
    abs (Real.log (1 + qNew + eNew) - Real.log (1 + qOld + eOld)) <=
      2 * (c + bNew + bOld) := by
  have hErrors : abs (eNew + -eOld) <= bNew + bOld := by
    calc
      _ <= abs eNew + abs (-eOld) := abs_add_le _ _
      _ = abs eNew + abs eOld := by rw [abs_neg]
      _ <= _ := add_le_add hErrorNew hErrorOld
  have hFull : abs ((1 + qNew + eNew) - (1 + qOld + eOld)) <= c + bNew + bOld := by
    calc
      _ = abs ((qNew - qOld) + (eNew + -eOld)) := by congr 1; ring
      _ <= abs (qNew - qOld) + abs (eNew + -eOld) := abs_add_le _ _
      _ <= c + (bNew + bOld) := add_le_add hDifference hErrors
      _ = _ := by ring
  exact (hamiltonian_log_half_lipschitz _ _ hNew hOld).trans
    (mul_le_mul_of_nonneg_left hFull (by norm_num))

end PrimeFactorOscillations
