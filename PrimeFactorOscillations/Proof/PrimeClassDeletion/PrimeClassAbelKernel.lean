/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.RightCutoffIntegral
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeWaveInitialRange

/-! # The exact logarithmic Abel kernel on the actual prime domain -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def primeClassAbelKernel (t : Real) : Real :=
  1 / (t * (Real.log t) ^ 2)

theorem primeClassAbelKernel_hasDerivAt (t : Real) (ht : 2 <= t) :
    HasDerivAt (fun y : Real => -(Inv.inv (Real.log y))) (primeClassAbelKernel t) t := by
  have ht0 : 0 < t := by linarith only [ht]
  have hl : 0 < Real.log t := Real.log_pos (by linarith only [ht])
  have h := ((Real.hasDerivAt_log ht0.ne').inv hl.ne').neg
  have hs : -(-(Inv.inv t) / (Real.log t) ^ 2) = primeClassAbelKernel t := by
    unfold primeClassAbelKernel
    field_simp
  rw [<- hs]
  exact h

theorem primeClassAbelKernel_continuousOn (a b : Real) (ha : 2 <= a) :
    ContinuousOn primeClassAbelKernel (Set.Icc a b) := by
  intro t ht
  have ht2 : 2 <= t := ha.trans ht.1
  have ht0 : 0 < t := by linarith only [ht2]
  have hl : 0 < Real.log t := Real.log_pos (by linarith only [ht2])
  exact (continuousAt_const.div
    (continuousAt_id.mul ((Real.continuousAt_log ht0.ne').pow 2))
    (mul_ne_zero ht0.ne' (pow_ne_zero 2 hl.ne'))).continuousWithinAt

theorem primeClassAbelKernel_intervalIntegrable (a b : Real)
    (ha : 2 <= a) (hab : a <= b) :
    IntervalIntegrable primeClassAbelKernel MeasureTheory.volume a b := by
  have h : ContinuousOn primeClassAbelKernel (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact primeClassAbelKernel_continuousOn a b ha
  exact h.intervalIntegrable

theorem primeClassAbelKernel_integral (p x : Real) (hp : 2 <= p) (hpx : p <= x) :
    intervalIntegral primeClassAbelKernel p x MeasureTheory.volume =
      1 / Real.log p - 1 / Real.log x := by
  have hderiv : forall t : Real, Membership.mem (Set.uIcc p x) t ->
      HasDerivAt (fun y : Real => -(Inv.inv (Real.log y))) (primeClassAbelKernel t) t := by
    intro t ht
    rw [Set.uIcc_of_le hpx] at ht
    exact primeClassAbelKernel_hasDerivAt t (hp.trans ht.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (primeClassAbelKernel_intervalIntegrable p x hp hpx)]
  simp only [one_div]
  ring

end PrimeFactorOscillations.PrimeClassDeletion
