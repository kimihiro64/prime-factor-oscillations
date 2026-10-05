/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeFactorOscillations.Helpers.PrimeProfileClockLimit
import PrimeNumberTheoremAnd.MediumPNT

/-!
# The theta-centered prime-profile clock

The unconditional prime number theorem and the finite Mertens product give
convergence of the inclusive prime-prefix clock to the theta-centered clock.
No Riemann-hypothesis premise is used.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Asymptotics

theorem primeProfile_theta_isEquivalent_id :
    Asymptotics.IsEquivalent Filter.atTop Chebyshev.theta (fun x : Real => x) := by
  choose c hc hmedium using MediumPNT
  have ht : Tendsto (fun x : Real => Real.log x ^ ((1 : Real) / 10))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 10)).comp
      Real.tendsto_log_atTop
  have hdecay : Tendsto
      (fun x : Real => Real.exp (-c * Real.log x ^ ((1 : Real) / 10)))
      atTop (nhds (0 : Real)) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (ht.const_mul_atTop hc)
  have hdecayLittle : Asymptotics.IsLittleO atTop
      (fun x : Real => Real.exp (-c * Real.log x ^ ((1 : Real) / 10)))
      (fun _ : Real => (1 : Real)) :=
    (Asymptotics.isLittleO_one_iff Real).mpr hdecay
  have hpsi : Asymptotics.IsLittleO atTop
      (Chebyshev.psi - id) (fun x : Real => x) := by
    apply hmedium.trans_isLittleO
    simpa only [mul_one] using
      (Asymptotics.isBigO_refl (fun x : Real => x) atTop).mul_isLittleO hdecayLittle
  have hsqrtBase : Asymptotics.IsLittleO atTop
      (fun _ : Real => (1 : Real)) Real.sqrt := by
    have hsqrtFunction : Real.sqrt =
        (fun x : Real => x ^ ((1 : Real) / 2)) := by
      funext x
      exact Real.sqrt_eq_rpow x
    rw [hsqrtFunction]
    simpa only [Real.rpow_zero] using
      isLittleO_log_rpow_rpow_atTop (0 : Real)
        (by norm_num : (0 : Real) < 1 / 2)
  have hsqrtProduct := hsqrtBase.mul_isBigO (Asymptotics.isBigO_refl Real.sqrt atTop)
  have hsqrt : Asymptotics.IsLittleO atTop Real.sqrt (fun x : Real => x) := by
    apply hsqrtProduct.congr'
    . filter_upwards [] with x
      simp
    . filter_upwards [eventually_ge_atTop (0 : Real)] with x hx
      simp only [Real.mul_self_sqrt hx]
  have hdiff := Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrt
  change Asymptotics.IsLittleO atTop
    (Chebyshev.theta - (fun x : Real => x)) (fun x : Real => x)
  apply (hpsi.sub hdiff).congr'
  . filter_upwards [] with x
    simp only [Pi.sub_apply, id_eq]
    ring
  . exact Filter.EventuallyEq.refl _ _

theorem tendsto_primeProfile_theta_ratio :
    Tendsto (fun N : Nat => Chebyshev.theta (N : Real) / (N : Real))
      atTop (nhds (1 : Real)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hequiv := primeProfile_theta_isEquivalent_id.comp_tendsto hn
  exact (Asymptotics.isEquivalent_iff_tendsto_one
    (hn.eventually_ne_atTop 0)).mp hequiv

theorem tendsto_primeProfile_theta_atTop :
    Tendsto (fun N : Nat => Chebyshev.theta (N : Real)) atTop atTop := by
  have hreal : Tendsto Chebyshev.theta atTop atTop :=
    primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id
  exact hreal.comp tendsto_natCast_atTop_atTop

theorem tendsto_primeProfile_thetaClock_atTop :
    Tendsto (fun N : Nat => Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta (N : Real)))) atTop atTop := by
  exact tendsto_const_nhds.add_atTop
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_primeProfile_theta_atTop))

theorem tendsto_primeProfile_loglogTheta_sub_loglog :
    Tendsto (fun N : Nat => Real.log (Real.log (Chebyshev.theta (N : Real))) -
        Real.log (Real.log (N : Real))) atTop (nhds (0 : Real)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlogN := Real.tendsto_log_atTop.comp hn
  have hlogTheta := Real.tendsto_log_atTop.comp tendsto_primeProfile_theta_atTop
  have hequiv := (primeProfile_theta_isEquivalent_id.comp_tendsto hn).log hn
  have hratio := (Asymptotics.isEquivalent_iff_tendsto_one
    (hlogN.eventually_ne_atTop 0)).mp hequiv
  have hlogRatio := hratio.log (by norm_num : Not ((1 : Real) = 0))
  have hfinal := hlogRatio.congr' (by
    filter_upwards [hlogTheta.eventually_ne_atTop 0,
      hlogN.eventually_ne_atTop 0] with N htheta hn0
    exact Real.log_div htheta hn0)
  simpa only [Function.comp_def, Real.log_one] using hfinal

theorem tendsto_primePrefixProfile_logSum_sub_thetaClock :
    Tendsto (fun N : Nat => (primeProfilePrefixSet N).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat))) -
      (Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta (N : Real)))))
      atTop (nhds (0 : Real)) := by
  have h := tendsto_primePrefixProfile_logSum_error.sub
    tendsto_primeProfile_loglogTheta_sub_loglog
  have heq :
      (fun N : Nat => (primeProfilePrefixSet N).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat))) -
          (Real.eulerMascheroniConstant +
            Real.log (Real.log (Chebyshev.theta (N : Real))))) =
      (fun N : Nat =>
        ((primeProfilePrefixSet N).sum
          (fun p => Real.log (1 + primeProfileWeight (p : Nat))) -
            Real.eulerMascheroniConstant - Real.log (Real.log (N : Real))) -
        (Real.log (Real.log (Chebyshev.theta (N : Real))) -
          Real.log (Real.log (N : Real)))) := by
    funext N
    ring
  rw [heq]
  simpa only [sub_self] using h

end PrimeFactorOscillations
