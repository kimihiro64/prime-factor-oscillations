/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import BombieriVinogradov.Helpers.ComplexAnalysis.CauchyTaylor
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import PrimeFactorOscillations.Helpers.PrimeClassSamplingEuler

/-!
# The count-profile law is the Euler product's coefficient law

Uniform finite-product convergence transfers every Taylor coefficient.
The independent real coefficient limit constructed from actual samples
therefore equals the coefficient of the entire Euler product, with no
assumption identifying the two laws.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open BombieriVinogradov.ComplexAnalysis

theorem tendsto_primePrefix_range :
    Tendsto (fun Y : Nat => Finset.range (Y + 1)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro s
  filter_upwards [eventually_ge_atTop (s.sup (fun p => p))] with Y hY
  intro p hp
  have hs : p <= s.sup (fun q => q) := Finset.le_sup (f := fun q : Nat => q) hp
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hs.trans hY))

theorem finiteReference_euler_eval_tendstoUniformlyOn
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1)) (R : Real) :
    TendstoUniformlyOn (fun Y : Nat => fun z : Complex =>
      ((finiteReferencePolynomial (primeClassPrefix P Y)).map Complex.ofRealHom).eval z)
      (classEulerProfile P) atTop (Metric.closedBall (1 : Complex) R) := by
  have hfull := hasProdUniformlyOn_iff_tendstoUniformlyOn.mp
    (hasProdUniformlyOn_classEulerFactor P hsum R)
  have hseq : TendstoUniformlyOn
      (fun Y : Nat => fun z : Complex =>
        (Finset.range (Y + 1)).prod (fun p => classEulerFactor P p z))
      (classEulerProfile P) atTop (Metric.closedBall (1 : Complex) R) := by
    intro u hu
    exact tendsto_primePrefix_range.eventually (hfull u hu)
  have heq : (fun Y : Nat => fun z : Complex =>
      (Finset.range (Y + 1)).prod (fun p => classEulerFactor P p z)) =
      (fun Y : Nat => fun z : Complex =>
        ((finiteReferencePolynomial (primeClassPrefix P Y)).map Complex.ofRealHom).eval z) := by
    funext Y z
    exact ((finiteReference_euler_eval P Y z).trans
      (primeClassPrefix_prod_eulerFactor P Y z)).symm
  rw [heq] at hseq
  exact hseq

theorem iteratedDeriv_polynomial_eval (p : Polynomial Complex) (n : Nat) :
    iteratedDeriv n (fun z : Complex => p.eval z) =
      fun z => ((Polynomial.derivative^[n]) p).eval z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext z
      rw [Polynomial.deriv, Function.iterate_succ_apply']

theorem taylorCoefficient_polynomial_eval (p : Polynomial Complex) (k : Nat) :
    taylorCoefficient (fun z : Complex => p.eval z) 0 k = p.coeff k := by
  unfold taylorCoefficient
  rw [iteratedDeriv_polynomial_eval]
  change ((Polynomial.derivative^[k]) p).eval 0 / (k.factorial : Complex) = p.coeff k
  have heval : ((Polynomial.derivative^[k]) p).eval 0 =
      ((Polynomial.derivative^[k]) p).coeff 0 :=
    (Polynomial.coeff_zero_eq_eval_zero _).symm
  rw [heval, Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  have hk : Not ((k.factorial : Complex) = 0) :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp [hk]

theorem finiteReference_euler_taylor_tendsto
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1)) (k : Nat) :
    Tendsto (fun Y : Nat => taylorCoefficient (fun z : Complex =>
      ((finiteReferencePolynomial (primeClassPrefix P Y)).map Complex.ofRealHom).eval z) 0 k)
      atTop (nhds (taylorCoefficient (classEulerProfile P) 0 k)) := by
  have huniform := finiteReference_euler_eval_tendstoUniformlyOn P hsum 2
  have hprofile := differentiable_classEulerProfile P hsum
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hsmall := (Metric.tendstoUniformlyOn_iff.mp huniform)
    (epsilon / 2) (half_pos hepsilon)
  filter_upwards [hsmall] with Y hY
  let p := (finiteReferencePolynomial (primeClassPrefix P Y)).map Complex.ofRealHom
  have hpoly : Differentiable Complex (fun z : Complex => p.eval z) := p.differentiable
  have hbound : forall z : Complex, Membership.mem (Metric.sphere (0 : Complex) 1) z ->
      norm (p.eval z - classEulerProfile P z) <= epsilon / 2 := by
    intro z hz
    have hn : norm z = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    have hz2 : Membership.mem (Metric.closedBall (1 : Complex) 2) z := by
      apply Metric.mem_closedBall.mpr
      rw [dist_eq_norm]
      calc
        norm (z - 1) <= norm z + norm (1 : Complex) := norm_sub_le _ _
        _ = 2 := by rw [hn, norm_one]; norm_num
    rw [<- dist_eq_norm, dist_comm]
    exact (hY z hz2).le
  have hnorm := norm_taylorCoefficient_le k (by norm_num : (0 : Real) < 1)
    (hpoly.sub hprofile) hbound
  have hid : iteratedDeriv k (fun z : Complex => p.eval z - classEulerProfile P z) 0 =
      iteratedDeriv k (fun z : Complex => p.eval z) 0 -
        iteratedDeriv k (classEulerProfile P) 0 :=
    iteratedDeriv_fun_sub hpoly.contDiff.contDiffAt hprofile.contDiff.contDiffAt
  have hcoeff : taylorCoefficient (fun z : Complex => p.eval z - classEulerProfile P z) 0 k =
      taylorCoefficient (fun z : Complex => p.eval z) 0 k -
        taylorCoefficient (classEulerProfile P) 0 k := by
    unfold taylorCoefficient
    rw [hid, sub_div]
  change norm (taylorCoefficient
    (fun z : Complex => p.eval z - classEulerProfile P z) 0 k) <=
      epsilon / 2 / 1 ^ k at hnorm
  rw [hcoeff] at hnorm
  simp only [one_pow, div_one] at hnorm
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hnorm (by linarith)

theorem classEulerProfile_taylor_eq_limitingCoefficient
    (P : Set Nat) (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) (k : Nat) :
    taylorCoefficient (classEulerProfile P) 0 k = (limitingCoefficient P k : Complex) := by
  have hsum1 := classPowerWeight_one_summable P sigma hs1.le hsum
  have hproduct := finiteReference_euler_taylor_tendsto P hsum1 k
  have heq : (fun Y : Nat => taylorCoefficient (fun z : Complex =>
      ((finiteReferencePolynomial (primeClassPrefix P Y)).map Complex.ofRealHom).eval z) 0 k) =
      (fun Y : Nat =>
        ((finiteReferencePolynomial (primeClassPrefix P Y)).coeff k : Complex)) := by
    funext Y
    rw [taylorCoefficient_polynomial_eval, Polynomial.coeff_map]
    rfl
  rw [heq] at hproduct
  have hreal := finiteReference_coefficient_tendsto P sigma hs0 hs1 hsum k
  have hcomplex : Tendsto (fun Y : Nat =>
      ((finiteReferencePolynomial (primeClassPrefix P Y)).coeff k : Complex))
      atTop (nhds (limitingCoefficient P k : Complex)) :=
    (Complex.continuous_ofReal.tendsto (limitingCoefficient P k)).comp hreal
  exact tendsto_nhds_unique hproduct hcomplex

end PrimeFactorOscillations.PrimeClassSampling
