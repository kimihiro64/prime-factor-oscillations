/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeCountLimit
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeCountingErrorAbel

/-!
# The actual zeta-zero supremum and its prime-count consumer

The nonempty zero set is proved from the existing entire Xi factorization.
No numerical zero certificate or zero-location assumption is used.
-/

set_option autoImplicit false
set_option Elab.async false

open Robin1984
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem riemannXi_two_eq_pi_div_six :
    Complex.riemannXi 2 = (Real.pi : Complex) / 6 := by
  have hGamma : Not (Complex.Gamma ((2 : Complex) / 2) = 0) := by
    norm_num [Complex.Gamma_one]
  have hHalf : (2 : Complex) / 2 = 1 := by norm_num
  have hNegHalf : -(2 : Complex) / 2 = -1 := by norm_num
  have hPi : Not ((Real.pi : Complex) = 0) := by
    exact_mod_cast Real.pi_ne_zero
  rw [Complex.riemannXi_eq_mul_completedRiemannZeta (by norm_num) (by norm_num),
    completedRiemannZeta_eq_cpow_mul_Gamma_mul_riemannZeta (by norm_num) hGamma,
    hNegHalf, hHalf, Complex.cpow_neg_one, Complex.Gamma_one, riemannZeta_two]
  field_simp [hPi]
  ring

theorem exists_riemannXi_zero :
    exists z : Complex, Complex.riemannXi z = 0 := by
  classical
  by_contra hMissing
  have hNo (z : Complex) : Not (Complex.riemannXi z = 0) := by
    intro hz
    exact hMissing (Exists.intro z hz)
  have : IsEmpty RiemannXiDivisorZeroIndex :=
    IsEmpty.mk (fun p => hNo (riemannXiDivisorZeroValue p)
      (riemannXiDivisorZeroValue_eq_zero p))
  have hProduct (z : Complex) :
      Complex.Hadamard.divisorCanonicalProduct 1 Complex.riemannXi Set.univ z = 1 := by
    unfold Complex.Hadamard.divisorCanonicalProduct
    simp
  choose P hDegree hFactor using riemannXi_hadamard_factorization_no_monomial
  have hExp (z : Complex) : Complex.riemannXi z = Complex.exp (P.eval z) := by
    rw [hFactor z, hProduct z, mul_one]
  have hPolynomial : P = Polynomial.C (P.coeff 0) +
      Polynomial.C (P.coeff 1) * Polynomial.X := by
    apply Polynomial.ext
    intro n
    by_cases hn0 : n = 0
    case pos =>
      subst n
      simp
    case neg =>
      by_cases hn1 : n = 1
      case pos =>
        subst n
        simp
      case neg =>
        have hn : 1 < n := by omega
        have hIndex : (1 : WithBot Nat) < (n : WithBot Nat) := by exact_mod_cast hn
        have hZero := Polynomial.coeff_eq_zero_of_degree_lt (hDegree.trans_lt hIndex)
        have hOneN : Not (1 = n) := Ne.symm hn1
        simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
          Polynomial.coeff_X, hn0, hOneN, hZero]
  have hEvaluation : P.eval (2 : Complex) + P.eval 0 = P.eval 1 + P.eval 1 := by
    rw [hPolynomial]
    simp
    ring
  have hIdentity := congrArg Complex.exp hEvaluation
  rw [Complex.exp_add, Complex.exp_add, <- hExp 2, <- hExp 0, <- hExp 1] at hIdentity
  have hOne : Complex.riemannXi 1 = (1 / 2 : Complex) := by
    simpa only [sub_zero, Complex.riemannXi_zero] using
      Complex.riemannXi_one_sub (0 : Complex)
  rw [Complex.riemannXi_zero, hOne] at hIdentity
  have hTwo : Complex.riemannXi 2 = (1 / 2 : Complex) := by
    have h := congrArg (fun z : Complex => z * 2) hIdentity
    convert h using 1 <;> ring
  rw [riemannXi_two_eq_pi_div_six] at hTwo
  have hReal := congrArg Complex.re hTwo
  norm_num at hReal
  have hPi := Real.pi_gt_three
  linarith only [hReal, hPi]

theorem exists_nontrivial_zeta_zero_re_ge_half :
    exists rho : Complex, And (riemannZeta rho = 0)
      (And (And (0 < rho.re) (rho.re < 1)) ((1 / 2 : Real) <= rho.re)) := by
  choose rho hXi using exists_riemannXi_zero
  have hZeta := (riemannXi_zero_iff_nontrivial_zeta_zero rho).mp hXi
  by_cases hHalf : (1 / 2 : Real) <= rho.re
  case pos =>
    exact Exists.intro rho (And.intro hZeta.1 (And.intro hZeta.2 hHalf))
  case neg =>
    have hReflected : Complex.riemannXi (1 - rho) = 0 :=
      (Complex.riemannXi_one_sub rho).trans hXi
    have hZetaReflected :=
      (riemannXi_zero_iff_nontrivial_zeta_zero (1 - rho)).mp hReflected
    refine Exists.intro (1 - rho)
      (And.intro hZetaReflected.1 (And.intro hZetaReflected.2 ?_))
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [lt_of_not_ge hHalf]

noncomputable def actualZetaZeroSupremum : Real :=
  sSup (Set.range (fun z : ZetaDistinctZero => z.val.re))

theorem actualZetaZeroSupremum_spec :
    And ((1 / 2 : Real) <= actualZetaZeroSupremum)
      (And (actualZetaZeroSupremum <= 1)
        (forall rho : Complex, riemannZeta rho = 0 ->
          And (0 < rho.re) (rho.re < 1) -> rho.re <= actualZetaZeroSupremum)) := by
  choose rho hZero hStrip hHalf using exists_nontrivial_zeta_zero_re_ge_half
  let z0 : ZetaDistinctZero := Subtype.mk rho (And.intro hZero hStrip)
  let S : Set Real := Set.range (fun z : ZetaDistinctZero => z.val.re)
  have hNonempty : Set.Nonempty S :=
    Exists.intro z0.val.re (Set.mem_range.mpr (Exists.intro z0 rfl))
  have hBdd : BddAbove S := by
    apply Exists.intro (1 : Real)
    intro y hy
    choose z hz using hy
    rw [<- hz]
    exact z.property.2.2.le
  have hOne : sSup S <= 1 := by
    apply csSup_le hNonempty
    intro y hy
    choose z hz using hy
    rw [<- hz]
    exact z.property.2.2.le
  have hUpper : forall w : Complex, riemannZeta w = 0 ->
      And (0 < w.re) (w.re < 1) -> w.re <= sSup S := by
    intro w hw hs
    apply le_csSup hBdd
    exact Set.mem_range.mpr (Exists.intro (Subtype.mk w (And.intro hw hs)) rfl)
  exact And.intro (hHalf.trans (hUpper rho hZero hStrip)) (And.intro hOne hUpper)

theorem primeCounting_error_bound_right_of_actual_zero_supremum
    (b : Real) (hb : actualZetaZeroSupremum < b) (hbOne : b < 1) :
    exists A : Real, And (0 < A) (forall x : Real, 2 <= x -> 1 <= Real.log x ->
      abs ((Nat.primeCounting (Nat.floor x) : Real) - primeLogarithmicIntegral x) <=
        A * x ^ b * Real.log x) := by
  have hSpec := actualZetaZeroSupremum_spec
  let eta : Real := (actualZetaZeroSupremum + b) / 2
  have hEtaHalf : (1 / 2 : Real) <= eta := by
    dsimp only [eta]
    linarith only [hSpec.1, hb]
  have hEtaOne : eta < 1 := by
    dsimp only [eta]
    linarith only [hb, hbOne]
  have hEtaB : eta < b := by
    dsimp only [eta]
    linarith only [hb]
  have hSupEta : actualZetaZeroSupremum <= eta := by
    dsimp only [eta]
    linarith only [hb]
  have hUpper (p : RiemannXiDivisorZeroIndex) :
      (riemannXiDivisorZeroValue p).re <= eta := by
    have hNative := (riemannXi_zero_iff_nontrivial_zeta_zero
      (riemannXiDivisorZeroValue p)).mp (riemannXiDivisorZeroValue_eq_zero p)
    exact (hSpec.2.2 _ hNative.1 hNative.2).trans hSupEta
  exact primeCounting_error_bound_of_uniform_zero_strip eta b
    hEtaHalf hEtaOne hEtaB hUpper

theorem primeCounting_error_bigO_right_of_actual_zero_supremum
    (b : Real) (hb : actualZetaZeroSupremum < b) (hbOne : b < 1) :
    Asymptotics.IsBigO Filter.atTop
      (fun x : Real =>
        (Nat.primeCounting (Nat.floor x) : Real) - primeLogarithmicIntegral x)
      (fun x : Real => x ^ b * (Real.log x) ^ 2) := by
  choose A hA hBound using
    primeCounting_error_bound_right_of_actual_zero_supremum b hb hbOne
  apply Asymptotics.IsBigO.of_bound A
  filter_upwards [Filter.eventually_ge_atTop (max 2 (Real.exp 1))] with x hx
  have hx2 : 2 <= x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith only [hx2]
  have hL : 1 <= Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hx)
    simpa only [Real.log_exp] using h
  have hLogSquare : Real.log x <= (Real.log x) ^ 2 := by nlinarith only [hL]
  have hPower : 0 <= x ^ b := Real.rpow_nonneg hx0.le b
  have hPay := mul_le_mul_of_nonneg_left hLogSquare (mul_nonneg hA.le hPower)
  have h := (hBound x hx2 hL).trans hPay
  have hWeight : 0 <= x ^ b * (Real.log x) ^ 2 := mul_nonneg hPower (sq_nonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hWeight, mul_assoc] using h

end PrimeFactorOscillations.PrimeClassDeletion
