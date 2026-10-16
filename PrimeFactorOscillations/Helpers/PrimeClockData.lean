/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClockTail
import PrimeFactorOscillations.Mathlib.Analysis.Analytic.ExponentialConvolution
import PrimeFactorOscillations.Mathlib.Analysis.Calculus.IteratedDeriv.LinearProduct

/-!
# Coefficient denominators for prime clocks

Finite elementary symmetric coefficients are compared with the entire reference at the exact arithmetic clock.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClockLaw

open Filter BombieriVinogradov.ComplexAnalysis

noncomputable def arithmeticClock (law : PrimeClockLaw) (N : Nat) : Real :=
  (primeProfilePrefixSet N).sum law.compensator

noncomputable def prefixEsymm (law : PrimeClockLaw) (N r : Nat) : Real :=
  ((primeProfilePrefixSet N).val.map law.weight).esymm r

noncomputable def densityRatio (law : PrimeClockLaw) (N r : Nat) : Real :=
  law.prefixEsymm N (r - 1) / law.prefixEsymm N r

noncomputable def referenceRatio (law : PrimeClockLaw) (r : Nat) (u : Real) : Real :=
  Nat.factorialConvolution law.realCoefficient (r - 1) u /
    Nat.factorialConvolution law.realCoefficient r u

theorem complexPrefix_mul_exp_clock (law : PrimeClockLaw) (N : Nat) (z : Complex) :
    law.complexPrefix N z * Complex.exp ((law.arithmeticClock N : Complex) * z) =
      (primeProfilePrefixSet N).prod (fun p => 1 + (law.weight p : Complex) * z) := by
  unfold complexPrefix complexFactor
  rw [Finset.prod_mul_distrib, <- Complex.exp_sum, mul_assoc, <- Complex.exp_add]
  have hsum : (primeProfilePrefixSet N).sum
      (fun p => -(law.compensator p : Complex) * z) =
      -(law.arithmeticClock N : Complex) * z := by
    rw [<- Finset.sum_mul, Finset.sum_neg_distrib]
    simp only [arithmeticClock, Complex.ofReal_sum]
  rw [hsum]
  simp

theorem prefix_factorialConvolution_eq_product_coefficient
    (law : PrimeClockLaw) (N r : Nat) :
    Nat.factorialConvolution
      (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r (law.arithmeticClock N) =
      (taylorCoefficient (fun z : Complex =>
        (primeProfilePrefixSet N).prod (fun p => 1 + (law.weight p : Complex) * z)) 0 r).re := by
  let B := law.arithmeticClock N
  have heq : (fun z : Complex => law.complexPrefix N z * Complex.exp ((B : Complex) * z)) =
      (fun z : Complex => (primeProfilePrefixSet N).prod
        (fun p => 1 + (law.weight p : Complex) * z)) := by
    funext z
    exact law.complexPrefix_mul_exp_clock N z
  have hconv := Complex.normalized_iteratedDeriv_mul_exp_zero
    (law.complexPrefix N) (law.differentiable_complexPrefix N) (B : Complex) r
  rw [heq] at hconv
  unfold taylorCoefficient
  rw [hconv]
  change _ = Complex.reAddGroupHom _
  rw [map_sum]
  simp only [Complex.coe_reAddGroupHom]
  unfold Nat.factorialConvolution
  apply Finset.sum_congr rfl
  intro j _
  have hcast : (B : Complex) ^ (r - j) / ((r - j).factorial : Complex) =
      Complex.ofReal (B ^ (r - j) / ((r - j).factorial : Real)) := by push_cast; rfl
  simp_rw [mul_div_assoc]
  rw [hcast]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rfl

theorem prefix_factorialConvolution_eq_esymm (law : PrimeClockLaw) (N r : Nat) :
    Nat.factorialConvolution
      (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r (law.arithmeticClock N) =
      law.prefixEsymm N r := by
  rw [law.prefix_factorialConvolution_eq_product_coefficient]
  unfold taylorCoefficient
  rw [Finset.normalized_iteratedDeriv_prod_linear_zero]
  have hmap : (primeProfilePrefixSet N).val.map (fun p => (law.weight p : Complex)) =
      ((primeProfilePrefixSet N).val.map law.weight).map Complex.ofRealHom := by
    rw [Multiset.map_map]
    rfl
  rw [hmap, <- RingHom.map_multiset_esymm]
  rfl

theorem densityRatio_eq_factorialConvolution (law : PrimeClockLaw) (N r : Nat) :
    law.densityRatio N r =
      Nat.factorialConvolution (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re)
          (r - 1) (law.arithmeticClock N) /
        Nat.factorialConvolution (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re)
          r (law.arithmeticClock N) := by
  rw [law.prefix_factorialConvolution_eq_esymm, law.prefix_factorialConvolution_eq_esymm]
  rfl

theorem abs_profile_secondMoment_le (law : PrimeClockLaw) (b t : Real)
    (hb : 0 <= b) (ht : 0 <= t) (htb : t <= b) :
    abs (tsum (fun j : Nat => law.realCoefficient j * t ^ j *
      ((j : Real) * (j - 1)))) <=
        tsum (fun j : Nat => (j : Real) ^ 2 * abs (law.realCoefficient j) * b ^ j) := by
  let bn : NNReal := { val := b, property := hb }
  have hrad : (bn : ENNReal) <
      (FormalMultilinearSeries.ofScalars Real law.realCoefficient).radius := by
    simp only [law.realCoefficient_radius_eq_top, ENNReal.coe_lt_top]
  have hs : Summable (fun j : Nat => (j : Real) ^ 2 *
      abs (law.realCoefficient j) * b ^ j) :=
    FormalMultilinearSeries.summable_nat_pow_mul_abs_of_lt_radius
      law.realCoefficient bn hrad 2
  have hmajor : forall j : Nat,
      norm (law.realCoefficient j * t ^ j * ((j : Real) * (j - 1))) <=
        (j : Real) ^ 2 * abs (law.realCoefficient j) * b ^ j := by
    intro j
    have hj : abs ((j : Real) * (j - 1)) <= (j : Real) ^ 2 := by
      cases j with
      | zero => simp
      | succ j =>
        simp only [Nat.cast_succ, add_sub_cancel_right]
        rw [abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg (j : Real)]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht j)]
    calc
      abs (law.realCoefficient j) * t ^ j *
          abs ((j : Real) * (j - 1)) <=
          abs (law.realCoefficient j) * b ^ j * (j : Real) ^ 2 := by
        gcongr
      _ = (j : Real) ^ 2 * abs (law.realCoefficient j) * b ^ j := by ring
  simpa only [Real.norm_eq_abs] using tsum_of_norm_bounded hs.hasSum hmajor

theorem exists_profile_normalized_coefficient_lower_bound (law : PrimeClockLaw)
    (b : Real) (hb : 0 <= b) :
    exists r0 : Nat, 0 < r0 /\ forall (r : Nat), r0 <= r ->
      forall (t : Real), 0 <= t -> t <= b ->
        law.positiveLowerBound b / 2 <=
            (Finset.range (r + 1)).sum (fun j =>
              law.realCoefficient j * t ^ j *
                ((r.descFactorial j : Real) / (r : Real) ^ j)) := by
  let bn : NNReal := { val := b, property := hb }
  have hrad : (bn : ENNReal) <
      (FormalMultilinearSeries.ofScalars Real law.realCoefficient).radius := by
    simp only [law.realCoefficient_radius_eq_top, ENNReal.coe_lt_top]
  obtain h := Nat.descFactorial_coefficient_uniform_error_of_radius
    law.realCoefficient bn hrad
  choose C hC herror using h
  let J := tsum (fun j : Nat => (j : Real) ^ 2 *
    abs (law.realCoefficient j) * b ^ j)
  have hJ : 0 <= J := tsum_nonneg (fun j => by positivity)
  let m := law.positiveLowerBound b
  have hm : 0 < m := Real.exp_pos _
  choose r0 hr0 using exists_nat_gt ((2 * C + J) / m)
  refine Exists.intro (r0 + 1) (And.intro (Nat.zero_lt_succ r0) ?_)
  intro r hr t ht htb
  have hrpos : 0 < r := (Nat.zero_lt_succ r0).trans_le hr
  have hrR : (0 : Real) < r := by exact_mod_cast hrpos
  have hr1 : (1 : Real) <= r := by exact_mod_cast hrpos
  have hr0R : (r0 : Real) <= r := by exact_mod_cast (Nat.le_succ r0).trans hr
  have hallow : 2 * C + J <= m * r := by
    have hc := mul_lt_mul_of_pos_right hr0 hm
    have hcancel : (2 * C + J) / m * m = 2 * C + J := by
      field_simp
    rw [hcancel] at hc
    nlinarith
  let tn : NNReal := { val := t, property := ht }
  have htn : tn <= bn := htb
  have he := herror r hrpos tn htn
  have hsum := (law.hasSum_realCoefficient t).tsum_eq
  have hmom := law.abs_profile_secondMoment_le b t hb ht htb
  have hprofile := law.complexProfile_re_lower_bound b t hb ht htb
  change m <= (law.complexProfile (t : Complex)).re at hprofile
  have hsmall : C / (r : Real) ^ 2 <= C / r := by
    apply div_le_div_of_nonneg_left hC hrR
    nlinarith
  have hmargin : C / (r : Real) + J / (2 * r) <= m / 2 := by
    have hc : C / (r : Real) * r = C := by field_simp
    have hj : J / (2 * (r : Real)) * (2 * r) = J := by field_simp
    apply le_of_mul_le_mul_right ?_ hrR
    nlinarith
  have hmom' : (tsum (fun j : Nat => law.realCoefficient j * t ^ j *
      ((j : Real) * (j - 1)))) / (2 * r) <= J / (2 * r) := by
    apply div_le_div_of_nonneg_right ((le_abs_self _).trans hmom)
    positivity
  change abs ((Finset.range (r + 1)).sum (fun j =>
      law.realCoefficient j * t ^ j *
        ((r.descFactorial j : Real) / (r : Real) ^ j)) -
      tsum (fun j : Nat => law.realCoefficient j * t ^ j) +
      (tsum (fun j : Nat => law.realCoefficient j * t ^ j *
        ((j : Real) * (j - 1)))) / (2 * r)) <= C / (r : Real) ^ 2 at he
  rw [hsum] at he
  have helow := (abs_le.mp he).1
  change m / 2 <= _
  linarith

open BombieriVinogradov.ComplexAnalysis

theorem exists_prefixProfile_normalized_errors (law : PrimeClockLaw) (b : Real) (hb : 0 <= b) :
    exists C D : Real, 0 <= C /\ 0 <= D /\
      forall N : Nat, 1 <= N -> forall r : Nat, 0 < r ->
      forall t : Real, 0 <= t -> t <= b ->
        norm ((Finset.range (r + 1)).sum (fun j =>
          (taylorCoefficient (law.complexPrefix N) 0 j -
            taylorCoefficient law.complexProfile 0 j) * (t : Complex) ^ j *
              ((r.descFactorial j : Complex) / (r : Complex) ^ j))) <= C / (N : Real) /\
        norm ((Finset.range (r + 1)).sum (fun j => (j : Complex) *
          (taylorCoefficient (law.complexPrefix N) 0 j -
            taylorCoefficient law.complexProfile 0 j) * (t : Complex) ^ (j - 1) *
              ((r.descFactorial j : Complex) / (r : Complex) ^ j))) <= D / (N : Real) := by
  let R := b + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hbR : b < R := by dsimp [R]; linarith
  have hden : 0 < 1 - b / R := sub_pos.mpr ((div_lt_one hR).mpr hbR)
  obtain h := law.exists_prefixProfile_taylor_error R hR
  choose A hA using h
  refine Exists.intro (A / (1 - b / R))
    (Exists.intro (A / (R * (1 - b / R) ^ 2)) ?_)
  refine And.intro (div_nonneg hA.1 hden.le)
    (And.intro (div_nonneg hA.1 (by positivity)) ?_)
  intro N hN r hr t ht htb
  let c : Nat -> Complex := fun j =>
    taylorCoefficient (law.complexPrefix N) 0 j - taylorCoefficient law.complexProfile 0 j
  have hc : forall j, norm (c j) <= (A / (N : Real)) / R ^ j := by
    intro j
    simpa only [div_div] using hA.2 N hN j
  have hAN : 0 <= A / (N : Real) := div_nonneg hA.1 (Nat.cast_nonneg N)
  have hv := Nat.norm_descFactorial_coefficient_le_geometric r hr c
    (A / (N : Real)) b R t hAN ht htb hbR hc
  have hd := Nat.norm_descFactorial_coefficient_deriv_le_geometric r hr c
    (A / (N : Real)) b R t hAN ht htb hbR hc
  have hvEq : (A / (N : Real)) / (1 - b / R) =
      (A / (1 - b / R)) / (N : Real) := by ring
  have hdEq : (A / (N : Real)) / (R * (1 - b / R) ^ 2) =
      (A / (R * (1 - b / R) ^ 2)) / (N : Real) := by ring
  rw [hvEq] at hv
  rw [hdEq] at hd
  exact And.intro hv hd

theorem exists_prefixProfile_real_normalized_errors (law : PrimeClockLaw) (b : Real) (hb : 0 <= b) :
    exists C D : Real, 0 <= C /\ 0 <= D /\
      forall N : Nat, 1 <= N -> forall r : Nat, 0 < r ->
      forall t : Real, 0 <= t -> t <= b ->
        abs (Nat.normalizedDescFactorialPolynomial
          (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r t -
            Nat.normalizedDescFactorialPolynomial law.realCoefficient r t) <=
              C / (N : Real) /\
        abs (deriv (Nat.normalizedDescFactorialPolynomial
          (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r) t -
            deriv (Nat.normalizedDescFactorialPolynomial law.realCoefficient r) t) <=
              D / (N : Real) := by
  obtain h := law.exists_prefixProfile_normalized_errors b hb
  choose C D hC hD hbound using h
  refine Exists.intro C (Exists.intro D (And.intro hC (And.intro hD ?_)))
  intro N hN r hr t ht htb
  have hc := hbound N hN r hr t ht htb
  let c : Nat -> Complex := fun j =>
    taylorCoefficient (law.complexPrefix N) 0 j - taylorCoefficient law.complexProfile 0 j
  have hreal (w : Complex) (m j : Nat) :
      (w * (t : Complex) ^ m *
        ((r.descFactorial j : Complex) / (r : Complex) ^ j)).re =
          w.re * t ^ m * ((r.descFactorial j : Real) / (r : Real) ^ j) := by
    have hw : ((r.descFactorial j : Complex) / (r : Complex) ^ j) =
        Complex.ofReal ((r.descFactorial j : Real) / (r : Real) ^ j) := by
      simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    rw [hw, <- Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hv : ((Finset.range (r + 1)).sum (fun j => c j * (t : Complex) ^ j *
      ((r.descFactorial j : Complex) / (r : Complex) ^ j))).re =
        Nat.normalizedDescFactorialPolynomial
          (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r t -
          Nat.normalizedDescFactorialPolynomial law.realCoefficient r t := by
    unfold Nat.normalizedDescFactorialPolynomial
    rw [Complex.re_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hreal]
    simp only [c, Complex.sub_re, realCoefficient]
    ring
  have hd : ((Finset.range (r + 1)).sum (fun j => (j : Complex) * c j *
      (t : Complex) ^ (j - 1) *
        ((r.descFactorial j : Complex) / (r : Complex) ^ j))).re =
        deriv (Nat.normalizedDescFactorialPolynomial
          (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r) t -
          deriv (Nat.normalizedDescFactorialPolynomial law.realCoefficient r) t := by
    rw [Nat.deriv_normalizedDescFactorialPolynomial,
      Nat.deriv_normalizedDescFactorialPolynomial,
      Complex.re_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hreal]
    simp only [c, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.sub_re, realCoefficient, zero_mul, sub_zero]
    ring
  have hvBound := (Complex.abs_re_le_norm
    ((Finset.range (r + 1)).sum (fun j => c j * (t : Complex) ^ j *
      ((r.descFactorial j : Complex) / (r : Complex) ^ j)))).trans hc.1
  have hdBound := (Complex.abs_re_le_norm
    ((Finset.range (r + 1)).sum (fun j => (j : Complex) * c j *
      (t : Complex) ^ (j - 1) *
        ((r.descFactorial j : Complex) / (r : Complex) ^ j)))).trans hc.2
  rw [hv] at hvBound
  rw [hd] at hdBound
  exact And.intro hvBound hdBound

end PrimeFactorOscillations.PrimeClockLaw
