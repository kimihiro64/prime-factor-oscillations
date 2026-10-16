/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClockData

/-!
# Ratio bounds for prime clocks

Derivative and prefix-ratio estimates consume the exact prime-dependent compensator.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClockLaw

open Filter BombieriVinogradov.ComplexAnalysis

theorem exists_profile_normalized_derivative_bounds (law : PrimeClockLaw)
    (b : Real) (hb : 0 <= b) :
    exists M : Real, 0 <= M /\
      forall (r : Nat), 0 < r -> forall (t : Real), 0 <= t -> t <= b ->
        abs (deriv (Nat.normalizedDescFactorialPolynomial
          law.realCoefficient r) t) <= M /\
        abs (deriv (deriv (Nat.normalizedDescFactorialPolynomial
          law.realCoefficient r)) t) <= M := by
  let B := b + 1
  have hB : 1 <= B := by dsimp [B]; linarith
  have hB0 : 0 <= B := le_trans zero_le_one hB
  let Bn : NNReal := { val := B, property := hB0 }
  have hrad : (Bn : ENNReal) <
      (FormalMultilinearSeries.ofScalars Real law.realCoefficient).radius := by
    simp only [law.realCoefficient_radius_eq_top, ENNReal.coe_lt_top]
  have hs : Summable (fun j : Nat => (j : Real) ^ 2 *
      abs (law.realCoefficient j) * B ^ j) :=
    FormalMultilinearSeries.summable_nat_pow_mul_abs_of_lt_radius
      law.realCoefficient Bn hrad 2
  let M := tsum (fun j : Nat => (j : Real) ^ 2 *
    abs (law.realCoefficient j) * B ^ j)
  have hM : 0 <= M := tsum_nonneg (fun j => by positivity)
  refine Exists.intro M (And.intro hM ?_)
  intro r hr t ht htb
  have hrR : (0 : Real) < r := by exact_mod_cast hr
  have hkernel : forall j : Nat,
      0 <= (r.descFactorial j : Real) / (r : Real) ^ j /\
        (r.descFactorial j : Real) / (r : Real) ^ j <= 1 := by
    intro j
    refine And.intro (by positivity) ?_
    apply (div_le_one (pow_pos hrR j)).mpr
    exact_mod_cast Nat.descFactorial_le_pow r j
  have hpow : forall j d : Nat, t ^ (j - d) <= B ^ j := by
    intro j d
    have htB : t <= B := by dsimp [B]; linarith
    calc
      t ^ (j - d) <= B ^ (j - d) := by gcongr
      _ <= B ^ j := by
        gcongr
        first | assumption | omega
  have hmajor1 : forall j : Nat,
      norm ((j : Real) * law.realCoefficient j * t ^ (j - 1) *
        ((r.descFactorial j : Real) / (r : Real) ^ j)) <=
        (j : Real) ^ 2 * abs (law.realCoefficient j) * B ^ j := by
    intro j
    have hj : (j : Real) <= (j : Real) ^ 2 := by
      cases j with
      | zero => simp
      | succ j =>
        simp only [Nat.cast_succ]
        nlinarith [sq_nonneg (j : Real), (show (0 : Real) <= j from Nat.cast_nonneg j)]
    rw [Real.norm_eq_abs]
    simp only [abs_mul, abs_of_nonneg (show (0 : Real) <= j from Nat.cast_nonneg j),
      abs_of_nonneg (pow_nonneg ht (j - 1)), abs_of_nonneg (hkernel j).1]
    calc
      (j : Real) * abs (law.realCoefficient j) * t ^ (j - 1) *
          ((r.descFactorial j : Real) / (r : Real) ^ j) <=
          (j : Real) ^ 2 * abs (law.realCoefficient j) * B ^ j * 1 := by
        gcongr <;> first | exact hj | exact hpow j 1 | exact (hkernel j).2
      _ = (j : Real) ^ 2 * abs (law.realCoefficient j) * B ^ j := by ring
  have hmajor2 : forall j : Nat,
      norm ((j : Real) * ((j - 1 : Nat) : Real) * law.realCoefficient j *
        t ^ (j - 2) * ((r.descFactorial j : Real) / (r : Real) ^ j)) <=
        (j : Real) ^ 2 * abs (law.realCoefficient j) * B ^ j := by
    intro j
    have hprev : (((j - 1 : Nat) : Real)) <= j := by
      exact_mod_cast Nat.sub_le j 1
    have hj : (j : Real) * ((j - 1 : Nat) : Real) <= (j : Real) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hprev
        (show (0 : Real) <= j from Nat.cast_nonneg j)]
    rw [Real.norm_eq_abs]
    simp only [abs_mul, abs_of_nonneg (show (0 : Real) <= j from Nat.cast_nonneg j),
      abs_of_nonneg (show (0 : Real) <= ((j - 1 : Nat) : Real) from Nat.cast_nonneg (j - 1)),
      abs_of_nonneg (pow_nonneg ht (j - 2)), abs_of_nonneg (hkernel j).1]
    calc
      (j : Real) * ((j - 1 : Nat) : Real) * abs (law.realCoefficient j) *
          t ^ (j - 2) * ((r.descFactorial j : Real) / (r : Real) ^ j) <=
          (j : Real) ^ 2 * abs (law.realCoefficient j) * B ^ j * 1 := by
        gcongr <;> first | exact hj | exact hpow j 2 | exact (hkernel j).2
      _ = (j : Real) ^ 2 * abs (law.realCoefficient j) * B ^ j := by ring
  have hsum : (Finset.range (r + 1)).sum (fun j : Nat =>
      (j : Real) ^ 2 * abs (law.realCoefficient j) * B ^ j) <= M :=
    sum_le_hasSum (Finset.range (r + 1)) (fun j _ => by positivity) hs.hasSum
  constructor
  . rw [Nat.deriv_normalizedDescFactorialPolynomial]
    have hn := (norm_sum_le (Finset.range (r + 1))
      (fun j => (j : Real) * law.realCoefficient j * t ^ (j - 1) *
        ((r.descFactorial j : Real) / (r : Real) ^ j))).trans
      ((Finset.sum_le_sum (fun j _ => hmajor1 j)).trans hsum)
    simpa only [Real.norm_eq_abs] using hn
  . rw [Nat.deriv_deriv_normalizedDescFactorialPolynomial]
    have hn := (norm_sum_le (Finset.range (r + 1))
      (fun j => (j : Real) * ((j - 1 : Nat) : Real) * law.realCoefficient j *
        t ^ (j - 2) * ((r.descFactorial j : Real) / (r : Real) ^ j))).trans
      ((Finset.sum_le_sum (fun j _ => hmajor2 j)).trans hsum)
    simpa only [Real.norm_eq_abs] using hn

theorem exists_profile_reference_slope_bound (law : PrimeClockLaw) (b : Real) (hb : 0 <= b) :
    exists (r0 : Nat) (K : Real), 0 < r0 /\ 0 <= K /\
      forall (r : Nat), r0 <= r -> forall (u : Real), 0 < u -> (r : Real) / u <= b ->
        abs (deriv (fun v : Real =>
          Nat.factorialConvolution law.realCoefficient (r - 1) v /
            Nat.factorialConvolution law.realCoefficient r v) u +
              (r : Real) / u ^ 2) <= K / u ^ 2 /\
        (2 * K <= r ->
          -(3 * (r : Real)) / (2 * u ^ 2) <=
            deriv (fun v : Real =>
              Nat.factorialConvolution law.realCoefficient (r - 1) v /
                Nat.factorialConvolution law.realCoefficient r v) u /\
          deriv (fun v : Real =>
            Nat.factorialConvolution law.realCoefficient (r - 1) v /
              Nat.factorialConvolution law.realCoefficient r v) u <=
                -(r : Real) / (2 * u ^ 2)) := by
  choose r0 hr0 hLower using law.exists_profile_normalized_coefficient_lower_bound b hb
  choose M hM hDeriv using law.exists_profile_normalized_derivative_bounds b hb
  let d := law.positiveLowerBound b / 2
  have hd : 0 < d := half_pos (law.positiveLowerBound_pos b)
  let Q := M / d
  have hQ : 0 <= Q := div_nonneg hM hd.le
  let K := 2 * b * Q + b ^ 2 * (Q + Q ^ 2)
  have hK : 0 <= K := by dsimp [K]; positivity
  refine Exists.intro r0 (Exists.intro K (And.intro hr0 (And.intro hK ?_)))
  intro r hr u hu htb
  have hrpos : 0 < r := hr0.trans_le hr
  have ht : 0 <= (r : Real) / u := div_nonneg (Nat.cast_nonneg r) hu.le
  have hA := hLower r hr ((r : Real) / u) ht htb
  change d <= Nat.normalizedDescFactorialPolynomial law.realCoefficient r
    ((r : Real) / u) at hA
  have hD := hDeriv r hrpos ((r : Real) / u) ht htb
  have he := Nat.abs_deriv_factorialConvolution_ratio_add_le
    law.realCoefficient r hrpos u b d M hu htb hd hM hA hD.1 hD.2
  change abs (deriv (fun v : Real =>
    Nat.factorialConvolution law.realCoefficient (r - 1) v /
      Nat.factorialConvolution law.realCoefficient r v) u +
        (r : Real) / u ^ 2) <= K / u ^ 2 at he
  refine And.intro he ?_
  intro hRank
  have hPayment : K / u ^ 2 <= (r : Real) / (2 * u ^ 2) := by
    calc
      K / u ^ 2 <= ((r : Real) / 2) / u ^ 2 := by
        apply div_le_div_of_nonneg_right
        . linarith
        . exact sq_nonneg u
      _ = (r : Real) / (2 * u ^ 2) := by ring
  have hSigned := abs_le.mp he
  have hScale : (r : Real) / u ^ 2 = 2 * ((r : Real) / (2 * u ^ 2)) := by ring
  have hThree : -(3 * (r : Real)) / (2 * u ^ 2) =
      -(r : Real) / u ^ 2 - (r : Real) / (2 * u ^ 2) := by ring
  constructor
  . rw [hThree, neg_div]
    linarith only [hSigned.1, hPayment]
  . rw [neg_div]
    linarith only [hSigned.2, hPayment, hScale]

open BombieriVinogradov.ComplexAnalysis

theorem exists_prefixProfile_factorialConvolution_ratio_error (law : PrimeClockLaw)
    (b : Real) (hb : 0 <= b) :
    exists r0 N0 : Nat, exists K : Real,
      0 < r0 /\ 1 <= N0 /\ 0 <= K /\
      forall r : Nat, r0 <= r -> forall N : Nat, N0 <= N ->
      forall u : Real, 0 < u -> (r : Real) / u <= b ->
        0 < Nat.factorialConvolution
          (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r u /\
        0 < Nat.factorialConvolution law.realCoefficient r u /\
        abs (Nat.factorialConvolution
            (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) (r - 1) u /
          Nat.factorialConvolution
            (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r u -
          Nat.factorialConvolution law.realCoefficient (r - 1) u /
            Nat.factorialConvolution law.realCoefficient r u) <=
          K / ((r : Real) * (N : Real)) := by
  obtain he := law.exists_prefixProfile_real_normalized_errors b hb
  choose C D hC hD herror using he
  obtain hd := law.exists_profile_normalized_derivative_bounds b hb
  choose M hM hderiv using hd
  obtain hl := law.exists_profile_normalized_coefficient_lower_bound b hb
  choose r0 hr0 hlower using hl
  let m := law.positiveLowerBound b
  let d := m / 4
  have hm : 0 < m := Real.exp_pos _
  have hd : 0 < d := by dsimp [d]; positivity
  let Q := D / d + M * C / (d * d)
  have hQ : 0 <= Q := by dsimp [Q]; positivity
  choose n0 hn0 using exists_nat_gt (C / d)
  refine Exists.intro r0 (Exists.intro (n0 + 1) (Exists.intro (b ^ 2 * Q)
    (And.intro hr0 (And.intro (Nat.succ_le_succ (Nat.zero_le n0))
      (And.intro (mul_nonneg (sq_nonneg b) hQ) ?_)))))
  intro r hr N hN u hu htb
  have hrpos : 0 < r := hr0.trans_le hr
  have hrR : (0 : Real) < r := by exact_mod_cast hrpos
  have hNpos : 0 < N := (Nat.zero_lt_succ n0).trans_le hN
  have hNR : (0 : Real) < N := by exact_mod_cast hNpos
  have hN1 : 1 <= N := hNpos
  let t := (r : Real) / u
  have ht : 0 <= t := (div_pos hrR hu).le
  have htbound : t <= b := htb
  let cN : Nat -> Real := fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re
  let A := Nat.normalizedDescFactorialPolynomial law.realCoefficient r t
  let AN := Nat.normalizedDescFactorialPolynomial cN r t
  let V := deriv (Nat.normalizedDescFactorialPolynomial law.realCoefficient r) t
  let VN := deriv (Nat.normalizedDescFactorialPolynomial cN r) t
  have herror' := herror N hN1 r hrpos t ht htbound
  change abs (AN - A) <= C / (N : Real) /\
    abs (VN - V) <= D / (N : Real) at herror'
  have hV : abs V <= M := (hderiv r hrpos t ht htbound).1
  have hA : m / 2 <= A := hlower r hr t ht htbound
  have hnN : (n0 : Real) < N := by
    exact_mod_cast (Nat.lt_succ_self n0).trans_le hN
  have hsmall : C / (N : Real) <= d := by
    have hc := mul_lt_mul_of_pos_right (hn0.trans hnN) hd
    have hcancel : C / d * d = C := by field_simp
    rw [hcancel] at hc
    apply le_of_mul_le_mul_right ?_ hNR
    have hcancelN : C / (N : Real) * N = C := by field_simp
    rw [hcancelN]
    nlinarith
  have hdA : d <= A := by dsimp [d]; linarith
  have hdAN : d <= AN := by
    have herr := (abs_le.mp herror'.1).1
    change m / 4 <= AN
    change C / (N : Real) <= m / 4 at hsmall
    linarith
  have hApos : 0 < A := hd.trans_le hdA
  have hANpos : 0 < AN := hd.trans_le hdAN
  have hquot : abs (VN / AN - V / A) <= Q / (N : Real) := by
    have hid : VN / AN - V / A =
        (VN - V) / AN + V * (A - AN) / (AN * A) := by
      field_simp [hANpos.ne', hApos.ne']
      ring
    have hprod : d * d <= AN * A := mul_le_mul hdAN hdA hd.le hANpos.le
    have hfirst : abs ((VN - V) / AN) <= (D / (N : Real)) / d := by
      rw [abs_div, abs_of_pos hANpos]
      exact (div_le_div_of_nonneg_right herror'.2 hANpos.le).trans
        (div_le_div_of_nonneg_left (div_nonneg hD hNR.le) hd hdAN)
    have hsecond : abs (V * (A - AN) / (AN * A)) <=
        (M * (C / (N : Real))) / (d * d) := by
      rw [abs_div, abs_mul, abs_sub_comm A AN, abs_of_pos (mul_pos hANpos hApos)]
      have hnum : abs V * abs (AN - A) <= M * (C / (N : Real)) :=
        mul_le_mul hV herror'.1 (abs_nonneg _) hM
      exact (div_le_div_of_nonneg_right hnum (mul_nonneg hANpos.le hApos.le)).trans
        (div_le_div_of_nonneg_left (by positivity) (mul_pos hd hd) hprod)
    calc
      abs (VN / AN - V / A) <=
          abs ((VN - V) / AN) + abs (V * (A - AN) / (AN * A)) := by
        rw [hid]
        exact abs_add_le _ _
      _ <= (D / (N : Real)) / d + (M * (C / (N : Real))) / (d * d) :=
        add_le_add hfirst hsecond
      _ = Q / (N : Real) := by dsimp [Q]; ring
  have hfront : 0 < u ^ r / (r.factorial : Real) := by positivity
  have hfinitePos : 0 < Nat.factorialConvolution cN r u := by
    rw [Nat.factorialConvolution_eq_normalizedDescFactorialPolynomial cN r hrpos u hu.ne']
    exact mul_pos hfront hANpos
  have hinfinitePos : 0 < Nat.factorialConvolution law.realCoefficient r u := by
    rw [Nat.factorialConvolution_eq_normalizedDescFactorialPolynomial
      law.realCoefficient r hrpos u hu.ne']
    exact mul_pos hfront hApos
  refine And.intro hfinitePos (And.intro hinfinitePos ?_)
  rw [Nat.factorialConvolution_ratio_eq_normalized_logDeriv cN r hrpos u hu.ne' hANpos.ne',
    Nat.factorialConvolution_ratio_eq_normalized_logDeriv
      law.realCoefficient r hrpos u hu.ne' hApos.ne']
  change abs ((t - (t ^ 2 / r) * VN / AN) - (t - (t ^ 2 / r) * V / A)) <=
    b ^ 2 * Q / ((r : Real) * (N : Real))
  have hid : (t - (t ^ 2 / r) * VN / AN) - (t - (t ^ 2 / r) * V / A) =
      -(t ^ 2 / r) * (VN / AN - V / A) := by ring
  rw [hid, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (sq_nonneg t) hrR.le)]
  calc
    t ^ 2 / (r : Real) * abs (VN / AN - V / A) <=
        b ^ 2 / (r : Real) * (Q / (N : Real)) := by
      apply mul_le_mul _ hquot (abs_nonneg _) (by positivity)
      apply div_le_div_of_nonneg_right _ hrR.le
      nlinarith
    _ = b ^ 2 * Q / ((r : Real) * (N : Real)) := by ring

open BombieriVinogradov.ComplexAnalysis

end PrimeFactorOscillations.PrimeClockLaw
