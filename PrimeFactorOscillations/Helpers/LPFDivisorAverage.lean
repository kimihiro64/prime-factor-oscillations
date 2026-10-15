/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMinorWeightedPacket

/-!
# Explicit averaged divisor-square bounds

The divisor-square sum is at most X*(1+log X)^3 for every positive X,
with coefficient one. Multiplicative factorization compares it with the
four-divisor convolution; exact finite convolution and harmonic identities
bound the complete prefix. No pointwise divisor-power constant is used.
The Type II, kernel and weighted-tail consumers are separate declarations.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_tau_convolution_prime_power (p e : Nat) (hp : Nat.Prime p) :
    ((ArithmeticFunction.sigma 0) (p ^ e)) ^ 2 <=
      (ArithmeticFunction.sigma 0 * ArithmeticFunction.sigma 0) (p ^ e) := by
  have hSum : (ArithmeticFunction.sigma 0 * ArithmeticFunction.sigma 0) (p ^ e) =
      Finset.sum (Finset.range (e + 1)) (fun j =>
        (ArithmeticFunction.sigma 0) (p ^ j) *
          (ArithmeticFunction.sigma 0) (p ^ e / p ^ j)) := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b =>
        (ArithmeticFunction.sigma 0) a * (ArithmeticFunction.sigma 0) b),
      Nat.divisors_prime_pow hp e, Finset.sum_map]
    rfl
  rw [hSum, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  have hTerm (j : Nat) (hj : Membership.mem (Finset.range (e + 1)) j) :
      e + 1 <= (ArithmeticFunction.sigma 0) (p ^ j) *
        (ArithmeticFunction.sigma 0) (p ^ e / p ^ j) := by
    have hje : j <= e := by have h := Finset.mem_range.mp hj; omega
    rw [Nat.pow_div hje hp.pos, ArithmeticFunction.sigma_zero_apply_prime_pow hp,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
    have hSub : j + (e - j) = e := by omega
    nlinarith only [hSub, Nat.zero_le (j * (e - j))]
  calc
    (e + 1) ^ 2 = Finset.sum (Finset.range (e + 1)) (fun _ => e + 1) := by
      simp [Finset.sum_const, Finset.card_range, pow_two]
    _ <= _ := Finset.sum_le_sum hTerm

theorem lpf_tau_square_convolution (n : Nat) :
    n.divisors.card ^ 2 <= (ArithmeticFunction.sigma 0 * ArithmeticFunction.sigma 0) n := by
  by_cases hn : n = 0
  . subst n
    simp
  . have hF : (ArithmeticFunction.sigma 0).IsMultiplicative :=
      ArithmeticFunction.isMultiplicative_sigma
    have hG := hF.mul hF
    rw [<- ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.IsMultiplicative.multiplicative_factorization
        (ArithmeticFunction.sigma 0) hF hn,
      ArithmeticFunction.IsMultiplicative.multiplicative_factorization
        (ArithmeticFunction.sigma 0 * ArithmeticFunction.sigma 0) hG hn]
    simp only [Finsupp.prod, <- Finset.prod_pow]
    apply Finset.prod_le_prod
    intro p hp
    have hpPrime : Nat.Prime p := by
      apply Nat.prime_of_mem_primeFactors
      rw [<- Nat.support_factorization]
      exact hp
    exact lpf_tau_convolution_prime_power p (n.factorization p) hpPrime

noncomputable def lpfReciprocalZeta : ArithmeticFunction Real :=
  ZeroHom.mk (fun n => 1 / (n : Real)) (by norm_num)

noncomputable def lpfTauReal : ArithmeticFunction Real :=
  ((ArithmeticFunction.sigma 0 : ArithmeticFunction Nat) : ArithmeticFunction Real)

theorem lpf_tau_real_apply (n : Nat) :
    lpfTauReal n = (n.divisors.card : Real) := by
  change ((ArithmeticFunction.sigma 0) n : Real) = (n.divisors.card : Real)
  rw [ArithmeticFunction.sigma_zero_apply]

theorem lpf_reciprocal_square_apply (n : Nat) :
    (lpfReciprocalZeta * lpfReciprocalZeta) n =
      (n.divisors.card : Real) / (n : Real) := by
  by_cases hn : n = 0
  . subst n
    simp
  . rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => lpfReciprocalZeta a * lpfReciprocalZeta b)]
    have hTerm (d : Nat) (hd : Membership.mem n.divisors d) :
        lpfReciprocalZeta d * lpfReciprocalZeta (n / d) = 1 / (n : Real) := by
      have hDvd := (Nat.mem_divisors.mp hd).1
      have hProd : d * (n / d) = n := by
        rw [Nat.mul_comm, Nat.div_mul_cancel hDvd]
      change (1 / (d : Real)) * (1 / ((n / d : Nat) : Real)) = 1 / (n : Real)
      rw [_root_.div_mul_div_comm, one_mul, <- Nat.cast_mul, hProd]
    calc
      _ = Finset.sum n.divisors (fun _ => 1 / (n : Real)) := Finset.sum_congr rfl hTerm
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul]

theorem lpf_tau_weighted_harmonic_bound (X : Nat) (hX : 0 < X) :
    Finset.sum (Finset.Ioc 0 X) (fun n => (n.divisors.card : Real) / (n : Real)) <=
      (1 + Real.log (X : Real)) ^ 2 := by
  let T := Finset.Ioc 0 X
  have hAll : Finset.sum T (fun n => (lpfReciprocalZeta * lpfReciprocalZeta) n) <=
      Finset.sum (T.product T) (fun x =>
        lpfReciprocalZeta x.1 * lpfReciprocalZeta x.2) := by
    rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro x hx hNot
    change 0 <= (1 / (x.1 : Real)) * (1 / (x.2 : Real))
    positivity
  have hProduct : Finset.sum (T.product T) (fun x =>
      lpfReciprocalZeta x.1 * lpfReciprocalZeta x.2) =
        (Finset.sum T (fun n => 1 / (n : Real))) ^ 2 := by
    have h := @Finset.sum_product Nat Real Nat inferInstance T T
      (fun x : Prod Nat Nat => lpfReciprocalZeta x.1 * lpfReciprocalZeta x.2)
    calc
      _ = Finset.sum T (fun n => Finset.sum T (fun m =>
          lpfReciprocalZeta n * lpfReciprocalZeta m)) := h
      _ = _ := by
        change Finset.sum T (fun n => Finset.sum T (fun m =>
          (1 / (n : Real)) * (1 / (m : Real)))) =
            (Finset.sum T (fun n => 1 / (n : Real))) ^ 2
        simp_rw [<- Finset.mul_sum, <- Finset.sum_mul]
        ring
  have hH := lpf_harmonic_Ioc_log_bound X hX
  have hHN : 0 <= Finset.sum T (fun n => 1 / (n : Real)) := by positivity
  have hHSq : (Finset.sum T (fun n => 1 / (n : Real))) ^ 2 <=
      (1 + Real.log (X : Real)) ^ 2 := by
    have hUpper : 0 <= 1 + Real.log (X : Real) := hHN.trans hH
    nlinarith only [hH, hHN, hUpper]
  simp_rw [lpf_reciprocal_square_apply] at hAll
  exact (hAll.trans_eq hProduct).trans hHSq

theorem lpf_tau_prefix_harmonic_bound (X Y : Nat) (hX : 0 < X) (hY : Y <= X) :
    Finset.sum (Finset.Ioc 0 Y) (fun n => lpfTauReal n) <=
      (Y : Real) * (1 + Real.log (X : Real)) := by
  have hCast := congrArg (fun z : Nat => (z : Real))
    (ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div Y)
  push_cast at hCast
  have hSum : Finset.sum (Finset.Ioc 0 Y) (fun n => lpfTauReal n) =
      Finset.sum (Finset.Ioc 0 Y) (fun n => ((Y / n : Nat) : Real)) := by
    exact hCast
  have hTerm (n : Nat) (hn : Membership.mem (Finset.Ioc 0 Y) n) :
      ((Y / n : Nat) : Real) <= (Y : Real) * (1 / (n : Real)) := by
    have hPos := (Finset.mem_Ioc.mp hn).1
    simpa only [div_eq_mul_inv, one_mul] using lpf_nat_div_cast_le Y n hPos
  have hSub : Finset.Ioc 0 Y <= Finset.Ioc 0 X := by
    intro n hn
    have h := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr (And.intro h.1 (h.2.trans hY))
  have hH : Finset.sum (Finset.Ioc 0 Y) (fun n => 1 / (n : Real)) <=
      1 + Real.log (X : Real) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hSub (fun n hn hNot => by positivity)).trans
      (lpf_harmonic_Ioc_log_bound X hX)
  calc
    _ = Finset.sum (Finset.Ioc 0 Y) (fun n => ((Y / n : Nat) : Real)) := hSum
    _ <= Finset.sum (Finset.Ioc 0 Y) (fun n => (Y : Real) * (1 / (n : Real))) :=
      Finset.sum_le_sum hTerm
    _ = (Y : Real) * Finset.sum (Finset.Ioc 0 Y) (fun n => 1 / (n : Real)) :=
      (Finset.mul_sum _ _ _).symm
    _ <= _ := mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg Y)

theorem lpf_tau_square_mean_bound (X : Nat) (hX : 0 < X) :
    Finset.sum (Finset.Ioc 0 X) (fun n => (n.divisors.card : Real) ^ 2) <=
      (X : Real) * (1 + Real.log (X : Real)) ^ 3 := by
  let f := lpfTauReal
  let H := 1 + Real.log (X : Real)
  have hLog : 0 <= Real.log (X : Real) := Real.log_nonneg
    (by exact_mod_cast (show 1 <= X by omega))
  have hH : 0 <= H := by dsimp [H]; linarith only [hLog]
  have hPoint (n : Nat) : (n.divisors.card : Real) ^ 2 <= (f * f) n := by
    have h : ((n.divisors.card ^ 2 : Nat) : Real) <=
        (((ArithmeticFunction.sigma 0 * ArithmeticFunction.sigma 0) n : Nat) : Real) :=
      Nat.cast_le.mpr (lpf_tau_square_convolution n)
    have hConv : (((ArithmeticFunction.sigma 0 * ArithmeticFunction.sigma 0) n : Nat) : Real) =
        (f * f) n := by
      simp only [ArithmeticFunction.mul_apply, Nat.cast_sum, Nat.cast_mul]
      rfl
    rw [hConv, Nat.cast_pow] at h
    exact h
  have hInner (n : Nat) (hn : Membership.mem (Finset.Ioc 0 X) n) :
      Finset.sum (Finset.Ioc 0 (X / n)) (fun m => f m) <=
        ((X : Real) / (n : Real)) * H := by
    have hFirst := lpf_tau_prefix_harmonic_bound X (X / n) hX (Nat.div_le_self X n)
    have hDiv := lpf_nat_div_cast_le X n (Finset.mem_Ioc.mp hn).1
    exact hFirst.trans (mul_le_mul_of_nonneg_right hDiv hH)
  have hWeighted := lpf_tau_weighted_harmonic_bound X hX
  calc
    _ <= Finset.sum (Finset.Ioc 0 X) (fun n => (f * f) n) :=
      Finset.sum_le_sum (fun n hn => hPoint n)
    _ = Finset.sum (Finset.Ioc 0 X) (fun n =>
        f n * Finset.sum (Finset.Ioc 0 (X / n)) (fun m => f m)) :=
      ArithmeticFunction.sum_Ioc_mul_eq_sum_sum f f X
    _ <= Finset.sum (Finset.Ioc 0 X) (fun n => f n * (((X : Real) / (n : Real)) * H)) := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left (hInner n hn)
      rw [lpf_tau_real_apply]
      positivity
    _ = (X : Real) * H * Finset.sum (Finset.Ioc 0 X)
        (fun n => (n.divisors.card : Real) / (n : Real)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [lpf_tau_real_apply]
      ring
    _ <= (X : Real) * H * H ^ 2 :=
      mul_le_mul_of_nonneg_left hWeighted (mul_nonneg (Nat.cast_nonneg X) hH)
    _ = _ := by dsimp [H]; ring

theorem lpf_divisors_square_subset_mean_bound (X : Nat) (T : Finset Nat)
    (hX : 0 < X) (hT : forall n, Membership.mem T n -> And (0 < n) (n <= X)) :
    Finset.sum T (fun n => (n.divisors.card : Real) ^ 2) <=
      (X : Real) * (1 + Real.log (X : Real)) ^ 3 := by
  have hSub : T <= Finset.Ioc 0 X := fun n hn => Finset.mem_Ioc.mpr (hT n hn)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hSub
    (fun n hn hNot => sq_nonneg _)).trans (lpf_tau_square_mean_bound X hX)

theorem lpfVaughanB_square_le_divisors (V n : Nat) :
    norm ((lpfVaughanB V n : Real) : Complex) ^ 2 <= (n.divisors.card : Real) ^ 2 := by
  have hAbs := abs_lpfVaughanB_le V n
  have hSq := mul_le_mul hAbs hAbs (abs_nonneg _) (Nat.cast_nonneg _)
  rw [Complex.norm_real, Real.norm_eq_abs]
  simpa only [pow_two] using hSq

theorem lpfVaughanB_square_sum_mean_bound (V C D : Nat) :
    Finset.sum (Finset.Ioc C D) (fun n => norm ((lpfVaughanB V n : Real) : Complex) ^ 2) <=
      (D : Real) * (1 + Real.log (D : Real)) ^ 3 := by
  by_cases hD : D = 0
  . subst D
    simp
  . have hDp : 0 < D := Nat.pos_of_ne_zero hD
    calc
      _ <= Finset.sum (Finset.Ioc C D) (fun n => (n.divisors.card : Real) ^ 2) :=
        Finset.sum_le_sum (fun n hn => lpfVaughanB_square_le_divisors V n)
      _ <= _ := lpf_divisors_square_subset_mean_bound D (Finset.Ioc C D) hDp (by
        intro n hn
        have h := Finset.mem_Ioc.mp hn
        exact And.intro (by omega) h.2)

theorem lpfVaughanB_square_sum_height_bound (V C D H : Nat)
    (hD : D <= H) (hH : 1 <= H) :
    Finset.sum (Finset.Ioc C D) (fun n => norm ((lpfVaughanB V n : Real) : Complex) ^ 2) <=
      (D : Real) * (1 + Real.log (H : Real)) ^ 3 := by
  have hBound := lpfVaughanB_square_sum_mean_bound V C D
  by_cases hDz : D = 0
  . subst D
    simpa using hBound
  . have hDp : (0 : Real) < (D : Real) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hDz)
    have hLogD : 0 <= Real.log (D : Real) :=
      Real.log_nonneg (by exact_mod_cast (show 1 <= D by omega))
    have hLog := Real.log_le_log hDp (Nat.cast_le.mpr hD)
    have hPower : (1 + Real.log (D : Real)) ^ 3 <= (1 + Real.log (H : Real)) ^ 3 := by
      gcongr
    exact hBound.trans (mul_le_mul_of_nonneg_left hPower (Nat.cast_nonneg D))

end PrimeFactorOscillations.LPF
