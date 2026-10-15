/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFDivisorAverage
import PrimeFactorOscillations.Helpers.LPFKernelMoment

/-!
# Explicit averaged kernel and weighted-tail corrections

The complete finite target set is covered by the divisor-square prefix average.
Both correction packets retain their actual weights. No pointwise divisor-power
constant is introduced. The full major/minor source assembly and its numerical
entry threshold remain separate obligations.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_kernel_correction_mean_bound {N : Nat} [NeZero N]
    (H M P s L : Nat) (T : Finset Nat)
    (hH : 0 < H) (hM : 0 < M) (hP : 0 < P) (hDiv : Dvd.dvd M N)
    (hT : forall n, Membership.mem T n -> And (0 < n) (n <= H)) :
    Finset.sum T (fun n => norm (lpfIntervalKernelCorrection N M P s L n) ^ 2) <=
      (289 / 4 : Real) * (M : Real) ^ 2 * (H : Real) *
        (1 + Real.log (H : Real)) ^ 3 / (P : Real) ^ 2 := by
  have hMean := lpf_divisors_square_subset_mean_bound H T hH hT
  calc
    _ <= Finset.sum T (fun n =>
        (289 * (M : Real) ^ 2 / (4 * (P : Real) ^ 2)) * (n.divisors.card : Real) ^ 2) :=
      Finset.sum_le_sum (fun n hn =>
        lpfIntervalKernelCorrection_square_le M P s L n hM hP hDiv (hT n hn).1)
    _ = (289 * (M : Real) ^ 2 / (4 * (P : Real) ^ 2)) *
        Finset.sum T (fun n => (n.divisors.card : Real) ^ 2) :=
      (Finset.mul_sum _ _ _).symm
    _ <= (289 * (M : Real) ^ 2 / (4 * (P : Real) ^ 2)) *
        ((H : Real) * (1 + Real.log (H : Real)) ^ 3) :=
      mul_le_mul_of_nonneg_left hMean (by positivity)
    _ = _ := by ring

theorem lpf_kernel_correction_physical_mean_bound {N : Nat} [NeZero N]
    (M P s L : Nat) (T : Finset Nat)
    (hM : 0 < M) (hP : 0 < P) (hDiv : Dvd.dvd M N)
    (hT : forall n, Membership.mem T n -> And (0 < n) (n <= 2 * M)) :
    Finset.sum T (fun n => norm (lpfIntervalKernelCorrection N M P s L n) ^ 2) <=
      (289 / 2 : Real) * (M : Real) ^ 3 *
        (1 + Real.log (2 * (M : Real))) ^ 3 / (P : Real) ^ 2 := by
  have h := lpf_kernel_correction_mean_bound (2 * M) M P s L T (by omega) hM hP hDiv hT
  push_cast at h
  convert h using 1 <;> ring

theorem lpf_weighted_singular_tail_mean_bound
    (H M P : Nat) (T : Finset Nat) (w : Nat -> Complex)
    (hH : 0 < H) (hP : 1 <= P)
    (hT : forall n, Membership.mem T n -> And (0 < n) (n <= H))
    (hw : forall n, Membership.mem T n -> norm (w n) <= (M : Real)) :
    Finset.sum T (fun n =>
      norm (w n * (lpfSingularSeries n - lpfSingularPartial P n)) ^ 2) <=
      256 * (M : Real) ^ 2 * (H : Real) *
        (1 + Real.log (H : Real)) ^ 3 / (P : Real) := by
  have hMean := lpf_divisors_square_subset_mean_bound H T hH hT
  have hPoint (n : Nat) (hn : Membership.mem T n) :
      norm (w n * (lpfSingularSeries n - lpfSingularPartial P n)) ^ 2 <=
        (256 * (M : Real) ^ 2 / (P : Real)) * (n.divisors.card : Real) ^ 2 := by
    rw [norm_mul, mul_pow]
    have hW : norm (w n) ^ 2 <= (M : Real) ^ 2 := by
      have h := mul_le_mul (hw n hn) (hw n hn) (norm_nonneg _) (Nat.cast_nonneg M)
      simpa only [pow_two] using h
    have hTail := lpfSingularSeries_tail_square_le P n hP (hT n hn).1
    have hBound := mul_le_mul hW hTail (sq_nonneg _) (sq_nonneg (M : Real))
    convert hBound using 1 <;> ring
  calc
    _ <= Finset.sum T (fun n =>
        (256 * (M : Real) ^ 2 / (P : Real)) * (n.divisors.card : Real) ^ 2) :=
      Finset.sum_le_sum hPoint
    _ = (256 * (M : Real) ^ 2 / (P : Real)) *
        Finset.sum T (fun n => (n.divisors.card : Real) ^ 2) :=
      (Finset.mul_sum _ _ _).symm
    _ <= (256 * (M : Real) ^ 2 / (P : Real)) *
        ((H : Real) * (1 + Real.log (H : Real)) ^ 3) :=
      mul_le_mul_of_nonneg_left hMean (by positivity)
    _ = _ := by ring

theorem lpf_weighted_singular_tail_physical_mean_bound
    (M P : Nat) (T : Finset Nat) (w : Nat -> Complex)
    (hM : 0 < M) (hP : 1 <= P)
    (hT : forall n, Membership.mem T n -> And (0 < n) (n <= 2 * M))
    (hw : forall n, Membership.mem T n -> norm (w n) <= (M : Real)) :
    Finset.sum T (fun n =>
      norm (w n * (lpfSingularSeries n - lpfSingularPartial P n)) ^ 2) <=
      512 * (M : Real) ^ 3 * (1 + Real.log (2 * (M : Real))) ^ 3 / (P : Real) := by
  have h := lpf_weighted_singular_tail_mean_bound (2 * M) M P T w (by omega) hP hT hw
  push_cast at h
  convert h using 1 <;> ring

end PrimeFactorOscillations.LPF
