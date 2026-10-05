/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasDiscretePeak
import PrimeFactorOscillations.Mathlib.Order.Interval.Finset.NatPeaks

/-!
# Reciprocal excursion transfer for Nicolas's logarithm

A finite positive maximum of the theta tail minus a reciprocal amplitude
controls the nonlinear height remainder. Unbounded positive tail amplitudes
and recurring negative values therefore force unbounded positive amplitudes
of the actual Nicolas logarithm. The analytic tail-excursion hypotheses remain
explicit; this module does not assume or conclude RH.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Robin1984

theorem nicolasLog_lower_of_adjacent_peak
    (n : Nat) (hn : 2 <= n) (A : Real) (hA : 0 < A)
    (hLeft : nicolasK (n : Real) - A / (n : Real) <=
      nicolasK ((n : Real) + 1) - A / ((n : Real) + 1))
    (hRight : nicolasK ((n : Real) + 2) - A / ((n : Real) + 2) <=
      nicolasK ((n : Real) + 1) - A / ((n : Real) + 1)) :
    nicolasK ((n : Real) + 1) -
      (2 * A + 1) ^ 2 * (Real.log ((n : Real) + 1) + 1) /
        (2 * ((n : Real) + 1) ^ 2) <=
      nicolasLogMertensOscillation ((n : Real) + 1) := by
  have hnReal : (2 : Real) <= (n : Real) := by exact_mod_cast hn
  have hLoss := nicolasRemainder_le_of_adjacent_peak n hn A hA hLeft hRight
  have hEuler := nicolasMertensSummandRemainder_nonneg ((n : Real) + 1)
  rw [nicolasLogMertensOscillation_eq_components (by linarith)]
  linarith

/-- Unbounded reciprocal positive excursions of the actual theta tail,
together with arbitrarily late negative values, force unbounded positive
reciprocal excursions of the actual finite Nicolas logarithm. -/
theorem nicolasLog_scaled_unbounded_of_K_integer_excursions
    (hPositive : forall A : Real, 0 < A -> forall N : Nat,
      exists n : Nat, N <= n /\ A / (n : Real) < nicolasK (n : Real))
    (hNegative : forall N : Nat,
      exists n : Nat, N <= n /\ nicolasK (n : Real) < 0)
    (C : Real) (N : Nat) :
    exists m : Nat, N <= m /\
      C < (m : Real) * nicolasLogMertensOscillation (m : Real) := by
  let A : Real := max C 0 + 1
  have hA : 0 < A := by
    dsimp [A]
    linarith [le_max_right C 0]
  have hReserve : C + 1 <= A := by
    dsimp [A]
    linarith [le_max_left C 0]
  let B : Real := 2 * A + 1
  let g : Nat -> Real := fun n => nicolasK (n : Real) - A / (n : Real)
  have hPos : forall T : Nat, exists n : Nat, T <= n /\ 0 < g n := by
    intro T
    choose n hn hk using hPositive A hA T
    exact Exists.intro n (And.intro hn (sub_pos.mpr hk))
  have hNeg : forall T : Nat, exists n : Nat, T <= n /\ g n < 0 := by
    intro T
    choose n hn hk using hNegative T
    have hDiv : 0 <= A / (n : Real) := div_nonneg hA.le (Nat.cast_nonneg n)
    exact Exists.intro n (And.intro hn (by dsimp [g]; linarith))
  choose j hj using exists_nat_gt (B ^ 4)
  choose n hn hnTwo hPeak hLeft hRight using
    Nat.exists_ge_pos_adjacent_max_of_unbounded_signs g hPos hNeg (max N j)
  have hN : N <= n := le_trans (le_max_left N j) hn
  have hjn : j <= n := le_trans (le_max_right N j) hn
  have hnReal : (2 : Real) <= (n : Real) := by exact_mod_cast hnTwo
  have hjnReal : (j : Real) <= (n : Real) := by exact_mod_cast hjn
  dsimp [g] at hPeak hLeft hRight
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hPeak hLeft hRight
  let m : Real := (n : Real) + 1
  have hmPos : 0 < m := by dsimp [m]; linarith
  have hLarge : B ^ 4 < m := by dsimp [m]; linarith
  let U : Real := B ^ 2 * (Real.log m + 1) / (2 * m ^ 2)
  have hLower := nicolasLog_lower_of_adjacent_peak n hnTwo A hA hLeft hRight
  change nicolasK m - U <= nicolasLogMertensOscillation m at hLower
  have hsPos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmPos
  have hsSq : (Real.sqrt m) ^ 2 = m := Real.sq_sqrt hmPos.le
  have hLog := Real.log_le_sub_one_of_pos hsPos
  have hLogPow := Real.log_pow (Real.sqrt m) 2
  rw [hsSq] at hLogPow
  norm_num at hLogPow
  have hLogBound : Real.log m + 1 <= 2 * Real.sqrt m := by linarith
  have hBNonneg : 0 <= B ^ 2 := sq_nonneg B
  have hSmall : B ^ 2 < Real.sqrt m := by
    by_contra hNot
    have hOpp : Real.sqrt m <= B ^ 2 := le_of_not_gt hNot
    have hSquares := mul_self_le_mul_self hsPos.le hOpp
    nlinarith
  have hNumerator := mul_le_mul_of_nonneg_left hLogBound hBNonneg
  have hProduct := mul_lt_mul_of_pos_right hSmall hsPos
  have hLoss : U < 1 / m := by
    by_contra hNot
    have hOpp : 1 / m <= U := le_of_not_gt hNot
    have hOppScaled := mul_le_mul_of_nonneg_left hOpp
      (by positivity : 0 <= 2 * m ^ 2)
    have hCancelU : (2 * m ^ 2) * U = B ^ 2 * (Real.log m + 1) := by
      dsimp [U]
      field_simp [hmPos.ne']
    have hCancelR : (2 * m ^ 2) * (1 / m) = 2 * m := by
      field_simp [hmPos.ne']
    rw [hCancelU, hCancelR] at hOppScaled
    nlinarith
  have hPeakReal : A / m < nicolasK m := by
    exact sub_pos.mp hPeak
  have hScaledK := mul_lt_mul_of_pos_left hPeakReal hmPos
  have hCancelA : m * (A / m) = A := by field_simp [hmPos.ne']
  rw [hCancelA] at hScaledK
  have hScaledU := mul_lt_mul_of_pos_left hLoss hmPos
  have hCancelOne : m * (1 / m) = 1 := by field_simp [hmPos.ne']
  rw [hCancelOne] at hScaledU
  have hScaledF := mul_le_mul_of_nonneg_left hLower hmPos.le
  refine Exists.intro (n + 1) (And.intro (by omega) ?_)
  simp only [Nat.cast_add, Nat.cast_one]
  change C < m * nicolasLogMertensOscillation m
  nlinarith

end PrimeFactorOscillations
