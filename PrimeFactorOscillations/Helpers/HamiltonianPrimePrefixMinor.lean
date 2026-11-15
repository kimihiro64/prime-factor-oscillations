/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeMinorArc

/-! # The whole prime-prefix minor-grid estimate

The discarded initial cutoff is retained and bounded explicitly.
The complete remaining physical window uses the actual coefficient-mean
Vaughan estimate. One constant precedes every scale and auxiliary grid.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_grid_interval_add {N : Nat} [NeZero N]
    (s A B : Nat) (k : Int) :
    lpfGridIntervalWeight N s (A + B) (k : ZMod N) =
      lpfGridIntervalWeight N s A (k : ZMod N) +
        lpfGridIntervalWeight N (s + A) B (k : ZMod N) := by
  unfold lpfGridIntervalWeight
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hIndex : s + 1 + (A + i) = (s + A) + 1 + i := by omega
  rw [hIndex]

theorem hamiltonian_prime_grid_interval_trivial {N : Nat} [NeZero N]
    (s L H : Nat) (hH : 1 <= H) (hTop : s + L <= H) (k : Int) :
    norm (lpfGridIntervalWeight N s L (k : ZMod N)) <=
      (L : Real) * Real.log (H : Real) := by
  unfold lpfGridIntervalWeight
  calc
    _ <= (Finset.range L).sum (fun i =>
        norm ((ArithmeticFunction.vonMangoldt (s + 1 + i) : Complex) *
          ZMod.stdAddChar ((k : ZMod N) * ((s + 1 + i : Nat) : ZMod N)))) :=
      norm_sum_le _ _
    _ <= (Finset.range L).sum (fun _ => Real.log (H : Real)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hI := Finset.mem_range.mp hi
      have hn : 0 < s + 1 + i := by omega
      have hnH : s + 1 + i <= H := by omega
      have hLog := ArithmeticFunction.vonMangoldt_le_log (n := s + 1 + i)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        lpfGrid_character_phase, norm_lpfPhase, mul_one]
      exact hLog.trans (Real.log_le_log (by exact_mod_cast hn)
        (by exact_mod_cast hnH))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem hamiltonian_prime_prefix_minor_logarithmic :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N] (M P : Nat),
        2 ^ 18 <= M -> 0 < P ->
        (P : Real) <= (M : Real) ^ ((1 : Real) / 40) ->
        Dvd.dvd M N -> (forall q, 0 < q -> q <= P -> Dvd.dvd q N) ->
        forall k : Int,
        Not (Membership.mem (lpfRationalGrid N P ((N / M) * P)) (k : ZMod N)) ->
        norm (lpfGridIntervalWeight N 0 M (k : ZMod N)) ^ 2 <=
          C * ((M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real)) *
            (1 + Real.log (2 * (M : Real))) ^ 10) := by
  choose C hC hWindow using hamiltonian_prime_minor_grid_logarithmic
  refine Exists.intro (8 + 2 * C) (And.intro (by positivity) ?_)
  intro N instN M P hM hP hPPower hDivM hDiv k hMinor
  let U := lpfVaughanCutoff M
  let ell : Real := 1 + Real.log (2 * (M : Real))
  let R : Real := (M : Real) ^ 2 / (P : Real) +
    (M : Real) ^ (8 / 5 : Real)
  let head := lpfGridIntervalWeight N 0 U (k : ZMod N)
  let tail := lpfGridIntervalWeight N U (M - U) (k : ZMod N)
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hOne
  have hPhysical := lpf_vaughan_cutoff_physical M hM
  have hUM : U <= M := by
    have hReal : (U : Real) <= (M : Real) := by
      change (lpfVaughanCutoff M : Real) <= (M : Real)
      linarith only [hPhysical.1, hMR]
    exact_mod_cast hReal
  have hTotal : U + (M - U) = M := Nat.add_sub_of_le hUM
  have hProduct : U * U <= M := by
    have hReal : ((U * U : Nat) : Real) <= (M : Real) := by
      change ((lpfVaughanCutoff M * lpfVaughanCutoff M : Nat) : Real) <= (M : Real)
      linarith only [hPhysical.2, hMR]
    exact_mod_cast hReal
  have hTail := hWindow (N := N) M P U (M - U) hM hP hPPower hDivM hDiv
    (le_refl U) (by simpa only [hTotal] using hProduct)
    (by rw [hTotal]; omega) k hMinor
  change norm tail ^ 2 <= C * R * ell ^ 10 at hTail
  have hSplit : lpfGridIntervalWeight N 0 M (k : ZMod N) = head + tail := by
    have h := hamiltonian_prime_grid_interval_add (N := N) 0 U (M - U) k
    simpa only [hTotal, Nat.zero_add] using h
  have hHead := hamiltonian_prime_grid_interval_trivial (N := N) 0 U (2 * M)
    (by omega) (by omega) k
  have hHCast : ((2 * M : Nat) : Real) = 2 * (M : Real) := by push_cast; rfl
  rw [hHCast] at hHead
  change norm head <= (U : Real) * Real.log (2 * (M : Real)) at hHead
  have hLog : 0 <= Real.log (2 * (M : Real)) :=
    Real.log_nonneg (by linarith only [hMR])
  have hEll : 1 <= ell := by dsimp [ell]; linarith only [hLog]
  have hLogSq : Real.log (2 * (M : Real)) ^ 2 <= ell ^ 2 := by
    dsimp [ell]
    nlinarith only [hLog]
  have hU2 : (U : Real) ^ 2 <= 4 * (M : Real) ^ (4 / 5 : Real) := by
    have h := lpf_vaughan_cutoff_product M hOne
    simpa only [U, Nat.cast_mul, pow_two] using h
  have hHeadSq : norm head ^ 2 <=
      (U : Real) ^ 2 * Real.log (2 * (M : Real)) ^ 2 := by
    have hProductNN : 0 <= (U : Real) * Real.log (2 * (M : Real)) :=
      mul_nonneg (Nat.cast_nonneg U) hLog
    have h := mul_le_mul hHead hHead (norm_nonneg _) hProductNN
    convert h using 1 <;> ring
  have hEll210 : ell ^ 2 <= ell ^ 10 := by
    calc
      _ = ell ^ (2 : Real) := (Real.rpow_natCast ell 2).symm
      _ <= ell ^ (10 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hEll (by norm_num)
      _ = _ := Real.rpow_natCast ell 10
  have hPower : (M : Real) ^ (4 / 5 : Real) <= (M : Real) ^ (8 / 5 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hMR (by norm_num)
  have hScale : (M : Real) ^ (8 / 5 : Real) <= R := by
    dsimp [R]
    exact le_add_of_nonneg_left (by positivity)
  have hHeadBound : norm head ^ 2 <= 4 * R * ell ^ 10 := by
    have h1 := mul_le_mul hU2 hLogSq (sq_nonneg _) (by positivity)
    have h2 := mul_le_mul (hPower.trans hScale) hEll210
      (sq_nonneg _) (by dsimp [R]; positivity)
    have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : Real) <= 4)
    calc
      _ <= (U : Real) ^ 2 * Real.log (2 * (M : Real)) ^ 2 := hHeadSq
      _ <= (4 * (M : Real) ^ (4 / 5 : Real)) * ell ^ 2 := h1
      _ <= 4 * R * ell ^ 10 := by nlinarith only [h3]
  have hTriangle : norm (lpfGridIntervalWeight N 0 M (k : ZMod N)) <=
      norm head + norm tail := by
    rw [hSplit]
    exact norm_add_le _ _
  have hFullSq : norm (lpfGridIntervalWeight N 0 M (k : ZMod N)) ^ 2 <=
      2 * norm head ^ 2 + 2 * norm tail ^ 2 := by
    have hSquare := mul_le_mul hTriangle hTriangle (norm_nonneg _) (by positivity)
    nlinarith only [hSquare, sq_nonneg (norm head - norm tail)]
  change norm (lpfGridIntervalWeight N 0 M (k : ZMod N)) ^ 2 <=
    (8 + 2 * C) * R * ell ^ 10
  nlinarith only [hFullSq, hHeadBound, hTail]

end PrimeFactorOscillations.LPF
