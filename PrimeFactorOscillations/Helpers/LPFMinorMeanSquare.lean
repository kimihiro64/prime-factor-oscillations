/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMinorParseval
import PrimeFactorOscillations.Helpers.LPFVaughanMean

/-!
# Explicit complete minor-arc mean square

The actual rational-grid complement is bounded with constant 32768. Parseval
retains the nonwrapping physical window and every prime-power weight. The
result has no additional divisor-power loss and no unspecified minor constant.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF
theorem lpf_vaughan_warm_grid_minor_mean_squared_bound
    {N : Nat} [NeZero N] (M P s L : Nat)
    (hM : 2 ^ 18 <= M) (hP : 0 < P)
    (hPPower : (P : Real) <= (M : Real) ^ ((1 : Real) / 40))
    (hDivM : Dvd.dvd M N) (hDiv : forall q, 0 < q -> q <= P -> Dvd.dvd q N)
    (hStart : (M : Real) / 4 <= (s : Real)) (hTop : s + L <= 2 * M)
    (k : Int)
    (hMinor : Not (Membership.mem (lpfRationalGrid N P ((N / M) * P)) (k : ZMod N))) :
    norm (lpfGridIntervalWeight N s L (k : ZMod N)) ^ 2 <=
      1296 * ((M : Real) / (P : Real)) ^ 2 * (1 + Real.log (2 * (M : Real))) ^ 4 +
      2304 * (M : Real) ^ (8 / 5 : Real) * (1 + Real.log (2 * (M : Real))) ^ 4 +
      96 * (lpfVaughanDyadicCount M : Real) ^ 4 *
        (3 * ((M : Real) ^ 2 / (P : Real)) + (M : Real) ^ (8 / 5 : Real)) *
          (1 + Real.log (2 * (M : Real))) ^ 6 := by
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hOne
  have hPowerTop : (M : Real) ^ ((1 : Real) / 40) <= (M : Real) := by
    calc
      _ <= (M : Real) ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le hMR (by norm_num)
      _ = _ := Real.rpow_one _
  have hPM : P <= M := by exact_mod_cast (hPPower.trans hPowerTop)
  choose a q u beta hApprox using lpf_exists_minor_unit_approximation M P k hP hPM hDivM hDiv hMinor
  have hq : 0 < q := hApprox.1
  letI : NeZero q := { out := Nat.ne_of_gt hq }
  have hCut := lpf_vaughan_cutoff_bounds M hOne
  have hPhysical := lpf_vaughan_cutoff_physical M hM
  have hBeta := lpf_vaughan_cutoff_beta M P q hM hq beta hPPower hApprox.2.2.2.2.2.2
  have hCount := lpf_vaughan_dyadic_count_bounds M hOne
  have hCutTopR : (lpfVaughanCutoff M : Real) <= 2 * (M : Real) := by
    linarith only [hPhysical.1, hMR]
  have hCutTop : lpfVaughanCutoff M <= 2 * M := by exact_mod_cast hCutTopR
  have hCutStart : lpfVaughanCutoff M <= s := by exact_mod_cast (hPhysical.1.trans hStart)
  have hCutX : lpfVaughanCutoff M <= s + L := hCutStart.trans (Nat.le_add_right s L)
  have hProductStart : lpfVaughanCutoff M * lpfVaughanCutoff M <= s := by
    exact_mod_cast (hPhysical.2.trans hStart)
  have hProductX : lpfVaughanCutoff M * lpfVaughanCutoff M <= s + L :=
    hProductStart.trans (Nat.le_add_right s L)
  have hCountCut : 2 * M <= lpfVaughanCutoff M * 2 ^ lpfVaughanDyadicCount M := by
    have hMul : 2 ^ lpfVaughanDyadicCount M <=
        lpfVaughanCutoff M * 2 ^ lpfVaughanDyadicCount M := by
      simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ lpfVaughanDyadicCount M) hCut.1
    exact hCount.1.trans hMul
  have h := lpf_vaughan_minor_mean_squared_bound (N := N) (q := q) M P hOne hP hApprox.2.2.1 hApprox.2.1.le
    hApprox.2.2.2.1 k a u hApprox.2.2.2.2.1 beta
    (lpfVaughanCutoff M) (lpfVaughanCutoff M)
    (lpfVaughanDyadicCount M) (lpfVaughanDyadicCount M) s L
    hCut.1 hCutTop hCutTop hCut.2.1 hCut.2.1 hCountCut hCountCut hTop hCutStart hCutX hProductX
    (lpf_vaughan_cutoff_product M hOne) hApprox.2.2.2.2.2.1 hBeta.1 hBeta.2.1 hBeta.2.2
  convert h using 1 <;> ring


theorem lpf_grid_minor_mean_uniform_squared_bound
    {N : Nat} [NeZero N] (M P s L : Nat)
    (hM : 2 ^ 18 <= M) (hP : 0 < P)
    (hPPower : (P : Real) <= (M : Real) ^ ((1 : Real) / 40))
    (hDivM : Dvd.dvd M N) (hDiv : forall q, 0 < q -> q <= P -> Dvd.dvd q N)
    (hStart : (M : Real) / 4 <= (s : Real)) (hTop : s + L <= 2 * M)
    (k : Int)
    (hMinor : Not (Membership.mem (lpfRationalGrid N P ((N / M) * P)) (k : ZMod N))) :
    norm (lpfGridIntervalWeight N s L (k : ZMod N)) ^ 2 <=
      32768 * ((M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real)) *
        (1 + Real.log (2 * (M : Real))) ^ 10 := by
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hOne
  have hPR : (1 : Real) <= (P : Real) := by exact_mod_cast (by omega : 1 <= P)
  have hPPos : (0 : Real) < (P : Real) := by exact_mod_cast hP
  let ell : Real := 1 + Real.log (2 * (M : Real))
  let j : Real := (lpfVaughanDyadicCount M : Real)
  let D : Real := ((M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real)) * ell ^ 10
  have hEll : 1 <= ell := by
    have hLog : 0 <= Real.log (2 * (M : Real)) := Real.log_nonneg (by linarith only [hMR])
    dsimp [ell]
    linarith only [hLog]
  have hEll2 : 1 <= ell ^ 2 := by nlinarith only [hEll, sq_nonneg (ell - 1)]
  have hEll4 : 1 <= ell ^ 4 := by
    have h := mul_le_mul hEll2 hEll2 (by norm_num : (0 : Real) <= 1) (sq_nonneg ell)
    convert h using 1 <;> ring
  have hEll6 : 1 <= ell ^ 6 := by
    have h := mul_le_mul hEll4 hEll2 (by norm_num : (0 : Real) <= 1) (by positivity)
    convert h using 1 <;> ring
  have hEll410 : ell ^ 4 <= ell ^ 10 := by
    calc
      _ = ell ^ 4 * 1 := by ring
      _ <= ell ^ 4 * ell ^ 6 := mul_le_mul_of_nonneg_left hEll6 (by positivity)
      _ = _ := by ring
  have hRatio : ((M : Real) / (P : Real)) ^ 2 <= (M : Real) ^ 2 / (P : Real) := by
    rw [div_pow]
    gcongr
    nlinarith only [hPR]
  have hA : ((M : Real) / (P : Real)) ^ 2 <=
      (M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real) := by
    have hAdd : (M : Real) ^ 2 / (P : Real) <=
        (M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real) := by
      have hNonneg : 0 <= (M : Real) ^ (8 / 5 : Real) := by positivity
      linarith only [hNonneg]
    exact hRatio.trans hAdd
  have hB : (M : Real) ^ (8 / 5 : Real) <=
      (M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real) := by
    have hNonneg : 0 <= (M : Real) ^ 2 / (P : Real) := by positivity
    linarith only [hNonneg]
  have hLogTwo : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hHalf : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < Inv.inv (2 : Real))
    rw [Real.log_inv] at h
    norm_num at h
    linarith only [h]
  have hInv : 1 / Real.log 2 <= (2 : Real) := by
    apply (mul_le_mul_iff_of_pos_right hLogTwo).mp
    have hCancel : (1 / Real.log 2) * Real.log 2 = (1 : Real) := by field_simp
    rw [hCancel]
    linarith only [hHalf]
  have hCount := (lpf_vaughan_dyadic_count_bounds M hOne).2
  change j <= (1 + 1 / Real.log 2) * ell at hCount
  have hJ : j <= 3 * ell := hCount.trans
    (mul_le_mul_of_nonneg_right (by linarith only [hInv]) (by linarith only [hEll]))
  have hjNonneg : 0 <= j := by dsimp [j]; positivity
  have hJ2 : j ^ 2 <= (3 * ell) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hJ hJ hjNonneg (by positivity)
  have hJ4 : j ^ 4 <= 81 * ell ^ 4 := by
    have h := mul_le_mul hJ2 hJ2 (sq_nonneg _) (sq_nonneg _)
    convert h using 1 <;> ring
  have hFirst : 1296 * ((M : Real) / (P : Real)) ^ 2 * ell ^ 4 <= 1296 * D := by
    have h := mul_le_mul hA hEll410 (by positivity) (by positivity)
    have hScaled := mul_le_mul_of_nonneg_left h (by norm_num : (0 : Real) <= 1296)
    convert hScaled using 1 <;> ring
  have hSecond : 2304 * (M : Real) ^ (8 / 5 : Real) * ell ^ 4 <= 2304 * D := by
    have h := mul_le_mul hB hEll410 (by positivity) (by positivity)
    have hScaled := mul_le_mul_of_nonneg_left h (by norm_num : (0 : Real) <= 2304)
    convert hScaled using 1 <;> ring
  have hThird : 96 * j ^ 4 *
      (3 * ((M : Real) ^ 2 / (P : Real)) + (M : Real) ^ (8 / 5 : Real)) * ell ^ 6 <=
      23328 * D := by
    calc
      _ <= 96 * (81 * ell ^ 4) *
        (3 * ((M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real))) * ell ^ 6 := by
          gcongr
          have hNonneg : 0 <= (M : Real) ^ (8 / 5 : Real) := by positivity
          linarith only [hNonneg]
      _ = _ := by dsimp [D]; ring
  have hRaw := lpf_vaughan_warm_grid_minor_mean_squared_bound (N := N)
    M P s L hM hP hPPower hDivM hDiv hStart hTop k hMinor
  change norm (lpfGridIntervalWeight N s L (k : ZMod N)) ^ 2 <=
    1296 * ((M : Real) / (P : Real)) ^ 2 * ell ^ 4 +
    2304 * (M : Real) ^ (8 / 5 : Real) * ell ^ 4 +
    96 * j ^ 4 * (3 * ((M : Real) ^ 2 / (P : Real)) + (M : Real) ^ (8 / 5 : Real)) * ell ^ 6 at hRaw
  have hD : 0 <= D := by dsimp [D]; positivity
  calc
    _ <= _ := hRaw
    _ <= 1296 * D + 2304 * D + 23328 * D :=
      add_le_add (add_le_add hFirst hSecond) hThird
    _ = 26928 * D := by ring
    _ <= 32768 * D := mul_le_mul_of_nonneg_right (by norm_num) hD
    _ = _ := by dsimp [D, ell]; ring

theorem lpf_grid_minor_meanSquare_explicit_bound
    {N : Nat} [NeZero N] (M P s L : Nat)
    (hM : 2 ^ 18 <= M) (hP : 0 < P)
    (hPPower : (P : Real) <= (M : Real) ^ ((1 : Real) / 40))
    (hDivM : Dvd.dvd M N) (hDiv : forall q, 0 < q -> q <= P -> Dvd.dvd q N)
    (hStart : (M : Real) / 4 <= (s : Real)) (hTop : s + L <= 2 * M)
    (hL : L <= M) (hInput : s + L < N) (T : Finset (ZMod N)) :
    Finset.sum T (fun t => Complex.normSq (lpfCyclicInverse
      (fun x => if Membership.mem (lpfRationalGrid N P ((N / M) * P)) x then 0
        else lpfGridIntervalWeight N s L x ^ 2) t)) <=
      32768 * ((M : Real) ^ 3 / (P : Real) + (M : Real) ^ (13 / 5 : Real)) *
        (1 + Real.log (2 * (M : Real))) ^ 12 := by
  classical
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hMPos : (0 : Real) < (M : Real) := by exact_mod_cast (by omega : 0 < M)
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hOne
  have hLog : 0 <= Real.log (2 * (M : Real)) := Real.log_nonneg (by linarith only [hMR])
  let ell : Real := 1 + Real.log (2 * (M : Real))
  let Q : Real := 32768 *
    ((M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real)) * ell ^ 10
  have hQ : 0 <= Q := by dsimp [Q, ell]; positivity
  have hAll (x : ZMod N)
      (hx : Not (Membership.mem (lpfRationalGrid N P ((N / M) * P)) x)) :
      norm (lpfGridIntervalWeight N s L x) ^ 2 <= Q := by
    have hxInt : Not (Membership.mem (lpfRationalGrid N P ((N / M) * P)) ((x.val : Int) : ZMod N)) := by
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hx
    have h := lpf_grid_minor_mean_uniform_squared_bound (N := N) M P s L hM hP hPPower hDivM hDiv hStart hTop (x.val : Int) hxInt
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h
  have hMean := lpf_grid_interval_minor_meanSquare_of_pointwise s L (2 * M)
    (by omega) hTop hInput (lpfRationalGrid N P ((N / M) * P)) T Q hQ hAll
  have hHCast : ((2 * M : Nat) : Real) = 2 * (M : Real) := by push_cast; rfl
  rw [hHCast] at hMean
  have hLogSq : Real.log (2 * (M : Real)) ^ 2 <= ell ^ 2 := by
    have hLe : Real.log (2 * (M : Real)) <= ell := by dsimp [ell]; linarith only
    simpa only [pow_two] using mul_le_mul hLe hLe hLog (by dsimp [ell]; positivity)
  have hPow : (M : Real) ^ (8 / 5 : Real) * (M : Real) = (M : Real) ^ (13 / 5 : Real) := by
    calc
      _ = (M : Real) ^ (8 / 5 : Real) * (M : Real) ^ (1 : Real) := by rw [Real.rpow_one]
      _ = (M : Real) ^ ((8 / 5 : Real) + 1) := (Real.rpow_add hMPos _ _).symm
      _ = _ := by norm_num
  calc
    _ <= Q * (L : Real) * Real.log (2 * (M : Real)) ^ 2 := hMean
    _ <= Q * (M : Real) * ell ^ 2 := by gcongr
    _ = 32768 *
        ((M : Real) ^ 3 / (P : Real) + (M : Real) ^ (8 / 5 : Real) * (M : Real)) * ell ^ 12 := by
      dsimp [Q]
      ring
    _ = _ := by rw [hPow]



end PrimeFactorOscillations.LPF
