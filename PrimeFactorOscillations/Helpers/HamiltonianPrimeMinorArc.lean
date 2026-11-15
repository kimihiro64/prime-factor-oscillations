/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFVaughanMean
import PrimeFactorOscillations.Helpers.LPFWarmCutoffs

/-! # Logarithmic minor-grid input to the prime-sum operator

The existing actual coefficient-mean Vaughan bound is consumed with the
proved physical cutoffs and complete reduced rational approximation.
The resulting uniform grid estimate has no divisor power loss.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_minor_grid_raw
    {N : Nat} [NeZero N] (M P s L : Nat)
    (hM : 2 ^ 18 <= M) (hP : 0 < P)
    (hPPower : (P : Real) <= (M : Real) ^ ((1 : Real) / 40))
    (hDivM : Dvd.dvd M N) (hDiv : forall q, 0 < q -> q <= P -> Dvd.dvd q N)
    (hStart : lpfVaughanCutoff M <= s)
    (hProduct : lpfVaughanCutoff M * lpfVaughanCutoff M <= s + L)
    (hTop : s + L <= 2 * M) (k : Int)
    (hMinor : Not (Membership.mem
      (lpfRationalGrid N P ((N / M) * P)) (k : ZMod N))) :
    norm (lpfGridIntervalWeight N s L (k : ZMod N)) ^ 2 <=
      1296 * ((M : Real) / (P : Real)) ^ 2 *
        (1 + Real.log (2 * (M : Real))) ^ 4 +
      2304 * (M : Real) ^ (8 / 5 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 4 +
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
  have hCutStart : lpfVaughanCutoff M <= s := hStart
  have hCutX : lpfVaughanCutoff M <= s + L := hCutStart.trans (Nat.le_add_right s L)
  have hProductX : lpfVaughanCutoff M * lpfVaughanCutoff M <= s + L := hProduct
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

theorem hamiltonian_prime_minor_grid_logarithmic :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N] (M P s L : Nat),
        2 ^ 18 <= M -> 0 < P ->
        (P : Real) <= (M : Real) ^ ((1 : Real) / 40) ->
        Dvd.dvd M N -> (forall q, 0 < q -> q <= P -> Dvd.dvd q N) ->
        lpfVaughanCutoff M <= s ->
        lpfVaughanCutoff M * lpfVaughanCutoff M <= s + L -> s + L <= 2 * M ->
        forall k : Int,
        Not (Membership.mem (lpfRationalGrid N P ((N / M) * P)) (k : ZMod N)) ->
        norm (lpfGridIntervalWeight N s L (k : ZMod N)) ^ 2 <=
          C * ((M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real)) *
            (1 + Real.log (2 * (M : Real))) ^ 10) := by
  let cJ : Real := 1 + 1 / Real.log 2
  have hLogTwo : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hcJ : 0 < cJ := by dsimp [cJ]; positivity
  refine Exists.intro (3600 + 288 * cJ ^ 4) (And.intro (by positivity) ?_)
  intro N instN M P s L hM hP hPPower hDivM hDiv hStart hProduct hTop k hMinor
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hOne
  have hPR : (1 : Real) <= (P : Real) := by exact_mod_cast (by omega : 1 <= P)
  let ell : Real := 1 + Real.log (2 * (M : Real))
  let j : Real := (lpfVaughanDyadicCount M : Real)
  let D : Real := ((M : Real) ^ 2 / (P : Real) +
    (M : Real) ^ (8 / 5 : Real)) * ell ^ 10
  have hEll : 1 <= ell := by
    have hLog : 0 <= Real.log (2 * (M : Real)) :=
      Real.log_nonneg (by linarith only [hMR])
    dsimp [ell]
    linarith only [hLog]
  have hEll410 : ell ^ 4 <= ell ^ 10 := by
    calc
      _ = ell ^ (4 : Real) := (Real.rpow_natCast ell 4).symm
      _ <= ell ^ (10 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hEll (by norm_num)
      _ = _ := Real.rpow_natCast ell 10
  have hRatio : ((M : Real) / (P : Real)) ^ 2 <=
      (M : Real) ^ 2 / (P : Real) := by
    rw [div_pow]
    gcongr
    nlinarith only [hPR]
  have hA : ((M : Real) / (P : Real)) ^ 2 <=
      (M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real) := by
    have hAdd : (M : Real) ^ 2 / (P : Real) <=
        (M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real) :=
      le_add_of_nonneg_right (by positivity)
    exact hRatio.trans hAdd
  have hB : (M : Real) ^ (8 / 5 : Real) <=
      (M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real) :=
    le_add_of_nonneg_left (by positivity)
  have hJ := (lpf_vaughan_dyadic_count_bounds M hOne).2
  change j <= cJ * ell at hJ
  have hjNonneg : 0 <= j := by dsimp [j]; positivity
  have hJ2 : j ^ 2 <= (cJ * ell) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hJ hJ hjNonneg (by positivity)
  have hJ4 : j ^ 4 <= cJ ^ 4 * ell ^ 4 := by
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
      (3 * ((M : Real) ^ 2 / (P : Real)) + (M : Real) ^ (8 / 5 : Real)) *
        ell ^ 6 <= 288 * cJ ^ 4 * D := by
    calc
      _ <= 96 * (cJ ^ 4 * ell ^ 4) *
          (3 * ((M : Real) ^ 2 / (P : Real) +
            (M : Real) ^ (8 / 5 : Real))) * ell ^ 6 := by
        gcongr
        have hNonneg : 0 <= (M : Real) ^ (8 / 5 : Real) := by positivity
        linarith only [hNonneg]
      _ = _ := by dsimp [D]; ring
  have hRaw := hamiltonian_prime_minor_grid_raw (N := N) M P s L
    hM hP hPPower hDivM hDiv hStart hProduct hTop k hMinor
  change norm (lpfGridIntervalWeight N s L (k : ZMod N)) ^ 2 <=
    1296 * ((M : Real) / (P : Real)) ^ 2 * ell ^ 4 +
    2304 * (M : Real) ^ (8 / 5 : Real) * ell ^ 4 +
    96 * j ^ 4 * (3 * ((M : Real) ^ 2 / (P : Real)) +
      (M : Real) ^ (8 / 5 : Real)) * ell ^ 6 at hRaw
  calc
    _ <= _ := hRaw
    _ <= 1296 * D + 2304 * D + 288 * cJ ^ 4 * D :=
      add_le_add (add_le_add hFirst hSecond) hThird
    _ = _ := by dsimp [D, ell]; ring

end PrimeFactorOscillations.LPF
