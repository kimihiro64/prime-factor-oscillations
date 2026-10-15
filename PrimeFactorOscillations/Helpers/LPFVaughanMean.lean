/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMinorEnergyPower
import PrimeFactorOscillations.Helpers.LPFVaughanMinor

/-!
# Vaughan bounds with the actual inner coefficient mean

The complete product-window Type II packet uses its squared coefficient mean.
The Type I terms and the rational-approximation hypotheses are retained. The
numerical constants 48 and 96 replace the pointwise divisor-power constant.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_vaughan_frequency_window_mean_norm_bound
    {N q : Nat} [NeZero N] [NeZero q] (M : Nat) (hM : 1 <= M) (hQ : q <= 2 * M)
    (k a : Int) (u : Units (ZMod q)) (hu : (a : ZMod q) = (u : ZMod q))
    (beta : Real) (U V J K s L : Nat) (hU : U <= 2 * M) (hV : V <= 2 * M)
    (hUP : (M : Real) ^ (2 / 5 : Real) <= (U : Real))
    (hVP : (M : Real) ^ (2 / 5 : Real) <= (V : Real))
    (hJ : 2 * M <= U * 2 ^ J) (hK : 2 * M <= V * 2 ^ K) (hTop : s + L <= 2 * M)
    (hUS : U <= s) (hVX : V <= s + L) (hUV : U * V <= s + L)
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBetaV : abs beta * (V : Real) <= 1 / (4 * (q : Real)))
    (hBetaUV : abs beta * ((U * V : Nat) : Real) <= 1 / (4 * (q : Real)))
    (hBetaII : abs beta * (2 * (M : Real) ^ (3 / 5 : Real)) <= 1 / (4 * (q : Real))) :
    norm (lpfArithmeticFrequencyWindow N ArithmeticFunction.vonMangoldt s L k) <=
      2 * Real.log ((2 * M : Nat) : Real) * lpfTypeIResidueCost q V (s + L) +
      Real.log ((2 * M : Nat) : Real) * lpfTypeIResidueCost q (U * V) (s + L) +
      (J : Real) * (K : Real) * Real.sqrt (48 *
        ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) + (M : Real) * (q : Real)) *
          (1 + Real.log (2 * (M : Real))) ^ 6) := by
  let I1 : Complex := Finset.sum (Finset.Ioc 0 V) (fun d =>
    ((lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V d : Real) : Complex) *
      Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
        (Real.log (m : Real) : Complex) * ZMod.stdAddChar (N := N)
          ((k : ZMod N) * (m : ZMod N) * (d : ZMod N))))
  let I2 : Complex := Finset.sum (Finset.Ioc 0 (U * V)) (fun d =>
    ((lpfVaughanA U V d : Real) : Complex) *
      Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
        ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N))))
  let II : Complex := Finset.sum (Finset.Ioc U (2 * M)) (fun m =>
    ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
      Finset.sum (Finset.Ioc V (2 * M)) (fun n => ((lpfVaughanB V n : Real) : Complex) *
        lpfBilinearFrequencyWindowPhase N s L k m n))
  let T : Real := 48 *
    ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) + (M : Real) * (q : Real)) *
      (1 + Real.log (2 * (M : Real))) ^ 6
  have hH : 1 <= 2 * M := by omega
  have hLog : 0 <= Real.log (2 * (M : Real)) := Real.log_nonneg (by
    have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hM
    linarith only [hMR])
  have hT : 0 <= T := by dsimp [T]; positivity
  have hI1 := lpf_typeI_moebius_log_window_bound k a u hu beta V s L (2 * M)
    hH hTop hAlpha hBetaV
  change norm I1 <= (2 * Real.log ((2 * M : Nat) : Real)) * lpfTypeIResidueCost q V (s + L) at hI1
  have hI2 := lpf_typeI_vaughanA_window_bound k a u hu beta U V s L (2 * M)
    hH (hUV.trans hTop) hAlpha hBetaUV
  change norm I2 <= Real.log ((2 * M : Nat) : Real) * lpfTypeIResidueCost q (U * V) (s + L) at hI2
  have hIISq := lpf_typeII_dyadic_mean_power_bound (N := N) (q := q) M hM hQ k a u hu beta U V J K s L
    hU hV hUP hVP hJ hK hTop hAlpha hBetaII
  have hSq : norm II ^ 2 <= (J : Real) ^ 2 * (K : Real) ^ 2 * T := by
    convert hIISq using 1 <;> dsimp [II, T] <;> ring
  have hRoot : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT
  have hTarget : 0 <= (J : Real) * (K : Real) * Real.sqrt T := by positivity
  have hII : norm II <= (J : Real) * (K : Real) * Real.sqrt T := by
    have hSqTarget : ((J : Real) * (K : Real) * Real.sqrt T) ^ 2 =
        (J : Real) ^ 2 * (K : Real) ^ 2 * T := by
      rw [mul_pow, mul_pow, hRoot]
    nlinarith only [hSq, hSqTarget, hTarget, norm_nonneg II]
  have hExact : lpfArithmeticFrequencyWindow N ArithmeticFunction.vonMangoldt s L k = I1 - I2 + II := by
    have h := lpf_vaughan_frequency_window_exact (N := N) U V s L k hVX hUV
    rw [lpf_cutoff_frequency_window_eq_zero ArithmeticFunction.vonMangoldt U s L k hUS, zero_add] at h
    rw [lpf_typeII_frequency_window_extend U V s L (2 * M) k
      (fun m => ((ArithmeticFunction.vonMangoldt m -
        lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex))
      (fun n => ((lpfVaughanB V n : Real) : Complex)) hTop] at h
    exact h
  calc
    _ = norm (I1 - I2 + II) := congrArg norm hExact
    _ <= norm (I1 - I2) + norm II := norm_add_le _ _
    _ <= norm I1 + norm I2 + norm II := add_le_add (norm_sub_le I1 I2) (le_refl (norm II))
    _ <= _ := add_le_add (add_le_add hI1 hI2) hII

theorem lpf_vaughan_minor_mean_squared_bound
    {N q : Nat} [NeZero N] [NeZero q] (M P : Nat) (hM : 1 <= M) (hP : 0 < P)
    (hQH : q <= 2 * M) (hPQ : P <= q)
    (hQ : (q : Real) <= 2 * (M : Real) / (P : Real))
    (k a : Int) (u : Units (ZMod q)) (hu : (a : ZMod q) = (u : ZMod q))
    (beta : Real) (U V J K s L : Nat) (hUOne : 1 <= U)
    (hU : U <= 2 * M) (hV : V <= 2 * M)
    (hUP : (M : Real) ^ (2 / 5 : Real) <= (U : Real))
    (hVP : (M : Real) ^ (2 / 5 : Real) <= (V : Real))
    (hJ : 2 * M <= U * 2 ^ J) (hK : 2 * M <= V * 2 ^ K)
    (hTop : s + L <= 2 * M) (hUS : U <= s) (hVX : V <= s + L) (hUV : U * V <= s + L)
    (hUVPower : ((U * V : Nat) : Real) <= 4 * (M : Real) ^ (4 / 5 : Real))
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBetaV : abs beta * (V : Real) <= 1 / (4 * (q : Real)))
    (hBetaUV : abs beta * ((U * V : Nat) : Real) <= 1 / (4 * (q : Real)))
    (hBetaII : abs beta * (2 * (M : Real) ^ (3 / 5 : Real)) <= 1 / (4 * (q : Real))) :
    norm (lpfGridIntervalWeight N s L (k : ZMod N)) ^ 2 <=
      1296 * ((M : Real) / (P : Real)) ^ 2 * (1 + Real.log (2 * (M : Real))) ^ 4 +
      2304 * (M : Real) ^ (8 / 5 : Real) * (1 + Real.log (2 * (M : Real))) ^ 4 +
      96 * (J : Real) ^ 2 * (K : Real) ^ 2 *
        (3 * ((M : Real) ^ 2 / (P : Real)) + (M : Real) ^ (8 / 5 : Real)) *
          (1 + Real.log (2 * (M : Real))) ^ 6 := by
  have hOriginal := lpf_vaughan_frequency_window_mean_norm_bound (N := N) (q := q) M hM hQH k a u hu beta U V J K s L
    hU hV hUP hVP hJ hK hTop hUS hVX hUV hAlpha hBetaV hBetaUV hBetaII
  rw [lpf_vonMangoldt_frequency_window_eq_grid] at hOriginal
  have hTypeI := lpf_typeI_minor_allowance M P q U V (s + L)
    hM hP hQH hPQ hQ hTop hUOne hVX hUV hUVPower
  have hTypeII := lpf_typeII_minor_cost_le M P q hP hPQ hQ
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hM
  have hMNonneg : (0 : Real) <= (M : Real) := by positivity
  have hLog : 0 <= Real.log (2 * (M : Real)) := Real.log_nonneg (by linarith only [hMR])
  let I : Real := (18 * ((M : Real) / (P : Real)) + 24 * (M : Real) ^ (4 / 5 : Real)) *
    (1 + Real.log (2 * (M : Real))) ^ 2
  let R : Real := 48 *
    (3 * ((M : Real) ^ 2 / (P : Real)) + (M : Real) ^ (8 / 5 : Real)) *
    (1 + Real.log (2 * (M : Real))) ^ 6
  let T : Real := (J : Real) * (K : Real) * Real.sqrt R
  have hR : 0 <= R := by dsimp [R]; positivity
  have hI : 0 <= I := by dsimp [I]; positivity
  have hT : 0 <= T := by dsimp [T]; positivity
  have hRoot :
      Real.sqrt (48 *
        ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) +
          (M : Real) * (q : Real)) * (1 + Real.log (2 * (M : Real))) ^ 6) <=
      Real.sqrt R := by
    apply Real.sqrt_le_sqrt
    dsimp [R]
    gcongr
  have hNorm : norm (lpfGridIntervalWeight N s L (k : ZMod N)) <= I + T := by
    calc
      _ <= _ := hOriginal
      _ <= I + T := by
        dsimp [I, T]
        exact add_le_add hTypeI (mul_le_mul_of_nonneg_left hRoot (by positivity))
  have hNormSq : norm (lpfGridIntervalWeight N s L (k : ZMod N)) ^ 2 <= (I + T) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hNorm hNorm
      (norm_nonneg (lpfGridIntervalWeight N s L (k : ZMod N))) (by positivity)
  have hSquare : norm (lpfGridIntervalWeight N s L (k : ZMod N)) ^ 2 <=
      2 * I ^ 2 + 2 * T ^ 2 := by
    nlinarith only [hNormSq, sq_nonneg (I - T)]
  have hBPower : ((M : Real) ^ (4 / 5 : Real)) ^ 2 = (M : Real) ^ (8 / 5 : Real) := by
    calc
      _ = ((M : Real) ^ (4 / 5 : Real)) ^ (2 : Real) := (Real.rpow_natCast _ 2).symm
      _ = (M : Real) ^ ((4 / 5 : Real) * 2) := (Real.rpow_mul hMNonneg _ _).symm
      _ = _ := by norm_num
  have hI2 : I ^ 2 <=
      648 * ((M : Real) / (P : Real)) ^ 2 * (1 + Real.log (2 * (M : Real))) ^ 4 +
      1152 * (M : Real) ^ (8 / 5 : Real) * (1 + Real.log (2 * (M : Real))) ^ 4 := by
    have hScalar : (18 * ((M : Real) / (P : Real)) + 24 * (M : Real) ^ (4 / 5 : Real)) ^ 2 <=
        648 * ((M : Real) / (P : Real)) ^ 2 + 1152 * ((M : Real) ^ (4 / 5 : Real)) ^ 2 := by
      nlinarith only [sq_nonneg (18 * ((M : Real) / (P : Real)) -
        24 * (M : Real) ^ (4 / 5 : Real))]
    calc
      _ = (18 * ((M : Real) / (P : Real)) + 24 * (M : Real) ^ (4 / 5 : Real)) ^ 2 *
        (1 + Real.log (2 * (M : Real))) ^ 4 := by dsimp [I]; ring
      _ <= (648 * ((M : Real) / (P : Real)) ^ 2 +
        1152 * ((M : Real) ^ (4 / 5 : Real)) ^ 2) *
          (1 + Real.log (2 * (M : Real))) ^ 4 :=
            mul_le_mul_of_nonneg_right hScalar (by positivity)
      _ = _ := by rw [hBPower]; ring
  have hT2 : T ^ 2 = (J : Real) ^ 2 * (K : Real) ^ 2 * R := by
    dsimp [T]
    rw [mul_pow, mul_pow, Real.sq_sqrt hR]
  calc
    _ <= 2 * I ^ 2 + 2 * T ^ 2 := hSquare
    _ <= 2 * (648 * ((M : Real) / (P : Real)) ^ 2 * (1 + Real.log (2 * (M : Real))) ^ 4 +
        1152 * (M : Real) ^ (8 / 5 : Real) * (1 + Real.log (2 * (M : Real))) ^ 4) +
        2 * T ^ 2 := by gcongr
    _ = _ := by rw [hT2]; dsimp [R]; ring


end PrimeFactorOscillations.LPF
