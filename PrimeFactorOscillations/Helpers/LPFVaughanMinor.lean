/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFVaughanWindow

/-!
# Complete Vaughan bound for physical frequency windows

One uniform constant controls the original von Mangoldt window using both
actual Type I sums and the entire dyadic Type II sum. The physical product
mask and cutoff supports are exact. Both Type I contributions and the
coupled Type II term enter the complete squared minor-frequency bound.
Physical cutoff placement and the final Parseval consumer remain open.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def lpfTypeIResidueCost (q D X : Nat) : Real :=
  (if D < q then 0 else ((X : Real) / (q : Real)) *
    (1 + Real.log ((D / q : Nat) : Real))) +
      ((D / q + 1 : Nat) : Real) * (2 * (q : Real) * (1 + Real.log (q : Real)))

theorem lpf_vaughan_frequency_window_norm_bound :
    exists C0 : Real, And (0 < C0)
      (forall {N q : Nat} [NeZero N] [NeZero q] (M : Nat), 1 <= M -> q <= 2 * M ->
        forall (k a : Int) (u : Units (ZMod q)), (a : ZMod q) = (u : ZMod q) ->
        forall (beta : Real) (U V J K s L : Nat), U <= 2 * M -> V <= 2 * M ->
        (M : Real) ^ (2 / 5 : Real) <= (U : Real) ->
        (M : Real) ^ (2 / 5 : Real) <= (V : Real) ->
        2 * M <= U * 2 ^ J -> 2 * M <= V * 2 ^ K -> s + L <= 2 * M ->
        U <= s -> V <= s + L -> U * V <= s + L ->
        (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta ->
        abs beta * (V : Real) <= 1 / (4 * (q : Real)) ->
        abs beta * ((U * V : Nat) : Real) <= 1 / (4 * (q : Real)) ->
        abs beta * (2 * (M : Real) ^ (3 / 5 : Real)) <= 1 / (4 * (q : Real)) ->
        norm (lpfArithmeticFrequencyWindow N ArithmeticFunction.vonMangoldt s L k) <=
          2 * Real.log ((2 * M : Nat) : Real) * lpfTypeIResidueCost q V (s + L) +
          Real.log ((2 * M : Nat) : Real) * lpfTypeIResidueCost q (U * V) (s + L) +
          (J : Real) * (K : Real) * Real.sqrt (C0 * (M : Real) ^ ((1 : Real) / 160) *
            ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) + (M : Real) * (q : Real)) *
              (1 + Real.log (2 * (M : Real))) ^ 3)) := by
  choose C0 hC0 hBound using exists_lpf_typeII_dyadic_power_bound
  refine Exists.intro C0 (And.intro hC0 ?_)
  intro N q instN instQ M hM hQ k a u hu beta U V J K s L hU hV hUP hVP hJ hK hTop hUS hVX hUV hAlpha hBetaV hBetaUV hBetaII
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
  let T : Real := C0 * (M : Real) ^ ((1 : Real) / 160) *
    ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) + (M : Real) * (q : Real)) *
      (1 + Real.log (2 * (M : Real))) ^ 3
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
  have hIISq := hBound (N := N) (q := q) M hM hQ k a u hu beta U V J K s L
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

theorem lpf_vonMangoldt_frequency_window_eq_grid {N : Nat} [NeZero N]
    (s L : Nat) (k : Int) :
    lpfArithmeticFrequencyWindow N ArithmeticFunction.vonMangoldt s L k =
      lpfGridIntervalWeight N s L (k : ZMod N) := by
  unfold lpfArithmeticFrequencyWindow lpfGridIntervalWeight
  rw [lpf_sum_Ioc_eq_range, Nat.add_sub_cancel_left]

theorem lpf_typeI_residue_cost_le (q D X H : Nat)
    (hq : 0 < q) (hQH : q <= H) (hDH : D <= H) :
    lpfTypeIResidueCost q D X <=
      ((X : Real) / (q : Real) + 2 * (D : Real) + 2 * (q : Real)) *
        (1 + Real.log (H : Real)) := by
  have hHR : (1 : Real) <= (H : Real) := by exact_mod_cast (hq.trans_le hQH)
  have hLog : 0 <= Real.log (H : Real) := Real.log_nonneg hHR
  have hqR : (0 : Real) < (q : Real) := by exact_mod_cast hq
  have hDiv : ((D / q : Nat) : Real) * (q : Real) <= (D : Real) := by
    exact_mod_cast Nat.div_mul_le_self D q
  have hqLog : Real.log (q : Real) <= Real.log (H : Real) := by
    apply Real.log_le_log hqR
    exact_mod_cast hQH
  have hResidue : ((D / q + 1 : Nat) : Real) *
      (2 * (q : Real) * (1 + Real.log (q : Real))) <=
      (2 * (D : Real) + 2 * (q : Real)) * (1 + Real.log (H : Real)) := by
    calc
      _ <= ((D / q + 1 : Nat) : Real) *
          (2 * (q : Real) * (1 + Real.log (H : Real))) := by
            gcongr
      _ = (2 * (((D / q : Nat) : Real) * (q : Real)) + 2 * (q : Real)) *
          (1 + Real.log (H : Real)) := by push_cast; ring
      _ <= _ := by gcongr
  have hMultiple :
      (if D < q then 0 else ((X : Real) / (q : Real)) *
        (1 + Real.log ((D / q : Nat) : Real))) <=
      ((X : Real) / (q : Real)) * (1 + Real.log (H : Real)) := by
    by_cases hSmall : D < q
    case pos =>
      rw [ite_eq_left hSmall]
      positivity
    case neg =>
      rw [ite_eq_right hSmall]
      have hDQ : q <= D := Nat.le_of_not_gt hSmall
      have hPos : 0 < D / q := Nat.div_pos hDQ hq
      have hPosR : (0 : Real) < ((D / q : Nat) : Real) := by exact_mod_cast hPos
      have hTop : D / q <= H := (Nat.div_le_self D q).trans hDH
      have hDivLog : Real.log ((D / q : Nat) : Real) <= Real.log (H : Real) := by
        apply Real.log_le_log hPosR
        exact_mod_cast hTop
      gcongr
  unfold lpfTypeIResidueCost
  calc
    _ <= ((X : Real) / (q : Real)) * (1 + Real.log (H : Real)) +
      (2 * (D : Real) + 2 * (q : Real)) * (1 + Real.log (H : Real)) :=
        add_le_add hMultiple hResidue
    _ = _ := by ring

theorem lpf_typeII_minor_cost_le (M P q : Nat)
    (hP : 0 < P) (hPQ : P <= q)
    (hQ : (q : Real) <= 2 * (M : Real) / (P : Real)) :
    (M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) +
      (M : Real) * (q : Real) <=
    3 * ((M : Real) ^ 2 / (P : Real)) + (M : Real) ^ (8 / 5 : Real) := by
  have hPR : (0 : Real) < (P : Real) := by exact_mod_cast hP
  have hPQR : (P : Real) <= (q : Real) := by exact_mod_cast hPQ
  have hDiv : (M : Real) ^ 2 / (q : Real) <= (M : Real) ^ 2 / (P : Real) := by
    gcongr
  have hMul : (M : Real) * (q : Real) <= 2 * ((M : Real) ^ 2 / (P : Real)) := by
    calc
      _ <= (M : Real) * (2 * (M : Real) / (P : Real)) := by gcongr
      _ = _ := by ring
  linarith only [hDiv, hMul]

theorem lpf_typeI_minor_allowance (M P q U V X : Nat)
    (hM : 1 <= M) (hP : 0 < P) (hQH : q <= 2 * M) (hPQ : P <= q)
    (hQ : (q : Real) <= 2 * (M : Real) / (P : Real))
    (hX : X <= 2 * M) (hU : 1 <= U) (hV : V <= X) (hUV : U * V <= X)
    (hUVPower : ((U * V : Nat) : Real) <= 4 * (M : Real) ^ (4 / 5 : Real)) :
    2 * Real.log ((2 * M : Nat) : Real) * lpfTypeIResidueCost q V X +
      Real.log ((2 * M : Nat) : Real) * lpfTypeIResidueCost q (U * V) X <=
    (18 * ((M : Real) / (P : Real)) + 24 * (M : Real) ^ (4 / 5 : Real)) *
      (1 + Real.log (2 * (M : Real))) ^ 2 := by
  have hq : 0 < q := hP.trans_le hPQ
  have hPR : (0 : Real) < (P : Real) := by exact_mod_cast hP
  have hqR : (0 : Real) < (q : Real) := by exact_mod_cast hq
  have hPQR : (P : Real) <= (q : Real) := by exact_mod_cast hPQ
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hM
  have hLog : 0 <= Real.log (2 * (M : Real)) := Real.log_nonneg (by linarith only [hMR])
  have hTop : (X : Real) <= 2 * (M : Real) := by exact_mod_cast hX
  have hXq : (X : Real) / (q : Real) <= 2 * ((M : Real) / (P : Real)) := by
    calc
      _ <= 2 * (M : Real) / (q : Real) := by gcongr
      _ <= 2 * (M : Real) / (P : Real) := by gcongr
      _ = _ := by ring
  have hVUV : V <= U * V := by
    simpa only [one_mul] using Nat.mul_le_mul_right V hU
  have hVUVR : (V : Real) <= ((U * V : Nat) : Real) := by exact_mod_cast hVUV
  have hQ' : (q : Real) <= 2 * ((M : Real) / (P : Real)) := by
    convert hQ using 1 <;> ring
  have hCoeff :
      3 * ((X : Real) / (q : Real)) + 4 * (V : Real) +
        2 * ((U * V : Nat) : Real) + 6 * (q : Real) <=
      18 * ((M : Real) / (P : Real)) + 24 * (M : Real) ^ (4 / 5 : Real) := by
    linarith only [hXq, hVUVR, hUVPower, hQ']
  have h1 := lpf_typeI_residue_cost_le q V X (2 * M) hq hQH (hV.trans hX)
  have h2 := lpf_typeI_residue_cost_le q (U * V) X (2 * M) hq hQH (hUV.trans hX)
  have hHCast : ((2 * M : Nat) : Real) = 2 * (M : Real) := by push_cast; rfl
  rw [hHCast] at h1 h2
  rw [hHCast]
  calc
    _ <= 2 * Real.log (2 * (M : Real)) *
        (((X : Real) / (q : Real) + 2 * (V : Real) + 2 * (q : Real)) *
          (1 + Real.log (2 * (M : Real)))) +
      Real.log (2 * (M : Real)) *
        (((X : Real) / (q : Real) + 2 * ((U * V : Nat) : Real) + 2 * (q : Real)) *
          (1 + Real.log (2 * (M : Real)))) := by gcongr
    _ = (3 * ((X : Real) / (q : Real)) + 4 * (V : Real) +
          2 * ((U * V : Nat) : Real) + 6 * (q : Real)) *
        (Real.log (2 * (M : Real)) * (1 + Real.log (2 * (M : Real)))) := by ring
    _ <= (18 * ((M : Real) / (P : Real)) + 24 * (M : Real) ^ (4 / 5 : Real)) *
        ((1 + Real.log (2 * (M : Real))) * (1 + Real.log (2 * (M : Real)))) := by
          gcongr
          linarith only
    _ = _ := by ring

theorem lpf_vaughan_minor_squared_bound :
    exists C0 : Real, And (0 < C0)
      (forall {N q : Nat} [NeZero N] [NeZero q] (M P : Nat),
        1 <= M -> 0 < P -> q <= 2 * M -> P <= q ->
        (q : Real) <= 2 * (M : Real) / (P : Real) ->
        forall (k a : Int) (u : Units (ZMod q)), (a : ZMod q) = (u : ZMod q) ->
        forall (beta : Real) (U V J K s L : Nat), 1 <= U ->
        U <= 2 * M -> V <= 2 * M ->
        (M : Real) ^ (2 / 5 : Real) <= (U : Real) ->
        (M : Real) ^ (2 / 5 : Real) <= (V : Real) ->
        2 * M <= U * 2 ^ J -> 2 * M <= V * 2 ^ K -> s + L <= 2 * M ->
        U <= s -> V <= s + L -> U * V <= s + L ->
        ((U * V : Nat) : Real) <= 4 * (M : Real) ^ (4 / 5 : Real) ->
        (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta ->
        abs beta * (V : Real) <= 1 / (4 * (q : Real)) ->
        abs beta * ((U * V : Nat) : Real) <= 1 / (4 * (q : Real)) ->
        abs beta * (2 * (M : Real) ^ (3 / 5 : Real)) <= 1 / (4 * (q : Real)) ->
        norm (lpfGridIntervalWeight N s L (k : ZMod N)) ^ 2 <=
          1296 * ((M : Real) / (P : Real)) ^ 2 * (1 + Real.log (2 * (M : Real))) ^ 4 +
          2304 * (M : Real) ^ (8 / 5 : Real) * (1 + Real.log (2 * (M : Real))) ^ 4 +
          2 * C0 * (J : Real) ^ 2 * (K : Real) ^ 2 *
            (M : Real) ^ ((1 : Real) / 160) *
            (3 * ((M : Real) ^ 2 / (P : Real)) + (M : Real) ^ (8 / 5 : Real)) *
            (1 + Real.log (2 * (M : Real))) ^ 3) := by
  choose C0 hC0 hBound using lpf_vaughan_frequency_window_norm_bound
  refine Exists.intro C0 (And.intro hC0 ?_)
  intro N q instN instQ M P hM hP hQH hPQ hQ k a u hu beta U V J K s L
    hUOne hU hV hUP hVP hJ hK hTop hUS hVX hUV hUVPower hAlpha hBetaV hBetaUV hBetaII
  have hOriginal := hBound (N := N) (q := q) M hM hQH k a u hu beta U V J K s L
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
  let R : Real := C0 * (M : Real) ^ ((1 : Real) / 160) *
    (3 * ((M : Real) ^ 2 / (P : Real)) + (M : Real) ^ (8 / 5 : Real)) *
    (1 + Real.log (2 * (M : Real))) ^ 3
  let T : Real := (J : Real) * (K : Real) * Real.sqrt R
  have hR : 0 <= R := by dsimp [R]; positivity
  have hI : 0 <= I := by dsimp [I]; positivity
  have hT : 0 <= T := by dsimp [T]; positivity
  have hRoot :
      Real.sqrt (C0 * (M : Real) ^ ((1 : Real) / 160) *
        ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) +
          (M : Real) * (q : Real)) * (1 + Real.log (2 * (M : Real))) ^ 3) <=
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
