/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMinorDyadic
import PrimeFactorOscillations.Helpers.LPFMinorEnergyPacket

/-!
# Averaged Type II physical power and complete dyadic assembly

The actual paired product-window estimate has coefficient48 and sixth-power
logarithm growth, with no pointwise divisor-power constant. Its complete clipped
dyadic consumer retains all endpoints and the exact J^2*K^2 cost. Passing this
estimate through Vaughan, minor Parseval and the complete source-error budget
is a separate obligation; no numerical entry threshold is asserted here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_typeII_actual_mean_power_bound {N q : Nat} [NeZero N] [NeZero q]
    (M : Nat) (hM : 1 <= M) (hQ : q <= 2 * M)
    (k a : Int) (u : Units (ZMod q)) (hU : (a : ZMod q) = (u : ZMod q))
    (beta : Real) (U V A B C D s L : Nat)
    (hB : B <= 2 * M) (hD : D <= 2 * M)
    (hAB : B - A <= A) (hDC : D <= 2 * C) (hAC : A * C <= 2 * M)
    (hASize : (A : Real) <= 2 * (M : Real) ^ (3 / 5 : Real))
    (hCSize : (C : Real) <= 2 * (M : Real) ^ (3 / 5 : Real))
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBeta : abs beta * ((D - C : Nat) : Real) <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.Ioc A B) (fun m =>
      ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
        Finset.sum (Finset.Ioc C D) (fun n => ((lpfVaughanB V n : Real) : Complex) *
          lpfBilinearFrequencyWindowPhase N s L k m n))) ^ 2 <=
      48 * ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) + (M : Real) * (q : Real)) *
        (1 + Real.log (2 * (M : Real))) ^ 6 := by
  let x : Real := ((B - A : Nat) : Real)
  let y : Real := (D : Real)
  let H : Real := 1 + Real.log (2 * (M : Real))
  let Z : Real := 1 + Real.log (q : Real)
  have hMR : (0 : Real) < (M : Real) := Nat.cast_pos.mpr (by omega : 0 < M)
  have hq : 0 < q := NeZero.pos q
  have hqR : (0 : Real) < (q : Real) := Nat.cast_pos.mpr hq
  have hLogM : 0 <= Real.log (2 * (M : Real)) := Real.log_nonneg (by
    have h : (1 : Real) <= (M : Real) := by exact_mod_cast hM
    linarith only [h])
  have hLogQ : 0 <= Real.log (q : Real) :=
    Real.log_nonneg (by exact_mod_cast (show 1 <= q by omega))
  have hH : 1 <= H := by dsimp [H]; linarith only [hLogM]
  have hZ : 1 <= Z := by dsimp [Z]; linarith only [hLogQ]
  have hZH : Z <= H := by
    have hQR : (q : Real) <= 2 * (M : Real) := by exact_mod_cast hQ
    have h := Real.log_le_log hqR hQR
    dsimp [Z, H]
    linarith only [h]
  have hx : 0 <= x := Nat.cast_nonneg _
  have hy : 0 <= y := Nat.cast_nonneg _
  have hxA : x <= (A : Real) := Nat.cast_le.mpr hAB
  have hyC : y <= 2 * (C : Real) := by dsimp [y]; exact_mod_cast hDC
  have hACR : (A : Real) * (C : Real) <= 2 * (M : Real) := by exact_mod_cast hAC
  have hProduct : x * y <= 4 * (M : Real) := by
    have h := mul_le_mul hxA hyC hy (Nat.cast_nonneg A)
    nlinarith only [h, hACR]
  have hWidth : x + y <= 6 * (M : Real) ^ (3 / 5 : Real) := by
    linarith only [hxA, hyC, hASize, hCSize]
  have hFloor : (((D - C) / q + 1 : Nat) : Real) <= y / (q : Real) + 1 := by
    have h := lpf_nat_div_cast_le (D - C) q hq
    have hN : ((D - C : Nat) : Real) <= y := Nat.cast_le.mpr (Nat.sub_le D C)
    have hDiv := div_le_div_of_nonneg_right hN hqR.le
    push_cast
    linarith only [h, hDiv]
  have hCost := lpf_typeII_residue_cost_bound x y (4 * (M : Real))
    (6 * (M : Real) ^ (3 / 5 : Real)) (q : Real) Z hx hy (by positivity)
      (by positivity) hqR hZ hProduct hWidth
  have hLogSq : Real.log (2 * (M : Real)) ^ 2 <= H ^ 2 := by
    dsimp [H]
    nlinarith only [hLogM]
  have hPow : (M : Real) * (M : Real) ^ (3 / 5 : Real) =
      (M : Real) ^ (8 / 5 : Real) := by
    calc
      _ = (M : Real) ^ (1 : Real) * (M : Real) ^ (3 / 5 : Real) := by rw [Real.rpow_one]
      _ = (M : Real) ^ ((1 : Real) + 3 / 5) := (Real.rpow_add hMR _ _).symm
      _ = _ := by norm_num
  have hRaw := lpf_typeII_actual_energy_packet_bound (N := N) (q := q)
    k a u hU beta U V A B C D s L (2 * M) hB hD (by omega) hAlpha hBeta
  push_cast at hRaw
  have hRHS :
      x * y * Real.log (2 * (M : Real)) ^ 2 * H ^ 3 *
        (((D - C) / q + 1 : Nat) : Real) * (x + 2 * (q : Real) * Z) <=
      48 * ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) + (M : Real) * (q : Real)) * H ^ 6 := by
    calc
      _ <= x * y * H ^ 2 * H ^ 3 * (y / (q : Real) + 1) * (x + 2 * (q : Real) * Z) := by
        gcongr
      _ = (x * y * (y / (q : Real) + 1) * (x + 2 * (q : Real) * Z)) * H ^ 5 := by ring
      _ <= (4 * (M : Real) * (4 * (M : Real) / (q : Real) +
          2 * (6 * (M : Real) ^ (3 / 5 : Real)) + 2 * (q : Real)) * Z) * H ^ 5 :=
        mul_le_mul_of_nonneg_right hCost (by positivity)
      _ <= (4 * (M : Real) * (4 * (M : Real) / (q : Real) +
          2 * (6 * (M : Real) ^ (3 / 5 : Real)) + 2 * (q : Real)) * H) * H ^ 5 := by
        gcongr
      _ = (16 * (M : Real) ^ 2 / (q : Real) +
          48 * ((M : Real) * (M : Real) ^ (3 / 5 : Real)) +
          8 * (M : Real) * (q : Real)) * H ^ 6 := by ring
      _ = (16 * (M : Real) ^ 2 / (q : Real) + 48 * (M : Real) ^ (8 / 5 : Real) +
          8 * (M : Real) * (q : Real)) * H ^ 6 := by rw [hPow]
      _ <= _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have h1 : 0 <= (M : Real) ^ 2 / (q : Real) := by positivity
        have h2 : 0 <= (M : Real) * (q : Real) := by positivity
        have hAdd : 0 <= 32 * ((M : Real) ^ 2 / (q : Real)) +
            40 * ((M : Real) * (q : Real)) := by positivity
        have hEq : 48 * ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) +
            (M : Real) * (q : Real)) =
            (16 * (M : Real) ^ 2 / (q : Real) + 48 * (M : Real) ^ (8 / 5 : Real) +
              8 * (M : Real) * (q : Real)) +
              (32 * ((M : Real) ^ 2 / (q : Real)) + 40 * ((M : Real) * (q : Real))) := by ring
        rw [hEq]
        exact le_add_of_nonneg_right hAdd
  dsimp [x, y, H, Z] at hRHS
  push_cast at hRHS
  simpa only [Complex.ofReal_sub] using hRaw.trans hRHS

theorem lpf_typeII_dyadic_mean_power_bound {N q : Nat} [NeZero N] [NeZero q]
    (M : Nat) (hM : 1 <= M) (hQ : q <= 2 * M)
    (k a : Int) (u : Units (ZMod q)) (hu : (a : ZMod q) = (u : ZMod q))
    (beta : Real) (U V J K s L : Nat) (hU : U <= 2 * M) (hV : V <= 2 * M)
    (hUP : (M : Real) ^ (2 / 5 : Real) <= (U : Real))
    (hVP : (M : Real) ^ (2 / 5 : Real) <= (V : Real))
    (hJ : 2 * M <= U * 2 ^ J) (hK : 2 * M <= V * 2 ^ K) (hTop : s + L <= 2 * M)
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBeta : abs beta * (2 * (M : Real) ^ (3 / 5 : Real)) <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.Ioc U (2 * M)) (fun m =>
      ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
        Finset.sum (Finset.Ioc V (2 * M)) (fun n => ((lpfVaughanB V n : Real) : Complex) *
          lpfBilinearFrequencyWindowPhase N s L k m n))) ^ 2 <=
      (J : Real) ^ 2 * (K : Real) ^ 2 * 48 *
        ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) + (M : Real) * (q : Real)) *
          (1 + Real.log (2 * (M : Real))) ^ 6 := by
  let H := 2 * M
  let F : Nat -> Nat -> Complex := fun m n =>
    ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
      (((lpfVaughanB V n : Real) : Complex) * lpfBilinearFrequencyWindowPhase N s L k m n)
  let T : Real := 48 *
    ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) + (M : Real) * (q : Real)) *
      (1 + Real.log (2 * (M : Real))) ^ 6
  have hMR : (0 : Real) < (M : Real) := Nat.cast_pos.mpr (by omega : 0 < M)
  have hLog : 0 <= Real.log (2 * (M : Real)) := Real.log_nonneg (by
    have hOne : (1 : Real) <= (M : Real) := by exact_mod_cast hM
    linarith)
  have hT : 0 <= T := by dsimp [T]; positivity
  have hPow : (M : Real) ^ (2 / 5 : Real) * (M : Real) ^ (3 / 5 : Real) = (M : Real) := by
    rw [<- Real.rpow_add hMR]
    norm_num
  have hPPos : (0 : Real) < (M : Real) ^ (2 / 5 : Real) := by positivity
  have hBlocks : forall j, j < J -> forall l, l < K ->
      norm (Finset.sum (Finset.Ioc (min H (U * 2 ^ j)) (min H (U * 2 ^ (j + 1)))) (fun m =>
        Finset.sum (Finset.Ioc (min H (V * 2 ^ l)) (min H (V * 2 ^ (l + 1)))) (F m))) <= Real.sqrt T := by
    intro j hj l hl
    let A := min H (U * 2 ^ j)
    let B := min H (U * 2 ^ (j + 1))
    let C := min H (V * 2 ^ l)
    let D := min H (V * 2 ^ (l + 1))
    have hAB : B - A <= A := lpf_dyadic_width_le_left U H j
    have hCD : D - C <= C := lpf_dyadic_width_le_left V H l
    have hUA : U <= A := lpf_dyadic_left_ge_cutoff U H j hU
    have hVC : V <= C := lpf_dyadic_left_ge_cutoff V H l hV
    by_cases hInactive : H <= A * C
    . have hZero : Finset.sum (Finset.Ioc A B) (fun m => Finset.sum (Finset.Ioc C D) (F m)) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        apply Finset.sum_eq_zero
        intro n hn
        have hMRange := Finset.mem_Ioc.mp hm
        have hNRange := Finset.mem_Ioc.mp hn
        have hProduct : H < m * n := hInactive.trans_lt
          ((Nat.mul_le_mul_left A hNRange.1.le).trans_lt
            (Nat.mul_lt_mul_of_pos_right hMRange.1 (by omega)))
        have hMask : Not (And (s < m * n) (m * n <= s + L)) := by intro h; omega
        simp only [F, lpfBilinearFrequencyWindowPhase, ite_eq_right hMask, mul_zero]
      change norm (Finset.sum (Finset.Ioc A B) (fun m => Finset.sum (Finset.Ioc C D) (F m))) <= _
      rw [hZero, norm_zero]
      exact Real.sqrt_nonneg T
    . have hAC : A * C <= 2 * M := by dsimp [H] at hInactive; omega
      have hACR : (A : Real) * (C : Real) <= 2 * (M : Real) := by exact_mod_cast hAC
      have hAP : (M : Real) ^ (2 / 5 : Real) <= (A : Real) := hUP.trans (Nat.cast_le.mpr hUA)
      have hCP : (M : Real) ^ (2 / 5 : Real) <= (C : Real) := hVP.trans (Nat.cast_le.mpr hVC)
      have hASize : (A : Real) <= 2 * (M : Real) ^ (3 / 5 : Real) := by
        apply (mul_le_mul_iff_of_pos_right hPPos).mp
        have h := (mul_le_mul_of_nonneg_left hCP (Nat.cast_nonneg A)).trans hACR
        nlinarith only [h, hPow]
      have hCSize : (C : Real) <= 2 * (M : Real) ^ (3 / 5 : Real) := by
        apply (mul_le_mul_iff_of_pos_right hPPos).mp
        have h := (mul_le_mul_of_nonneg_right hAP (Nat.cast_nonneg C)).trans hACR
        nlinarith only [h, hPow]
      have hWidth : ((B - A : Nat) : Real) + ((D - C : Nat) : Real) <=
          4 * (M : Real) ^ (3 / 5 : Real) := by
        have hm := (Nat.cast_le.mpr hAB).trans hASize
        have hn := (Nat.cast_le.mpr hCD).trans hCSize
        linarith
      have hError : abs beta * ((D - C : Nat) : Real) <= 1 / (4 * (q : Real)) :=
        (mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr hCD).trans hCSize) (abs_nonneg beta)).trans hBeta
      have hBlock := lpf_typeII_actual_mean_power_bound (N := N) (q := q)
        M hM hQ k a u hu beta U V A B C D s L
        (min_le_left _ _) (min_le_left _ _) hAB (by omega) hAC hASize hCSize hAlpha hError
      have hBlock' : norm (Finset.sum (Finset.Ioc A B) (fun m => Finset.sum (Finset.Ioc C D) (F m))) ^ 2 <= T := by
        simpa only [F, T, Finset.mul_sum] using hBlock
      have hSqrt := Real.sq_sqrt hT
      have hSqrtNonneg := Real.sqrt_nonneg T
      have hNorm := norm_nonneg (Finset.sum (Finset.Ioc A B) (fun m => Finset.sum (Finset.Ioc C D) (F m)))
      change norm (Finset.sum (Finset.Ioc A B) (fun m => Finset.sum (Finset.Ioc C D) (F m))) <= _
      nlinarith only [hBlock', hSqrt, hSqrtNonneg, hNorm]
  have hBound := lpf_dyadic_rectangle_norm_bound U V H J K hU hV hJ hK F (Real.sqrt T) hBlocks
  have hBound' : norm (Finset.sum (Finset.Ioc U (2 * M)) (fun m =>
      ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
        Finset.sum (Finset.Ioc V (2 * M)) (fun n => ((lpfVaughanB V n : Real) : Complex) *
          lpfBilinearFrequencyWindowPhase N s L k m n))) <= (J : Real) * (K : Real) * Real.sqrt T := by
    simpa only [H, F, Finset.mul_sum] using hBound
  have hSquared := mul_le_mul hBound' hBound' (norm_nonneg _) (by positivity)
  calc
    _ <= ((J : Real) * (K : Real) * Real.sqrt T) ^ 2 := by simpa only [pow_two] using hSquared
    _ = _ := by rw [mul_pow, Real.sq_sqrt hT]; dsimp [T]; ring


end PrimeFactorOscillations.LPF
