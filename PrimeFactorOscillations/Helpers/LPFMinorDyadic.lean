/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMinorPower

/-!
# Complete dyadic assembly of the actual Type II packet

The exact clipped partition includes every endpoint. Boxes whose products
exceed the input window vanish; each remaining box satisfies the physical
power bound. The full sum costs J^2*K^2 in its squared norm. Rational
approximation, Vaughan window reindexing and Parseval remain separate steps.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_dyadic_cutoff_monotone (U H : Nat) : Monotone (fun j : Nat => min H (U * 2 ^ j)) := by
  intro i j hij
  apply min_le_min_left H
  exact Nat.mul_le_mul_left U (Nat.pow_le_pow_right (by omega : 0 < 2) hij)

theorem lpf_dyadic_interval_sum {R : Type} [AddCommMonoid R]
    (U H J : Nat) (f : Nat -> R) :
    Finset.sum (Finset.Ioc (min H U) (min H (U * 2 ^ J))) f =
      Finset.sum (Finset.range J) (fun j =>
        Finset.sum (Finset.Ioc (min H (U * 2 ^ j)) (min H (U * 2 ^ (j + 1)))) f) := by
  classical
  induction J with
  | zero => simp
  | succ J ih =>
    have hBase : min H U <= min H (U * 2 ^ J) := by
      simpa using lpf_dyadic_cutoff_monotone U H (Nat.zero_le J)
    have hNext : min H (U * 2 ^ J) <= min H (U * 2 ^ (J + 1)) :=
      lpf_dyadic_cutoff_monotone U H (Nat.le_succ J)
    have hUnion : Finset.Ioc (min H U) (min H (U * 2 ^ (J + 1))) =
        Union.union (Finset.Ioc (min H U) (min H (U * 2 ^ J)))
          (Finset.Ioc (min H (U * 2 ^ J)) (min H (U * 2 ^ (J + 1)))) := by
      ext m
      simp only [Finset.mem_Ioc, Finset.mem_union]
      omega
    have hDisjoint : Disjoint (Finset.Ioc (min H U) (min H (U * 2 ^ J)))
        (Finset.Ioc (min H (U * 2 ^ J)) (min H (U * 2 ^ (J + 1)))) := by
      apply Finset.disjoint_left.mpr
      intro m hm1 hm2
      have h1 := Finset.mem_Ioc.mp hm1
      have h2 := Finset.mem_Ioc.mp hm2
      omega
    rw [hUnion, Finset.sum_union hDisjoint, ih, Finset.sum_range_succ]

theorem lpf_dyadic_rectangle_sum {R : Type} [AddCommMonoid R]
    (U V H J K : Nat) (f : Nat -> Nat -> R) :
    Finset.sum (Finset.Ioc (min H U) (min H (U * 2 ^ J))) (fun m =>
      Finset.sum (Finset.Ioc (min H V) (min H (V * 2 ^ K))) (f m)) =
        Finset.sum (Finset.range J) (fun j => Finset.sum (Finset.range K) (fun k =>
          Finset.sum (Finset.Ioc (min H (U * 2 ^ j)) (min H (U * 2 ^ (j + 1)))) (fun m =>
            Finset.sum (Finset.Ioc (min H (V * 2 ^ k)) (min H (V * 2 ^ (k + 1)))) (f m)))) := by
  rw [lpf_dyadic_interval_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp_rw [lpf_dyadic_interval_sum V H K]
  exact Finset.sum_comm

theorem lpf_dyadic_rectangle_norm_bound
    (U V H J K : Nat) (hU : U <= H) (hV : V <= H)
    (hUJ : H <= U * 2 ^ J) (hVK : H <= V * 2 ^ K)
    (f : Nat -> Nat -> Complex) (T : Real)
    (hBlocks : forall j, j < J -> forall k, k < K ->
      norm (Finset.sum (Finset.Ioc (min H (U * 2 ^ j)) (min H (U * 2 ^ (j + 1)))) (fun m =>
        Finset.sum (Finset.Ioc (min H (V * 2 ^ k)) (min H (V * 2 ^ (k + 1)))) (f m))) <= T) :
    norm (Finset.sum (Finset.Ioc U H) (fun m => Finset.sum (Finset.Ioc V H) (f m))) <=
      (J : Real) * (K : Real) * T := by
  have h := lpf_dyadic_rectangle_sum U V H J K f
  rw [min_eq_right hU, min_eq_right hV, min_eq_left hUJ, min_eq_left hVK] at h
  rw [h]
  calc
    _ <= Finset.sum (Finset.range J) (fun j => norm (Finset.sum (Finset.range K) (fun k =>
        Finset.sum (Finset.Ioc (min H (U * 2 ^ j)) (min H (U * 2 ^ (j + 1)))) (fun m =>
          Finset.sum (Finset.Ioc (min H (V * 2 ^ k)) (min H (V * 2 ^ (k + 1)))) (f m))))) := norm_sum_le _ _
    _ <= Finset.sum (Finset.range J) (fun _ => Finset.sum (Finset.range K) (fun _ => T)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk =>
        hBlocks j (Finset.mem_range.mp hj) k (Finset.mem_range.mp hk)))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem lpf_dyadic_width_le_left (U H j : Nat) :
    min H (U * 2 ^ (j + 1)) - min H (U * 2 ^ j) <= min H (U * 2 ^ j) := by
  by_cases h : H <= U * 2 ^ j
  . rw [min_eq_left h]
    have hTop := min_le_left H (U * 2 ^ (j + 1))
    omega
  . rw [min_eq_right (le_of_not_ge h)]
    have hTop : min H (U * 2 ^ (j + 1)) <= 2 * (U * 2 ^ j) := by
      calc
        _ <= U * 2 ^ (j + 1) := min_le_right _ _
        _ = _ := by rw [pow_succ]; ring
    omega

theorem lpf_dyadic_left_ge_cutoff (U H j : Nat) (hU : U <= H) :
    U <= min H (U * 2 ^ j) := by
  apply le_min hU
  have hPower : 1 <= (2 : Nat) ^ j := Nat.one_le_pow j 2 (by omega)
  simpa using Nat.mul_le_mul_left U hPower

theorem exists_lpf_typeII_dyadic_power_bound :
    exists C0 : Real, And (0 < C0)
      (forall {N q : Nat} [NeZero N] [NeZero q] (M : Nat), 1 <= M -> q <= 2 * M ->
        forall (k a : Int) (u : Units (ZMod q)), (a : ZMod q) = (u : ZMod q) ->
        forall (beta : Real) (U V J K s L : Nat), U <= 2 * M -> V <= 2 * M ->
        (M : Real) ^ (2 / 5 : Real) <= (U : Real) ->
        (M : Real) ^ (2 / 5 : Real) <= (V : Real) ->
        2 * M <= U * 2 ^ J -> 2 * M <= V * 2 ^ K -> s + L <= 2 * M ->
        (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta ->
        abs beta * (2 * (M : Real) ^ (3 / 5 : Real)) <= 1 / (4 * (q : Real)) ->
        norm (Finset.sum (Finset.Ioc U (2 * M)) (fun m =>
          ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
            Finset.sum (Finset.Ioc V (2 * M)) (fun n => ((lpfVaughanB V n : Real) : Complex) *
              lpfBilinearFrequencyWindowPhase N s L k m n))) ^ 2 <=
          (J : Real) ^ 2 * (K : Real) ^ 2 * C0 * (M : Real) ^ ((1 : Real) / 160) *
            ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) + (M : Real) * (q : Real)) *
              (1 + Real.log (2 * (M : Real))) ^ 3) := by
  choose C0 hC0 hActual using exists_lpf_typeII_actual_power_bound
  refine Exists.intro C0 (And.intro hC0 ?_)
  intro N q instN instQ M hM hQ k a u hu beta U V J K s L hU hV hUP hVP hJ hK hTop hAlpha hBeta
  let H := 2 * M
  let F : Nat -> Nat -> Complex := fun m n =>
    ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
      (((lpfVaughanB V n : Real) : Complex) * lpfBilinearFrequencyWindowPhase N s L k m n)
  let T : Real := C0 * (M : Real) ^ ((1 : Real) / 160) *
    ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) + (M : Real) * (q : Real)) *
      (1 + Real.log (2 * (M : Real))) ^ 3
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
      have hBlock := hActual (N := N) (q := q) M hM hQ k a u hu beta U V A B C D s L
        (min_le_left _ _) (min_le_left _ _) ((Nat.mul_le_mul hAB hCD).trans hAC) hWidth hAlpha hError
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

