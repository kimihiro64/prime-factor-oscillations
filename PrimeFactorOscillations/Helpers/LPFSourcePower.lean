/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFixedSourceBudget

/-!
# Uniform power saving for the complete fixed-interval source error

The floor cutoff retains both sides of its quantitative normalization. All
four signed corrections enter the same budget before logarithm absorption.
One constant precedes every scale, grid, interval and natural target set.
The infinite singular series still requires a positive arithmetic identification;
this source estimate alone is not a density-entry theorem for generated states.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def lpfSourceCutoff (M : Nat) : Nat :=
  Nat.floor ((M : Real) ^ ((1 : Real) / 40))

theorem lpf_source_cutoff_bounds (M : Nat) (hM : 1 <= M) :
    And (0 < lpfSourceCutoff M)
      (And ((lpfSourceCutoff M : Real) <= (M : Real) ^ ((1 : Real) / 40))
        ((M : Real) ^ ((1 : Real) / 40) / 2 <= (lpfSourceCutoff M : Real))) := by
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hM
  have hOne : 1 <= (M : Real) ^ ((1 : Real) / 40) := Real.one_le_rpow hMR (by norm_num)
  have hLt := Nat.lt_floor_add_one ((M : Real) ^ ((1 : Real) / 40))
  change (M : Real) ^ ((1 : Real) / 40) < (lpfSourceCutoff M : Real) + 1 at hLt
  have hPosR : (0 : Real) < (lpfSourceCutoff M : Real) := by linarith only [hLt, hOne]
  have hPos : 0 < lpfSourceCutoff M := by exact_mod_cast hPosR
  have hFloor := Nat.floor_le (by positivity : 0 <= (M : Real) ^ ((1 : Real) / 40))
  have hP1 : (1 : Real) <= (lpfSourceCutoff M : Real) := by exact_mod_cast (by omega : 1 <= lpfSourceCutoff M)
  exact And.intro hPos (And.intro hFloor (by linarith only [hLt, hP1]))

theorem lpf_source_cutoff_div_rpow_le (M P : Nat) (hM : 0 < M) (hP : 0 < P)
    (hLower : (M : Real) ^ ((1 : Real) / 40) / 2 <= (P : Real)) (a : Real) :
    (M : Real) ^ a / (P : Real) <= 2 * (M : Real) ^ (a - (1 : Real) / 40) := by
  have hMR : (0 : Real) < (M : Real) := by exact_mod_cast hM
  have hPR : (0 : Real) < (P : Real) := by exact_mod_cast hP
  have hLower' : (M : Real) ^ ((1 : Real) / 40) <= 2 * (P : Real) := by linarith only [hLower]
  have hMul := mul_le_mul_of_nonneg_right hLower'
    (Real.rpow_nonneg hMR.le (a - (1 : Real) / 40))
  have hPower : (M : Real) ^ ((1 : Real) / 40) * (M : Real) ^ (a - (1 : Real) / 40) =
      (M : Real) ^ a := by
    rw [<- Real.rpow_add hMR]
    congr 1
    ring
  rw [hPower] at hMul
  apply (mul_le_mul_iff_of_pos_right hPR).mp
  calc
    _ = (M : Real) ^ a := by field_simp
    _ <= 2 * (P : Real) * (M : Real) ^ (a - (1 : Real) / 40) := hMul
    _ = _ := by ring

theorem lpf_source_log_power_le_nine (M k : Nat) (hM : 1 <= M) (hk : k <= 9) :
    (1 + Real.log (M : Real)) ^ k <= (1 + Real.log (2 * (M : Real))) ^ 9 := by
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hM
  have hPos : (0 : Real) < (M : Real) := by linarith only [hMR]
  have hLog := Real.log_nonneg hMR
  have hLogLe : Real.log (M : Real) <= Real.log (2 * (M : Real)) :=
    Real.log_le_log hPos (by linarith only [hMR])
  have hEll : 1 <= 1 + Real.log (2 * (M : Real)) := by linarith only [hLog, hLogLe]
  calc
    _ <= (1 + Real.log (2 * (M : Real))) ^ k := by gcongr
    _ = (1 + Real.log (2 * (M : Real))) ^ (k : Real) := (Real.rpow_natCast _ _).symm
    _ <= (1 + Real.log (2 * (M : Real))) ^ (9 : Real) :=
      Real.rpow_le_rpow_of_exponent_le hEll (by exact_mod_cast hk)
    _ = _ := Real.rpow_natCast _ 9

theorem lpf_source_four_packet_envelope (M P : Nat) (K C B D : Real)
    (hM : 1 <= M) (hP : 0 < P) (hC : 0 <= C) (hB : 0 <= B) (hD : 0 <= D)
    (hLower : (M : Real) ^ ((1 : Real) / 40) / 2 <= (P : Real)) :
    (8 * K ^ 2 * (1 + Real.log (M : Real)) ^ 4 +
        6 * K ^ 4 * (1 + Real.log (M : Real)) ^ 8) * (M : Real) ^ (119 / 40 : Real) +
      C * (M : Real) ^ ((1 : Real) / 160) *
        ((M : Real) ^ 3 / (P : Real) + (M : Real) ^ (13 / 5 : Real)) *
        (1 + Real.log (2 * (M : Real))) ^ 9 +
      B * (M : Real) ^ (481 / 160 : Real) / (P : Real) ^ 2 +
      D * (M : Real) ^ (481 / 160 : Real) / (P : Real) <=
    (8 * K ^ 2 + 6 * K ^ 4 + 3 * C + 4 * B + 2 * D) *
      (M : Real) ^ (477 / 160 : Real) * (1 + Real.log (2 * (M : Real))) ^ 9 := by
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hM
  have hMPos : 0 < M := by omega
  have hPos : (0 : Real) < (M : Real) := by linarith only [hMR]
  have hPR : (0 : Real) < (P : Real) := by exact_mod_cast hP
  have hExp (a b : Real) (hab : a <= b) : (M : Real) ^ a <= (M : Real) ^ b :=
    Real.rpow_le_rpow_of_exponent_le hMR hab
  have hLog := Real.log_nonneg (show (1 : Real) <= 2 * (M : Real) by linarith only [hMR])
  have hEll : 1 <= (1 + Real.log (2 * (M : Real))) ^ 9 := by
    calc
      _ = (1 : Real) ^ 9 := by norm_num
      _ <= _ := by gcongr; linarith only [hLog]
  have hDiv3 := lpf_source_cutoff_div_rpow_le M P hMPos hP hLower 3
  have hDiv481 := lpf_source_cutoff_div_rpow_le M P hMPos hP hLower (481 / 160)
  have hDiv477 := lpf_source_cutoff_div_rpow_le M P hMPos hP hLower (477 / 160)
  norm_num at hDiv3 hDiv481 hDiv477
  have hCScale : (M : Real) ^ ((1 : Real) / 160) *
      ((M : Real) ^ 3 / (P : Real) + (M : Real) ^ (13 / 5 : Real)) <=
      3 * (M : Real) ^ (477 / 160 : Real) := by
    have hMul := mul_le_mul_of_nonneg_left hDiv3
      (Real.rpow_nonneg hPos.le ((1 : Real) / 160))
    have hProd : (M : Real) ^ ((1 : Real) / 160) * (M : Real) ^ (119 / 40 : Real) =
        (M : Real) ^ (477 / 160 : Real) := by rw [<- Real.rpow_add hPos]; norm_num
    have hProdSmall : (M : Real) ^ ((1 : Real) / 160) * (M : Real) ^ (13 / 5 : Real) =
        (M : Real) ^ (417 / 160 : Real) := by rw [<- Real.rpow_add hPos]; norm_num
    have hSmall := hExp (417 / 160) (477 / 160) (by norm_num)
    rw [mul_add, hProdSmall]
    have hMul' : (M : Real) ^ ((1 : Real) / 160) * ((M : Real) ^ 3 / (P : Real)) <=
        2 * (M : Real) ^ (477 / 160 : Real) := by
      calc
        _ <= (M : Real) ^ ((1 : Real) / 160) * (2 * (M : Real) ^ (119 / 40 : Real)) := hMul
        _ = _ := by rw [<- mul_assoc, mul_comm ((M : Real) ^ ((1 : Real) / 160)) 2,
          mul_assoc, hProd]
    linarith only [hMul', hSmall]
  have hBScale : (M : Real) ^ (481 / 160 : Real) / (P : Real) ^ 2 <=
      4 * (M : Real) ^ (477 / 160 : Real) := by
    have hTwice := div_le_div_of_nonneg_right hDiv481 hPR.le
    have hSmall := hExp (473 / 160) (477 / 160) (by norm_num)
    calc
      _ = ((M : Real) ^ (481 / 160 : Real) / (P : Real)) / (P : Real) := by
        rw [div_div, pow_two]
      _ <= (2 * (M : Real) ^ (477 / 160 : Real)) / (P : Real) := hTwice
      _ = 2 * ((M : Real) ^ (477 / 160 : Real) / (P : Real)) := by ring
      _ <= 4 * (M : Real) ^ (473 / 160 : Real) := by linarith only [hDiv477]
      _ <= _ := by linarith only [hSmall]
  have hMajor :
      (8 * K ^ 2 * (1 + Real.log (M : Real)) ^ 4 +
        6 * K ^ 4 * (1 + Real.log (M : Real)) ^ 8) * (M : Real) ^ (119 / 40 : Real) <=
      (8 * K ^ 2 + 6 * K ^ 4) * (M : Real) ^ (477 / 160 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 9 := by
    have h4 := lpf_source_log_power_le_nine M 4 hM (by norm_num)
    have h8 := lpf_source_log_power_le_nine M 8 hM (by norm_num)
    have hScale := hExp (119 / 40) (477 / 160) (by norm_num)
    calc
      _ <= (8 * K ^ 2 * (1 + Real.log (2 * (M : Real))) ^ 9 +
        6 * K ^ 4 * (1 + Real.log (2 * (M : Real))) ^ 9) *
          (M : Real) ^ (477 / 160 : Real) := by gcongr
      _ = _ := by ring
  have hMinor : C * (M : Real) ^ ((1 : Real) / 160) *
      ((M : Real) ^ 3 / (P : Real) + (M : Real) ^ (13 / 5 : Real)) *
        (1 + Real.log (2 * (M : Real))) ^ 9 <=
      3 * C * (M : Real) ^ (477 / 160 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 9 := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCScale hC)
      (by positivity : 0 <= (1 + Real.log (2 * (M : Real))) ^ 9)
    nlinarith only [h]
  have hKernel : B * (M : Real) ^ (481 / 160 : Real) / (P : Real) ^ 2 <=
      4 * B * (M : Real) ^ (477 / 160 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 9 := by
    calc
      _ = B * ((M : Real) ^ (481 / 160 : Real) / (P : Real) ^ 2) := by ring
      _ <= B * (4 * (M : Real) ^ (477 / 160 : Real)) := mul_le_mul_of_nonneg_left hBScale hB
      _ <= _ := by
        have h := mul_le_mul_of_nonneg_left hEll
          (by positivity : 0 <= 4 * B * (M : Real) ^ (477 / 160 : Real))
        nlinarith only [h]
  have hTail : D * (M : Real) ^ (481 / 160 : Real) / (P : Real) <=
      2 * D * (M : Real) ^ (477 / 160 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 9 := by
    calc
      _ = D * ((M : Real) ^ (481 / 160 : Real) / (P : Real)) := by ring
      _ <= D * (2 * (M : Real) ^ (477 / 160 : Real)) := mul_le_mul_of_nonneg_left hDiv481 hD
      _ <= _ := by
        have h := mul_le_mul_of_nonneg_left hEll
          (by positivity : 0 <= 2 * D * (M : Real) ^ (477 / 160 : Real))
        nlinarith only [h]
  have hTotal := add_le_add (add_le_add (add_le_add hMajor hMinor) hKernel) hTail
  nlinarith only [hTotal]

theorem lpf_source_log_absorption (M : Nat) (hM : 1 <= M) :
    (1 + Real.log (2 * (M : Real))) ^ 9 <=
      (1442 : Real) ^ 9 * (M : Real) ^ ((1 : Real) / 160) := by
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hM
  have hPos : (0 : Real) < (M : Real) := by linarith only [hMR]
  have hRootPos := Real.rpow_pos_of_pos hPos ((1 : Real) / 1440)
  have hRootOne := Real.one_le_rpow hMR (show (0 : Real) <= 1 / 1440 by norm_num)
  have hLogBound := Real.log_le_sub_one_of_pos hRootPos
  rw [Real.log_rpow hPos] at hLogBound
  have hTwo := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
  have hLog : 1 + Real.log (2 * (M : Real)) <=
      1442 * (M : Real) ^ ((1 : Real) / 1440) := by
    rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hPos.ne']
    nlinarith only [hLogBound, hTwo, hRootOne]
  have hNonneg : 0 <= 1 + Real.log (2 * (M : Real)) := by
    have := Real.log_nonneg (show (1 : Real) <= 2 * (M : Real) by linarith only [hMR])
    linarith
  calc
    _ <= (1442 * (M : Real) ^ ((1 : Real) / 1440)) ^ 9 := by gcongr
    _ = (1442 : Real) ^ 9 * ((M : Real) ^ ((1 : Real) / 1440)) ^ 9 := mul_pow _ _ _
    _ = (1442 : Real) ^ 9 * (M : Real) ^ ((1 : Real) / 160) := by
      rw [<- Real.rpow_natCast ((M : Real) ^ ((1 : Real) / 1440)) 9,
        <- Real.rpow_mul hPos.le]
      norm_num

theorem lpf_fixed_source_log_power_bound :
    exists A : Real, And (0 < A)
      (forall {N : Nat} [NeZero N] (M s L : Nat) (T : Finset Nat),
        2 ^ 18 <= M -> Dvd.dvd M N ->
        (forall q, 0 < q -> q <= lpfSourceCutoff M -> Dvd.dvd q N) ->
        (M : Real) / 4 <= (s : Real) -> s + L <= 2 * M -> L <= M -> s + L < N ->
        2 * M < N -> (forall n, Membership.mem T n -> And (0 < n) (n <= 2 * M)) ->
        T.card <= 2 * M ->
        Finset.sum T (fun n => norm (lpfFixedSourceError N s L n) ^ 2) <=
          A * (M : Real) ^ (477 / 160 : Real) * (1 + Real.log (2 * (M : Real))) ^ 9) := by
  choose K C B D hK hC hB hD hBudget using lpf_fixed_source_four_packet_budget
  let A : Real := 4 * (8 * K ^ 2 + 6 * K ^ 4 + 3 * C + 4 * B + 2 * D)
  refine Exists.intro A (And.intro (by dsimp [A]; positivity) ?_)
  intro N instN M s L T hM hDivM hDiv hStart hTop hL hInput hNTop hT hCard
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hCut := lpf_source_cutoff_bounds M hOne
  have h := hBudget M (lpfSourceCutoff M) s L T hM hCut.1 hCut.2.1
    hDivM hDiv hStart hTop hL hInput hNTop hT hCard
  have hEnvelope := lpf_source_four_packet_envelope M (lpfSourceCutoff M) K C B D
    hOne hCut.1 hC.le hB.le hD.le hCut.2.2
  have hFinal := h.trans (mul_le_mul_of_nonneg_left hEnvelope (show (0 : Real) <= 4 by norm_num))
  calc
    _ <= 4 * ((8 * K ^ 2 + 6 * K ^ 4 + 3 * C + 4 * B + 2 * D) *
      (M : Real) ^ (477 / 160 : Real) * (1 + Real.log (2 * (M : Real))) ^ 9) := hFinal
    _ = _ := by dsimp [A]; ring

theorem lpf_fixed_source_power_bound :
    exists A : Real, And (0 < A)
      (forall {N : Nat} [NeZero N] (M s L : Nat) (T : Finset Nat),
        2 ^ 18 <= M -> Dvd.dvd M N ->
        (forall q, 0 < q -> q <= lpfSourceCutoff M -> Dvd.dvd q N) ->
        (M : Real) / 4 <= (s : Real) -> s + L <= 2 * M -> L <= M -> s + L < N ->
        2 * M < N -> (forall n, Membership.mem T n -> And (0 < n) (n <= 2 * M)) ->
        T.card <= 2 * M ->
        Finset.sum T (fun n => norm (lpfFixedSourceError N s L n) ^ 2) <=
          A * (M : Real) ^ (239 / 80 : Real)) := by
  choose B hB hBudget using lpf_fixed_source_log_power_bound
  let A : Real := B * (1442 : Real) ^ 9
  refine Exists.intro A (And.intro (by dsimp [A]; positivity) ?_)
  intro N instN M s L T hM hDivM hDiv hStart hTop hL hInput hNTop hT hCard
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hPos : (0 : Real) < (M : Real) := by exact_mod_cast (by omega : 0 < M)
  have h := hBudget M s L T hM hDivM hDiv hStart hTop hL hInput hNTop hT hCard
  have hLog := lpf_source_log_absorption M hOne
  have hMul := mul_le_mul_of_nonneg_left hLog
    (by positivity : 0 <= B * (M : Real) ^ (477 / 160 : Real))
  calc
    _ <= B * (M : Real) ^ (477 / 160 : Real) *
      ((1442 : Real) ^ 9 * (M : Real) ^ ((1 : Real) / 160)) := h.trans hMul
    _ = A * ((M : Real) ^ (477 / 160 : Real) * (M : Real) ^ ((1 : Real) / 160)) := by
      dsimp [A]
      ring
    _ = A * (M : Real) ^ (239 / 80 : Real) := by
      rw [<- Real.rpow_add hPos]
      norm_num

end PrimeFactorOscillations.LPF
