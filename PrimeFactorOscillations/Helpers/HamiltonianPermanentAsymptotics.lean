/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermanentUniform

/-! # Public normalized permanent asymptotics

The actual scaled permanent expansion is normalized by its positive
determinant factor. The signed first correction is kept explicitly in
the second-order theorem and is bounded only for the first-order consumer.
Every sufficiently-large threshold is uniform over admissible kernels.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem stochastic_permanent_relative_correction_polylog_uniform (delta K : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) :
    Exists (fun N0 : Nat => And (16 <= N0)
      (forall n : Nat, N0 <= n ->
        forall (T : Matrix (Fin n) (Fin n) Real) (q a : Real),
          (n : Real) * q = 1 -> 1 <= a -> a <= (Real.log (n : Real)) ^ K ->
          (forall i, Finset.sum Finset.univ (fun j => T i j) = 1) ->
          (forall j, Finset.sum Finset.univ (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          And
            (abs ((((n : Real) ^ n / (n.factorial : Real)) * weightedPermutationSum T) /
                realGramDeterminantFactor (centeredKernel T q) 1 -
                (1 + stochasticPermanentFirstCorrection T q)) <=
              (1 + a) ^ 24 * hamiltonianPermanentUniformBudget delta / (n : Real) ^ 2)
            (abs (stochasticPermanentFirstCorrection T q) <=
              21 * a ^ 2 / (delta ^ 3 * (n : Real))))) := by
  let estimate := stochastic_permanent_first_correction_polylog_uniform delta K hDelta0 hDelta1
  refine Exists.intro estimate.choose (And.intro estimate.choose_spec.1 ?_)
  intro n hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  let D := realGramDeterminantFactor (centeredKernel T q) 1
  let Q := stochasticPermanentFirstCorrection T q
  let x := ((n : Real) ^ n / (n.factorial : Real)) * weightedPermutationSum T
  have hn16 : 16 <= n := le_trans estimate.choose_spec.1 hn
  letI : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 (by omega))
  have hN0 : 0 < (n : Real) := Nat.cast_pos.mpr (by omega)
  have hD1 : 1 <= D :=
    stochasticGramDeterminantFactor_one_le T q a delta hq hRow hNonneg hUpper
      hDelta0 hDelta1 hNorm
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) hD1
  have hPer := estimate.choose_spec.2 n hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  change abs (x - D * (1 + Q)) <=
    D * (1 + a) ^ 24 * hamiltonianPermanentUniformBudget delta / (n : Real) ^ 2 at hPer
  have hRelative : abs (x / D - (1 + Q)) <=
      (1 + a) ^ 24 * hamiltonianPermanentUniformBudget delta / (n : Real) ^ 2 := by
    calc
      _ = abs ((x - D * (1 + Q)) / D) := by
        congr 1
        field_simp [ne_of_gt hD] <;> ring
      _ = abs (x - D * (1 + Q)) / D := by rw [abs_div, abs_of_pos hD]
      _ <= (D * (1 + a) ^ 24 * hamiltonianPermanentUniformBudget delta /
          (n : Real) ^ 2) / D :=
        div_le_div_of_nonneg_right hPer hD.le
      _ = _ := by field_simp [ne_of_gt hD] <;> ring
  have hqValue : q = 1 / (n : Real) := by
    calc
      _ = ((n : Real) * q) / (n : Real) := by field_simp [ne_of_gt hN0]
      _ = _ := by rw [hq]
  have hQ := stochasticPermanentFirstCorrection_bound T q a (1 - delta)
    (by simpa only [Fintype.card_fin] using hq) ha
    (by simpa only [Fintype.card_fin] using (show 2 <= n by omega))
    hRow hCol hNonneg hUpper (by linarith only [hDelta0]) hNorm
  have hGap : 1 - (1 - delta) = delta := by ring
  rw [hGap] at hQ
  have hQScaled : delta ^ 3 * abs Q <= 21 * a ^ 2 / (n : Real) := by
    calc
      _ <= 21 * a ^ 2 * q := hQ
      _ = _ := by rw [hqValue]; ring
  have hCleared : delta ^ 3 * abs Q <=
      delta ^ 3 * (21 * a ^ 2 / (delta ^ 3 * (n : Real))) := by
    calc
      _ <= 21 * a ^ 2 / (n : Real) := hQScaled
      _ = _ := by field_simp [ne_of_gt hDelta0] <;> ring
  exact And.intro hRelative (le_of_mul_le_mul_left hCleared (pow_pos hDelta0 3))


theorem hamiltonian_permanent_polylog_first_order_budget (delta K : Real)
    (hDelta : 0 < delta) (hK : 0 < K) :
    Exists (fun N0 : Nat => And (16 <= N0)
      (forall n : Nat, N0 <= n -> forall a : Real,
        1 <= a -> a <= (Real.log (n : Real)) ^ K ->
          21 * a ^ 2 / (delta ^ 3 * (n : Real)) +
            abs (hamiltonianPermanentUniformBudget delta) * (1 + a) ^ 24 /
              (n : Real) ^ 2 <= (n : Real) ^ (-1 / 8 : Real))) := by
  let M := abs (hamiltonianPermanentUniformBudget delta)
  let c1 := delta ^ 3 / 42
  let c2 := 1 / (2 * (1 + M) * (2 : Real) ^ 24)
  have hM : 0 <= M := abs_nonneg _
  have hMPlus : 0 < 1 + M := by linarith only [hM]
  have hc1 : 0 < c1 := by dsimp only [c1]; positivity
  have hc2 : 0 < c2 := by dsimp only [c2]; positivity
  let first := Filter.eventually_atTop.mp
    ((_root_.isLittleO_log_rpow_rpow_atTop (s := (7 / 8 : Real))
      (K * 2) (by norm_num)).bound hc1)
  let second := Filter.eventually_atTop.mp
    ((_root_.isLittleO_log_rpow_rpow_atTop (s := (15 / 8 : Real))
      (K * 24) (by norm_num)).bound hc2)
  let x1 := first.choose
  let x2 := second.choose
  let x0 := 16 + Real.exp 1 + max 0 x1 + max 0 x2
  let N0 := max 16 (Nat.ceil x0)
  refine Exists.intro N0 (And.intro (le_max_left _ _) ?_)
  intro n hn a ha hA
  have hNat : Nat.ceil x0 <= n := le_trans (le_max_right _ _) hn
  have hx : x0 <= (n : Real) := le_trans (Nat.le_ceil x0) (by exact_mod_cast hNat)
  have hMax10 : 0 <= max 0 x1 := le_max_left _ _
  have hMax11 : x1 <= max 0 x1 := le_max_right _ _
  have hMax20 : 0 <= max 0 x2 := le_max_left _ _
  have hMax21 : x2 <= max 0 x2 := le_max_right _ _
  have hExp0 : 0 < Real.exp 1 := Real.exp_pos _
  have hx1 : x1 <= (n : Real) := by
    dsimp only [x0] at hx
    linarith only [hx, hMax10, hMax11, hMax20, hExp0]
  have hx2 : x2 <= (n : Real) := by
    dsimp only [x0] at hx
    linarith only [hx, hMax10, hMax20, hMax21, hExp0]
  have hxExp : Real.exp 1 <= (n : Real) := by
    dsimp only [x0] at hx
    linarith only [hx, hMax10, hMax20]
  have hN16 : (16 : Real) <= (n : Real) := by
    have h := le_trans (le_max_left 16 (Nat.ceil x0)) hn
    exact_mod_cast h
  have hN : 0 < (n : Real) := by linarith only [hN16]
  have hLog1 : 1 <= Real.log (n : Real) := by
    calc
      _ = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ <= _ := Real.log_le_log hExp0 hxExp
  have hLog0 : 0 <= Real.log (n : Real) := le_trans (by norm_num) hLog1
  have hLogK1 : 1 <= (Real.log (n : Real)) ^ K := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : Real) <= 1) hLog1 hK.le
  have hLogPower : forall j : Nat,
      ((Real.log (n : Real)) ^ K) ^ j =
        (Real.log (n : Real)) ^ (K * (j : Real)) := by
    intro j
    calc
      _ = ((Real.log (n : Real)) ^ K) ^ (j : Real) :=
        (Real.rpow_natCast _ j).symm
      _ = _ := (Real.rpow_mul hLog0 K (j : Real)).symm
  have hAPower : a ^ 2 <= (Real.log (n : Real)) ^ (K * 2) := by
    calc
      _ <= ((Real.log (n : Real)) ^ K) ^ 2 :=
        wick_nonnegative_power_le _ _ (by linarith only [ha]) hA 2
      _ = _ := hLogPower 2
  have hHPower : (1 + a) ^ 24 <=
      (2 : Real) ^ 24 * (Real.log (n : Real)) ^ (K * 24) := by
    calc
      _ <= (2 * ((Real.log (n : Real)) ^ K)) ^ 24 :=
        wick_nonnegative_power_le _ _ (by linarith only [ha])
          (by linarith only [hA, hLogK1]) 24
      _ = _ := by
        rw [mul_pow, hLogPower 24]
        norm_num only [Nat.cast_ofNat]
  have hBound1 := first.choose_spec (n : Real) hx1
  have hBound2 := second.choose_spec (n : Real) hx2
  simp only [Real.norm_eq_abs] at hBound1 hBound2
  rw [abs_of_nonneg (Real.rpow_nonneg hLog0 (K * 2)),
    abs_of_nonneg (Real.rpow_nonneg hN.le (7 / 8 : Real))] at hBound1
  rw [abs_of_nonneg (Real.rpow_nonneg hLog0 (K * 24)),
    abs_of_nonneg (Real.rpow_nonneg hN.le (15 / 8 : Real))] at hBound2
  have hPow1 : (n : Real) ^ (7 / 8 : Real) =
      (n : Real) ^ (-1 / 8 : Real) * (n : Real) := by
    calc
      _ = (n : Real) ^ ((-1 / 8 : Real) + 1) := by congr 1 <;> norm_num
      _ = _ := by rw [Real.rpow_add hN, Real.rpow_one]
  have hPow2 : (n : Real) ^ (15 / 8 : Real) =
      (n : Real) ^ (-1 / 8 : Real) * (n : Real) ^ 2 := by
    calc
      _ = (n : Real) ^ ((-1 / 8 : Real) + 2) := by congr 1 <;> norm_num
      _ = (n : Real) ^ (-1 / 8 : Real) * (n : Real) ^ (2 : Real) :=
        Real.rpow_add hN _ _
      _ = _ := congrArg (fun z : Real => (n : Real) ^ (-1 / 8 : Real) * z)
        (Real.rpow_natCast (n : Real) 2)
  have hFirstNumerator : 21 * a ^ 2 <=
      21 * (c1 * (n : Real) ^ (7 / 8 : Real)) :=
    mul_le_mul_of_nonneg_left (le_trans hAPower hBound1) (by norm_num)
  have hFirstProduct :
      (21 * a ^ 2 / (delta ^ 3 * (n : Real))) * (delta ^ 3 * (n : Real)) <=
        ((n : Real) ^ (-1 / 8 : Real) / 2) * (delta ^ 3 * (n : Real)) := by
    calc
      _ = 21 * a ^ 2 := by field_simp [ne_of_gt hDelta, ne_of_gt hN]
      _ <= 21 * (c1 * (n : Real) ^ (7 / 8 : Real)) := hFirstNumerator
      _ = _ := by rw [hPow1]; dsimp only [c1]; ring
  have hFirst := le_of_mul_le_mul_right hFirstProduct (mul_pos (pow_pos hDelta 3) hN)
  have hCoef : M * (2 : Real) ^ 24 * c2 <= 1 / 2 := by
    calc
      _ = M * ((2 : Real) ^ 24 * c2) := by ring
      _ <= (1 + M) * ((2 : Real) ^ 24 * c2) :=
        mul_le_mul_of_nonneg_right (by linarith only [hM] : M <= 1 + M) (by positivity)
      _ = _ := by dsimp only [c2]; field_simp [ne_of_gt hMPlus] <;> ring
  have hSecondNumerator : M * (1 + a) ^ 24 <= (n : Real) ^ (15 / 8 : Real) / 2 := by
    calc
      _ <= M * ((2 : Real) ^ 24 * (Real.log (n : Real)) ^ (K * 24)) :=
        mul_le_mul_of_nonneg_left hHPower hM
      _ = (M * (2 : Real) ^ 24) * (Real.log (n : Real)) ^ (K * 24) := by ring
      _ <= (M * (2 : Real) ^ 24) * (c2 * (n : Real) ^ (15 / 8 : Real)) :=
        mul_le_mul_of_nonneg_left hBound2 (by positivity)
      _ = (M * (2 : Real) ^ 24 * c2) * (n : Real) ^ (15 / 8 : Real) := by ring
      _ <= (1 / 2 : Real) * (n : Real) ^ (15 / 8 : Real) :=
        mul_le_mul_of_nonneg_right hCoef (Real.rpow_nonneg hN.le _)
      _ = _ := by ring
  have hSecond : M * (1 + a) ^ 24 / (n : Real) ^ 2 <=
      (n : Real) ^ (-1 / 8 : Real) / 2 := by
    calc
      _ <= ((n : Real) ^ (15 / 8 : Real) / 2) / (n : Real) ^ 2 :=
        div_le_div_of_nonneg_right hSecondNumerator (sq_nonneg _)
      _ = _ := by rw [hPow2]; field_simp [ne_of_gt hN] <;> ring
  calc
    _ <= (n : Real) ^ (-1 / 8 : Real) / 2 + (n : Real) ^ (-1 / 8 : Real) / 2 :=
      add_le_add hFirst hSecond
    _ = _ := by ring


theorem stochastic_permanent_first_order_polylog_uniform (delta K : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) (hK : 0 < K) :
    Exists (fun N0 : Nat => And (16 <= N0)
      (forall n : Nat, N0 <= n ->
        forall (T : Matrix (Fin n) (Fin n) Real) (q a : Real),
          (n : Real) * q = 1 -> 1 <= a -> a <= (Real.log (n : Real)) ^ K ->
          (forall i, Finset.sum Finset.univ (fun j => T i j) = 1) ->
          (forall j, Finset.sum Finset.univ (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          abs ((((n : Real) ^ n / (n.factorial : Real)) * weightedPermutationSum T) /
              realGramDeterminantFactor (centeredKernel T q) 1 - 1) <=
            (n : Real) ^ (-1 / 8 : Real))) := by
  let relative := stochastic_permanent_relative_correction_polylog_uniform
    delta K hDelta0 hDelta1
  let scalar := hamiltonian_permanent_polylog_first_order_budget delta K hDelta0 hK
  let N0 := max relative.choose scalar.choose
  refine Exists.intro N0 (And.intro
    (le_trans relative.choose_spec.1 (le_max_left _ _)) ?_)
  intro n hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hnR : relative.choose <= n := le_trans (le_max_left _ _) hn
  have hnS : scalar.choose <= n := le_trans (le_max_right _ _) hn
  let x := (((n : Real) ^ n / (n.factorial : Real)) * weightedPermutationSum T) /
    realGramDeterminantFactor (centeredKernel T q) 1
  let Q := stochasticPermanentFirstCorrection T q
  let C := hamiltonianPermanentUniformBudget delta
  have hRelative := relative.choose_spec.2 n hnR T q a hq ha hA
    hRow hCol hNonneg hUpper hNorm
  change And (abs (x - (1 + Q)) <= (1 + a) ^ 24 * C / (n : Real) ^ 2)
    (abs Q <= 21 * a ^ 2 / (delta ^ 3 * (n : Real))) at hRelative
  have hH : 0 <= (1 + a) ^ 24 := by positivity
  have hC : (1 + a) ^ 24 * C / (n : Real) ^ 2 <=
      abs C * (1 + a) ^ 24 / (n : Real) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    calc
      _ <= (1 + a) ^ 24 * abs C := mul_le_mul_of_nonneg_left (le_abs_self C) hH
      _ = _ := mul_comm _ _
  change abs (x - 1) <= (n : Real) ^ (-1 / 8 : Real)
  calc
    _ = abs ((x - (1 + Q)) + Q) := by congr 1 <;> ring
    _ <= abs (x - (1 + Q)) + abs Q := abs_add_le _ _
    _ <= abs C * (1 + a) ^ 24 / (n : Real) ^ 2 +
        21 * a ^ 2 / (delta ^ 3 * (n : Real)) :=
      add_le_add (le_trans hRelative.1 hC) hRelative.2
    _ = 21 * a ^ 2 / (delta ^ 3 * (n : Real)) +
        abs C * (1 + a) ^ 24 / (n : Real) ^ 2 := add_comm _ _
    _ <= _ := scalar.choose_spec.2 n hnS a ha hA

end PrimeFactorOscillations
