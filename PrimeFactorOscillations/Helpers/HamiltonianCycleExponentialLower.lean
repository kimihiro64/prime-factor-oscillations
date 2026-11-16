/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAperiodicFamilyLimit
import PrimeFactorOscillations.Helpers.HamiltonianCycleScaling
import PrimeFactorOscillations.Helpers.HamiltonianPrescribedPathMinor
import PrimeFactorOscillations.Helpers.HamiltonianSublogBipartiteCount

/-! # A finite-support exponential cycle lower bound and exact unscaling

The actual signed cycle/permanent comparison, positive permanent
and determinant lower bound supply an independent positive cycle
mass on any finite stochastic support. Two-sided scaling retains
its full product before returning to the unrepaired kernel.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_cycle_sum_two_sided_scaling
    (M : Matrix Iota Iota Real) (x y : Iota -> Real) :
    hamiltonianCycleSum (hamiltonianCrossScaled M x y) =
      (Finset.univ.prod x * Finset.univ.prod y) * hamiltonianCycleSum M := by
  unfold hamiltonianCycleSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases h : (hamiltonianPermutationOrbits f).card = 1
  . simp only [h, ite_true, hamiltonianCrossScaled, Finset.prod_mul_distrib]
    rw [Equiv.prod_comp f x]
    ring
  . simp only [h, ite_false, mul_zero]

theorem hamiltonian_cycle_unscale_lower
    (M : Matrix Iota Iota Real) (x y : Iota -> Real) (B L : Real)
    (hNonneg : forall i j, 0 <= M i j)
    (hx : forall i, 0 < x i) (hy : forall i, 0 < y i)
    (hLog : Finset.univ.sum (fun i => Real.log (x i)) +
      Finset.univ.sum (fun i => Real.log (y i)) <= B)
    (hCount : L <= hamiltonianCycleSum (hamiltonianCrossScaled M x y)) :
    Real.exp (-B) * L <= hamiltonianCycleSum M := by
  have hMass : 0 <= hamiltonianCycleSum M := hamiltonian_cycle_sum_nonnegative M hNonneg
  have hProduct : Finset.univ.prod x * Finset.univ.prod y <= Real.exp B := by
    rw [hamiltonian_positive_product_exp x hx, hamiltonian_positive_product_exp y hy,
      <- Real.exp_add]
    exact Real.exp_le_exp.mpr hLog
  rw [hamiltonian_cycle_sum_two_sided_scaling] at hCount
  have hCompare : L <= Real.exp B * hamiltonianCycleSum M :=
    hCount.trans (mul_le_mul_of_nonneg_right hProduct hMass)
  have h := mul_le_mul_of_nonneg_left hCompare (Real.exp_pos (-B)).le
  have hCancel : Real.exp (-B) * Real.exp B = 1 := by
    rw [<- Real.exp_add, neg_add_cancel, Real.exp_zero]
  simpa only [<- mul_assoc, hCancel, one_mul] using h

theorem hamiltonian_cycle_lower_from_half_ratio
    (n P D C H : Real) (hn : 0 < n) (hP : 0 < P) (hD : 0 < D)
    (hPer : (1 / 2 : Real) * Real.exp (-n) <= P)
    (hSignal : Real.exp (-H) <= D)
    (hRatio : (1 / 2 : Real) <= (n * C / P) / D) :
    Real.exp (-n - H) / (4 * n) <= C := by
  have hR := mul_le_mul_of_nonneg_right hRatio (mul_nonneg hP.le hD.le)
  have hClear : ((n * C / P) / D) * (P * D) = n * C := by
    field_simp [ne_of_gt hP, ne_of_gt hD]
  rw [hClear] at hR
  have hPD := mul_le_mul hPer hSignal (Real.exp_pos (-H)).le hP.le
  have hExp : Real.exp (-n) * Real.exp (-H) = Real.exp (-n - H) := by
    rw [<- Real.exp_add]
    congr 1
  have hPD' : (1 / 2 : Real) * Real.exp (-n - H) <= P * D := by
    simpa only [mul_assoc, hExp] using hPD
  have hFinal : Real.exp (-n - H) / 4 <= n * C := by
    nlinarith only [hR, hPD']
  apply le_of_mul_le_mul_right _ hn
  have hDiv : (Real.exp (-n - H) / (4 * n)) * n = Real.exp (-n - H) / 4 := by
    field_simp [ne_of_gt hn]
  rw [hDiv]
  simpa only [mul_comm] using hFinal

universe u

theorem stochastic_aperiodic_cycle_exponential_lower_uniform
    (delta : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          a ^ 2 <= hamiltonianAperiodicSublogDensity delta *
            Real.log (Fintype.card J : Real) ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          0 < hamiltonianCycleSum T /\
            Real.exp (-(Fintype.card J : Real) - ((a - 1) + (a - 1) / delta)) /
              (4 * (Fintype.card J : Real)) <= hamiltonianCycleSum T := by
  choose A hA hRelative using
    stochastic_aperiodic_relative_envelope_uniform.{u} delta hDelta hDelta1
  choose P hP hPositive using
    stochastic_permanent_positive_polylog_uniform.{u} delta 1 hDelta hDelta1 (by norm_num)
  choose W hW hPower using hamiltonian_log_power_dominated_uniform
    16 (by norm_num) 0 (1 / 18) (by norm_num)
  let D := Nat.ceil (Real.exp hamiltonianAperiodicTailLogThreshold)
  let N0 := max A (max P (max W D))
  refine Exists.intro N0 (And.intro (hA.trans (le_max_left _ _)) ?_)
  intro J instF instD instN hn T q a hq ha hSmall hRow hCol hNonneg hUpper hNorm
  have hnA : A <= Fintype.card J := (le_max_left _ _).trans hn
  have hnP : P <= Fintype.card J := by dsimp only [N0] at hn; omega
  have hnW : W <= Fintype.card J := by dsimp only [N0] at hn; omega
  have hnD : D <= Fintype.card J := by dsimp only [N0] at hn; omega
  let n : Real := Fintype.card J
  have hn256 : (256 : Real) <= n := by
    dsimp only [n]
    exact_mod_cast hA.trans hnA
  have hn1 : 1 <= n := by linarith only [hn256]
  have hnPos : 0 < n := by linarith only [hn256]
  have hLog0 : 0 <= Real.log n := Real.log_nonneg hn1
  have hBudget := hamiltonian_aperiodic_density_budget delta hDelta
  have hASquare : a <= a ^ 2 := by nlinarith only [ha, sq_nonneg (a - 1)]
  have hCap : a <= Real.log n := by
    calc
      _ <= a ^ 2 := hASquare
      _ <= hamiltonianAperiodicSublogDensity delta * Real.log n := hSmall
      _ <= 1 * Real.log n := mul_le_mul_of_nonneg_right hBudget.2.2.1 hLog0
      _ = _ := one_mul _
  have hExpN : Real.exp hamiltonianAperiodicTailLogThreshold <= n :=
    (Nat.le_ceil _).trans (by
      dsimp only [n]
      dsimp only [D] at hnD
      exact_mod_cast hnD)
  have hLog : hamiltonianAperiodicTailLogThreshold <= Real.log n := by
    have h := Real.log_le_log (Real.exp_pos _) hExpN
    simpa only [Real.log_exp] using h
  have hExponent : hamiltonianAperiodicErrorConstant delta * a ^ 2 <= Real.log n / 18 := by
    calc
      _ <= hamiltonianAperiodicErrorConstant delta *
          (hamiltonianAperiodicSublogDensity delta * Real.log n) :=
        mul_le_mul_of_nonneg_left hSmall hBudget.1.le
      _ = (hamiltonianAperiodicErrorConstant delta * hamiltonianAperiodicSublogDensity delta) *
          Real.log n := by ring
      _ <= (1 / 18 : Real) * Real.log n :=
        mul_le_mul_of_nonneg_right hBudget.2.2.2 hLog0
      _ = _ := by ring
  have hSixteen : 16 <= n ^ (1 / 18 : Real) := by
    simpa only [pow_zero, mul_one] using hPower (Fintype.card J) hnW
  have hRecip : n ^ (-1 / 18 : Real) <= 1 / 16 := by
    have hInv := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 16) hSixteen
    have hId : n ^ (-1 / 18 : Real) = 1 / n ^ (1 / 18 : Real) := by
      rw [show (-1 / 18 : Real) = -(1 / 18 : Real) by ring, Real.rpow_neg hnPos.le]
      exact (one_div _).symm
    rw [hId]
    exact hInv
  have hRate :
      Real.exp ((a - 1) + (a - 1) / delta) *
        hamiltonianAperiodicResidualEnvelope n a <= 1 / 2 := by
    calc
      _ <= 8 * n ^ (-1 / 9 : Real) *
          Real.exp (hamiltonianAperiodicErrorConstant delta * a ^ 2) :=
        hamiltonian_aperiodic_relative_log_envelope n a delta hn1 ha hDelta hCap hLog
      _ = 8 * (n ^ (-1 / 9 : Real) *
          Real.exp (hamiltonianAperiodicErrorConstant delta * a ^ 2)) := by ring
      _ <= 8 * n ^ (-1 / 18 : Real) := mul_le_mul_of_nonneg_left
        (hamiltonian_aperiodic_power_from_exponent n _ a hnPos hExponent) (by norm_num)
      _ <= 8 * (1 / 16 : Real) := mul_le_mul_of_nonneg_left hRecip (by norm_num)
      _ = _ := by norm_num
  have hRaw := hRelative J hnA T q a hq ha hCap hRow hCol hNonneg hUpper hNorm
  have hData := hPositive J hnP T q a hq ha (by simpa only [Real.rpow_one] using hCap)
    hRow hCol hNonneg hUpper hNorm
  have hPer := hamiltonian_positive_permanent_exponential_lower T q hData
  have hSignal := stochastic_aperiodic_determinant_lower_bound T q a delta hq hDelta
    hRow hCol hNonneg hUpper hNorm
  have hRatio : (1 / 2 : Real) <=
      ((n * hamiltonianCycleSum T / weightedPermutationSum T) /
        Matrix.det ((1 : Matrix J J Real) - centeredKernel T q)) := by
    have hRel := hRaw.2.2.trans hRate
    have hLower := (abs_le.mp hRel).1
    linarith only [hLower]
  have hBound := hamiltonian_cycle_lower_from_half_ratio n
    (weightedPermutationSum T) (Matrix.det ((1 : Matrix J J Real) - centeredKernel T q))
    (hamiltonianCycleSum T) ((a - 1) + (a - 1) / delta)
    hnPos hRaw.1 hSignal.1 hPer hSignal.2 hRatio
  refine And.intro ?_ hBound
  exact (div_pos (Real.exp_pos _) (mul_pos (by norm_num) hnPos)).trans_le hBound


theorem hamiltonian_cycle_mass_from_half_ratio
    (n P C : Real) (hn : 0 < n) (hP : 0 < P)
    (hRatio : (1 / 2 : Real) <= n * C / P) :
    P / (2 * n) <= C := by
  have h := mul_le_mul_of_nonneg_right hRatio hP.le
  have hClear : (n * C / P) * P = n * C := by field_simp [ne_of_gt hP]
  rw [hClear] at h
  apply le_of_mul_le_mul_right _ hn
  have hDiv : (P / (2 * n)) * n = P / 2 := by field_simp [ne_of_gt hn]
  rw [hDiv]
  nlinarith only [h]

theorem stochastic_bipartite_cycle_exponential_lower_uniform
    (rho : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          a <= hamiltonianSublogCountDensity rho * Real.log (Fintype.card J : Real) ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= rho ->
          0 < hamiltonianCycleSum (bipartiteLift T) /\
            Real.exp (-2 * (Fintype.card J : Real)) /
              (2 * (Fintype.card J : Real)) <= hamiltonianCycleSum (bipartiteLift T) := by
  choose A hA hCount using stochastic_unoriented_bipartite_sublog_uniform.{u}
    rho hRho0 hRho1
  choose W hW hPower using hamiltonian_log_power_dominated_uniform
    2 (by norm_num) 0 (1 / 2) (by norm_num)
  let N0 := max A W
  refine Exists.intro N0 (And.intro (hA.trans (le_max_left _ _)) ?_)
  intro J instF instD instN hn T q a hq ha hCap hRow hCol hNonneg hUpper hNorm
  have hnA : A <= Fintype.card J := (le_max_left _ _).trans hn
  have hnW : W <= Fintype.card J := (le_max_right _ _).trans hn
  let k := Fintype.card J
  let n : Real := k
  let F : Real := k.factorial
  let P := F ^ 2 / n ^ (2 * k)
  have hk : 1 <= k := by
    have h := hA.trans hnA
    dsimp only [k]
    omega
  have hnPos : 0 < n := by
    dsimp only [n]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hF : 0 < F := by dsimp only [F]; exact_mod_cast Nat.factorial_pos k
  have hP : 0 < P := div_pos (sq_pos_of_pos hF) (pow_pos hnPos _)
  have hTwo : 2 <= n ^ (1 / 2 : Real) := by
    simpa only [pow_zero, mul_one] using hPower k hnW
  have hRecip : n ^ (-1 / 2 : Real) <= 1 / 2 := by
    have hInv := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2) hTwo
    have hId : n ^ (-1 / 2 : Real) = 1 / n ^ (1 / 2 : Real) := by
      rw [show (-1 / 2 : Real) = -(1 / 2 : Real) by ring, Real.rpow_neg hnPos.le]
      exact (one_div _).symm
    rw [hId]
    exact hInv
  have hRaw := hCount J hnA T q a hq ha hCap hRow hCol hNonneg hUpper hNorm
  have hAbs : abs ((2 * n * n ^ (2 * k) / F ^ 2) *
      (hamiltonianCycleSum (bipartiteLift T) / 2) - 1) <= 1 / 2 :=
    hRaw.trans hRecip
  have hSame : (2 * n * n ^ (2 * k) / F ^ 2) *
      (hamiltonianCycleSum (bipartiteLift T) / 2) =
        n * hamiltonianCycleSum (bipartiteLift T) / P := by
    dsimp only [P]
    field_simp [ne_of_gt hnPos, ne_of_gt hF]
    <;> ring
  rw [hSame] at hAbs
  have hRatio : (1 / 2 : Real) <= n * hamiltonianCycleSum (bipartiteLift T) / P := by
    have h := (abs_le.mp hAbs).1
    linarith only [h]
  have hBase := hamiltonian_factorial_exponential_lower k hk
  have hPower0 : 0 <= F / n ^ k := div_nonneg hF.le (pow_nonneg hnPos.le k)
  have hSquare := mul_le_mul hBase hBase (Real.exp_pos (-n)).le hPower0
  have hPow : (n ^ k) ^ 2 = n ^ (2 * k) := by
    rw [<- pow_mul, Nat.mul_comm k 2]
  have hExp : Real.exp (-n) ^ 2 = Real.exp (-2 * n) := by
    rw [pow_two, <- Real.exp_add]
    exact congrArg Real.exp (by ring)
  have hSignal : Real.exp (-2 * n) <= P := by
    change Real.exp (-n) * Real.exp (-n) <= (F / n ^ k) * (F / n ^ k) at hSquare
    have hSquare' : Real.exp (-n) ^ 2 <= (F / n ^ k) ^ 2 := by
      simpa only [pow_two] using hSquare
    rw [div_pow, hPow, hExp] at hSquare'
    exact hSquare'
  have hMass := hamiltonian_cycle_mass_from_half_ratio n P
    (hamiltonianCycleSum (bipartiteLift T)) hnPos hP hRatio
  have hLower : Real.exp (-2 * n) / (2 * n) <= hamiltonianCycleSum (bipartiteLift T) :=
    (div_le_div_of_nonneg_right hSignal (mul_nonneg (by norm_num) hnPos.le)).trans hMass
  refine And.intro ?_ hLower
  exact (div_pos (Real.exp_pos _) (mul_pos (by norm_num) hnPos)).trans_le hLower

end PrimeFactorOscillations
