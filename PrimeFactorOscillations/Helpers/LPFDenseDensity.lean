/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFDenseIteration

/-!
# Vanishing defects for the actual LPF-generated states

The proved geometric recurrence forces a vanishing normalized defect once
finite-density entry and the ordinary positive representation source hold.
It does not establish entry for {2} or reachability of every prime.
-/

namespace PrimeFactorOscillations.LPF

private theorem cutoff_linear_growth (M : Nat) (hM : 4 <= M) (j : Nat) :
    M + j <= lpfDensityCutoff M j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change M + (j + 1) <= 5 * lpfDensityCutoff M j / 4
    omega

theorem lpfDensityCutoff_tendsto (M : Nat) (hM : 4 <= M) :
    Filter.Tendsto (lpfDensityCutoff M) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [Filter.eventually_ge_atTop b] with j hj
  have h := cutoff_linear_growth M hM j
  omega

private theorem initial_error_eventually_le_floor (E0 : Real) (F : Nat -> Real)
    (hF0 : 0 < F 0)
    (hGrow : forall j, (9 / 8 : Real) * F j <= F (j + 1)) :
    Filter.Eventually (fun j => (17 / 16 : Real) ^ j * E0 <= F j) Filter.atTop := by
  have hFloor (j : Nat) :
      (17 / 16 : Real) ^ j * (1 + (j : Real) / 17) * F 0 <= F j := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hStep := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : Real) <= 9 / 8)
      have hPos : 0 <= (17 / 16 : Real) ^ j * F 0 := by positivity
      have hj : (0 : Real) <= (j : Real) := by positivity
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      nlinarith only [hGrow j, hStep, hPos, mul_nonneg hPos hj]
  choose J hJ using exists_nat_gt (17 * E0 / F 0)
  apply Filter.eventually_atTop.mpr
  refine Exists.intro J ?_
  intro j hj
  have hJj : (J : Real) <= (j : Real) := by exact_mod_cast hj
  have hRatio : 17 * E0 / F 0 < (j : Real) := hJ.trans_le hJj
  have hScale := mul_lt_mul_of_pos_right hRatio hF0
  have hCancel : (17 * E0 / F 0) * F 0 = 17 * E0 := by
    field_simp [ne_of_gt hF0]
  rw [hCancel] at hScale
  have hE : E0 <= (1 + (j : Real) / 17) * F 0 := by nlinarith only [hScale, hF0]
  have h := mul_le_mul_of_nonneg_left hE (by positivity : 0 <= (17 / 16 : Real) ^ j)
  calc
    _ <= (17 / 16 : Real) ^ j * ((1 + (j : Real) / 17) * F 0) := h
    _ = (17 / 16 : Real) ^ j * (1 + (j : Real) / 17) * F 0 := by ring
    _ <= F j := hFloor j

private theorem eventually_scaled_floor_small (eps D : Real) (hEps : 0 < eps) :
    Filter.Eventually (fun M : Nat =>
      D * ((M : Real) / Real.log (M : Real) ^ 4) <=
        eps * ((M : Real) / Real.log (M : Real))) Filter.atTop := by
  have hNat : Filter.Tendsto (fun M : Nat => (M : Real)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hLogEvent := (Real.tendsto_log_atTop.comp hNat).eventually
    (Filter.eventually_ge_atTop (max 1 (D / eps)))
  filter_upwards [hLogEvent, Filter.eventually_ge_atTop (2 : Nat)] with M hSize hM
  let X : Real := (M : Real)
  let ell := Real.log X
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (by omega : 0 < M)
  have hell : 0 < ell := Real.log_pos (by dsimp [X]; exact_mod_cast (by omega : 1 < M))
  have hell1 : 1 <= ell := (le_max_left _ _).trans hSize
  have hConst : D / eps <= ell := (le_max_right _ _).trans hSize
  have hPow : ell <= ell ^ 3 := by
    have h2 : 1 <= ell ^ 2 := by nlinarith only [hell1]
    have h := mul_le_mul_of_nonneg_right h2 (le_of_lt hell)
    nlinarith only [h]
  have hScaledConst := mul_le_mul_of_nonneg_left hConst (le_of_lt hEps)
  have hCancel : eps * (D / eps) = D := by field_simp
  rw [hCancel] at hScaledConst
  have hCoeff : D <= eps * ell ^ 3 :=
    hScaledConst.trans (mul_le_mul_of_nonneg_left hPow (le_of_lt hEps))
  change D * (X / ell ^ 4) <= eps * (X / ell)
  apply (mul_le_mul_iff_of_pos_right (pow_pos hell 4)).mp
  have h := mul_le_mul_of_nonneg_left hCoeff (le_of_lt hX)
  convert h using 1 <;> field_simp

theorem fullOrbit_defect_density_zero (M : Nat) (S : Finset Nat) (C : Real)
    (hM : 4 <= M)
    (hGrow : forall j,
      (9 / 8 : Real) * (((lpfDensityCutoff M j : Nat) : Real) /
        Real.log ((lpfDensityCutoff M j : Nat) : Real) ^ 4) <=
      (((lpfDensityCutoff M (j + 1) : Nat) : Real) /
        Real.log ((lpfDensityCutoff M (j + 1) : Nat) : Real) ^ 4))
    (hBound : forall j,
      ((SDiff.sdiff (inputPrimePrefix (lpfDensityCutoff M j)) (fullOrbit S j)).card : Real) <=
        (17 / 16 : Real) ^ j * ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) +
          16 * C * (((lpfDensityCutoff M j : Nat) : Real) /
            Real.log ((lpfDensityCutoff M j : Nat) : Real) ^ 4)) :
    Filter.Tendsto (fun j =>
      ((SDiff.sdiff (inputPrimePrefix (lpfDensityCutoff M j)) (fullOrbit S j)).card : Real) /
        (((lpfDensityCutoff M j : Nat) : Real) /
          Real.log ((lpfDensityCutoff M j : Nat) : Real)))
      Filter.atTop (nhds 0) := by
  let m := lpfDensityCutoff M
  let E := fun j => ((SDiff.sdiff (inputPrimePrefix (m j)) (fullOrbit S j)).card : Real)
  let N := fun j => (m j : Real) / Real.log (m j : Real)
  let F := fun j => (m j : Real) / Real.log (m j : Real) ^ 4
  have hN (j : Nat) : 0 < N j := by
    have h := cutoff_linear_growth M hM j
    have hX : (0 : Real) < (m j : Real) := by dsimp [m]; exact_mod_cast (by omega : 0 < lpfDensityCutoff M j)
    have hLog : 0 < Real.log (m j : Real) := Real.log_pos (by
      dsimp [m]; exact_mod_cast (by omega : 1 < lpfDensityCutoff M j))
    exact div_pos hX hLog
  have hF0 : 0 < F 0 := by
    dsimp [F, m, lpfDensityCutoff]
    have hX : (0 : Real) < (M : Real) := by exact_mod_cast (by omega : 0 < M)
    have hLog : 0 < Real.log (M : Real) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
    positivity
  have hInit := initial_error_eventually_le_floor
    ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) F hF0 hGrow
  have hFloor : Filter.Eventually (fun j => E j <= (16 * C + 1) * F j) Filter.atTop := by
    filter_upwards [hInit] with j hj
    have h := hBound j
    change E j <= (17 / 16 : Real) ^ j * ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) + 16 * C * F j at h
    nlinarith only [h, hj]
  change Filter.Tendsto (fun j => E j / N j) Filter.atTop (nhds 0)
  apply tendsto_order.2
  constructor
  next =>
    intro eps hEps
    filter_upwards [] with j
    have hE : 0 <= E j := by dsimp [E]; positivity
    exact hEps.trans_le (div_nonneg hE (le_of_lt (hN j)))
  next =>
    intro eps hEps
    have hSmall := (lpfDensityCutoff_tendsto M hM).eventually
      (eventually_scaled_floor_small (eps / 2) (16 * C + 1) (by linarith))
    filter_upwards [hFloor, hSmall] with j hj hSmallj
    have hEF : E j <= (eps / 2) * N j := hj.trans hSmallj
    have hRatio : E j / N j <= eps / 2 := by
      apply (mul_le_mul_iff_of_pos_right (hN j)).mp
      have hLeft : (E j / N j) * N j = E j := by field_simp [ne_of_gt (hN j)]
      rw [hLeft]
      exact hEF
    exact hRatio.trans_lt (by linarith)

/-- The actual generated-state defect tends to zero after finite-density entry.
The ordinary representation supply is retained as an explicit hypothesis. -/
theorem exists_fullOrbit_dense_density_zero (a C : Real) (ha : 0 < a) (hC : 0 <= C)
    (hRepresentations : Filter.Eventually (fun M : Nat =>
      exists Z : Finset Nat, And
        ((Z.card : Real) <= C * ((M : Real) / Real.log (M : Real) ^ 4))
        (forall r, Membership.mem (SDiff.sdiff (nextPrimeWindow M) Z) r ->
          a * ((M : Real) / Real.log (M : Real) ^ 2) <=
            (1 / singularDivisorProduct (primeTargetSum r)) *
              ((Finset.sumPartners (inputPrimePrefix M) (primeTargetSum r)).card : Real)))
      Filter.atTop) :
    exists eta : Real, And (0 < eta)
      (Filter.Eventually (fun M : Nat =>
        forall S : Finset Nat,
        ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) <=
          eta * ((M : Real) / Real.log (M : Real)) ->
        Filter.Tendsto (fun j =>
          ((SDiff.sdiff (inputPrimePrefix (lpfDensityCutoff M j)) (fullOrbit S j)).card : Real) /
            (((lpfDensityCutoff M j : Nat) : Real) /
              Real.log ((lpfDensityCutoff M j : Nat) : Real)))
          Filter.atTop (nhds 0)) Filter.atTop) := by
  choose eta hEta hEvent using exists_fullOrbit_dense_defect_bounds a C ha hC hRepresentations
  choose nBound hBound using Filter.eventually_atTop.mp hEvent
  choose nScale hScale using Filter.eventually_atTop.mp eventually_dense_prefix_scales_grow
  let T : Nat := max 4 (max nBound nScale)
  refine Exists.intro eta (And.intro hEta ?_)
  apply Filter.eventually_atTop.mpr
  refine Exists.intro T ?_
  intro M hM S hInit
  have hM4 : 4 <= M := by dsimp [T] at hM; omega
  have hDefect := hBound M (by dsimp [T] at hM; omega) S hInit
  have hGrow (j : Nat) :
      (9 / 8 : Real) * (((lpfDensityCutoff M j : Nat) : Real) /
        Real.log ((lpfDensityCutoff M j : Nat) : Real) ^ 4) <=
      (((lpfDensityCutoff M (j + 1) : Nat) : Real) /
        Real.log ((lpfDensityCutoff M (j + 1) : Nat) : Real) ^ 4) := by
    have hGrowth := cutoff_linear_growth M hM4 j
    have hDom : nScale <= lpfDensityCutoff M j := by dsimp [T] at hM; omega
    exact (hScale (lpfDensityCutoff M j) hDom).2
  exact fullOrbit_defect_density_zero M S (C + 1) hM4 hGrow hDefect.2

end PrimeFactorOscillations.LPF
