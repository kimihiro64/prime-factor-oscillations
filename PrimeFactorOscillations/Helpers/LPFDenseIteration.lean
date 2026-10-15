/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFDenseTransfer

/-!
# Iteration scales for the dense-seed recurrence

The cutoff scale grows faster than the proved defect recurrence.
These estimates do not supply the positive representations or orbit entry.
-/

namespace PrimeFactorOscillations.LPF

theorem eventually_dense_prefix_scales_grow :
    Filter.Eventually (fun M : Nat =>
      And
        ((9 / 8 : Real) * ((M : Real) / Real.log (M : Real)) <=
          ((5 * M / 4 : Nat) : Real) / Real.log ((5 * M / 4 : Nat) : Real))
        ((9 / 8 : Real) * ((M : Real) / Real.log (M : Real) ^ 4) <=
          ((5 * M / 4 : Nat) : Real) / Real.log ((5 * M / 4 : Nat) : Real) ^ 4))
      Filter.atTop := by
  have hNat : Filter.Tendsto (fun M : Nat => (M : Real)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hLogEvent := (Real.tendsto_log_atTop.comp hNat).eventually
    (Filter.eventually_ge_atTop (64 * Real.log (5 / 4 : Real)))
  filter_upwards [hLogEvent, Filter.eventually_ge_atTop (32 : Nat)] with M hLogSize hM
  let X : Real := (M : Real)
  let Y : Real := ((5 * M / 4 : Nat) : Real)
  let ell := Real.log X
  let ell' := Real.log Y
  have hRatioNat : 39 * M <= 32 * (5 * M / 4) := by omega
  have hUpperNat : 4 * (5 * M / 4) <= 5 * M := by omega
  have hLower : (39 / 32 : Real) * X <= Y := by
    have h : (39 : Real) * X <= 32 * Y := by
      dsimp [X, Y]
      exact_mod_cast hRatioNat
    linarith
  have hUpper : Y <= (5 / 4 : Real) * X := by
    have h : (4 : Real) * Y <= 5 * X := by
      dsimp [X, Y]
      exact_mod_cast hUpperNat
    linarith
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (by omega : 0 < M)
  have hY : 0 < Y := by nlinarith only [hLower, hX]
  have hell : 0 < ell := Real.log_pos (by dsimp [X]; exact_mod_cast (by omega : 1 < M))
  have hell' : 0 < ell' := Real.log_pos (by
    dsimp [Y]
    exact_mod_cast (by omega : 1 < 5 * M / 4))
  have hLogUpper := Real.log_le_log hY hUpper
  rw [Real.log_mul (by norm_num) (ne_of_gt hX)] at hLogUpper
  have hEllUpper : ell' <= (65 / 64 : Real) * ell := by
    change ell' <= Real.log (5 / 4 : Real) + ell at hLogUpper
    change 64 * Real.log (5 / 4 : Real) <= ell at hLogSize
    linarith only [hLogUpper, hLogSize]
  have hEllCoarse : ell' <= (13 / 12 : Real) * ell := by
    nlinarith only [hEllUpper, hell]
  have hPow2 : ell' ^ 2 <= ((65 / 64 : Real) * ell) ^ 2 := by
    have h := mul_le_mul hEllUpper hEllUpper (le_of_lt hell') (by positivity)
    simpa only [pow_two] using h
  have hPow4 : ell' ^ 4 <= ((65 / 64 : Real) * ell) ^ 4 := by
    have h := mul_le_mul hPow2 hPow2 (sq_nonneg _) (sq_nonneg _)
    convert h using 1 <;> ring
  have hPowCoarse : ell' ^ 4 <= (13 / 12 : Real) * ell ^ 4 := by
    calc
      _ <= ((65 / 64 : Real) * ell) ^ 4 := hPow4
      _ = (65 / 64 : Real) ^ 4 * ell ^ 4 := by ring
      _ <= (13 / 12 : Real) * ell ^ 4 :=
        mul_le_mul_of_nonneg_right (by norm_num) (le_of_lt (pow_pos hell 4))
  change And ((9 / 8 : Real) * (X / ell) <= Y / ell')
    ((9 / 8 : Real) * (X / ell ^ 4) <= Y / ell' ^ 4)
  constructor
  next =>
    apply (mul_le_mul_iff_of_pos_right (mul_pos hell hell')).mp
    have hLeft : ((9 / 8 : Real) * (X / ell)) * (ell * ell') =
        (9 / 8 : Real) * X * ell' := by field_simp
    have hRight : (Y / ell') * (ell * ell') = Y * ell := by field_simp
    rw [hLeft, hRight]
    have hA := mul_le_mul_of_nonneg_left hEllCoarse (by positivity : 0 <= (9 / 8 : Real) * X)
    have hB := mul_le_mul_of_nonneg_right hLower (le_of_lt hell)
    nlinarith only [hA, hB]
  next =>
    apply (mul_le_mul_iff_of_pos_right (mul_pos (pow_pos hell 4) (pow_pos hell' 4))).mp
    have hLeft : ((9 / 8 : Real) * (X / ell ^ 4)) * (ell ^ 4 * ell' ^ 4) =
        (9 / 8 : Real) * X * ell' ^ 4 := by field_simp
    have hRight : (Y / ell' ^ 4) * (ell ^ 4 * ell' ^ 4) = Y * ell ^ 4 := by field_simp
    rw [hLeft, hRight]
    have hA := mul_le_mul_of_nonneg_left hPowCoarse (by positivity : 0 <= (9 / 8 : Real) * X)
    have hB := mul_le_mul_of_nonneg_right hLower (le_of_lt (pow_pos hell 4))
    nlinarith only [hA, hB]

theorem dense_recurrence_preserves_fraction (E E' F N N' eta C : Real)
    (hEta : 0 <= eta) (hE : E <= eta * N)
    (hStep : E' <= (17 / 16 : Real) * E + C * F)
    (hGrow : (9 / 8 : Real) * N <= N')
    (hError : C * F <= eta * N / 16) : E' <= eta * N' := by
  have h1 := mul_le_mul_of_nonneg_left hE (by norm_num : (0 : Real) <= 17 / 16)
  have h2 := mul_le_mul_of_nonneg_left hGrow hEta
  nlinarith only [hStep, hError, h1, h2]

theorem dense_recurrence_iterate (E F : Nat -> Real) (C : Real)
    (hC : 0 <= C) (hF0 : 0 <= F 0)
    (hStep : forall j, E (j + 1) <= (17 / 16 : Real) * E j + C * F j)
    (hGrow : forall j, (9 / 8 : Real) * F j <= F (j + 1)) (j : Nat) :
    E j <= (17 / 16 : Real) ^ j * E 0 + 16 * C * F j := by
  induction j with
  | zero =>
    simp only [pow_zero, one_mul]
    have h : 0 <= 16 * C * F 0 := by positivity
    linarith
  | succ j ih =>
    have h1 := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : Real) <= 17 / 16)
    have h2 := mul_le_mul_of_nonneg_left (hGrow j) (by positivity : 0 <= 16 * C)
    rw [pow_succ]
    nlinarith only [hStep j, h1, h2]

private theorem eventually_dense_error_small (eta C : Real) (hEta : 0 < eta) :
    Filter.Eventually (fun M : Nat =>
      C * ((M : Real) / Real.log (M : Real) ^ 4) <=
        eta * ((M : Real) / Real.log (M : Real)) / 16) Filter.atTop := by
  have hNat : Filter.Tendsto (fun M : Nat => (M : Real)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hLogEvent := (Real.tendsto_log_atTop.comp hNat).eventually
    (Filter.eventually_ge_atTop (max 1 (16 * C / eta)))
  filter_upwards [hLogEvent, Filter.eventually_ge_atTop (2 : Nat)] with M hSize hM
  let X : Real := (M : Real)
  let ell := Real.log X
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (by omega : 0 < M)
  have hell : 0 < ell := Real.log_pos (by dsimp [X]; exact_mod_cast (by omega : 1 < M))
  have hell1 : 1 <= ell := (le_max_left _ _).trans hSize
  have hConst : 16 * C / eta <= ell := (le_max_right _ _).trans hSize
  have hPow : ell <= ell ^ 3 := by
    have h2 : 1 <= ell ^ 2 := by nlinarith only [hell1]
    have h := mul_le_mul_of_nonneg_right h2 (le_of_lt hell)
    nlinarith only [h]
  have hScaledConst := mul_le_mul_of_nonneg_left hConst (le_of_lt hEta)
  have hCancel : eta * (16 * C / eta) = 16 * C := by field_simp
  rw [hCancel] at hScaledConst
  have hCoeff : 16 * C <= eta * ell ^ 3 :=
    hScaledConst.trans (mul_le_mul_of_nonneg_left hPow (le_of_lt hEta))
  change C * (X / ell ^ 4) <= eta * (X / ell) / 16
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 16 * ell ^ 4)).mp
  have h := mul_le_mul_of_nonneg_left hCoeff (le_of_lt hX)
  convert h using 1 <;> field_simp <;> ring

def lpfDensityCutoff (M : Nat) : Nat -> Nat
  | 0 => M
  | j + 1 => 5 * lpfDensityCutoff M j / 4

private theorem lpfDensityCutoff_ge (M j : Nat) : M <= lpfDensityCutoff M j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h : lpfDensityCutoff M j <= 5 * lpfDensityCutoff M j / 4 := by omega
    exact ih.trans h

/-- The quantitative bounds concern the actual generated states. The ordinary
prime representation source and a finite-density entry remain explicit. -/
theorem exists_fullOrbit_dense_defect_bounds (a C : Real) (ha : 0 < a) (hC : 0 <= C)
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
        let E := fun j => ((SDiff.sdiff (inputPrimePrefix (lpfDensityCutoff M j))
          (fullOrbit S j)).card : Real)
        let N := fun j => ((lpfDensityCutoff M j : Nat) : Real) /
          Real.log ((lpfDensityCutoff M j : Nat) : Real)
        let F := fun j => ((lpfDensityCutoff M j : Nat) : Real) /
          Real.log ((lpfDensityCutoff M j : Nat) : Real) ^ 4
        E 0 <= eta * N 0 ->
        And (forall j, E j <= eta * N j)
          (forall j, E j <= (17 / 16 : Real) ^ j * E 0 + 16 * (C + 1) * F j))
        Filter.atTop) := by
  classical
  choose eta hEta hRecEvent using exists_dense_fullStep_prefix_recurrence a ha
  choose nRec hRec using Filter.eventually_atTop.mp hRecEvent
  choose nScale hScale using Filter.eventually_atTop.mp eventually_dense_prefix_scales_grow
  choose nError hError using Filter.eventually_atTop.mp (eventually_dense_error_small eta (C + 1) hEta)
  choose nRep hRep using Filter.eventually_atTop.mp hRepresentations
  let T : Nat := max 32 (max nRec (max nScale (max nError nRep)))
  refine Exists.intro eta (And.intro hEta ?_)
  apply Filter.eventually_atTop.mpr
  refine Exists.intro T ?_
  intro M hM S
  let m := fun j => lpfDensityCutoff M j
  let E := fun j => ((SDiff.sdiff (inputPrimePrefix (m j)) (fullOrbit S j)).card : Real)
  let N := fun j => (m j : Real) / Real.log (m j : Real)
  let F := fun j => (m j : Real) / Real.log (m j : Real) ^ 4
  change E 0 <= eta * N 0 ->
    And (forall j, E j <= eta * N j)
      (forall j, E j <= (17 / 16 : Real) ^ j * E 0 + 16 * (C + 1) * F j)
  intro hInit
  have hDom (j : Nat) : T <= m j := hM.trans (lpfDensityCutoff_ge M j)
  have hRecAt (j : Nat) := hRec (m j) (by have h := hDom j; dsimp [T] at h; omega)
  have hScaleAt (j : Nat) := hScale (m j) (by have h := hDom j; dsimp [T] at h; omega)
  have hErrorAt (j : Nat) := hError (m j) (by have h := hDom j; dsimp [T] at h; omega)
  have hRepAt (j : Nat) := hRep (m j) (by have h := hDom j; dsimp [T] at h; omega)
  have hGrowN : forall j, (9 / 8 : Real) * N j <= N (j + 1) :=
    fun j => (hScaleAt j).1
  have hGrowF : forall j, (9 / 8 : Real) * F j <= F (j + 1) :=
    fun j => (hScaleAt j).2
  have hStepOfSmall : forall j, E j <= eta * N j ->
      E (j + 1) <= (17 / 16 : Real) * E j + (C + 1) * F j := by
    intro j hj
    choose Z hZ hSupply using hRepAt j
    have h := hRecAt j (fullOrbit S j) Z hj hSupply
    have hNext : E (j + 1) <= (17 / 16 : Real) * E j + (Z.card : Real) + F j := h
    have hZ' : (Z.card : Real) <= C * F j := hZ
    nlinarith only [hNext, hZ']
  have hPreserve : forall j, E j <= eta * N j := by
    intro j
    induction j with
    | zero => exact hInit
    | succ j ih =>
      exact dense_recurrence_preserves_fraction (E j) (E (j + 1)) (F j)
        (N j) (N (j + 1)) eta (C + 1) (le_of_lt hEta) ih
        (hStepOfSmall j ih) (hGrowN j) (hErrorAt j)
  refine And.intro hPreserve ?_
  intro j
  have hM32 : 32 <= M := by dsimp [T] at hM; omega
  have hX : (0 : Real) < (M : Real) := by exact_mod_cast (by omega : 0 < M)
  have hLog : 0 < Real.log (M : Real) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hF0 : 0 <= F 0 := by dsimp [F, m, lpfDensityCutoff]; positivity
  exact dense_recurrence_iterate E F (C + 1) (by linarith) hF0
    (fun j => hStepOfSmall j (hPreserve j)) hGrowF j

end PrimeFactorOscillations.LPF
