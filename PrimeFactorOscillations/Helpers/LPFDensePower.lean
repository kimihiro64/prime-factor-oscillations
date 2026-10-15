/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFDenseDensity
import PrimeFactorOscillations.Helpers.LPFPositiveSupply

/-!
# Power-saving defects after dense LPF entry

The complete positive source and deletion recurrence imply an eventual
79/80 power bound for the actual finite generations. A first-crossing
argument gives the same exponent for the permanently unreachable primes
at every sufficiently large cutoff. The constants may depend on the fixed
seed and entry scale. Entry from {2} is not assumed or proved here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

private theorem cutoff_power_base_growth :
    (13 / 12 : Real) <= (9 / 8 : Real) ^ (79 / 80 : Real) := by
  have hRoot : (13 / 12 : Real) <= (9 / 8 : Real) ^ (3 / 4 : Real) := by
    by_contra h
    have hLe : (9 / 8 : Real) ^ (3 / 4 : Real) <= 13 / 12 :=
      (lt_of_not_ge h).le
    have hPow : ((9 / 8 : Real) ^ (3 / 4 : Real)) ^ 4 <= (13 / 12 : Real) ^ 4 := by
      gcongr
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (by norm_num : (0 : Real) <= 9 / 8)] at hPow
    norm_num at hPow
  exact hRoot.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))

private theorem cutoff_power_growth (M j : Nat) (hM : 8 <= M)
    (hBase : M <= lpfDensityCutoff M j) :
    (13 / 12 : Real) * ((lpfDensityCutoff M j : Nat) : Real) ^ (79 / 80 : Real) <=
      ((lpfDensityCutoff M (j + 1) : Nat) : Real) ^ (79 / 80 : Real) := by
  let X : Real := (lpfDensityCutoff M j : Nat)
  let Y : Real := (lpfDensityCutoff M (j + 1) : Nat)
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (by omega : 0 < lpfDensityCutoff M j)
  have hNat : 9 * lpfDensityCutoff M j <= 8 * (5 * lpfDensityCutoff M j / 4) := by omega
  have hLower : (9 / 8 : Real) * X <= Y := by
    have h : (9 : Real) * X <= 8 * Y := by
      dsimp [X, Y, lpfDensityCutoff]
      exact_mod_cast hNat
    linarith
  change (13 / 12 : Real) * X ^ (79 / 80 : Real) <= Y ^ (79 / 80 : Real)
  calc
    _ <= ((9 / 8 : Real) ^ (79 / 80 : Real)) * X ^ (79 / 80 : Real) :=
      mul_le_mul_of_nonneg_right cutoff_power_base_growth (Real.rpow_nonneg hX.le _)
    _ = ((9 / 8 : Real) * X) ^ (79 / 80 : Real) :=
      (Real.mul_rpow (by norm_num) hX.le).symm
    _ <= _ := Real.rpow_le_rpow (by positivity) hLower (by norm_num)

private theorem log_le_two_power (X : Real) (hX : 0 < X) :
    Real.log X <= 2 * X ^ (79 / 80 : Real) := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hX (79 / 80 : Real))
  rw [Real.log_rpow hX] at h
  have hPow : 0 <= X ^ (79 / 80 : Real) := Real.rpow_nonneg hX.le _
  linarith only [h, hPow]

private theorem cutoff_ge (M j : Nat) : M <= lpfDensityCutoff M j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change M <= 5 * lpfDensityCutoff M j / 4
    omega

private theorem eventual_power_bound_from_recurrence (E F : Nat -> Real) (C : Real)
    (hF : forall j, 0 < F j)
    (hGrow : forall j, (13 / 12 : Real) * F j <= F (j + 1))
    (hRec : Filter.Eventually (fun j =>
      E (j + 1) <= (17 / 16 : Real) * E j + C * F j) Filter.atTop) :
    exists K : Real, And (0 < K)
      (Filter.Eventually (fun j => E j <= K * F j) Filter.atTop) := by
  choose J hJ using Filter.eventually_atTop.mp hRec
  let K : Real := max 1 (max (E J / F J) (48 * C))
  have hK1 : 1 <= K := le_max_left _ _
  have hKE : E J / F J <= K := (le_max_left _ _).trans (le_max_right _ _)
  have hKC : 48 * C <= K := (le_max_right _ _).trans (le_max_right _ _)
  have hK : 0 < K := by linarith
  have hBase : E J <= K * F J := by
    have h := mul_le_mul_of_nonneg_right hKE (hF J).le
    have hCancel : E J / F J * F J = E J := by field_simp [ne_of_gt (hF J)]
    rwa [hCancel] at h
  have hAll (n : Nat) : E (J + n) <= K * F (J + n) := by
    induction n with
    | zero => simpa using hBase
    | succ n ih =>
      have hStep := hJ (J + n) (by omega)
      have hScaled := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : Real) <= 17 / 16)
      have hCoef : C <= (13 / 12 - 17 / 16 : Real) * K := by linarith only [hKC]
      have hError := mul_le_mul_of_nonneg_right hCoef (hF (J + n)).le
      have hGrowth := mul_le_mul_of_nonneg_left (hGrow (J + n)) hK.le
      have hBound : E (J + n + 1) <= K * F (J + n + 1) := by
        nlinarith only [hStep, hScaled, hError, hGrowth]
      simpa [Nat.add_assoc] using hBound
  refine Exists.intro K (And.intro hK ?_)
  apply Filter.eventually_atTop.mpr
  refine Exists.intro J ?_
  intro j hj
  simpa [Nat.add_sub_of_le hj] using hAll (j - J)

theorem fullOrbit_defect_power_bound_of_density_zero (M : Nat) (S : Finset Nat) (hM : 8 <= M)
    (hDensity : Filter.Tendsto (fun j =>
      ((SDiff.sdiff (inputPrimePrefix (lpfDensityCutoff M j)) (fullOrbit S j)).card : Real) /
        (((lpfDensityCutoff M j : Nat) : Real) /
          Real.log ((lpfDensityCutoff M j : Nat) : Real)))
      Filter.atTop (nhds 0)) :
    exists K : Real, And (0 < K)
      (Filter.Eventually (fun j =>
        ((SDiff.sdiff (inputPrimePrefix (lpfDensityCutoff M j)) (fullOrbit S j)).card : Real) <=
          K * ((lpfDensityCutoff M j : Nat) : Real) ^ (79 / 80 : Real)) Filter.atTop) := by
  choose C D eta hC hD hEta hStep using
    exists_fullStep_dense_power_log_bound_from_wide_source
  let m := lpfDensityCutoff M
  let E := fun j => ((SDiff.sdiff (inputPrimePrefix (m j)) (fullOrbit S j)).card : Real)
  let F := fun j => (m j : Real) ^ (79 / 80 : Real)
  have hPos (j : Nat) : 0 < (m j : Real) := by
    have h := cutoff_ge M j
    dsimp [m]
    exact_mod_cast (by omega : 0 < lpfDensityCutoff M j)
  have hF (j : Nat) : 0 < F j := Real.rpow_pos_of_pos (hPos j) _
  have hGrow (j : Nat) : (13 / 12 : Real) * F j <= F (j + 1) :=
    cutoff_power_growth M j hM (cutoff_ge M j)
  have hSmall := (tendsto_order.mp hDensity).2 eta hEta
  have hScales := (lpfDensityCutoff_tendsto M (by omega)).eventually hStep
  have hRec : Filter.Eventually (fun j =>
      E (j + 1) <= (17 / 16 : Real) * E j + (C + 2 * D) * F j) Filter.atTop := by
    filter_upwards [hSmall, hScales] with j hSmallj hScalej
    have hLog : 0 < Real.log (m j : Real) := Real.log_pos (by
      have h := cutoff_ge M j
      dsimp [m]
      exact_mod_cast (by omega : 1 < lpfDensityCutoff M j))
    have hN : 0 < (m j : Real) / Real.log (m j : Real) := div_pos (hPos j) hLog
    have hEntry : E j <= eta * ((m j : Real) / Real.log (m j : Real)) := by
      have h := mul_le_mul_of_nonneg_right hSmallj.le hN.le
      have hCancel : (E j / ((m j : Real) / Real.log (m j : Real))) *
          ((m j : Real) / Real.log (m j : Real)) = E j := by
        field_simp [ne_of_gt (hPos j), ne_of_gt hLog]
      rwa [hCancel] at h
    have hNext := hScalej (fullOrbit S j) hEntry
    have hNext' : E (j + 1) <= (17 / 16 : Real) * E j + C * F j +
        D * Real.log (m j : Real) := hNext
    have hLogBound := mul_le_mul_of_nonneg_left (log_le_two_power _ (hPos j)) hD.le
    change E (j + 1) <= (17 / 16 : Real) * E j + (C + 2 * D) * F j
    change D * Real.log (m j : Real) <= D * (2 * F j) at hLogBound
    nlinarith only [hNext', hLogBound]
  exact eventual_power_bound_from_recurrence E F (C + 2 * D) hF hGrow hRec

theorem exists_fullOrbit_dense_power_bound :
    exists eta : Real, And (0 < eta)
      (Filter.Eventually (fun M : Nat =>
        forall S : Finset Nat,
        ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) <=
          eta * ((M : Real) / Real.log (M : Real)) ->
        exists K : Real, And (0 < K)
          (Filter.Eventually (fun j =>
            ((SDiff.sdiff (inputPrimePrefix (lpfDensityCutoff M j)) (fullOrbit S j)).card : Real) <=
              K * ((lpfDensityCutoff M j : Nat) : Real) ^ (79 / 80 : Real)) Filter.atTop))
        Filter.atTop) := by
  choose C hC hSupply using exists_wide_primeTarget_supply_log
  choose eta hEta hDense using exists_fullOrbit_dense_density_zero (63 / 1024) C
    (by norm_num) hC hSupply
  refine Exists.intro eta (And.intro hEta ?_)
  filter_upwards [hDense, Filter.eventually_ge_atTop (8 : Nat)] with M hDenseM hM
  intro S hEntry
  exact fullOrbit_defect_power_bound_of_density_zero M S hM (hDenseM S hEntry)

noncomputable def fullOrbitMissingPrimes (S : Finset Nat) (X : Nat) : Finset Nat := by
  classical
  exact (inputPrimePrefix X).filter
    (fun r => forall j, Not (Membership.mem (fullOrbit S j) r))

theorem fullOrbit_closure_power_bound_of_stage (M : Nat) (S : Finset Nat) (K : Real)
    (hM : 8 <= M) (hK : 0 < K)
    (hStage : Filter.Eventually (fun j =>
      ((SDiff.sdiff (inputPrimePrefix (lpfDensityCutoff M j)) (fullOrbit S j)).card : Real) <=
        K * ((lpfDensityCutoff M j : Nat) : Real) ^ (79 / 80 : Real)) Filter.atTop) :
    exists L : Real, And (0 < L)
      (Filter.Eventually (fun X : Nat =>
        ((fullOrbitMissingPrimes S X).card : Real) <= L * (X : Real) ^ (79 / 80 : Real))
        Filter.atTop) := by
  classical
  choose J hJ using Filter.eventually_atTop.mp hStage
  let m := lpfDensityCutoff M
  have hMono : Monotone m := by
    apply monotone_nat_of_le_succ
    intro j
    change lpfDensityCutoff M j <= 5 * lpfDensityCutoff M j / 4
    omega
  let L : Real := K * (5 / 4 : Real) ^ (79 / 80 : Real)
  have hL : 0 < L := mul_pos hK (Real.rpow_pos_of_pos (by norm_num) _)
  refine Exists.intro L (And.intro hL ?_)
  apply Filter.eventually_atTop.mpr
  refine Exists.intro (m J + 1) ?_
  intro X hX
  have hExists : exists j, X <= m j := by
    choose n hn using Filter.eventually_atTop.mp
      ((lpfDensityCutoff_tendsto M (by omega)).eventually (Filter.eventually_ge_atTop X))
    exact Exists.intro n (hn n (le_refl n))
  let j := Nat.find hExists
  have hXj : X <= m j := Nat.find_spec hExists
  have hJj : J <= j := by
    by_contra h
    have hLe : j <= J := by omega
    have hCut := hMono hLe
    omega
  have hjPos : 0 < j := by
    have hMJ : M <= m J := cutoff_ge M J
    by_contra h
    have hjZero : j = 0 := by omega
    have hM0 : m 0 = M := rfl
    rw [hjZero, hM0] at hXj
    omega
  have hPrev : m (j - 1) < X := by
    have hNot : Not (X <= m (j - 1)) := Nat.find_min hExists (by omega : j - 1 < j)
    omega
  have hEq : m j = 5 * m (j - 1) / 4 := by
    have hIndex : j = (j - 1) + 1 := by omega
    conv_lhs => rw [hIndex]
    rfl
  have hUpperNat : 4 * m j <= 5 * X := by rw [hEq]; omega
  have hUpper : (m j : Real) <= (5 / 4 : Real) * (X : Real) := by
    have h : (4 : Real) * (m j : Real) <= 5 * (X : Real) := by exact_mod_cast hUpperNat
    linarith
  have hSubset : fullOrbitMissingPrimes S X <=
      SDiff.sdiff (inputPrimePrefix (m j)) (fullOrbit S j) := by
    intro r hr
    have hMem := Finset.mem_filter.mp hr
    have hPrime := Finset.mem_filter.mp hMem.1
    have hInterval := Finset.mem_Icc.mp hPrime.1
    apply Finset.mem_sdiff.mpr
    exact And.intro (Finset.mem_filter.mpr (And.intro
      (Finset.mem_Icc.mpr (And.intro hInterval.1 (hInterval.2.trans hXj))) hPrime.2))
      (hMem.2 j)
  have hCard : ((fullOrbitMissingPrimes S X).card : Real) <=
      ((SDiff.sdiff (inputPrimePrefix (m j)) (fullOrbit S j)).card : Real) := by
    exact_mod_cast Finset.card_le_card hSubset
  calc
    _ <= K * (m j : Real) ^ (79 / 80 : Real) := hCard.trans (hJ j hJj)
    _ <= K * ((5 / 4 : Real) * (X : Real)) ^ (79 / 80 : Real) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hUpper (by norm_num)) hK.le
    _ = L * (X : Real) ^ (79 / 80 : Real) := by
      rw [Real.mul_rpow (by norm_num : (0 : Real) <= 5 / 4) (Nat.cast_nonneg X)]
      dsimp [L]
      ring

theorem exists_fullOrbit_dense_closure_power_bound :
    exists eta : Real, And (0 < eta)
      (Filter.Eventually (fun M : Nat =>
        forall S : Finset Nat,
        ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) <=
          eta * ((M : Real) / Real.log (M : Real)) ->
        exists K : Real, And (0 < K)
          (Filter.Eventually (fun X : Nat =>
            ((fullOrbitMissingPrimes S X).card : Real) <= K * (X : Real) ^ (79 / 80 : Real))
            Filter.atTop)) Filter.atTop) := by
  choose eta hEta hEvent using exists_fullOrbit_dense_power_bound
  refine Exists.intro eta (And.intro hEta ?_)
  filter_upwards [hEvent, Filter.eventually_ge_atTop (8 : Nat)] with M hEventM hM
  intro S hEntry
  choose K hK hStage using hEventM S hEntry
  exact fullOrbit_closure_power_bound_of_stage M S K hM hK hStage

end PrimeFactorOscillations.LPF
