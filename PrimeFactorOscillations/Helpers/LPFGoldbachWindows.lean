/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFGoldbachPrimePowers

/-!
# Exact interval placement for the positive Goldbach source

Both cofactor branches, the raw reflected windows, and the width conditions
retain their integer floors and strict source endpoints.
-/

namespace PrimeFactorOscillations.LPF

def goldbachEvenTargets (N : Nat) : Finset Nat :=
  (Finset.Ioo N (2 * N)).filter (fun t => t % 2 = 0)

def goldbachWindowInputs (M t : Nat) : Finset Nat :=
  Finset.Ioo (t / 2 - M / 64) (t / 2 + M / 64)

theorem primeTargetSum_even (r : Nat) (hr : Nat.Prime r) (hr3 : 3 <= r) :
    primeTargetSum r % 2 = 0 := by
  have hOdd : r % 2 = 1 := hr.eq_two_or_odd.resolve_left (by omega)
  unfold primeTargetSum
  split_ifs <;> omega

/-- The cofactor branches fall in the two exact source intervals. -/
theorem primeTarget_goldbach_source_interval (M r : Nat) (hM : 16 <= M)
    (hr : Membership.mem (nextPrimeWindow M) r) :
    if r % 4 = 1 then Membership.mem (goldbachEvenTargets M) (primeTargetSum r)
    else Membership.mem (goldbachEvenTargets (M / 2)) (primeTargetSum r) := by
  have hR := nextPrimeWindow_spec M r hr
  have hEven := primeTargetSum_even r hR.1 (by omega)
  by_cases hBranch : r % 4 = 1
  next =>
    simp only [hBranch, ite_eq_left]
    apply Finset.mem_filter.mpr
    refine And.intro ?_ hEven
    apply Finset.mem_Ioo.mpr
    unfold primeTargetSum
    simp only [hBranch, ite_eq_left]
    omega
  next =>
    simp [hBranch]
    apply Finset.mem_filter.mpr
    refine And.intro ?_ hEven
    apply Finset.mem_Ioo.mpr
    unfold primeTargetSum
    simp [hBranch]
    omega

theorem primeTarget_goldbach_center_bounds (M r : Nat) (hM : 128 <= M)
    (hr : Membership.mem (nextPrimeWindow M) r) :
    And (M / 64 + 1 <= primeTargetSum r / 2)
      (primeTargetSum r / 2 + M / 64 <= M) := by
  have hR := nextPrimeWindow_spec M r hr
  unfold primeTargetSum
  split_ifs <;> omega

theorem goldbachWindow_partner_mem (M t p : Nat) (hEven : t % 2 = 0)
    (hCenter : M / 64 <= t / 2)
    (hp : Membership.mem (goldbachWindowInputs M t) p) :
    Membership.mem (goldbachWindowInputs M t) (t - p) := by
  have hP := Finset.mem_Ioo.mp hp
  apply Finset.mem_Ioo.mpr
  have hDouble : 2 * (t / 2) = t := by omega
  omega

/-- Both summands really lie in the prefix used by the LPF generation bound. -/
theorem primeTarget_goldbach_input_bounds (M r : Nat) (hM : 128 <= M)
    (hr : Membership.mem (nextPrimeWindow M) r) (p : Nat)
    (hp : Membership.mem (goldbachWindowInputs M (primeTargetSum r)) p) :
    And (Membership.mem (Finset.Icc 1 M) p)
      (Membership.mem (Finset.Icc 1 M) (primeTargetSum r - p)) := by
  have hR := nextPrimeWindow_spec M r hr
  have hCenter := primeTarget_goldbach_center_bounds M r hM hr
  have hEven := primeTargetSum_even r hR.1 (by omega)
  have hQ := goldbachWindow_partner_mem M (primeTargetSum r) p hEven (by omega) hp
  have hPData := Finset.mem_Ioo.mp hp
  have hQData := Finset.mem_Ioo.mp hQ
  exact And.intro (Finset.mem_Icc.mpr (by omega)) (Finset.mem_Icc.mpr (by omega))

/-- The raw window sum is exactly the source sum with both summands in the window. -/
theorem goldbachWindow_sumPartners_eq (M t : Nat) (hEven : t % 2 = 0)
    (hCenter : M / 64 <= t / 2) :
    Finset.sumPartners (goldbachWindowInputs M t) t = goldbachWindowInputs M t := by
  ext p
  constructor
  next => intro hp; exact (Finset.mem_filter.mp hp).1
  next =>
    intro hp
    have hQ := goldbachWindow_partner_mem M t p hEven hCenter hp
    have hPData := Finset.mem_Ioo.mp hp
    have hDouble : 2 * (t / 2) = t := by omega
    exact Finset.mem_filter.mpr (And.intro hp (And.intro hQ (by omega)))

theorem goldbach_source_window_center (M t : Nat) (hM : 128 <= M)
    (ht : Membership.mem (Union.union (goldbachEvenTargets (M / 2)) (goldbachEvenTargets M)) t) :
    M / 64 <= t / 2 := by
  rcases Finset.mem_union.mp ht with h | h
  next => have hI := Finset.mem_Ioo.mp (Finset.mem_filter.mp h).1; omega
  next => have hI := Finset.mem_Ioo.mp (Finset.mem_filter.mp h).1; omega

/-- This quartic inequality is the exact integer form of U > N^(3/4). -/
theorem goldbachWidth_quartic_range (M : Nat) (hM : 128 ^ 4 + 1 <= M) :
    And (M ^ 3 < (M / 64) ^ 4) (And (M / 64 < M / 2) (M / 64 < M)) := by
  have hLarge : 128 ^ 4 < M := by omega
  have hM128 : 128 <= M := by norm_num at hM; omega
  have hWidth : M <= 128 * (M / 64) := by omega
  have hMPos : 0 < M := by omega
  have hScaled : 128 ^ 4 * M ^ 3 < 128 ^ 4 * (M / 64) ^ 4 := by
    calc
      _ < M * M ^ 3 := Nat.mul_lt_mul_of_pos_right hLarge (by positivity)
      _ = M ^ 4 := by ring
      _ <= (128 * (M / 64)) ^ 4 := Nat.pow_le_pow_left hWidth 4
      _ = _ := by rw [Nat.mul_pow]
  have hQuartic : M ^ 3 < (M / 64) ^ 4 := Nat.lt_of_mul_lt_mul_left hScaled
  exact And.intro hQuartic (And.intro (by omega) (by omega))

end PrimeFactorOscillations.LPF
