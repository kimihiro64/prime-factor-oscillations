/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeLogReference

/-! # Actual coprime-cycle entropy with a logarithmic remainder

The full relative arithmetic count supplies positivity and a uniformly
small logarithmic ratio. The exact reference correction yields the
stronger logarithmic error and its stated paper-scale consequence.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_log_near_one_bound (x : Real) (hx : abs (x - 1) <= (1 / 2 : Real)) :
    0 < x /\ abs (Real.log x) <= 1 := by
  have hRange := abs_le.mp hx
  have hPos : 0 < x := by linarith only [hRange.1]
  have hUpper := Real.log_le_sub_one_of_pos hPos
  have hTwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
  have hHalf : Real.log (1 / 2 : Real) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  have hLower := Real.log_le_log (by norm_num : (0 : Real) < 1 / 2)
    (by linarith only [hRange.1] : (1 / 2 : Real) <= x)
  rw [hHalf] at hLower
  refine And.intro hPos (abs_le.mpr (And.intro ?_ ?_))
  all_goals linarith only [hUpper, hTwo, hLower, hRange.2]

theorem hamiltonian_log_count_half_relative (h d : Real) (hd : 0 < d)
    (hRelative : abs (h / d - 1) <= (1 / 2 : Real)) :
    0 < h /\ abs (Real.log h - Real.log d) <= 1 := by
  have hNear := hamiltonian_log_near_one_bound (h / d) hRelative
  have hId : (h / d) * d = h := by field_simp [ne_of_gt hd]
  have hPos := mul_pos hNear.1 hd
  rw [hId] at hPos
  refine And.intro hPos ?_
  rw [<- Real.log_div (ne_of_gt hPos) (ne_of_gt hd)]
  exact hNear.2

theorem hamiltonian_tenth_error_eventually_half :
    exists N0 : Nat, 256 <= N0 /\ forall n : Nat, N0 <= n ->
      23 * (n : Real) ^ (-1 / 10 : Real) <= (1 / 2 : Real) := by
  choose N0 hN0 hSmall using hamiltonian_log_power_dominated_uniform
    46 (by norm_num) 0 (1 / 10) (by norm_num)
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n hn
  have hnR : 0 <= (n : Real) := Nat.cast_nonneg n
  have hPower : (46 : Real) <= (n : Real) ^ (1 / 10 : Real) := by
    simpa only [pow_zero, mul_one] using hSmall n hn
  have hInv := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 46) hPower
  have hNeg : (n : Real) ^ (-1 / 10 : Real) = 1 / (n : Real) ^ (1 / 10 : Real) := by
    rw [show (-1 / 10 : Real) = -(1 / 10 : Real) by ring, Real.rpow_neg hnR]
    exact (one_div _).symm
  rw [hNeg]
  calc
    _ <= 23 * (1 / 46 : Real) := mul_le_mul_of_nonneg_left hInv (by norm_num)
    _ = _ := by norm_num

def hamiltonianCoprimeCycleEntropyBudget : Real :=
  hamiltonianCoprimeReferenceLogBudget + 1

theorem hamiltonian_coprime_cycle_log_count_uniform :
    exists N0 : Nat, 512 <= N0 /\
      forall (n : Nat) [NeZero n], N0 <= n ->
        0 < (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) /\
        abs (Real.log (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) -
          hamiltonianCoprimeEntropyMain n) <=
            hamiltonianCoprimeCycleEntropyBudget * Real.log (2 * (n : Real)) := by
  choose A hA hCount using hamiltonian_coprime_relative_count_uniform
  choose B hB hHalf using hamiltonian_tenth_error_eventually_half
  let N0 := max A B
  refine Exists.intro N0 (And.intro (hA.trans (le_max_left _ _)) ?_)
  intro n inst hn
  have hnA : A <= n := (le_max_left _ _).trans hn
  have hnB : B <= n := (le_max_right _ _).trans hn
  have hn3 : 3 <= n := by omega
  have hRaw := hCount n hnA
  have hLog := hamiltonian_log_count_half_relative
    (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real)
    (hamiltonianCoprimeRelativeReference n) hRaw.1 (hRaw.2.trans (hHalf n hnB))
  have hRef := hamiltonian_coprime_reference_log_error n hn3
  have hL := hamiltonian_log_twice_dimension_lower n (by omega)
  refine And.intro hLog.1 ?_
  calc
    _ = abs ((Real.log
        (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) -
          Real.log (hamiltonianCoprimeRelativeReference n)) +
        (Real.log (hamiltonianCoprimeRelativeReference n) - hamiltonianCoprimeEntropyMain n)) := by
      congr 1
      ring
    _ <= abs (Real.log
        (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) -
          Real.log (hamiltonianCoprimeRelativeReference n)) +
        abs (Real.log (hamiltonianCoprimeRelativeReference n) - hamiltonianCoprimeEntropyMain n) :=
      abs_add_le _ _
    _ <= 1 + hamiltonianCoprimeReferenceLogBudget * Real.log (2 * (n : Real)) :=
      add_le_add hLog.2 hRef
    _ <= hamiltonianCoprimeCycleEntropyBudget * Real.log (2 * (n : Real)) := by
      unfold hamiltonianCoprimeCycleEntropyBudget
      nlinarith only [hL]

theorem hamiltonian_totient_entropy_scale_dominates (n : Nat) (hn : 3 <= n) :
    Real.log (2 * (n : Real)) <=
      (n : Real) * (n.totient : Real) ^ (-1 / 8 : Real) * Real.log (2 * (n : Real)) := by
  have hnPos : 0 < n := by omega
  have hnR : 0 < (n : Real) := by exact_mod_cast hnPos
  have hPhiPos : 0 < (n.totient : Real) := by exact_mod_cast Nat.totient_pos.mpr hnPos
  have hPhi1 : (1 : Real) <= n.totient := by
    exact_mod_cast (Nat.totient_pos.mpr hnPos)
  have hPhiLe : (n.totient : Real) <= n := by exact_mod_cast Nat.totient_le n
  have hPowLe : (n.totient : Real) ^ (1 / 8 : Real) <= n := by
    have h := Real.rpow_le_rpow_of_exponent_le hPhi1 (by norm_num : (1 / 8 : Real) <= 1)
    have hPower : (n.totient : Real) ^ (1 / 8 : Real) <= (n.totient : Real) := by
      simpa only [Real.rpow_one] using h
    exact hPower.trans hPhiLe
  have hPowPos : 0 < (n.totient : Real) ^ (1 / 8 : Real) := Real.rpow_pos_of_pos hPhiPos _
  have hInv := one_div_le_one_div_of_le hPowPos hPowLe
  have hProduct := mul_le_mul_of_nonneg_left hInv hnR.le
  have hId : (n : Real) * (1 / (n : Real)) = 1 := by field_simp [ne_of_gt hnR]
  rw [hId] at hProduct
  have hNeg : (n.totient : Real) ^ (-1 / 8 : Real) =
      1 / (n.totient : Real) ^ (1 / 8 : Real) := by
    rw [show (-1 / 8 : Real) = -(1 / 8 : Real) by ring, Real.rpow_neg hPhiPos.le]
    exact (one_div _).symm
  rw [<- hNeg] at hProduct
  have hL := hamiltonian_log_twice_dimension_lower n (by omega)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hProduct (by linarith only [hL])

theorem hamiltonian_coprime_cycle_entropy_uniform :
    exists N0 : Nat, 512 <= N0 /\
      forall (n : Nat) [NeZero n], N0 <= n ->
        0 < (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) /\
        abs (Real.log (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) -
          hamiltonianCoprimeEntropyMain n) <=
            hamiltonianCoprimeCycleEntropyBudget *
              ((n : Real) * (n.totient : Real) ^ (-1 / 8 : Real) *
                Real.log (2 * (n : Real))) := by
  choose N0 hN0 hCount using hamiltonian_coprime_cycle_log_count_uniform
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n inst hn
  have h := hCount n hn
  have hK : 0 <= hamiltonianCoprimeCycleEntropyBudget := by
    unfold hamiltonianCoprimeCycleEntropyBudget hamiltonianCoprimeReferenceLogBudget
    positivity
  exact And.intro h.1 (h.2.trans (mul_le_mul_of_nonneg_left
    (hamiltonian_totient_entropy_scale_dominates n (by omega)) hK))

theorem hamiltonian_coprime_normalized_cycle_entropy :
    forall eps : Real, 0 < eps -> exists N0 : Nat, 512 <= N0 /\
      forall (n : Nat) [NeZero n], N0 <= n ->
        abs (Real.log (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) /
          (n : Real) - (Real.log (n.totient : Real) - 1)) <= eps := by
  intro eps hEps
  have hK : 0 < hamiltonianCoprimeCycleEntropyBudget := by
    unfold hamiltonianCoprimeCycleEntropyBudget hamiltonianCoprimeReferenceLogBudget
    positivity
  choose A hA hCount using hamiltonian_coprime_cycle_log_count_uniform
  choose B hB hSmall using hamiltonian_log_power_dominated_uniform
    (hamiltonianCoprimeCycleEntropyBudget / eps) (div_pos hK hEps) 1 1 (by norm_num)
  let N0 := max A B
  refine Exists.intro N0 (And.intro (hA.trans (le_max_left _ _)) ?_)
  intro n inst hn
  have hnA : A <= n := (le_max_left _ _).trans hn
  have hnB : B <= n := (le_max_right _ _).trans hn
  have hnR : 0 < (n : Real) := by exact_mod_cast (show 0 < n by omega)
  have hRaw := hCount n hnA
  have hBound : hamiltonianCoprimeCycleEntropyBudget * Real.log (2 * (n : Real)) <=
      eps * (n : Real) := by
    have h := mul_le_mul_of_nonneg_left (hSmall n hnB) hEps.le
    simp only [pow_one, Real.rpow_one] at h
    have hId : eps * ((hamiltonianCoprimeCycleEntropyBudget / eps) *
        Real.log (2 * (n : Real))) =
      hamiltonianCoprimeCycleEntropyBudget * Real.log (2 * (n : Real)) := by
      field_simp [ne_of_gt hEps]
    rw [hId] at h
    exact h
  calc
    _ = abs ((Real.log
        (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) -
          hamiltonianCoprimeEntropyMain n) / (n : Real)) := by
      unfold hamiltonianCoprimeEntropyMain
      congr 1
      field_simp [ne_of_gt hnR]
      <;> ring
    _ = abs (Real.log
        (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) -
          hamiltonianCoprimeEntropyMain n) / (n : Real) := by
      rw [abs_div, abs_of_nonneg hnR.le]
    _ <= (hamiltonianCoprimeCycleEntropyBudget * Real.log (2 * (n : Real))) / (n : Real) :=
      div_le_div_of_nonneg_right hRaw.2 hnR.le
    _ <= (eps * (n : Real)) / (n : Real) := div_le_div_of_nonneg_right hBound hnR.le
    _ = eps := by field_simp [ne_of_gt hnR]

end PrimeFactorOscillations
