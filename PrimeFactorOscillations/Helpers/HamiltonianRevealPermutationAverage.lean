/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermutationSubsets
import PrimeFactorOscillations.Helpers.HamiltonianWeightedRevealLog

/-! # The actual conditional row-order average

A fixed current row leaves a uniform permutation of the remaining
rows. Its available mass is the fixed matched entry plus a subset
sum of the remaining row weights. The exact permutation average,
followed by log(x) <= x - 1, gives the required row-cap logarithm.
No independence of later rows or replacement by their magnitudes
is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_permutation_point_sum (n : Nat) (i : Fin (n + 1))
    (f : Fin (n + 1) -> Real) :
    Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 1)) => f (sigma i)) =
      (Fintype.card (Equiv.Perm (Fin n)) : Real) * Finset.univ.sum f := by
  have h := finitePermutationSubsetSum_delete
    (fun j _ : Fin (n + 1) => f j) ({i} : Finset (Fin (n + 1))) i (by simp)
  simpa [finDeleteSupport, <- Finset.sum_mul, mul_comm] using h

theorem hamiltonian_permutation_card_step (n : Nat) :
    (Fintype.card (Equiv.Perm (Fin (n + 1))) : Real) =
      (n + 1 : Real) * (Fintype.card (Equiv.Perm (Fin n)) : Real) := by
  have h : (n + 1) * Fintype.card (Equiv.Perm (Fin n)) =
      Fintype.card (Equiv.Perm (Fin (n + 1))) := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      Fintype.card_congr (finPermutationDeleteEquiv (0 : Fin (n + 1)))
  exact_mod_cast h.symm

theorem hamiltonian_permutation_subset_sum (n : Nat)
    (S : Finset (Fin (n + 1))) (f : Fin (n + 1) -> Real) :
    Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 1)) =>
      S.sum (fun k => f (sigma k))) =
      (S.card : Real) * (Fintype.card (Equiv.Perm (Fin n)) : Real) * Finset.univ.sum f := by
  calc
    _ = S.sum (fun k => Finset.univ.sum
        (fun sigma : Equiv.Perm (Fin (n + 1)) => f (sigma k))) := Finset.sum_comm
    _ = S.sum (fun _ => (Fintype.card (Equiv.Perm (Fin n)) : Real) * Finset.univ.sum f) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hamiltonian_permutation_point_sum n k f
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

theorem hamiltonian_finite_log_mean_upper {L : Type*}
    (s : Finset L) (w : L -> Real) (y : Real) (hy : 0 < y)
    (hPositive : forall z, Membership.mem s z -> 0 < w z)
    (hMean : s.sum w <= (s.card : Real) * y) :
    s.sum (fun z => Real.log (w z)) <= (s.card : Real) * Real.log y := by
  have hEach (z : L) (hz : Membership.mem s z) :
      y * Real.log (w z) <= y * Real.log y + w z - y := by
    have hw := hPositive z hz
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hw hy)) (le_of_lt hy)
    rw [Real.log_div (ne_of_gt hw) (ne_of_gt hy)] at h
    have hClear : y * (w z / y - 1) = w z - y := by
      field_simp [ne_of_gt hy]
    rw [hClear] at h
    nlinarith only [h]
  have hSum := Finset.sum_le_sum hEach
  have hLeft : s.sum (fun z => y * Real.log (w z)) =
      y * s.sum (fun z => Real.log (w z)) := (Finset.mul_sum _ _ _).symm
  have hRight : s.sum (fun z => y * Real.log y + w z - y) =
      (s.card : Real) * y * Real.log y + s.sum w - (s.card : Real) * y := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hLeft, hRight] at hSum
  apply le_of_mul_le_mul_left _ hy
  nlinarith only [hSum, hMean]

theorem hamiltonian_conditional_reveal_log_bound
    (n : Nat) (S : Finset (Fin (n + 1))) (f : Fin (n + 1) -> Real)
    (v c : Real) (hv : 0 < v) (hCap : v <= c)
    (hNonneg : forall k, 0 <= f k) (hSum : Finset.univ.sum f <= 1) :
    Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 1)) =>
        Real.log (v + S.sum (fun k => f (sigma k)))) <=
      (Fintype.card (Equiv.Perm (Fin (n + 1))) : Real) *
        Real.log (c + (S.card : Real) / (n + 1 : Real)) := by
  let m : Real := Fintype.card (Equiv.Perm (Fin (n + 1)))
  let m0 : Real := Fintype.card (Equiv.Perm (Fin n))
  have hM : 0 <= m := Nat.cast_nonneg _
  have hM0 : 0 <= m0 := Nat.cast_nonneg _
  have hN : 0 < (n + 1 : Real) := by exact_mod_cast Nat.succ_pos n
  have hCard : m = (n + 1 : Real) * m0 := hamiltonian_permutation_card_step n
  have hScard : (0 : Real) <= S.card := Nat.cast_nonneg _
  have hTarget : 0 < c + (S.card : Real) / (n + 1 : Real) :=
    add_pos_of_pos_of_nonneg (lt_of_lt_of_le hv hCap) (div_nonneg hScard (le_of_lt hN))
  have hPositive (sigma : Equiv.Perm (Fin (n + 1))) :
      0 < v + S.sum (fun k => f (sigma k)) :=
    add_pos_of_pos_of_nonneg hv (Finset.sum_nonneg (fun k _ => hNonneg (sigma k)))
  have hAverage : Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 1)) =>
      v + S.sum (fun k => f (sigma k))) =
      m * v + (S.card : Real) * m0 * Finset.univ.sum f := by
    rw [Finset.sum_add_distrib, hamiltonian_permutation_subset_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m, m0]
  have hTargetExpand : m * (c + (S.card : Real) / (n + 1 : Real)) =
      m * c + (S.card : Real) * m0 := by
    rw [hCard]
    field_simp [ne_of_gt hN] <;> ring
  have hMean : Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 1)) =>
      v + S.sum (fun k => f (sigma k))) <=
      m * (c + (S.card : Real) / (n + 1 : Real)) := by
    rw [hAverage, hTargetExpand]
    have hOwn := mul_le_mul_of_nonneg_left hCap hM
    have hRest := mul_le_mul_of_nonneg_left hSum (mul_nonneg hScard hM0)
    nlinarith only [hOwn, hRest]
  simpa only [Finset.card_univ] using
    hamiltonian_finite_log_mean_upper Finset.univ
      (fun sigma : Equiv.Perm (Fin (n + 1)) => v + S.sum (fun k => f (sigma k)))
      (c + (S.card : Real) / (n + 1 : Real)) hTarget (fun sigma _ => hPositive sigma) hMean

end PrimeFactorOscillations
