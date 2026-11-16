/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianStirlingNormalization

/-! # The pi-normalized actual prime-circle asymptotic -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_cycle_relation_matrix (m : Nat) (hm : 1 <= m)
    (s t : Sum (Fin m) (Fin m)) :
    hamiltonianPrimeCycleRelation m s t <->
      Not (hamiltonianUnweightedPrimeMatrix (2 * m)
        (hamiltonianParityIndex m s) (hamiltonianParityIndex m t) = 0) := by
  have hc := hamiltonian_prime_edge_scalar_positive m hm
  change hamiltonianPrimeCycleRelation m s t <->
    Not (((hamiltonianUnweightedPrimeMatrix (2 * m)).submatrix
      (hamiltonianParityEquiv m) (hamiltonianParityEquiv m)) s t = 0)
  rw [hamiltonian_prime_cross_reindex]
  have hMask (P : Prop) [Decidable P] :
      P <-> Not ((if P then Real.log (2 * m : Nat) / (2 * m : Nat) else 0) = 0) := by
    by_cases h : P
    . rw [if_pos h]
      exact Iff.intro (fun _ => ne_of_gt hc) (fun _ => h)
    . rw [if_neg h]
      exact Iff.intro (fun hp => False.elim (h hp)) (fun hn => False.elim (hn rfl))
  cases s with
  | inl i =>
      cases t with
      | inl j =>
          change False <-> Not ((0 : Real) = 0)
          simp
      | inr j =>
          change Nat.Prime (2 * i.val + 2 * j.val + 3) <->
            Not (hamiltonianPrimeCrossBlock m i j = 0)
          rw [hamiltonian_prime_cross_formula]
          exact hMask _
  | inr i =>
      cases t with
      | inl j =>
          change Nat.Prime (2 * j.val + 2 * i.val + 3) <->
            Not (hamiltonianPrimeCrossBlock m j i = 0)
          rw [hamiltonian_prime_cross_formula]
          exact hMask _
      | inr j =>
          change False <-> Not ((0 : Real) = 0)
          simp

theorem hamiltonian_prime_cycle_relation_physical (m : Nat) (hm : 1 <= m)
    (s t : Sum (Fin m) (Fin m)) :
    hamiltonianPrimeCycleRelation m s t <->
      And (Not (hamiltonianParityIndex m s = hamiltonianParityIndex m t))
        (Nat.Prime (((hamiltonianParityIndex m s).val + 1) +
          ((hamiltonianParityIndex m t).val + 1))) := by
  rw [hamiltonian_prime_cycle_relation_matrix m hm s t]
  have hc := hamiltonian_prime_edge_scalar_positive m hm
  by_cases hEq : hamiltonianParityIndex m s = hamiltonianParityIndex m t
  . simp [hamiltonianUnweightedPrimeMatrix, hEq]
  . by_cases hp : Nat.Prime (((hamiltonianParityIndex m s).val + 1) +
        ((hamiltonianParityIndex m t).val + 1))
    . rw [hamiltonianUnweightedPrimeMatrix, if_neg hEq, if_pos hp]
      exact Iff.intro (fun _ => And.intro hEq hp) (fun _ => ne_of_gt hc)
    . simp [hamiltonianUnweightedPrimeMatrix, hEq, hp]

theorem hamiltonian_relative_product_error (r s e d : Real)
    (he : 0 <= e) (he1 : e <= 1) (hd : 0 <= d)
    (hr : abs (r - 1) <= e) (hs : abs (s - 1) <= d) :
    abs (r * s - 1) <= e + 2 * d := by
  have hR : abs r <= 1 + e := by
    have h := abs_add_le (r - 1) (1 : Real)
    rw [show r - 1 + 1 = r by ring, abs_one] at h
    linarith only [h, hr]
  have hProd := mul_le_mul hR hs (abs_nonneg _) (by linarith only [he] : 0 <= 1 + e)
  have hId : r * s - 1 = r * (s - 1) + (r - 1) := by ring
  rw [hId]
  have hTri := abs_add_le (r * (s - 1)) (r - 1)
  rw [abs_mul] at hTri
  have hEd := mul_le_mul_of_nonneg_right he1 hd
  nlinarith only [hTri, hProd, hr, hEd]

theorem hamiltonian_prime_pi_ratio_identity (m : Nat) (hm : 1 <= m) (H : Real) :
    hamiltonianPrimeCircleRatio m H * (Stirling.stirlingSeq m ^ 2 / Real.pi) =
      (hamiltonianPrimeCircleCount m : Real) /
        (Real.pi * Real.exp (2 * H - 2 * (m : Real))) := by
  have hmR : 0 < (m : Real) := Nat.cast_pos.mpr (by omega)
  have hFact : 0 < (m.factorial : Real) := Nat.cast_pos.mpr (Nat.factorial_pos m)
  have hE : Real.exp (m : Real) = (Real.exp 1) ^ m := by
    simpa only [mul_one] using hamiltonian_exp_nat_scalar 1 m
  have hE2 : Real.exp (2 * (m : Real)) = ((Real.exp 1) ^ m) ^ 2 := by
    rw [show 2 * (m : Real) = (m : Real) + (m : Real) by ring, Real.exp_add, hE]
    ring
  have hNeg : Real.exp (-2 * H) = 1 / Real.exp (2 * H) := by
    rw [show -2 * H = -(2 * H) by ring, Real.exp_neg, one_div]
  unfold hamiltonianPrimeCircleRatio
  simp only [Stirling.stirlingSeq, div_pow, mul_pow,
    Real.sq_sqrt (mul_nonneg (by norm_num : (0 : Real) <= 2) hmR.le)]
  rw [Real.exp_sub, hE2, hNeg]
  field_simp [ne_of_gt hmR, ne_of_gt hFact, Real.pi_ne_zero, Real.exp_ne_zero]

theorem hamiltonian_prime_circle_pi_relative_uniform :
    exists M0 : Nat, And (256 <= M0)
      (forall m : Nat, M0 <= m ->
        And (exists H : Real, hamiltonianPrimeEntropyMaximum m H)
          (forall H : Real, hamiltonianPrimeEntropyMaximum m H ->
            abs ((hamiltonianPrimeCircleCount m : Real) /
              (Real.pi * Real.exp (2 * H - 2 * (m : Real))) - 1) <=
                2 * (m : Real) ^ (-3 / 5 : Real))) := by
  choose M0 hM0 hCount using hamiltonian_prime_circle_entropy_relative_uniform
  refine Exists.intro M0 (And.intro hM0 ?_)
  intro m hm
  have hm1 : 1 <= m := by omega
  have hmR : (1 : Real) <= m := by exact_mod_cast hm1
  have hBase := hCount m hm
  refine And.intro hBase.1 ?_
  intro H hH
  have hE : 0 <= (m : Real) ^ (-3 / 5 : Real) := Real.rpow_nonneg (by positivity) _
  have hE1 : (m : Real) ^ (-3 / 5 : Real) <= 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hmR (by norm_num)
  have hD : 0 <= 1 / (3 * (m : Real)) := by positivity
  have hProduct := hamiltonian_relative_product_error (hamiltonianPrimeCircleRatio m H)
    (Stirling.stirlingSeq m ^ 2 / Real.pi) ((m : Real) ^ (-3 / 5 : Real))
    (1 / (3 * (m : Real))) hE hE1 hD (hBase.2 H hH)
    (hamiltonian_stirling_square_relative m hm1)
  rw [hamiltonian_prime_pi_ratio_identity m hm1 H] at hProduct
  have hPower : 1 / (m : Real) <= (m : Real) ^ (-3 / 5 : Real) := by
    have h := Real.rpow_le_rpow_of_exponent_le hmR
      (by norm_num : (-1 : Real) <= -3 / 5)
    simpa only [Real.rpow_neg_one, one_div] using h
  have hSmall : 2 * (1 / (3 * (m : Real))) <= (m : Real) ^ (-3 / 5 : Real) := by
    calc
      _ = (2 / 3 : Real) * (1 / (m : Real)) := by ring
      _ <= 1 / (m : Real) := by nlinarith only [show (0 : Real) <= 1 / (m : Real) by positivity]
      _ <= _ := hPower
  exact hProduct.trans (by linarith only [hSmall])

end PrimeFactorOscillations.LPF
