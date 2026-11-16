/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCenteredCuts

/-! # Full signed constant/parity cut bound for actual prime edges -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_constant_parity_quadratic (n : Nat) (x : Fin n -> Real) :
    hamiltonianQuadratic (hamiltonianRealConstantParityMatrix n) x =
      ((Finset.univ.sum x) ^ 2 -
        (Finset.univ.sum (fun i => (-1 : Real) ^ (i.val + 1) * x i)) ^ 2) /
          (n : Real) := by
  let y := fun i : Fin n => (-1 : Real) ^ (i.val + 1) * x i
  have hProduct (f : Fin n -> Real) :
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => f i * f j)) =
        (Finset.univ.sum f) ^ 2 := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  have hPoint (i j : Fin n) :
      x i * hamiltonianRealConstantParityMatrix n i j * x j =
        (x i * x j) / (n : Real) - (y i * y j) / (n : Real) := by
    simp only [hamiltonianRealConstantParityMatrix, pow_add]
    dsimp only [y]
    ring
  unfold hamiltonianQuadratic
  simp_rw [hPoint, Finset.sum_sub_distrib, <- Finset.sum_div]
  rw [hProduct x, hProduct y]
  dsimp only [y]
  ring

theorem hamiltonian_constant_parity_centered_nonpositive (n : Nat)
    (x : Fin n -> Real) (hSum : Finset.univ.sum x = 0) :
    hamiltonianQuadratic (hamiltonianRealConstantParityMatrix n) x <= 0 := by
  rw [hamiltonian_constant_parity_quadratic, hSum, zero_pow (by norm_num : Not (2 = 0)), zero_sub]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (Nat.cast_nonneg n)

theorem hamiltonian_cut_variance_half_min (n w : Real)
    (hn : 0 < n) (hw : 0 <= w) (hwn : w <= n) :
    (1 / 2 : Real) * min w (n - w) <= w * (n - w) / n := by
  by_cases h : w <= n - w
  . rw [min_eq_left h]
    have hFactor : n / 2 <= n - w := by linarith only [h]
    have hProd := mul_le_mul_of_nonneg_left hFactor hw
    calc
      _ = (w * (n / 2)) / n := by field_simp [ne_of_gt hn]
      _ <= _ := div_le_div_of_nonneg_right hProd hn.le
  . have hOther : n - w <= w := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right hOther]
    have hFactor : n / 2 <= w := by linarith only [hOther]
    have hProd := mul_le_mul_of_nonneg_right hFactor (sub_nonneg.mpr hwn)
    calc
      _ = ((n / 2) * (n - w)) / n := by field_simp [ne_of_gt hn]
      _ <= _ := div_le_div_of_nonneg_right hProd hn.le

theorem hamiltonian_prime_cut_weight_uniform :
    exists N0 : Nat, And (256 <= N0)
      (forall n : Nat, N0 <= n -> forall W : Finset (Fin n),
        (1 / 5 : Real) * min (W.card : Real) ((n : Real) - (W.card : Real)) <=
          hamiltonianCutBoundary (hamiltonianUnweightedPrimeMatrix n) W) := by
  choose N1 hN1 hDegree using hamiltonian_unweighted_prime_degree_uniform (1 / 20) (by norm_num)
  choose N2 hN2 hGap using hamiltonian_unweighted_prime_operator_gap (1 / 20) (by norm_num)
  let N0 := max 256 (max N1 N2)
  refine Exists.intro N0 (And.intro (le_max_left _ _) ?_)
  intro n hn W
  have hn256 : 256 <= n := (le_max_left _ _).trans hn
  have hn1 : N1 <= n := by dsimp only [N0] at hn; omega
  have hn2 : N2 <= n := by dsimp only [N0] at hn; omega
  haveI : NeZero n := { out := by omega }
  have hRows (i : Fin n) : (19 / 20 : Real) <=
      Finset.univ.sum (fun j => hamiltonianUnweightedPrimeMatrix n i j) := by
    have h := (abs_le.mp (hDegree n hn1 i)).1
    linarith only [h]
  have hReference : hamiltonianQuadratic (hamiltonianRealConstantParityMatrix n)
      (hamiltonianCutCentered W) <= 0 :=
    hamiltonian_constant_parity_centered_nonpositive n _ (hamiltonian_cut_centered_sum W)
  have hNorm : norm (hamiltonianUnweightedPrimeMatrix n -
      hamiltonianRealConstantParityMatrix n) <= (11 / 20 : Real) := by
    have h := hGap n hn2
    linarith only [h]
  have hCut := hamiltonian_cut_reference_bound (hamiltonianUnweightedPrimeMatrix n)
    (hamiltonianRealConstantParityMatrix n) W (19 / 20) (11 / 20)
    (hamiltonian_unweighted_prime_symmetric n) hRows hReference hNorm
  simp only [Fintype.card_fin] at hCut
  have hnR : 0 < (n : Real) := Nat.cast_pos.mpr (by omega)
  have hwNat : W.card <= n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ W
  have hw : (W.card : Real) <= (n : Real) := by exact_mod_cast hwNat
  have hVar := hamiltonian_cut_variance_half_min (n : Real) (W.card : Real)
    hnR (Nat.cast_nonneg _) hw
  nlinarith only [hCut, hVar]

def hamiltonianPrimeCutEdges (n : Nat) (W : Finset (Fin n)) :
    Finset (Prod (Fin n) (Fin n)) :=
  (W.product (Finset.univ \ W)).filter (fun p =>
    And (Not (p.1 = p.2)) (Nat.Prime ((p.1.val + 1) + (p.2.val + 1))))

theorem hamiltonian_prime_cut_boundary_card (n : Nat) (W : Finset (Fin n)) :
    hamiltonianCutBoundary (hamiltonianUnweightedPrimeMatrix n) W =
      (Real.log (n : Real) / (n : Real)) * ((hamiltonianPrimeCutEdges n W).card : Real) := by
  have hPoint (i j : Fin n) :
      hamiltonianUnweightedPrimeMatrix n i j =
        (Real.log (n : Real) / (n : Real)) *
          (if And (Not (i = j)) (Nat.Prime ((i.val + 1) + (j.val + 1)))
            then (1 : Real) else 0) := by
    by_cases hEq : i = j
    . simp [hamiltonianUnweightedPrimeMatrix, hEq]
    . by_cases hp : Nat.Prime ((i.val + 1) + (j.val + 1))
      . simp [hamiltonianUnweightedPrimeMatrix, hEq, hp]
      . simp [hamiltonianUnweightedPrimeMatrix, hEq, hp]
  have hCard : ((hamiltonianPrimeCutEdges n W).card : Real) =
      W.sum (fun i => (Finset.univ \ W).sum (fun j =>
        if And (Not (i = j)) (Nat.Prime ((i.val + 1) + (j.val + 1)))
          then (1 : Real) else 0)) := by
    unfold hamiltonianPrimeCutEdges
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one, Finset.sum_filter]
    exact Finset.sum_product' W (Finset.univ \ W) (fun i j =>
      if And (Not (i = j)) (Nat.Prime ((i.val + 1) + (j.val + 1))) then (1 : Real) else 0)
  rw [hCard]
  unfold hamiltonianCutBoundary
  simp_rw [hPoint]
  simp only [Finset.mul_sum]

theorem hamiltonian_prime_cut_edge_count_uniform :
    exists N0 : Nat, And (256 <= N0)
      (forall n : Nat, N0 <= n -> forall W : Finset (Fin n),
        ((n : Real) / (5 * Real.log (n : Real))) *
          min (W.card : Real) ((n : Real) - (W.card : Real)) <=
            ((hamiltonianPrimeCutEdges n W).card : Real)) := by
  choose N0 hN0 hCut using hamiltonian_prime_cut_weight_uniform
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n hn W
  have hn256 : 256 <= n := hN0.trans hn
  have hnR : 0 < (n : Real) := Nat.cast_pos.mpr (by omega)
  have hLog : 0 < Real.log (n : Real) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hC : 0 < Real.log (n : Real) / (n : Real) := div_pos hLog hnR
  have h := hCut n hn W
  rw [hamiltonian_prime_cut_boundary_card] at h
  have hScaled := mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos.mpr hC))
  have hLeft : ((1 / 5 : Real) * min (W.card : Real) ((n : Real) - (W.card : Real))) *
      Inv.inv (Real.log (n : Real) / (n : Real)) =
      ((n : Real) / (5 * Real.log (n : Real))) *
        min (W.card : Real) ((n : Real) - (W.card : Real)) := by
    field_simp [ne_of_gt hnR, ne_of_gt hLog]
  have hCancel : ((Real.log (n : Real) / (n : Real)) *
      ((hamiltonianPrimeCutEdges n W).card : Real)) *
        Inv.inv (Real.log (n : Real) / (n : Real)) =
      ((hamiltonianPrimeCutEdges n W).card : Real) := by
    field_simp [ne_of_gt hC]
  rwa [hLeft, hCancel] at hScaled

end PrimeFactorOscillations.LPF
