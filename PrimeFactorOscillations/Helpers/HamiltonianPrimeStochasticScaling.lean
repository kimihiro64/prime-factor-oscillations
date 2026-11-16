/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeScalingWindow

/-! # Support-preserving stochastic scaling of the actual prime cross block -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_cross_degree_sqrt :
    exists B : Real, And (0 < B)
      (exists M0 : Nat, And (256 <= M0)
        (forall m : Nat, M0 <= m ->
          And (64 <= Real.log (2 * m : Nat))
          (And (forall i : Fin m,
            abs (Finset.univ.sum (fun j => hamiltonianPrimeCrossBlock m i j) - 1) <=
              B / Real.sqrt (Real.log (2 * m : Nat)))
            (forall j : Fin m,
            abs (Finset.univ.sum (fun i => hamiltonianPrimeCrossBlock m i j) - 1) <=
              B / Real.sqrt (Real.log (2 * m : Nat)))))) := by
  choose D hD N1 hN1 hDegree using hamiltonian_prime_cross_degree_rate 1
  choose N2 hN2 hLog using hamiltonian_log_terminal_lower 64
  let B := hamiltonianPrimeLogDecayConstant + D
  have hB : 0 < B := add_pos hamiltonian_prime_log_decay_constant_positive hD
  refine Exists.intro B (And.intro hB (Exists.intro (max N1 N2)
    (And.intro (hN1.trans (le_max_left _ _)) ?_)))
  intro m hm
  have hm1 : N1 <= m := (le_max_left _ _).trans hm
  have hm2 : N2 <= 2 * m := by have h := (le_max_right N1 N2).trans hm; omega
  let L := Real.log (2 * m : Nat)
  have hL : 64 <= L := hLog (2 * m) hm2
  have hLpos : 0 < L := by linarith only [hL]
  have hSqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hSqrtLe : Real.sqrt L <= L := by
    nlinarith only [Real.sq_sqrt hLpos.le, Real.sqrt_nonneg L, hL]
  have hTransfer : hamiltonianPrimeLogTransferError (2 * m) + D / L <=
      B / Real.sqrt L := by
    calc
      _ <= hamiltonianPrimeLogDecayConstant / Real.sqrt L + D / Real.sqrt L :=
        add_le_add (hamiltonian_prime_log_transfer_sqrt_bound (2 * m) hL)
          (div_le_div_of_nonneg_left hD.le hSqrt hSqrtLe)
      _ = _ := by dsimp only [B]; ring
  have h := hDegree m hm1
  refine And.intro hL (And.intro ?_ ?_)
  . intro i
    have hd := h.1 i
    simp only [pow_one] at hd
    exact hd.trans hTransfer
  . intro j
    have hd := h.2 j
    simp only [pow_one] at hd
    exact hd.trans hTransfer

theorem hamiltonian_prime_cross_stochastic_scaling (eta : Real) (hEta : 0 < eta) :
    exists M0 : Nat, And (256 <= M0)
      (forall m : Nat, M0 <= m ->
        exists z : Sum (Fin m) (Fin m) -> Real,
          norm z <= eta /\
          (forall i, 0 < 1 + z i) /\
          (forall i j, 0 <= hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) /\
          (forall i, Finset.univ.sum (fun j =>
            hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1) /\
          (forall j, Finset.univ.sum (fun i =>
            hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1) /\
          (forall i j, hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j = 0 <->
            hamiltonianPrimeCrossBlock m i j = 0) /\
          (forall i j, hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j <=
            ((3 / 5 : Real) * Real.log (2 * m : Nat)) / (m : Real)) /\
          norm (centeredKernel (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)
            (1 / (m : Real))) <= 3 / 5) := by
  choose B hB N1 hN1 hDegree using hamiltonian_prime_cross_degree_sqrt
  let t := min (1 / 1024 : Real) (eta / 4)
  have ht : 0 < t := lt_min (by norm_num) (div_pos hEta (by norm_num))
  choose L0 hL0 hWindow using hamiltonian_prime_scaling_real_window B t hB ht
  choose N2 hN2 hLog using hamiltonian_log_terminal_lower L0
  choose N3 hN3 hGap using hamiltonian_prime_cross_operator_uniform (1 / 20) (by norm_num)
  let M0 := max N1 (max N2 N3)
  refine Exists.intro M0 (And.intro (by dsimp only [M0]; omega) ?_)
  intro m hm
  have hm1 : N1 <= m := by dsimp only [M0] at hm; omega
  have hm2 : N2 <= 2 * m := by dsimp only [M0] at hm; omega
  have hm3 : N3 <= m := by dsimp only [M0] at hm; omega
  have hmPos : 1 <= m := by omega
  haveI : NeZero m := { out := by omega }
  let L := Real.log (2 * m : Nat)
  let eps := B / Real.sqrt L
  let g := hamiltonianDiffuseInverseBudget (L / 2 + 9 * eps) (2 / 3)
  let r := 4 * g * eps
  have hLarge : L0 <= L := hLog (2 * m) hm2
  have hL : 64 <= L := hL0.trans hLarge
  have hW := hWindow L hLarge
  have hEps : 0 < eps := hW.1
  have hEpsSmall : eps <= 1 / 100 := hW.2.1
  have hSmall : eps * g ^ 2 <= t := hW.2.2
  have hg : 1 <= g := hamiltonian_diffuse_inverse_budget_positive _ _
    (by linarith only [hL, hEps]) (by norm_num) (by norm_num)
  have hgSq : g <= g ^ 2 := by nlinarith only [hg]
  have hR0 : 0 <= r := by dsimp only [r]; positivity
  have hRsmall : r <= 1 / 256 := by
    have ht1 : t <= 1 / 1024 := min_le_left _ _
    have hProd := mul_le_mul_of_nonneg_left hgSq hEps.le
    dsimp only [r]
    nlinarith only [hProd, hSmall, ht1]
  have hReta : r <= eta := by
    have ht2 : t <= eta / 4 := min_le_right _ _
    have hProd := mul_le_mul_of_nonneg_left hgSq hEps.le
    dsimp only [r]
    nlinarith only [hProd, hSmall, ht2]
  have hRow := (hDegree m hm1).2.1
  have hCol := (hDegree m hm1).2.2
  have hNorm : norm (centeredKernel (hamiltonianPrimeCrossBlock m) (1 / (m : Real))) <=
      (2 / 3 : Real) - 6 * eps := by
    have h := hGap m hm3
    linarith only [h, hEpsSmall]
  have hq : (Fintype.card (Fin m) : Real) * (1 / (m : Real)) = 1 := by
    simp only [Fintype.card_fin]
    field_simp [ne_of_gt (Nat.cast_pos.mpr (by omega : 0 < m) : (0 : Real) < (m : Real))]
  have hCap (i j : Fin m) : hamiltonianPrimeCrossBlock m i j <=
      (L / 2) * (1 / (m : Real)) := by
    simpa only [L, div_eq_mul_inv, mul_one, one_mul] using hamiltonian_prime_cross_entry_bound m hmPos i j
  have hRepairSmall : eps * g ^ 2 <= 1 / 256 :=
    hSmall.trans ((min_le_left _ _).trans (by norm_num : (1 / 1024 : Real) <= 1 / 256))
  choose z hZ hPos hNonneg hRows hCols hSupport hUpper hError using
    hamiltonian_actual_diffuse_stochastic_repair (hamiltonianPrimeCrossBlock m)
      (1 / (m : Real)) (L / 2) eps (2 / 3) hq (by linarith only [hL])
      hEps (by linarith only [hEpsSmall])
      (hamiltonian_prime_cross_nonnegative m hmPos) hRow hCol hCap hNorm
      (by norm_num) (by norm_num) hRepairSmall
  have hR2 : r ^ 2 <= (1 / 256 : Real) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hRsmall hRsmall hR0 (by norm_num : (0 : Real) <= 1 / 256)
  have hErrSmall : (2 * r + r ^ 2) * (1 + eps) <= 1 / 100 := by
    calc
      _ <= (2 * (1 / 256 : Real) + (1 / 256 : Real) ^ 2) * (101 / 100 : Real) :=
        mul_le_mul (by nlinarith only [hRsmall, hR2])
          (by linarith only [hEpsSmall]) (by positivity) (by norm_num)
      _ <= _ := by norm_num
  have hScaledNorm :
      norm (centeredKernel (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)
        (1 / (m : Real))) <= 3 / 5 := by
    have hId : centeredKernel (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)
        (1 / (m : Real)) =
        (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z - hamiltonianPrimeCrossBlock m) +
          centeredKernel (hamiltonianPrimeCrossBlock m) (1 / (m : Real)) := by
      unfold centeredKernel
      abel
    rw [hId]
    have hTri := norm_add_le
      (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z - hamiltonianPrimeCrossBlock m)
      (centeredKernel (hamiltonianPrimeCrossBlock m) (1 / (m : Real)))
    have hOld := hGap m hm3
    have hErr : norm (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z -
        hamiltonianPrimeCrossBlock m) <= 1 / 100 := hError.trans hErrSmall
    linarith only [hTri, hOld, hErr]
  have hFinalCap (i j : Fin m) :
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j <=
        ((3 / 5 : Real) * Real.log (2 * m : Nat)) / (m : Real) := by
    have hCoeff : (1 + r) ^ 2 / 2 <= (3 / 5 : Real) := by
      nlinarith only [hRsmall, hR2]
    have hLdiv : 0 <= L / (m : Real) := div_nonneg (by linarith only [hL]) (Nat.cast_nonneg m)
    calc
      _ <= (1 + r) ^ 2 * ((L / 2) * (1 / (m : Real))) := hUpper i j
      _ = ((1 + r) ^ 2 / 2) * (L / (m : Real)) := by ring
      _ <= (3 / 5 : Real) * (L / (m : Real)) :=
        mul_le_mul_of_nonneg_right hCoeff hLdiv
      _ = _ := by ring
  exact Exists.intro z (And.intro (hZ.trans hReta)
    (And.intro hPos (And.intro hNonneg (And.intro hRows (And.intro hCols
      (And.intro hSupport (And.intro hFinalCap hScaledNorm)))))))

end PrimeFactorOscillations.LPF
