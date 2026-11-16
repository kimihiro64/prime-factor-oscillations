/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFiniteFactorCount
import PrimeFactorOscillations.Helpers.HamiltonianPrimeFactorFiniteModes
import PrimeFactorOscillations.Helpers.HamiltonianPrimePackingBudgets
import PrimeFactorOscillations.Helpers.HamiltonianRegularDeletionModes

/-! # The actual signed count uniformly through every fixed packing margin -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

universe u v

theorem stochastic_fixed_space_cycle_power_uniform
    (F : Type v) [Fintype F] [DecidableEq F] (rho L : Real)
    (hRho0 : 0 <= rho) (hRho1 : rho < 1) (hL : 0 <= L) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real)
          (R : Matrix J J Real) (U : Matrix J F Real) (V : Matrix F J Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= rho ->
          a - 1 <= (7 / 10 : Real) * Real.log (Fintype.card J : Real) ->
          centeredKernel T q = R + U * V -> norm R <= (2 / 5 : Real) ->
          norm U <= L -> norm V <= L ->
          abs (hamiltonianBipartiteCountRatio T - 1) <=
            (Fintype.card J : Real) ^ (-1 / 3 : Real) := by
  choose N0 hN0 hCount using stochastic_fixed_factor_cycle_power_uniform.{u}
    (Fintype.card F) rho L hRho0 hRho1 hL
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro J instF instD instN hn T q a R U V hq ha hRow hCol hNonneg hUpper
    hNorm hCap hFactor hR hU hV
  let e : Equiv (Fin (Fintype.card F)) F := (Fintype.equivFin F).symm
  let A := U.submatrix id e
  let B := V.submatrix e id
  have hAB : A * B = U * V := by
    ext i j
    change Finset.univ.sum (fun x => U i (e x) * V (e x) j) =
      Finset.univ.sum (fun x => U i x * V x j)
    exact hamiltonian_sum_reindex e (fun x => U i x * V x j)
  have hA : norm A <= L := (hamiltonian_injective_columns_norm e e.injective U).trans hU
  have hB : norm B <= L := (hamiltonian_injective_rows_norm e e.injective V).trans hV
  have hFactor' : centeredKernel T q = R + A * B := by rw [hAB]; exact hFactor
  exact hCount J hn T q a R A B hq ha hRow hCol hNonneg hUpper hNorm hCap hFactor' hR hA hB

namespace LPF

theorem hamiltonian_prime_packing_count_uniform
    (B kappa : Real) (hB : 0 < B) (hk0 : 0 <= kappa) (hk1 : kappa < (1 / 8 : Real)) :
    exists M0 : Nat, 256 <= M0 /\
      forall m : Nat, M0 <= m ->
        forall (F : Finset (Prod (Fin m) (Fin m)))
          (P : Matrix (Fin (2 * m)) (Fin (2 * m)) Real),
          HamiltonianPrimeFactorReferencePacket B m F P ->
          forall (Q : Matrix (Fin m) (Fin m) Real) (alpha : Real),
            0 <= alpha -> alpha <= 2 * kappa ->
            (forall i, Finset.univ.sum (fun j => Q i j) = alpha) ->
            (forall j, Finset.univ.sum (fun i => Q i j) = alpha) ->
            (forall i j, 0 <= Q i j) ->
            (forall i j, Q i j <=
              hamiltonianRegularFactorCross (hamiltonianPrimeFactorRank B m) F i j) ->
            abs (hamiltonianBipartiteCountRatio
              (hamiltonianRegularDeletionKernel
                (hamiltonianRegularFactorCross (hamiltonianPrimeFactorRank B m) F)
                  Q alpha) - 1) <= (m : Real) ^ (-1 / 3 : Real) := by
  have hBudget := hamiltonian_packing_margin_budget kappa hk0 hk1
  let eta := hamiltonianPackingModePrecision kappa
  let rho := hamiltonianPackingCenteredRho kappa
  have hEta : 0 < eta := hBudget.1
  have hEtaSmall : eta <= (1 / 100 : Real) := hBudget.2.1
  have hRho0 : 0 <= rho := hBudget.2.2.1
  have hRho1 : rho < 1 := hBudget.2.2.2.1
  choose K hK M1 hM1 hModes using hamiltonian_prime_factor_finite_modes_terminal B eta hB hEta
  let J := Sum (lpfRationalCenters (27 * K ^ 4)) (lpfRationalCenters (27 * K ^ 4))
  let L := (Fintype.card J : Real) + 1
  have hL : 0 <= L := by dsimp [L]; positivity
  have hL2 : 0 <= 2 * L + 2 := by positivity
  choose MC hMC hCount using stochastic_fixed_space_cycle_power_uniform.{0, 0}
    (Sum J PUnit) rho (2 * L + 2) hRho0 hRho1 hL2
  choose M2 hM2 hWindow using
    hamiltonian_prime_factor_spectral_terminal B (1 / 100) hB (by norm_num)
  let M0 := max M1 (max M2 MC)
  refine Exists.intro M0 (And.intro (hM1.trans (le_max_left _ _)) ?_)
  intro m hm F P hPacket Q alpha ha0 hab hQRow hQCol hQNonneg hQSub
  have hm1 : M1 <= m := (le_max_left _ _).trans hm
  have hm2 : M2 <= m := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hm
  have hmC : MC <= m := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hm
  have hm256 : 256 <= m := hM1.trans hm1
  have hmNat : 0 < m := by omega
  letI : NeZero m := NeZero.mk (Nat.ne_of_gt hmNat)
  have hmR : 0 < (m : Real) := Nat.cast_pos.mpr hmNat
  have hrNat : 0 < hamiltonianPrimeFactorRank B m := by
    have h := hPacket.factor_packet.rank_positive
    omega
  let r : Real := (hamiltonianPrimeFactorRank B m : Real)
  have hr : 0 < r := Nat.cast_pos.mpr hrNat
  let S := hamiltonianRegularFactorCross (hamiltonianPrimeFactorRank B m) F
  let T := hamiltonianRegularDeletionKernel S Q alpha
  let q := 1 / (m : Real)
  let a := 1 + (7 / 10 : Real) * Real.log (m : Real)
  have hq : (Fintype.card (Fin m) : Real) * q = 1 := by
    simp only [Fintype.card_fin]
    dsimp [q]
    field_simp
  have hq0 : 0 <= q := by dsimp [q]; positivity
  have hAlpha := hBudget.2.2.2.2 alpha ha0 hab
  have haQuarter : alpha <= (1 / 4 : Real) := hAlpha.1
  have ha1 : alpha < 1 := by linarith only [haQuarter]
  have hGap : 0 < 1 - alpha := sub_pos.mpr ha1
  choose U V hApprox hU hV hBaseGap using hModes m hm1 F P hPacket
  choose R A C hFactor hR hA hC hGlobal using
    hamiltonian_regular_deletion_modes S Q U V q alpha eta (1 / 2 + eta) L
      hq hq0 ha0 haQuarter hEtaSmall hL hQRow hQCol hQNonneg hBaseGap hApprox hU hV
  have hNorm : norm (centeredKernel T q) <= rho := hGlobal.trans hAlpha.2
  have hSRows := hamiltonian_regular_factor_cross_stochastic m
    (hamiltonianPrimeFactorRank B m) hrNat F hPacket.factor_packet.left_regular
      hPacket.factor_packet.right_regular
  have hStoch := hamiltonian_regular_deletion_stochastic S Q alpha ha1
    hSRows.1 hSRows.2 hQRow hQCol hQSub
  let D := hamiltonianPrimeFactorDegree m
  have hD : 0 < D := (hamiltonian_prime_factor_scalars m (by omega)).2.1
  have hPhysical := hWindow m hm2 F P hPacket
  have hRelative := (abs_le.mp hPhysical.relative_rank).1
  have hRankRatio : (99 / 100 : Real) <= r / D := by
    change -(1 / 100 : Real) <= r / D - 1 at hRelative
    linarith only [hRelative]
  have hRank : (99 / 100 : Real) * D <= r := by
    have h := mul_le_mul_of_nonneg_right hRankRatio hD.le
    have he : (r / D) * D = r := by field_simp
    rw [he] at h
    exact h
  let d := (1 - alpha) * r
  have hd : 0 < d := mul_pos hGap hr
  have hRemain : (3 / 4 : Real) * r <= d := by
    have h := mul_le_mul_of_nonneg_right
      (show (3 / 4 : Real) <= 1 - alpha by linarith only [haQuarter]) hr.le
    exact h
  have hScale : D * Real.log (2 * (m : Real)) = 2 * (m : Real) := by
    have hLog : 0 < Real.log (2 * (m : Real)) := by
      have h := hPacket.factor_packet.log_large
      push_cast at h
      linarith only [h]
    dsimp [D, hamiltonianPrimeFactorDegree]
    push_cast
    field_simp
  have hDensity : (m : Real) / d <= a :=
    hamiltonian_prime_packing_density_budget m D r d (by omega) hD hd hScale hRank hRemain
  have hSUpper (i j : Fin m) : S i j <= 1 / r := by
    change (1 / r) * (if Membership.mem F (i, j) then (1 : Real) else 0) <= 1 / r
    split_ifs <;> nlinarith only [le_of_lt (one_div_pos.mpr hr)]
  have hEntry (i j : Fin m) : T i j <= a * q := by
    have h := hamiltonian_regular_deletion_entry_cap S Q alpha (1 / r) ha1
      hQNonneg hSUpper i j
    have he : (1 / (1 - alpha)) * (1 / r) = 1 / d := by
      dsimp [d]
      field_simp [ne_of_gt hr, ne_of_gt hGap]
      <;> ring
    have hCap : 1 / d <= a * q := by
      calc
        _ = ((m : Real) / d) / (m : Real) := by field_simp
        _ <= a / (m : Real) := div_le_div_of_nonneg_right hDensity hmR.le
        _ = _ := by dsimp [q]; ring
    rw [he] at h
    exact h.trans hCap
  have ha : 1 <= a := by
    have hLog := Real.log_nonneg (show (1 : Real) <= m by exact_mod_cast (by omega : 1 <= m))
    dsimp [a]
    linarith only [hLog]
  have hCap : a - 1 <= (7 / 10 : Real) * Real.log (Fintype.card (Fin m) : Real) := by
    simp only [Fintype.card_fin]
    dsimp [a]
    linarith
  have hn : MC <= Fintype.card (Fin m) := by simpa only [Fintype.card_fin] using hmC
  have hFinal := hCount (Fin m) hn T q a R A C hq ha hStoch.1 hStoch.2.1
    hStoch.2.2 hEntry hNorm hCap hFactor hR hA hC
  simpa only [Fintype.card_fin] using hFinal

end LPF
end PrimeFactorOscillations
