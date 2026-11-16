/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCycleExponentialLower
import PrimeFactorOscillations.Helpers.HamiltonianRepairedSquareExists

/-! # Independent cycle mass after balanced bipartite endpoint deletion

The full retained bipartite kernel is conjugated to the repaired
square lift. Its complete vertex-scaling product is then removed,
with both sides of the original support and their shifted rank kept.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

universe u

theorem stochastic_balanced_deleted_cycle_exponential_lower_uniform
    (rho : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1) :
    exists N0 : Nat, 256 <= N0 /\
      forall (I : Type u) [Fintype I] [DecidableEq I] [Nonempty I]
        (T : Matrix I I Real) (S U : Finset I) (hCard : S.card = U.card) (q a : Real),
        4 <= Fintype.card I -> (Fintype.card I : Real) * q = 1 -> 1 <= a ->
        (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
        (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
        (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
        norm (centeredKernel T q) <= rho ->
        (U.card : Real) * (a / (1 - rho)) ^ 3 * q <= 1 / 10000 ->
        N0 <= Fintype.card (Compl.compl U : Finset I) ->
        2 * a <= hamiltonianSublogCountDensity (1 - (1 - rho) / 2) *
          Real.log (Fintype.card (Compl.compl U : Finset I) : Real) ->
        let J : Finset I := Compl.compl U
        0 < hamiltonianCycleSum (hamiltonianRetainedKernel T S U) /\
          Real.exp (-2 * (Fintype.card J : Real) -
              80 * (U.card : Real) * a / (1 - rho)) /
            (2 * (Fintype.card J : Real)) <=
              hamiltonianCycleSum (hamiltonianRetainedKernel T S U) := by
  let rhoNew := 1 - (1 - rho) / 2
  have hNew0 : 0 <= rhoNew := by dsimp only [rhoNew]; linarith only [hRho0]
  have hNew1 : rhoNew < 1 := by dsimp only [rhoNew]; linarith only [hRho1]
  choose N0 hN0 hCount using stochastic_bipartite_cycle_exponential_lower_uniform.{u}
    rhoNew hNew0 hNew1
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro I instF instD instN T S U hCard q a hN hq ha hRow hCol hNonneg hUpper
    hNorm hSmall hRetained hDensity
  let J : Finset I := Compl.compl U
  let R : Finset (Sum I I) := Compl.compl (S.disjSum U)
  let M := hamiltonianRetainedKernel T S U
  let qNew := q / (1 - (U.card : Real) * q)
  have hRepair := stochastic_repaired_square_exists T S U hCard q a rho
    hN hq ha hRow hCol hNonneg hUpper hNorm hRho1 hSmall
  let z := hRepair.2.2.choose
  have hz := hRepair.2.2.choose_spec
  let A := hamiltonianRepairedSquareKernel T S U hCard z
  let v := hamiltonianRepairedSquareEquiv S U hCard
  let w := fun i : R => 1 + z i
  have hJPos : 0 < Fintype.card J := by
    change 0 < Fintype.card (Compl.compl U : Finset I)
    have h := hN0.trans hRetained
    omega
  have : Nonempty J := Fintype.card_pos_iff.mp hJPos
  have hCountNew := hCount J hRetained A qNew (2 * a) hRepair.2.1
    (by linarith only [ha]) hDensity hz.2.2.2.2.2.1.1 hz.2.2.2.2.2.1.2
    hz.2.2.2.2.1 hz.2.2.2.2.2.2.1 hz.2.2.2.2.2.2.2
  have hw (i : R) : 0 < w i := hz.2.2.1 i
  have hLiftNonneg (i j : Sum I I) : 0 <= bipartiteLift T i j := by
    cases i <;> cases j <;>
      simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply, hNonneg]
  have hMNonneg (i j : R) : 0 <= M i j := hLiftNonneg i.val j.val
  have hMatrix :
      (hamiltonianCrossScaled M w w).submatrix v v = bipartiteLift A := by
    have hDiag : hamiltonianCrossScaled M w w =
        Matrix.diagonal w * M * Matrix.diagonal w := by
      ext i j
      simp only [hamiltonianCrossScaled, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hDiag]
    exact hamiltonian_repaired_scaled_bipartite_reindex T S U hCard z
  have hScaled : hamiltonianCycleSum (hamiltonianCrossScaled M w w) =
      hamiltonianCycleSum (bipartiteLift A) := by
    calc
      _ = hamiltonianCycleSum ((hamiltonianCrossScaled M w w).submatrix v v) :=
        (hamiltonian_cycle_sum_reindex v (hamiltonianCrossScaled M w w)).symm
      _ = _ := congrArg hamiltonianCycleSum hMatrix
  let zeta := 20 * (U.card : Real) * a * q / (1 - rho)
  have hZ : norm z <= zeta := hz.1
  have hZ0 : 0 <= zeta := (norm_nonneg z).trans hZ
  have hPoint (i : R) : abs (z i) <= zeta := by
    have h := (pi_norm_le_iff_of_nonneg hZ0).mp hZ i
    simpa only [Real.norm_eq_abs] using h
  have hLogW (i : R) : Real.log (w i) <= zeta := by
    have h := (le_abs_self (z i)).trans (hPoint i)
    have hL := Real.log_le_sub_one_of_pos (hw i)
    dsimp only [w] at hL
    dsimp only [w]
    linarith only [hL, h]
  have hRank : Fintype.card R <= Fintype.card (Sum I I) :=
    Fintype.card_le_of_injective (fun i : R => i.val) Subtype.val_injective
  have hDim : 0 < (Fintype.card I : Real) := by exact_mod_cast Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hDim]
  have hOriginalTwo : (Fintype.card (Sum I I) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hRankReal : (Fintype.card R : Real) <= Fintype.card (Sum I I) := by
    exact_mod_cast hRank
  have hRankQ : (Fintype.card R : Real) * q <= 2 :=
    (mul_le_mul_of_nonneg_right hRankReal hq0).trans_eq hOriginalTwo
  let B := 80 * (U.card : Real) * a / (1 - rho)
  have hB0 : 0 <= 40 * (U.card : Real) * a / (1 - rho) := by
    apply div_nonneg
    . exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        (le_trans (by norm_num) ha)
    . exact (sub_pos.mpr hRho1).le
  have hLogs : Finset.univ.sum (fun i => Real.log (w i)) +
      Finset.univ.sum (fun i => Real.log (w i)) <= B := by
    have hSum := Finset.sum_le_sum (s := (Finset.univ : Finset R)) (fun i hi => hLogW i)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hSum
    calc
      _ <= 2 * (Fintype.card R : Real) * zeta := by linarith only [hSum]
      _ = (40 * (U.card : Real) * a / (1 - rho)) *
          ((Fintype.card R : Real) * q) := by dsimp only [zeta]; ring
      _ <= (40 * (U.card : Real) * a / (1 - rho)) * 2 :=
        mul_le_mul_of_nonneg_left hRankQ hB0
      _ = B := by dsimp only [B]; ring
  let m : Real := Fintype.card J
  have hCountScaled : Real.exp (-2 * m) / (2 * m) <=
      hamiltonianCycleSum (hamiltonianCrossScaled M w w) :=
    hCountNew.2.trans_eq hScaled.symm
  have hUnscale := hamiltonian_cycle_unscale_lower M w w B
    (Real.exp (-2 * m) / (2 * m)) hMNonneg hw hw hLogs hCountScaled
  have hIdentity : Real.exp (-2 * m - B) / (2 * m) =
      Real.exp (-B) * (Real.exp (-2 * m) / (2 * m)) := by
    calc
      _ = Real.exp ((-B) + (-2 * m)) / (2 * m) :=
        congrArg (fun t => Real.exp t / (2 * m)) (by ring)
      _ = _ := by rw [Real.exp_add]; ring
  rw [<- hIdentity] at hUnscale
  refine And.intro ?_ hUnscale
  have hm : 0 < m := by dsimp only [m]; exact_mod_cast hJPos
  exact (div_pos (Real.exp_pos _) (mul_pos (by norm_num) hm)).trans_le hUnscale

end PrimeFactorOscillations
