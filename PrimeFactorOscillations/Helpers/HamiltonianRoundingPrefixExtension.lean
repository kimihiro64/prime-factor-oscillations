/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Abel
import PrimeFactorOscillations.Helpers.HamiltonianRoundingPrefix

/-! # Actual graph-rounding prefix extension with every earlier path entry retained -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_rounding_prefix_extension
    (P : Matrix Iota Iota Real) (S1 S2 : Finset (Sum Iota Iota))
    (delta alpha : Real) (p n : Nat)
    (hd0 : 0 < delta) (hd1 : delta < 1) (ha : 0 <= alpha)
    (hP : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hPRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hPCols : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (hGap : norm (centeredKernel P (1 / (Fintype.card Iota : Real))) <= 1 - delta)
    (hSmall : ((n : Real) * alpha) * Real.log (4 * (Fintype.card Iota : Real)) ^ 2 <=
      hamiltonianForbiddenRepairSmall delta)
    (h : HamiltonianRoundingPrefix P S1 S2 delta alpha p n) :
    Nonempty (HamiltonianRoundingPrefix P S1 S2 delta alpha p (n + 1)) := by
  let L := hamiltonianBipartiteJointLift S1 S2
  choose W f hRaw using hamiltonian_used_edge_joint_repair_step
    S1 S2 P h.cross delta alpha n p (h.centered n) hd0 hd1 ha hP hCap hPRows hPCols
    hGap h.binary h.rows h.cols h.support hSmall
  let Y := L (hamiltonianPermutationCross f - W)
  let D := L (W - P)
  let Znext := Function.update h.centered (n + 1) (h.centered n + Y)
  let Xnext := Function.update h.increments n Y
  let B := hamiltonianRoundingDriftCost Iota delta alpha
  have hExtension := hRaw.2.2.2.2.2.2.1
  have hY : Y.IsHermitian /\ norm Y <= 2 /\
      Matrix.trace ((h.centered n) ^ p.pred * Y) <= 0 := hRaw.2.2.2.2.2.2.2
  have hZOld (k : Nat) (hk : k <= n) : Znext k = h.centered k := by
    have hNe : Not (k = n + 1) := by omega
    exact Function.update_of_ne hNe _ _
  have hXOld (k : Nat) (hk : k < n) : Xnext k = h.increments k := by
    have hNe : Not (k = n) := by omega
    exact Function.update_of_ne hNe _ _
  have hZLast : Znext (n + 1) = h.centered n + Y := by
    simp only [Znext, Function.update_apply, ite_true]
  have hXLast : Xnext n = Y := by
    simp only [Xnext, Function.update_apply, ite_true]
  have hCardNat : 1 <= Fintype.card Iota := Nat.succ_le_of_lt Fintype.card_pos
  have hCard : (1 : Real) <= Fintype.card Iota := by exact_mod_cast hCardNat
  have hLog : 0 <= Real.log (4 * (Fintype.card Iota : Real)) :=
    (Real.log_pos (by nlinarith only [hCard])).le
  have hB : 0 <= B :=
    mul_nonneg
      (mul_nonneg (hamiltonian_forbidden_observable_constant_positive delta hd0 hd1).le ha)
      hLog
  have hD : norm D <= B * (n : Real) :=
    hRaw.2.2.2.2.1.trans_eq (by dsimp [B, hamiltonianRoundingDriftCost]; ring)
  have hR : norm (h.drift + D) <= B * ((n + 1 : Nat) : Real) ^ 2 := by
    calc
      _ <= norm h.drift + norm D := norm_add_le _ _
      _ <= B * (n : Real) ^ 2 + B * (n : Real) := add_le_add h.drift_norm hD
      _ <= _ := by
        rw [Nat.cast_add, Nat.cast_one]
        nlinarith only [hB, mul_nonneg hB (Nat.cast_nonneg n : (0 : Real) <= n)]
  have hMatrix :
      (h.cross + hamiltonianPermutationCross f) - HSMul.hSMul ((n + 1 : Nat) : Real) P =
        (h.cross - HSMul.hSMul (n : Real) P) +
          (hamiltonianPermutationCross f - W) + (W - P) := by
    ext i j
    change h.cross i j + hamiltonianPermutationCross f i j -
        ((n + 1 : Nat) : Real) * P i j =
      (h.cross i j - (n : Real) * P i j) +
        (hamiltonianPermutationCross f i j - W i j) + (W i j - P i j)
    rw [Nat.cast_add, Nat.cast_one]
    ring
  refine Nonempty.intro {
    cross := h.cross + hamiltonianPermutationCross f
    centered := Znext
    increments := Xnext
    drift := h.drift + D
    binary := hExtension.1
    rows := hExtension.2.1
    cols := hExtension.2.2.1
    support := hExtension.2.2.2
    start := ?_
    hermitian := ?_
    increment_hermitian := ?_
    increment_norm := ?_
    direction := ?_
    step := ?_
    error_identity := ?_
    drift_norm := hR }
  . exact (hZOld 0 (Nat.zero_le n)).trans h.start
  . intro k hk
    by_cases hLast : k = n + 1
    . rw [hLast, hZLast]
      exact (h.hermitian n le_rfl).add hY.1
    . have hkOld : k <= n := by omega
      rw [hZOld k hkOld]
      exact h.hermitian k hkOld
  . intro k hk
    by_cases hLast : k = n
    . rw [hLast, hXLast]
      exact hY.1
    . have hkOld : k < n := by omega
      rw [hXOld k hkOld]
      exact h.increment_hermitian k hkOld
  . intro k hk
    by_cases hLast : k = n
    . rw [hLast, hXLast]
      exact hY.2.1
    . have hkOld : k < n := by omega
      rw [hXOld k hkOld]
      exact h.increment_norm k hkOld
  . intro k hk
    by_cases hLast : k = n
    . rw [hLast, hXLast, hZOld n le_rfl]
      exact hY.2.2
    . have hkOld : k < n := by omega
      rw [hXOld k hkOld, hZOld k (Nat.le_of_lt hkOld)]
      exact h.direction k hkOld
  . intro k hk
    by_cases hLast : k = n
    . rw [hLast, hZLast, hZOld n le_rfl, hXLast]
    . have hkOld : k < n := by omega
      have hkSucc : k + 1 <= n := by omega
      rw [hZOld (k + 1) hkSucc, hZOld k (Nat.le_of_lt hkOld), hXOld k hkOld]
      exact h.step k hkOld
  . change L ((h.cross + hamiltonianPermutationCross f) -
      HSMul.hSMul ((n + 1 : Nat) : Real) P) = Znext (n + 1) + (h.drift + D)
    rw [hMatrix, map_add, map_add, h.error_identity, hZLast]
    change (h.centered n + h.drift) + Y + D = (h.centered n + Y) + (h.drift + D)
    abel

end PrimeFactorOscillations
