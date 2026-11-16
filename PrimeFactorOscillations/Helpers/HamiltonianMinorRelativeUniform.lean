/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCountPowerDecay
import PrimeFactorOscillations.Helpers.HamiltonianMinorFirstOrderLogBound

/-! # Uniform direct permanent ratios for independently deleted supports

This is a weaker corollary of the full signed two-power expansion.
The full first-order correction remains available to every sharp consumer.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_nonnegative_square_error (x : Real) (hx : 0 <= x) :
    abs (x - 1) <= abs (x ^ 2 - 1) := by
  have hFactor : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
  rw [hFactor, abs_mul, abs_of_nonneg (by linarith only [hx] : 0 <= x + 1)]
  have h := mul_le_mul_of_nonneg_left (by linarith only [hx] : (1 : Real) <= x + 1)
    (abs_nonneg (x - 1))
  simpa only [mul_one] using h

theorem hamiltonian_rectangular_minor_permanent_nonnegative
    {Iota : Type*} [Fintype Iota] [DecidableEq Iota]
    (T : Matrix Iota Iota Real) (S U : Finset Iota)
    (hT : forall i j, 0 <= T i j) : 0 <= rectangularMinorPermanent T S U := by
  classical
  unfold rectangularMinorPermanent
  split_ifs
  . unfold finitePermutationSum
    exact Finset.sum_nonneg (fun f _ => Finset.prod_nonneg (fun i _ => hT _ _))
  . exact le_refl 0

universe u

theorem stochastic_minor_relative_polylog_uniform
    (delta K : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hK : 0 <= K) :
    exists N0 : Nat, 256 <= N0 /\
      forall (Iota : Type u) [Fintype Iota] [DecidableEq Iota] [Nonempty Iota],
        N0 <= Fintype.card Iota ->
        forall (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
          (q a : Real),
          (Fintype.card Iota : Real) * q = 1 -> 1 <= a ->
          a <= Real.log (Fintype.card Iota : Real) ^ K ->
          (U.card : Real) <= Real.log (2 * (Fintype.card Iota : Real)) ^ 3 ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          0 < weightedPermutationSum T /\
            abs (rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
              weightedPermutationSum T - 1) <=
                (Fintype.card Iota : Real) ^ (-1 / 9 : Real) := by
  have hRange := stochastic_minor_two_power_polylog_uniform.{u} delta K hDelta hDelta1 hK
  let C := hamiltonianMinorUniformConstant delta
  let H := hamiltonianMinorUniformExponent K
  have hC : 0 < C := hRange.1
  choose A hA hExpansion using hRange.2
  choose B hB hAbsorb using hamiltonian_log_power_dominated_uniform
    (2 * C) (mul_pos (by norm_num) hC) H (1 / 2) (by norm_num)
  let N0 := max A (max B (Nat.ceil (Real.exp 1)))
  refine Exists.intro N0 (And.intro (hB.trans ((le_max_left _ _).trans (le_max_right _ _))) ?_)
  intro Iota instF instD instN hn T S U hCard q a hq ha hCap hSize hRow hCol hNonneg hUpper hNorm
  have hnA : A <= Fintype.card Iota := (le_max_left _ _).trans hn
  have hnB : B <= Fintype.card Iota := by dsimp [N0] at hn; omega
  have hnCeil : Nat.ceil (Real.exp 1) <= Fintype.card Iota := by dsimp [N0] at hn; omega
  let n : Real := Fintype.card Iota
  let L := Real.log (2 * n)
  let X := C * L ^ H
  have hn256 : (256 : Real) <= n := by
    change (256 : Real) <= (Fintype.card Iota : Real)
    exact_mod_cast hB.trans hnB
  have hn0 : 0 < n := by linarith only [hn256]
  have hn1 : 1 <= n := by linarith only [hn256]
  have hnExp : Real.exp 1 <= n :=
    (Nat.le_ceil (Real.exp 1)).trans (by
      change (Nat.ceil (Real.exp 1) : Real) <= (Fintype.card Iota : Real)
      exact_mod_cast hnCeil)
  have hqValue : q = 1 / n := by
    calc
      _ = (n * q) / n := by field_simp [ne_of_gt hn0]
      _ = _ := by rw [hq]
  have hFull := hExpansion Iota hnA T S U hCard q a hq ha hCap hSize
    hRow hCol hNonneg hUpper hNorm
  let R := rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
    weightedPermutationSum T
  let Q := hamiltonianMinorFirstOrder T S U q
  have hR0 : 0 <= R := div_nonneg
    (hamiltonian_rectangular_minor_permanent_nonnegative T _ _ hNonneg) hFull.1.le
  have hNumerator := hamiltonian_minor_first_order_log_numerator n (U.card : Real)
    a delta K hnExp (Nat.cast_nonneg _) hSize ha hCap hDelta hDelta1 hK
  have hQ : abs Q <= X / n := by
    have h := stochastic_minor_first_order_budget T S U hCard q a delta hq ha
      hDelta hDelta1 hRow hCol hNonneg hUpper hNorm
    calc
      _ <= 100 * (1 + (U.card : Real)) ^ 2 * (a / delta) ^ 2 * q := h
      _ = (100 * (1 + (U.card : Real)) ^ 2 * (a / delta) ^ 2) / n := by
        rw [hqValue]
        ring
      _ <= X / n := div_le_div_of_nonneg_right hNumerator hn0.le
  have hTwo : abs (R ^ 2 - (1 + Q)) <= X / n ^ 2 := hFull.2
  have hId : R ^ 2 - 1 = (R ^ 2 - (1 + Q)) + Q := by ring
  have hSq : abs (R ^ 2 - 1) <= X / n + X / n ^ 2 := by
    have h := abs_add_le (R ^ 2 - (1 + Q)) Q
    rw [<- hId] at h
    linarith only [h, hTwo, hQ]
  have hX : 2 * X <= n ^ (1 / 2 : Real) := by
    have h := hAbsorb (Fintype.card Iota) hnB
    change (2 * C) * L ^ H <= n ^ (1 / 2 : Real) at h
    dsimp [X]
    nlinarith only [h]
  have hFinal : X / n + X / n ^ 2 <= n ^ (-1 / 9 : Real) := by
    have h := hamiltonian_count_power_decay_scalar n X 1 0 (1 / 9) (1 / 2) hn1
      (by norm_num) (by norm_num) hX (by norm_num) (by norm_num)
    simpa only [mul_one, neg_div] using h
  exact And.intro hFull.1 ((hamiltonian_nonnegative_square_error R hR0).trans (hSq.trans hFinal))

end PrimeFactorOscillations
