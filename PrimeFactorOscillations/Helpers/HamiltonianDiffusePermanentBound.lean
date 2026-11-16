/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import PrimeFactorOscillations.Helpers.HamiltonianRowCapPotential

/-! # Effective and uniform diffuse stochastic permanent upper bounds

The already proved full matching reveal-order bound is evaluated
without column assumptions. Zero cap and zero permanent are included.
The asymptotic threshold is uniform over every matrix at each order.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_cap_entropy_sqrt (c : Real) (hc : 0 < c) :
    2 * c - c * Real.log c <= 2 * Real.sqrt c := by
  let r := Real.sqrt c
  have hr : 0 < r := Real.sqrt_pos.mpr hc
  have hSquare : r ^ 2 = c := Real.sq_sqrt hc.le
  have hLog := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : Real) < 1) hr)
  have hLogInv : Real.log (1 / r) = -Real.log r := by rw [one_div, Real.log_inv]
  rw [hLogInv] at hLog
  have hScaled := mul_le_mul_of_nonneg_left hLog (by positivity : 0 <= 2 * c)
  have hCancel : c * (1 / r) = r := by
    rw [<- hSquare]
    field_simp [ne_of_gt hr]
    <;> ring
  have hLogC : Real.log c = 2 * Real.log r := by
    rw [<- hSquare, Real.log_pow]
    norm_num
  rw [hLogC]
  change 2 * c - c * (2 * Real.log r) <= 2 * r
  nlinarith only [hScaled, hCancel]

theorem hamiltonian_diffuse_permanent_entropy_upper
    (n : Nat) (P : Matrix (Fin (n + 2)) (Fin (n + 2)) Real) (c : Real)
    (hc : 0 < c) (hc1 : c <= 1)
    (hNonneg : forall i j, 0 <= P i j)
    (hRow : forall i, Finset.univ.sum (fun j => P i j) <= 1)
    (hCap : forall i j, P i j <= c) :
    Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 2)) =>
      Finset.univ.prod (fun i => P i (sigma i))) <=
        Real.exp (-(n + 2 : Real) + 1 + (n + 2 : Real) * (2 * c - c * Real.log c)) := by
  exact (hamiltonian_row_cap_permanent_exponential n P c hNonneg hRow hCap).trans
    (Real.exp_le_exp.mpr (hamiltonian_row_cap_entropy_bound n c hc hc1))

theorem hamiltonian_diffuse_permanent_sqrt_upper
    (n : Nat) (P : Matrix (Fin (n + 2)) (Fin (n + 2)) Real) (c : Real)
    (hc0 : 0 <= c) (hc1 : c <= 1)
    (hNonneg : forall i j, 0 <= P i j)
    (hRow : forall i, Finset.univ.sum (fun j => P i j) <= 1)
    (hCap : forall i j, P i j <= c) :
    Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 2)) =>
      Finset.univ.prod (fun i => P i (sigma i))) <=
        Real.exp (-(n + 2 : Real) + 1 + 2 * (n + 2 : Real) * Real.sqrt c) := by
  by_cases hZero : c = 0
  . have hEntry (i j : Fin (n + 2)) : P i j = 0 :=
      le_antisymm (by simpa only [hZero] using hCap i j) (hNonneg i j)
    have hPermanent : Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 2)) =>
        Finset.univ.prod (fun i => P i (sigma i))) = 0 := by
      apply Finset.sum_eq_zero
      intro sigma hs
      let i : Fin (n + 2) := Fin.mk 0 (by omega)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hEntry i (sigma i))
    rw [hPermanent]
    exact (Real.exp_pos _).le
  . have hc : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hZero)
    have hLog := hamiltonian_row_cap_entropy_bound n c hc hc1
    have hEntropy := hamiltonian_cap_entropy_sqrt c hc
    have hScaled := mul_le_mul_of_nonneg_left hEntropy
      (by positivity : 0 <= (n + 2 : Real))
    have hBound : hamiltonianRowCapLogBound n c <=
        -(n + 2 : Real) + 1 + 2 * (n + 2 : Real) * Real.sqrt c := by
      nlinarith only [hLog, hScaled]
    exact (hamiltonian_row_cap_permanent_exponential n P c hNonneg hRow hCap).trans
      (Real.exp_le_exp.mpr hBound)

theorem hamiltonian_effective_diffuse_permanent_upper
    (n : Nat) (P : Matrix (Fin (n + 2)) (Fin (n + 2)) Real)
    (c eps : Real) (hc0 : 0 <= c) (hc1 : c <= 1) (heps : 0 < eps)
    (hSmall : c <= (eps / 4) ^ 2) (hOrder : 2 <= eps * (n + 2 : Real))
    (hNonneg : forall i j, 0 <= P i j)
    (hRow : forall i, Finset.univ.sum (fun j => P i j) <= 1)
    (hCap : forall i j, P i j <= c) :
    Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 2)) =>
      Finset.univ.prod (fun i => P i (sigma i))) <=
        Real.exp (-(1 - eps) * (n + 2 : Real)) := by
  have hSqrt : Real.sqrt c <= eps / 4 := by
    have hSquare := Real.sq_sqrt hc0
    have hPositive := Real.sqrt_nonneg c
    nlinarith only [hSquare, hPositive, hSmall, heps]
  have hScaled := mul_le_mul_of_nonneg_left hSqrt
    (by positivity : 0 <= 2 * (n + 2 : Real))
  have hExponent : -(n + 2 : Real) + 1 + 2 * (n + 2 : Real) * Real.sqrt c <=
      -(1 - eps) * (n + 2 : Real) := by
    nlinarith only [hScaled, hOrder]
  exact (hamiltonian_diffuse_permanent_sqrt_upper n P c hc0 hc1 hNonneg hRow hCap).trans
    (Real.exp_le_exp.mpr hExponent)

theorem hamiltonian_eventual_diffuse_permanent_upper
    (alpha : Nat -> Real) (hAlpha : forall n, 0 <= alpha n)
    (hLimit : Filter.Tendsto alpha Filter.atTop (nhds (0 : Real)))
    (eps : Real) (heps : 0 < eps) :
    Filter.Eventually (fun n =>
      forall (P : Matrix (Fin (n + 2)) (Fin (n + 2)) Real),
        (forall i j, 0 <= P i j) ->
        (forall i, Finset.univ.sum (fun j => P i j) <= 1) ->
        (forall i j, P i j <= alpha n) ->
        Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 2)) =>
          Finset.univ.prod (fun i => P i (sigma i))) <=
            Real.exp (-(1 - eps) * (n + 2 : Real))) Filter.atTop := by
  have hSmallPos : 0 < min (1 : Real) ((eps / 4) ^ 2) :=
    lt_min (by norm_num) (sq_pos_of_pos (by linarith only [heps]))
  have hSmall := (tendsto_order.1 hLimit).2 (min (1 : Real) ((eps / 4) ^ 2)) hSmallPos
  let M := Nat.ceil (2 / eps)
  have hCeil : 2 / eps <= (M : Real) := Nat.le_ceil _
  have hScale := mul_le_mul_of_nonneg_right hCeil heps.le
  have hCancel : (2 / eps) * eps = 2 := by field_simp [ne_of_gt heps]
  rw [hCancel] at hScale
  have hIndex : Filter.Eventually (fun n : Nat => M <= n) Filter.atTop :=
    Filter.eventually_ge_atTop M
  apply Filter.Eventually.mono (Filter.Eventually.and hSmall hIndex)
  intro n hn P hNonneg hRow hCap
  have hOrderNat : (M : Real) <= (n + 2 : Real) := by exact_mod_cast (by omega : M <= n + 2)
  have hOrderScale := mul_le_mul_of_nonneg_right hOrderNat heps.le
  have hOrder : 2 <= eps * (n + 2 : Real) := by nlinarith only [hScale, hOrderScale]
  exact hamiltonian_effective_diffuse_permanent_upper n P (alpha n) eps (hAlpha n)
    ((le_of_lt hn.1).trans (min_le_left _ _)) heps
    ((le_of_lt hn.1).trans (min_le_right _ _)) hOrder hNonneg hRow hCap

end PrimeFactorOscillations
