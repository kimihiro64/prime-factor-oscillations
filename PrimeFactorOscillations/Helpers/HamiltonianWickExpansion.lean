/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.Basic
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceCorrection

/-! # Signed Wick contributions and their uniform pair bound

The recursion enumerates every pairing by the partner of its first label.
All labels and matrix entries remain quantified. The low-degree identities
retain all return pairings, including repeated labels and birth diagonals.
The pair bound holds for every number of pairs, not a finite test range.

Identification with the normalized rook function and the infinite diagram
remainder are separate consumers; they are not assumed as theorems here.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*}

def wickPairMoment (M : Matrix Iota Iota Real) : Nat -> List Iota -> Real
  | 0, [] => 1
  | 0, _ :: _ => 0
  | _ + 1, [] => 0
  | e + 1, i :: xs =>
    Finset.sum (Finset.range xs.length) (fun j =>
      M i (xs.getD j i) * wickPairMoment M e (xs.eraseIdx j))

def wickPairCount : Nat -> Nat
  | 0 => 1
  | e + 1 => (2 * e + 1) * wickPairCount e

theorem wickPairMoment_wrong_length (M : Matrix Iota Iota Real)
    (e : Nat) (xs : List Iota) (hLen : Not (xs.length = 2 * e)) :
    wickPairMoment M e xs = 0 := by
  induction e generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hLen
    | cons i xs => rfl
  | succ e ih =>
    cases xs with
    | nil => rfl
    | cons i xs =>
      rw [wickPairMoment]
      apply Finset.sum_eq_zero
      intro j hj
      have hjLt : j < xs.length := Finset.mem_range.mp hj
      have hErase := List.length_eraseIdx_add_one hjLt
      have hWrong : Not ((xs.eraseIdx j).length = 2 * e) := by
        intro h
        apply hLen
        simp only [List.length_cons]
        omega
      rw [ih (xs.eraseIdx j) hWrong, mul_zero]

theorem wickPairMoment_bound (M : Matrix Iota Iota Real) (c : Real)
    (hc : 0 <= c) (hEntry : forall i j, abs (M i j) <= c)
    (e : Nat) (xs : List Iota) (hLen : xs.length = 2 * e) :
    abs (wickPairMoment M e xs) <= (wickPairCount e : Real) * c ^ e := by
  induction e generalizing xs with
  | zero =>
    have hEmpty : xs = [] := by
      cases xs with
      | nil => rfl
      | cons i xs => simp only [List.length_cons] at hLen; omega
    subst xs
    simp [wickPairMoment, wickPairCount]
  | succ e ih =>
    cases xs with
    | nil => simp only [List.length_nil] at hLen; omega
    | cons i xs =>
      have hXs : xs.length = 2 * e + 1 := by
        simp only [List.length_cons] at hLen
        omega
      have hTerm : forall j, Membership.mem (Finset.range xs.length) j ->
          abs (M i (xs.getD j i) * wickPairMoment M e (xs.eraseIdx j)) <=
            c * ((wickPairCount e : Real) * c ^ e) := by
        intro j hj
        have hErase := List.length_eraseIdx_add_one (Finset.mem_range.mp hj)
        have hEraseLength : (xs.eraseIdx j).length = 2 * e := by omega
        rw [abs_mul]
        exact mul_le_mul (hEntry i (xs.getD j i)) (ih (xs.eraseIdx j) hEraseLength)
          (abs_nonneg _) hc
      rw [wickPairMoment]
      calc
        _ <= Finset.sum (Finset.range xs.length)
            (fun j => abs (M i (xs.getD j i) * wickPairMoment M e (xs.eraseIdx j))) :=
          Finset.abs_sum_le_sum_abs _ _
        _ <= Finset.sum (Finset.range xs.length)
            (fun _ => c * ((wickPairCount e : Real) * c ^ e)) :=
          Finset.sum_le_sum (fun j hj => hTerm j hj)
        _ = _ := by simp [hXs, wickPairCount, pow_succ]; ring

private theorem wick_nat_power_mono (a b : Nat) (h : a <= b) (e : Nat) :
    a ^ e <= b ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, pow_succ]
    exact Nat.mul_le_mul ih h

theorem wickPairCount_le_even_power (e : Nat) : wickPairCount e <= (2 * e) ^ e := by
  induction e with
  | zero => simp [wickPairCount]
  | succ e ih =>
    have hStep : 2 * e + 1 <= 2 * (e + 1) := by omega
    have hPower := wick_nat_power_mono (2 * e) (2 * (e + 1)) (by omega) e
    calc
      _ = (2 * e + 1) * wickPairCount e := rfl
      _ <= (2 * (e + 1)) * (2 * e) ^ e := Nat.mul_le_mul hStep ih
      _ <= (2 * (e + 1)) * (2 * (e + 1)) ^ e :=
        Nat.mul_le_mul_left _ hPower
      _ = _ := by rw [pow_succ]; ring

theorem wickPairMoment_uniform_bound (M : Matrix Iota Iota Real) (c : Real)
    (hc : 0 <= c) (hEntry : forall i j, abs (M i j) <= c)
    (e : Nat) (xs : List Iota) (hLen : xs.length = 2 * e) :
    abs (wickPairMoment M e xs) <= (2 * (e : Real)) ^ e * c ^ e := by
  have hCount : (wickPairCount e : Real) <= (2 * (e : Real)) ^ e := by
    exact_mod_cast wickPairCount_le_even_power e
  exact le_trans (wickPairMoment_bound M c hc hEntry e xs hLen)
    (mul_le_mul_of_nonneg_right hCount (pow_nonneg hc e))

theorem wickPairMoment_four_same (M : Matrix Iota Iota Real) (i : Iota) :
    wickPairMoment M 2 [i, i, i, i] = 3 * M i i ^ 2 := by
  norm_num [wickPairMoment, Finset.sum_range_succ, List.eraseIdx, List.getD]
  <;> ring

theorem wickPairMoment_two_triples (M : Matrix Iota Iota Real) (i j : Iota) :
    wickPairMoment M 3 [i, i, i, j, j, j] =
      9 * (M i i * M j j * M i j) + 6 * M i j ^ 3 := by
  norm_num [wickPairMoment, Finset.sum_range_succ, List.eraseIdx, List.getD]
  <;> ring

theorem wickPairMoment_six_same (M : Matrix Iota Iota Real) (i : Iota) :
    wickPairMoment M 3 [i, i, i, i, i, i] = 15 * M i i ^ 3 := by
  norm_num [wickPairMoment, Finset.sum_range_succ, List.eraseIdx, List.getD]
  <;> ring

variable [DecidableEq Iota] [Fintype Iota]

def wickDegreeSixCorrection (M : Matrix Iota Iota Real) : Real :=
  -(1 / 4 : Real) * Finset.sum Finset.univ (fun i => wickPairMoment M 2 [i, i, i, i]) +
    (1 / 18 : Real) * Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
      (fun j => if i = j then 0 else wickPairMoment M 3 [i, i, i, j, j, j])) -
    (1 / 9 : Real) * Finset.sum Finset.univ (fun i => wickPairMoment M 3 [i, i, i, i, i, i])

private theorem wick_off_diagonal_sum (f : Iota -> Iota -> Real) (i : Iota) :
    Finset.sum Finset.univ (fun j => if i = j then 0 else f i j) =
      Finset.sum Finset.univ (fun j => f i j) - f i i := by
  calc
    _ = Finset.sum Finset.univ
        (fun j => f i j - if i = j then f i j else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : i = j
      case pos => simp [h]
      case neg => simp [h]
    _ = _ := by rw [Finset.sum_sub_distrib]; simp

theorem wickDegreeSixCorrection_eq (M : Matrix Iota Iota Real) :
    wickDegreeSixCorrection M = covarianceCorrection M -
      (5 / 2 : Real) * Finset.sum Finset.univ (fun i => M i i ^ 3) := by
  have hFour :
      Finset.sum Finset.univ (fun i => wickPairMoment M 2 [i, i, i, i]) =
        3 * Finset.sum Finset.univ (fun i => M i i ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact wickPairMoment_four_same M i
  have hSix :
      Finset.sum Finset.univ (fun i => wickPairMoment M 3 [i, i, i, i, i, i]) =
        15 * Finset.sum Finset.univ (fun i => M i i ^ 3) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact wickPairMoment_six_same M i
  have hTriples :
      Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
        (fun j => if i = j then 0 else wickPairMoment M 3 [i, i, i, j, j, j])) =
      Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun j =>
          9 * (M i i * M j j * M i j) + 6 * M i j ^ 3) - 15 * M i i ^ 3) := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = Finset.sum Finset.univ
          (fun j => if i = j then 0 else 9 * (M i i * M j j * M i j) + 6 * M i j ^ 3) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i = j
        case pos => rw [if_pos hij, if_pos hij]
        case neg =>
          rw [if_neg hij, if_neg hij]
          exact wickPairMoment_two_triples M i j
      _ = _ := by
        rw [wick_off_diagonal_sum
          (fun a b => 9 * (M a a * M b b * M a b) + 6 * M a b ^ 3) i]
        congr 1
        ring
  unfold wickDegreeSixCorrection
  rw [hFour, hSix, hTriples]
  unfold covarianceCorrection covarianceDiagonalEnergy covarianceTriple covarianceCubic
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, <- Finset.mul_sum]
  ring

theorem wickDegreeSixCorrection_error_bound (M : Matrix Iota Iota Real) (c : Real)
    (hc : 0 <= c) (hEntry : forall i j, abs (M i j) <= c) :
    abs (wickDegreeSixCorrection M - covarianceCorrection M) <=
      (5 / 2 : Real) * (Fintype.card Iota : Real) * c ^ 3 := by
  have hDiagonal : abs (Finset.sum Finset.univ (fun i => M i i ^ 3)) <=
      (Fintype.card Iota : Real) * c ^ 3 := by
    calc
      _ <= Finset.sum Finset.univ (fun i => abs (M i i ^ 3)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum Finset.univ (fun _ : Iota => c ^ 3) := by
        apply Finset.sum_le_sum
        intro i hi
        have h := hEntry i i
        have hSq := mul_le_mul h h (abs_nonneg (M i i)) hc
        have hCube := mul_le_mul hSq h (abs_nonneg (M i i))
          (mul_nonneg hc hc)
        rw [abs_pow]
        nlinarith only [hCube]
      _ = _ := by simp
  rw [wickDegreeSixCorrection_eq]
  have hDifference : covarianceCorrection M -
      (5 / 2 : Real) * Finset.sum Finset.univ (fun i => M i i ^ 3) -
      covarianceCorrection M =
        -(5 / 2 : Real) * Finset.sum Finset.univ (fun i => M i i ^ 3) := by ring
  rw [hDifference, abs_mul]
  norm_num
  nlinarith only [hDiagonal]


theorem wickDegreeSixCorrection_scaled_error_bound
    (M : Matrix Iota Iota Real) (g c : Real) (hg : 0 <= g) (hc : 0 <= c)
    (hDiagonal : forall i, g * abs (M i i) <= c) :
    g ^ 3 * abs (wickDegreeSixCorrection M - covarianceCorrection M) <=
      (5 / 2 : Real) * (Fintype.card Iota : Real) * c ^ 3 := by
  have hError : abs (wickDegreeSixCorrection M - covarianceCorrection M) =
      (5 / 2 : Real) * abs (Finset.sum Finset.univ (fun i => M i i ^ 3)) := by
    rw [wickDegreeSixCorrection_eq]
    have h : covarianceCorrection M -
        (5 / 2 : Real) * Finset.sum Finset.univ (fun i => M i i ^ 3) -
        covarianceCorrection M =
          -(5 / 2 : Real) * Finset.sum Finset.univ (fun i => M i i ^ 3) := by ring
    rw [h, abs_mul]
    norm_num
  have hPower : forall i, (g * abs (M i i)) ^ 3 <= c ^ 3 := by
    intro i
    have h := hDiagonal i
    have hNonneg : 0 <= g * abs (M i i) := mul_nonneg hg (abs_nonneg _)
    have hSq := mul_le_mul h h hNonneg hc
    have hCube := mul_le_mul hSq h hNonneg (mul_nonneg hc hc)
    nlinarith only [hCube]
  calc
    _ = (5 / 2 : Real) * (g ^ 3 *
        abs (Finset.sum Finset.univ (fun i => M i i ^ 3))) := by rw [hError]; ring
    _ <= (5 / 2 : Real) * (g ^ 3 *
        Finset.sum Finset.univ (fun i => abs (M i i ^ 3))) := by
      apply mul_le_mul_of_nonneg_left
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg hg 3)
      norm_num
    _ = (5 / 2 : Real) * Finset.sum Finset.univ (fun i => (g * abs (M i i)) ^ 3) := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_pow, mul_pow]
    _ <= (5 / 2 : Real) * Finset.sum Finset.univ (fun _ : Iota => c ^ 3) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hPower i)) (by norm_num)
    _ = _ := by simp; ring

variable [Nonempty Iota]

theorem stochastic_block_wick_diagonal_error_bound
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hcol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hnonneg : forall i j, 0 <= T i j) (hupper : forall i j, T i j <= a * q)
    (hRho : rho < 1) (hNorm : norm (centeredKernel T q) <= rho) :
    (1 - rho) ^ 3 * abs (
      wickDegreeSixCorrection (resolventCovariance (bipartiteLift (centeredKernel T q))) -
      covarianceCorrection (resolventCovariance (bipartiteLift (centeredKernel T q)))) <=
        40 * a ^ 3 * q ^ 2 := by
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hGap : 0 <= 1 - rho := le_of_lt (sub_pos.mpr hRho)
  have hCardPos : 0 < (Fintype.card Iota : Real) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hCardPos, hq]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hAq : 0 <= a * q := mul_nonneg ha0 hq0
  have hDiagonal : forall i, (1 - rho) * abs (G i i) <= 2 * a * q := by
    intro i
    have h := stochastic_block_covariance_entry_bound T q a rho hq ha hrow hcol
      hnonneg hupper hRho hNorm i i
    change (1 - rho) * norm (G i i) <= (2 - rho) * (a * q) at h
    rw [Real.norm_eq_abs] at h
    have hCap := mul_le_mul_of_nonneg_right
      (show 2 - rho <= 2 by linarith only [hRho0]) hAq
    nlinarith only [h, hCap]
  have hBase := wickDegreeSixCorrection_scaled_error_bound G (1 - rho) (2 * a * q)
    hGap (by positivity) hDiagonal
  have hCard : (Fintype.card (Sum Iota Iota) : Real) =
      2 * (Fintype.card Iota : Real) := by
    simp only [Fintype.card_sum, Nat.cast_add]
    ring
  have hNq : (Fintype.card Iota : Real) * q ^ 3 = q ^ 2 := by
    calc
      _ = ((Fintype.card Iota : Real) * q) * q ^ 2 := by ring
      _ = q ^ 2 := by rw [hq, one_mul]
  change (1 - rho) ^ 3 *
    abs (wickDegreeSixCorrection G - covarianceCorrection G) <= 40 * a ^ 3 * q ^ 2
  calc
    _ <= (5 / 2 : Real) * (Fintype.card (Sum Iota Iota) : Real) * (2 * a * q) ^ 3 := hBase
    _ = 40 * a ^ 3 * ((Fintype.card Iota : Real) * q ^ 3) := by rw [hCard]; ring
    _ = _ := by rw [hNq]

end PrimeFactorOscillations
