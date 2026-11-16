/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeRealMatrix
import PrimeFactorOscillations.Helpers.HamiltonianSchurBudget

/-! # Actual logarithmic prime weights versus constant edge weights

The small outputs are counted and the large outputs are charged to the
actual Chebyshev prime mass. These are transfer errors only: the signed
arithmetic operator and its proved half-gap remain unchanged.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_log_weight_small (n x : Real)
    (hn : 1 <= n) (hx : 1 <= x) (hxn : x <= n) :
    abs (Real.log n - Real.log x) <= Real.log n := by
  have hLog : Real.log x <= Real.log n :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hx) hxn
  rw [abs_of_nonneg (sub_nonneg.mpr hLog)]
  exact sub_le_self _ (Real.log_nonneg hx)

theorem hamiltonian_log_weight_large (n x : Real)
    (hn : 0 < n) (hL : 1 <= Real.log n)
    (hLogLog : 4 * Real.log (Real.log n) <= Real.log n)
    (hx : 0 < x) (hCut : n / Real.log n ^ 2 <= x) (hUpper : x <= 2 * n) :
    abs (Real.log n - Real.log x) <=
      (2 * (2 * Real.log (Real.log n) + Real.log 2) / Real.log n) * Real.log x := by
  let L := Real.log n
  let A := 2 * Real.log L + Real.log 2
  have hLPos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hCutPos : 0 < n / L ^ 2 := div_pos hn (sq_pos_of_pos hLPos)
  have hLogCut : Real.log (n / L ^ 2) = L - 2 * Real.log L := by
    rw [Real.log_div (ne_of_gt hn) (pow_ne_zero 2 (ne_of_gt hLPos)), Real.log_pow]
    rfl
  have hLowerLog : L - 2 * Real.log L <= Real.log x := by
    rw [<- hLogCut]
    exact Real.log_le_log hCutPos hCut
  have hUpperLog : Real.log x <= L + Real.log 2 := by
    have h := Real.log_le_log hx hUpper
    rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt hn)] at h
    exact h.trans_eq (add_comm _ _)
  have hLL : 0 <= Real.log L := Real.log_nonneg hL
  have hTwo : 0 <= Real.log (2 : Real) := Real.log_nonneg (by norm_num)
  have hA : 0 <= A := by dsimp only [A]; positivity
  have hAbs : abs (L - Real.log x) <= A := by
    apply abs_le.mpr
    dsimp only [A]
    constructor <;> linarith only [hLowerLog, hUpperLog, hLL, hTwo]
  have hHalf : L / 2 <= Real.log x := by
    change 4 * Real.log L <= L at hLogLog
    linarith only [hLogLog, hLowerLog]
  have hScale := mul_le_mul_of_nonneg_left hHalf
    (div_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 2) hA) hLPos.le)
  have hCancel : (2 * A / L) * (L / 2) = A := by
    field_simp [ne_of_gt hLPos]
  rw [hCancel] at hScale
  exact hAbs.trans hScale

theorem hamiltonian_four_log_le_self (L : Real) (hL : 64 <= L) :
    4 * Real.log L <= L := by
  have hL0 : 0 <= L := by linarith only [hL]
  have hLPos : 0 < L := by linarith only [hL]
  have hSqrt : 0 <= Real.sqrt L := Real.sqrt_nonneg L
  have hSquare : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0
  have hSqrtEight : 8 <= Real.sqrt L := by
    nlinarith only [hSquare, hSqrt, hL]
  have hLogEq : Real.log L = 2 * Real.log (Real.sqrt L) := by
    calc
      _ = Real.log (Real.sqrt L ^ 2) := congrArg Real.log hSquare.symm
      _ = _ := by rw [Real.log_pow]; norm_num
  have hLogBound := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hLPos)
  have hProduct := mul_nonneg hSqrt (sub_nonneg.mpr hSqrtEight)
  nlinarith only [hLogEq, hLogBound, hProduct, hSquare]


theorem hamiltonian_nonnegative_shift_budget (n a M : Nat) (w : Nat -> Real)
    (hRange : a + n <= M)
    (hNonnegative : forall t : Nat, Membership.mem (Finset.Ioc 0 M) t -> 0 <= w t) :
    Finset.univ.sum (fun j : Fin n => w (a + (j.val + 1))) <=
      (Finset.Ioc 0 M).sum w := by
  rw [hamiltonian_finite_shift_window]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  . intro t ht
    have h := Finset.mem_Ioc.mp ht
    exact Finset.mem_Ioc.mpr (And.intro (by omega) (by omega))
  . intro t ht htNot
    exact hNonnegative t ht

theorem hamiltonian_finite_prime_weight_split (M K : Nat) (w : Nat -> Real)
    (L c : Real) (hL : 0 <= L) (hc : 0 <= c)
    (hSmall : forall t : Nat, Membership.mem (Finset.Ioc 0 M) t -> t <= K -> w t <= L)
    (hLarge : forall t : Nat, Membership.mem (Finset.Ioc 0 M) t -> K < t ->
      w t <= c * hamiltonianPrimeValue t) :
    (Finset.Ioc 0 M).sum w <= (K : Real) * L + c * Chebyshev.theta (M : Real) := by
  let S := Finset.Ioc 0 M
  let low := S.filter (fun t => t <= K)
  have hLowSubset : forall t : Nat, Membership.mem low t -> Membership.mem (Finset.Ioc 0 K) t := by
    intro t ht
    have h := Finset.mem_filter.mp ht
    have hPositive := (Finset.mem_Ioc.mp h.1).1
    exact Finset.mem_Ioc.mpr (And.intro hPositive h.2)
  have hCardNat : low.card <= K := by
    simpa using Finset.card_le_card hLowSubset
  have hCard : (low.card : Real) <= (K : Real) := Nat.cast_le.mpr hCardNat
  have hPoint (t : Nat) (ht : Membership.mem S t) :
      w t <= (if t <= K then L else 0) + c * hamiltonianPrimeValue t := by
    by_cases htk : t <= K
    . rw [if_pos htk]
      have hMass := mul_nonneg hc (hamiltonian_prime_value_nonnegative t)
      linarith only [hSmall t ht htk, hMass]
    . rw [if_neg htk, zero_add]
      exact hLarge t ht (Nat.lt_of_not_ge htk)
  have hLowSum : S.sum (fun t => if t <= K then L else 0) = (low.card : Real) * L := by
    have hFilter : low.sum (fun _ => L) = S.sum (fun t => if t <= K then L else 0) := by
      simp only [low, Finset.sum_filter]
    rw [<- hFilter]
    simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    _ <= S.sum (fun t => (if t <= K then L else 0) + c * hamiltonianPrimeValue t) :=
      Finset.sum_le_sum (fun t ht => hPoint t ht)
    _ = (low.card : Real) * L + c * Chebyshev.theta (M : Real) := by
      rw [Finset.sum_add_distrib, hLowSum, <- Finset.mul_sum]
      change _ + c * (Finset.Ioc 0 M).sum hamiltonianPrimeValue = _
      rw [hamiltonian_prime_value_prefix]
    _ <= _ := add_le_add (mul_le_mul_of_nonneg_right hCard hL) (le_refl _)

end PrimeFactorOscillations.LPF
