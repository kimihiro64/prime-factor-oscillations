/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorTailTilt

/-! # The actual compensated complementary-minor tail

The ratio squared, constant subtraction and full first-order correction
are all present. Only the retained tail is estimated by tilted Gram mass.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_rank_square_exponential (r : Nat) :
    (1 + (r : Real)) ^ 2 <= (4 : Real) ^ r := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    have hr : (0 : Real) <= r := Nat.cast_nonneg r
    have hQuad : (1 + ((r : Real) + 1)) ^ 2 <=
        4 * (1 + (r : Real)) ^ 2 := by nlinarith only [hr]
    have h := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : Real) <= 4)
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith only [hQuad, h]

theorem hamiltonian_exp_nat_scalar (c : Real) (r : Nat) :
    Real.exp ((r : Real) * c) = Real.exp c ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.exp_add, ih, pow_succ]

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

def hamiltonianCompensatedMinorError (T : Matrix Iota Iota Real) (q : Real)
    (S U : Finset Iota) : Real :=
  (rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
    weightedPermutationSum T) ^ 2 - 1 - hamiltonianMinorFirstOrder T S U q

def hamiltonianCompensatedTailPrefactor (a q delta L : Real) : Real :=
  4 * Real.exp (32 * a * L) + 1 + 100 * (a / delta) ^ 2 * q

def hamiltonianCompensatedTailBase : Real := Real.exp 2 + 4

theorem stochastic_compensated_minor_error_growth
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a delta : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hData : hamiltonianPermanentPositiveData T q) :
    abs (hamiltonianCompensatedMinorError T q S U) <=
      hamiltonianCompensatedTailPrefactor a q delta
        (Real.log (2 * (Fintype.card Iota : Real))) *
      hamiltonianCompensatedTailBase ^ U.card := by
  let L := Real.log (2 * (Fintype.card Iota : Real))
  let r : Real := U.card
  let v := rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
    weightedPermutationSum T
  let b := hamiltonianCompensatedTailBase
  let H := 100 * (a / delta) ^ 2 * q
  have hN : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hN]
  have hH : 0 <= H := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hq0
  have hExp2 : 0 <= Real.exp 2 := le_of_lt (Real.exp_pos 2)
  have hb0 : 0 <= b := by dsimp only [b, hamiltonianCompensatedTailBase]; linarith only [hExp2]
  have hb4 : 4 <= b := by dsimp only [b, hamiltonianCompensatedTailBase]; linarith only [hExp2]
  have hbExp : Real.exp 2 <= b := by dsimp only [b, hamiltonianCompensatedTailBase]; linarith
  have hb1 : 1 <= b := le_trans (by norm_num) hb4
  have hPowerExp := wick_nonnegative_power_le (Real.exp 2) b hExp2 hbExp U.card
  have hPower4 := wick_nonnegative_power_le 4 b (by norm_num) hb4 U.card
  have hPower1 : 1 <= b ^ U.card := by
    simpa only [one_pow] using
      wick_nonnegative_power_le 1 b (by norm_num) hb1 U.card
  have hRatio := stochastic_complementary_permanent_ratio_upper
    T S U q a hq ha hNonneg hCol hUpper hData
  have hRatio0 : 0 <= v := hRatio.1
  have hRatioUpper : v <= 2 * Real.exp (r + 16 * a * L) := hRatio.2
  have hRatioCap0 : 0 <= 2 * Real.exp (r + 16 * a * L) :=
    mul_nonneg (by norm_num) (le_of_lt (Real.exp_pos _))
  have hSquare : v ^ 2 <= (2 * Real.exp (r + 16 * a * L)) ^ 2 := by
    nlinarith only [hRatio0, hRatioUpper, hRatioCap0]
  have hExpSquare : (2 * Real.exp (r + 16 * a * L)) ^ 2 =
      4 * Real.exp (32 * a * L) * Real.exp 2 ^ U.card := by
    calc
      _ = 4 * (Real.exp (r + 16 * a * L) * Real.exp (r + 16 * a * L)) := by ring
      _ = 4 * Real.exp ((r + 16 * a * L) + (r + 16 * a * L)) :=
        congrArg (fun z : Real => 4 * z)
          (Real.exp_add (r + 16 * a * L) (r + 16 * a * L)).symm
      _ = 4 * Real.exp (2 * (r + 16 * a * L)) := by
        congr 1
        ring
      _ = 4 * Real.exp (32 * a * L + (U.card : Real) * 2) := by
        congr 2
        dsimp only [r]
        ring
      _ = _ := by rw [Real.exp_add, hamiltonian_exp_nat_scalar]; ring
  have hCoeff0 : 0 <= 4 * Real.exp (32 * a * L) :=
    mul_nonneg (by norm_num) (le_of_lt (Real.exp_pos _))
  have hV2 : v ^ 2 <= 4 * Real.exp (32 * a * L) * b ^ U.card := by
    rw [hExpSquare] at hSquare
    exact le_trans hSquare (mul_le_mul_of_nonneg_left hPowerExp hCoeff0)
  have hAlpha := stochastic_minor_first_order_budget T S U hCard q a delta
    hq ha hDelta hDelta1 hRow hCol hNonneg hUpper hNorm
  have hAlphaBound : abs (hamiltonianMinorFirstOrder T S U q) <= H * b ^ U.card := by
    calc
      _ <= H * (1 + (U.card : Real)) ^ 2 := by nlinarith only [hAlpha]
      _ <= H * (4 : Real) ^ U.card :=
        mul_le_mul_of_nonneg_left (hamiltonian_rank_square_exponential U.card) hH
      _ <= H * b ^ U.card := mul_le_mul_of_nonneg_left hPower4 hH
  have hSub1 := norm_sub_le (v ^ 2) (1 : Real)
  have hSub2 := norm_sub_le (v ^ 2 - 1) (hamiltonianMinorFirstOrder T S U q)
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg v), abs_one] at hSub1
  simp only [Real.norm_eq_abs] at hSub2
  change abs (v ^ 2 - 1 - hamiltonianMinorFirstOrder T S U q) <= _
  change _ <= (4 * Real.exp (32 * a * L) + 1 + H) * b ^ U.card
  nlinarith only [hSub1, hSub2, hV2, hAlphaBound, hPower1]

theorem stochastic_compensated_minor_tail_tilt
    (T : Matrix Iota Iota Real) (R : Nat) (q a delta t : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1) (ht : 1 <= t)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hData : hamiltonianPermanentPositiveData T q) :
    t ^ R * abs (hamiltonianMinorTailPacket T
      (hamiltonianCompensatedMinorError T q) R) <=
      hamiltonianCompensatedTailPrefactor a q delta
        (Real.log (2 * (Fintype.card Iota : Real))) *
      (hamiltonianCompensatedTailBase * t) * a *
      (1 + hamiltonianCompensatedTailBase * t) *
      Real.exp ((hamiltonianCompensatedTailBase * t) * (a - 1)) := by
  have hN : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hN]
  have hC : 0 <= hamiltonianCompensatedTailPrefactor a q delta
      (Real.log (2 * (Fintype.card Iota : Real))) := by
    unfold hamiltonianCompensatedTailPrefactor
    positivity
  have hb : 0 <= hamiltonianCompensatedTailBase := by
    unfold hamiltonianCompensatedTailBase
    positivity
  apply stochastic_minor_tail_tilt_bound T _ R q a _ _ t hq ha hC hb ht
    hRow hCol hNonneg hUpper
  intro S U hS hSize
  exact stochastic_compensated_minor_error_growth T S U
    (Finset.mem_powersetCard.mp hS).2 q a delta hq ha hDelta hDelta1
      hRow hCol hNonneg hUpper hNorm hData

end PrimeFactorOscillations
