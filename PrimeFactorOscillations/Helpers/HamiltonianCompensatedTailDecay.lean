/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedMinorTail

/-! # Explicit scalar decay for the complete compensated minor tail

The positive logarithmic budget is quadratic in the logarithmic order.
The retained cutoff contributes a cubic times log-log negative budget.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianCompensatedTailBudget (c delta : Real) : Real :=
  32 * c + 100 * (c / delta) ^ 2 + c + 6 +
    hamiltonianCompensatedTailBase + hamiltonianCompensatedTailBase * c

theorem hamiltonian_compensated_tail_positive_budget
    (a q delta c L : Real) (ha : 1 <= a) (hq0 : 0 <= q) (hq1 : q <= 1)
    (hDelta : 0 < delta) (hc : 0 <= c) (hL : 1 <= L) (hA : a <= c * L) :
    hamiltonianCompensatedTailPrefactor a q delta L *
      (hamiltonianCompensatedTailBase * L) * a *
      (1 + hamiltonianCompensatedTailBase * L) *
      Real.exp ((hamiltonianCompensatedTailBase * L) * (a - 1)) <=
      Real.exp (hamiltonianCompensatedTailBudget c delta * L ^ 2) := by
  let b := hamiltonianCompensatedTailBase
  let D := 100 * (a / delta) ^ 2
  let X := 32 * a * L
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hL0 : 0 <= L := le_trans (by norm_num) hL
  have hb : 0 <= b := by dsimp only [b, hamiltonianCompensatedTailBase]; positivity
  have hD : 0 <= D := mul_nonneg (by norm_num) (sq_nonneg _)
  have hX : 0 <= X := mul_nonneg (mul_nonneg (by norm_num) ha0) hL0
  have hExp1 : 1 <= Real.exp X := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hX
  have hDq := mul_le_mul_of_nonneg_left hq1 hD
  have hOneD : 0 <= 1 + D := by linarith only [hD]
  have hScale := mul_le_mul_of_nonneg_right hExp1 hOneD
  have hCFirst : hamiltonianCompensatedTailPrefactor a q delta L <=
      Real.exp X * (5 + D) := by
    change 4 * Real.exp X + 1 + D * q <= _
    nlinarith only [hDq, hScale]
  have hExpBound (x : Real) (hx : 0 <= x) : x <= Real.exp x := by
    simpa using Real.pow_div_factorial_le_exp x hx 1
  have hCFive := hExpBound (5 + D) (by linarith only [hD])
  have hCSecond := mul_le_mul_of_nonneg_left hCFive (le_of_lt (Real.exp_pos X))
  have hC : hamiltonianCompensatedTailPrefactor a q delta L <=
      Real.exp (X + (5 + D)) := by
    calc
      _ <= Real.exp X * (5 + D) := hCFirst
      _ <= Real.exp X * Real.exp (5 + D) := hCSecond
      _ = _ := (Real.exp_add _ _).symm
  have hbL : 0 <= b * L := mul_nonneg hb hL0
  have hP1 := mul_le_mul hC (hExpBound (b * L) hbL) hbL
    (le_of_lt (Real.exp_pos _))
  have hP2 := mul_le_mul hP1 (hExpBound a ha0) ha0
    (mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _)))
  have hP3 := mul_le_mul hP2
    (hExpBound (1 + b * L) (by linarith only [hbL]))
    (by linarith only [hbL] : 0 <= 1 + b * L)
    (by positivity)
  have hP4 := mul_le_mul_of_nonneg_right hP3
    (le_of_lt (Real.exp_pos ((b * L) * (a - 1))))
  have hProduct :
      hamiltonianCompensatedTailPrefactor a q delta L * (b * L) * a *
        (1 + b * L) * Real.exp ((b * L) * (a - 1)) <=
      Real.exp (X + (5 + D) + b * L + a + (1 + b * L) + (b * L) * (a - 1)) := by
    calc
      _ <= ((Real.exp (X + (5 + D)) * Real.exp (b * L)) * Real.exp a) *
          Real.exp (1 + b * L) * Real.exp ((b * L) * (a - 1)) := hP4
      _ = _ := by rw [<- Real.exp_add, <- Real.exp_add, <- Real.exp_add, <- Real.exp_add]
  have hLSquare : L <= L ^ 2 := by nlinarith only [hL]
  have hL2 : 1 <= L ^ 2 := le_trans hL hLSquare
  have hAL := mul_le_mul_of_nonneg_right hA hL0
  have hLinear := mul_le_mul_of_nonneg_left hLSquare hc
  have hA2 : a <= c * L ^ 2 := le_trans hA hLinear
  have hbLinear := mul_le_mul_of_nonneg_left hLSquare hb
  have hSix := mul_le_mul_of_nonneg_left hL2 (by norm_num : (0 : Real) <= 6)
  have hBAL := mul_le_mul_of_nonneg_left hA hbL
  have hDiv : a / delta <= (c / delta) * L := by
    have h := div_le_div_of_nonneg_right hA (le_of_lt hDelta)
    convert h using 1 <;> ring
  have hDiv0 : 0 <= a / delta := div_nonneg ha0 (le_of_lt hDelta)
  have hDivPower := wick_nonnegative_power_le _ _ hDiv0 hDiv 2
  have hDBound : D <= 100 * (c / delta) ^ 2 * L ^ 2 := by
    dsimp only [D]
    nlinarith only [hDivPower]
  have hBudget :
      X + (5 + D) + b * L + a + (1 + b * L) + (b * L) * (a - 1) <=
      hamiltonianCompensatedTailBudget c delta * L ^ 2 := by
    dsimp only [X, hamiltonianCompensatedTailBudget]
    change 32 * a * L + (5 + D) + b * L + a + (1 + b * L) + (b * L) * (a - 1) <=
      (32 * c + 100 * (c / delta) ^ 2 + c + 6 + b + b * c) * L ^ 2
    nlinarith only [hAL, hA2, hbLinear, hSix, hBAL, hDBound]
  exact le_trans hProduct (Real.exp_le_exp.mpr hBudget)

theorem hamiltonian_compensated_tail_decay_scalar
    (a q delta c L z : Real) (R : Nat)
    (ha : 1 <= a) (hq0 : 0 <= q) (hq1 : q <= 1)
    (hDelta : 0 < delta) (hc : 0 <= c)
    (hL : 1 <= L) (hLog : 1 <= Real.log L) (hA : a <= c * L)
    (hLarge : 4 * hamiltonianCompensatedTailBudget c delta <= L)
    (hRank : L ^ 3 / 2 <= (R : Real))
    (hTilt : L ^ R * abs z <=
      hamiltonianCompensatedTailPrefactor a q delta L *
        (hamiltonianCompensatedTailBase * L) * a *
        (1 + hamiltonianCompensatedTailBase * L) *
        Real.exp ((hamiltonianCompensatedTailBase * L) * (a - 1))) :
    abs z <= Real.exp (-(L ^ 3 * Real.log L) / 4) := by
  have hLPos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hL0 : 0 <= L := le_of_lt hLPos
  have hLog0 : 0 <= Real.log L := le_trans (by norm_num) hLog
  have hRaw := le_trans hTilt
    (hamiltonian_compensated_tail_positive_budget a q delta c L
      ha hq0 hq1 hDelta hc hL hA)
  have hPower : L ^ R = Real.exp ((R : Real) * Real.log L) := by
    rw [hamiltonian_exp_nat_scalar, Real.exp_log hLPos]
  have hCancel : Real.exp (-((R : Real) * Real.log L)) * L ^ R = 1 := by
    rw [hPower, <- Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hRankBudget := mul_le_mul_of_nonneg_right hRank hLog0
  have hLLog : L <= L * Real.log L := by
    have h := mul_le_mul_of_nonneg_left hLog hL0
    simpa only [mul_one] using h
  have hLargeLog : 4 * hamiltonianCompensatedTailBudget c delta <= L * Real.log L :=
    le_trans hLarge hLLog
  have hLargeSquare := mul_le_mul_of_nonneg_right hLargeLog (sq_nonneg L)
  have hExponent :
      hamiltonianCompensatedTailBudget c delta * L ^ 2 - (R : Real) * Real.log L <=
        -(L ^ 3 * Real.log L) / 4 := by
    nlinarith only [hRankBudget, hLargeSquare]
  calc
    _ = Real.exp (-((R : Real) * Real.log L)) * (L ^ R * abs z) := by
      rw [<- mul_assoc, hCancel, one_mul]
    _ <= Real.exp (-((R : Real) * Real.log L)) *
        Real.exp (hamiltonianCompensatedTailBudget c delta * L ^ 2) :=
      mul_le_mul_of_nonneg_left hRaw (le_of_lt (Real.exp_pos _))
    _ = Real.exp (hamiltonianCompensatedTailBudget c delta * L ^ 2 -
        (R : Real) * Real.log L) := by
      rw [<- Real.exp_add]
      congr 1
      ring
    _ <= _ := Real.exp_le_exp.mpr hExponent


theorem hamiltonian_log_cubic_cutoff_lower (L : Real) (hL : 2 <= L) :
    L ^ 3 / 2 <= (Nat.floor (L ^ 3) : Real) := by
  have hFloor := Nat.lt_floor_add_one (L ^ 3)
  have hL0 : 0 <= L := le_trans (by norm_num) hL
  have hCube : 8 <= L ^ 3 := by
    have h := wick_nonnegative_power_le (2 : Real) L (by norm_num) hL 3
    norm_num at h
    exact h
  linarith only [hFloor, hCube]

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_compensated_minor_tail_decay
    (T : Matrix Iota Iota Real) (q a delta c : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hc : 0 <= c)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hData : hamiltonianPermanentPositiveData T q)
    (hA : a <= c * Real.log (2 * (Fintype.card Iota : Real)))
    (hL : 2 <= Real.log (2 * (Fintype.card Iota : Real)))
    (hLog : 1 <= Real.log (Real.log (2 * (Fintype.card Iota : Real))))
    (hLarge : 4 * hamiltonianCompensatedTailBudget c delta <=
      Real.log (2 * (Fintype.card Iota : Real))) :
    abs (hamiltonianMinorTailPacket T (hamiltonianCompensatedMinorError T q)
      (Nat.floor ((Real.log (2 * (Fintype.card Iota : Real))) ^ 3))) <=
      Real.exp (-((Real.log (2 * (Fintype.card Iota : Real))) ^ 3 *
        Real.log (Real.log (2 * (Fintype.card Iota : Real)))) / 4) := by
  let L := Real.log (2 * (Fintype.card Iota : Real))
  let R := Nat.floor (L ^ 3)
  have hN1 : (1 : Real) <= Fintype.card Iota := by
    exact_mod_cast Nat.succ_le_of_lt (show 0 < Fintype.card Iota from Fintype.card_pos)
  have hN : 0 < (Fintype.card Iota : Real) := lt_of_lt_of_le (by norm_num) hN1
  have hq0 : 0 <= q := by nlinarith only [hq, hN]
  have hq1 : q <= 1 := by nlinarith only [hq, hN1, hq0]
  have hL1 : 1 <= L := le_trans (by norm_num) hL
  have hTilt := stochastic_compensated_minor_tail_tilt T R q a delta L
    hq ha hDelta hDelta1 hL1 hRow hCol hNonneg hUpper hNorm hData
  exact hamiltonian_compensated_tail_decay_scalar a q delta c L _ R
    ha hq0 hq1 hDelta hc hL1 hLog hA hLarge
    (hamiltonian_log_cubic_cutoff_lower L hL) hTilt

universe u

theorem stochastic_compensated_minor_tail_logarithmic_uniform
    (delta c : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hc : 0 <= c) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          a <= c * Real.log (2 * (Fintype.card J : Real)) ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          abs (hamiltonianMinorTailPacket T (hamiltonianCompensatedMinorError T q)
            (Nat.floor ((Real.log (2 * (Fintype.card J : Real))) ^ 3))) <=
            Real.exp (-((Real.log (2 * (Fintype.card J : Real))) ^ 3 *
              Real.log (Real.log (2 * (Fintype.card J : Real)))) / 4) := by
  have hPositive := stochastic_permanent_positive_polylog_uniform.{u}
    delta 2 hDelta hDelta1 (by norm_num)
  refine hPositive.elim ?_
  intro N1 hN1
  let B := hamiltonianCompensatedTailBudget c delta
  let x0 := 2 + Real.exp 1 + 4 * abs B + 2 * c
  let N0 := max N1 (Nat.ceil (Real.exp x0))
  refine Exists.intro N0 (And.intro (le_trans hN1.1 (le_max_left _ _)) ?_)
  intro J instF instD instN hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hn1 : N1 <= Fintype.card J := le_trans (le_max_left _ _) hn
  have hnCeil : Nat.ceil (Real.exp x0) <= Fintype.card J :=
    le_trans (le_max_right _ _) hn
  have hExpN : Real.exp x0 <= (Fintype.card J : Real) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hnCeil)
  have hLogN : x0 <= Real.log (Fintype.card J : Real) := by
    have h := Real.log_le_log (Real.exp_pos x0) hExpN
    simpa only [Real.log_exp] using h
  have hN256 : (256 : Real) <= Fintype.card J := by exact_mod_cast le_trans hN1.1 hn1
  have hN : 0 < (Fintype.card J : Real) := by linarith only [hN256]
  have hLog2 : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
  have hLog2N : Real.log 2 <= Real.log (Fintype.card J : Real) :=
    Real.log_le_log (by norm_num) (by linarith only [hN256])
  have hLogMul : Real.log (2 * (Fintype.card J : Real)) =
      Real.log 2 + Real.log (Fintype.card J : Real) :=
    Real.log_mul (by norm_num) (ne_of_gt hN)
  have hExp1 : 0 < Real.exp 1 := Real.exp_pos 1
  have hAbs0 : 0 <= abs B := abs_nonneg B
  have hAbsB : B <= abs B := le_abs_self B
  have hLogN2 : 2 <= Real.log (Fintype.card J : Real) := by
    dsimp only [x0] at hLogN
    linarith only [hLogN, hc, hExp1, hAbs0]
  have hLogNC : 2 * c <= Real.log (Fintype.card J : Real) := by
    dsimp only [x0] at hLogN
    linarith only [hLogN, hExp1, hAbs0]
  have hL2 : 2 <= Real.log (2 * (Fintype.card J : Real)) := by
    linarith only [hLogMul, hLogN2, hLog2]
  have hLExp : Real.exp 1 <= Real.log (2 * (Fintype.card J : Real)) := by
    dsimp only [x0] at hLogN
    linarith only [hLogN, hLogMul, hLog2, hAbs0, hc]
  have hLogLog : 1 <= Real.log (Real.log (2 * (Fintype.card J : Real))) := by
    have h := Real.log_le_log (Real.exp_pos 1) hLExp
    simpa only [Real.log_exp] using h
  have hLarge : 4 * B <= Real.log (2 * (Fintype.card J : Real)) := by
    dsimp only [x0] at hLogN
    linarith only [hLogN, hLogMul, hLog2, hAbsB, hc, hExp1]
  have hDouble : Real.log (2 * (Fintype.card J : Real)) <=
      2 * Real.log (Fintype.card J : Real) := by
    linarith only [hLogMul, hLog2N]
  have hCap1 := mul_le_mul_of_nonneg_left hDouble hc
  have hCap2 := mul_le_mul_of_nonneg_right hLogNC
    (by linarith only [hLogN2] : 0 <= Real.log (Fintype.card J : Real))
  have hAPower : a <= Real.log (Fintype.card J : Real) ^ (2 : Nat) := by
    nlinarith only [hA, hCap1, hCap2]
  have hRealTwo : (Real.log (Fintype.card J : Real)) ^ (2 : Real) =
      (Real.log (Fintype.card J : Real)) ^ (2 : Nat) := by
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log (Fintype.card J : Real)) 2
  have hData := hN1.2 J hn1 T q a hq ha (by rw [hRealTwo]; exact hAPower)
    hRow hCol hNonneg hUpper hNorm
  exact stochastic_compensated_minor_tail_decay T q a delta c hq ha hDelta hDelta1 hc
    hRow hCol hNonneg hUpper hNorm hData hA hL2 hLogLog hLarge

end PrimeFactorOscillations
