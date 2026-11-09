/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QRHPrimeSquareSampling
import PrimeFactorOscillations.Helpers.QRHPrimeSquareTail

/-! # Uniform square-divisor tail limits on actual primes

The moving-vertex tail is separated from the signed finite kernel.
The split at floor(X^(1/16)) retains both finite source error terms.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Filter
open scoped Classical
namespace PrimeFactorOscillations.QRH

private def tailSplit (X : Nat) : Nat := Nat.floor ((X : Real) ^ (1 / 16 : Real))

private theorem tailSplit_bounds (R X : Nat) (hR : 2 <= R)
    (hX : (R + 2) ^ 16 <= X) :
    R <= tailSplit X /\ 0 < tailSplit X /\
      (X : Real) ^ (1 / 16 : Real) / 2 <= (tailSplit X : Real) /\
      (tailSplit X : Real) <= (X : Real) ^ (1 / 16 : Real) /\
      tailSplit X <= X := by
  let Y : Real := (X : Real) ^ (1 / 16 : Real)
  have hRoot : ((((R + 2 : Nat) : Real) ^ 16) ^ (1 / 16 : Real)) =
      ((R + 2 : Nat) : Real) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (Nat.cast_nonneg (R + 2))]
    norm_num
  have hCast : (((R + 2 : Nat) : Real) ^ 16) <= (X : Real) := by
    exact_mod_cast hX
  have hY : ((R + 2 : Nat) : Real) <= Y := by
    rw [<- hRoot]
    exact Real.rpow_le_rpow (by positivity) hCast (by norm_num)
  have hTbig : R + 2 <= tailSplit X := Nat.le_floor hY
  have hTpos : 0 < tailSplit X := by omega
  have hY0 : 0 <= Y := Real.rpow_nonneg (Nat.cast_nonneg X) _
  have hTupper : (tailSplit X : Real) <= Y := Nat.floor_le hY0
  have hFloor : Y < (tailSplit X : Real) + 1 := Nat.lt_floor_add_one Y
  have hRcast : (2 : Real) <= R := by exact_mod_cast hR
  have hYtwo : 2 <= Y := by
    push_cast at hY
    linarith
  have hHalf : Y / 2 <= (tailSplit X : Real) := by linarith
  have hXpos : 0 < X := by
    have hNatPow : 0 < (R + 2) ^ 16 := by positivity
    omega
  have hXone : (1 : Real) <= X := by exact_mod_cast hXpos
  have hYX : Y <= (X : Real) := by
    calc
      _ <= (X : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hXone (by norm_num)
      _ = _ := Real.rpow_one _
  have hTX : tailSplit X <= X := by exact_mod_cast (hTupper.trans hYX)
  exact And.intro (by omega) (And.intro hTpos
    (And.intro hHalf (And.intro hTupper hTX)))

/-- A power-saving envelope for the separated row tail, uniform in the moving prime. -/
theorem exists_uniform_prime_square_tail_power_upper :
    exists C : Real, 0 < C /\
      forall p X R : Nat, Nat.Prime p -> p <= X -> 2 <= R ->
        (R + 2) ^ 16 <= X ->
        (primeSquareTailCount p X R : Real) <=
          ((Nat.primesBelow (X + 1)).card : Real) / (R : Real) +
          9 * C * (X : Real) ^ (15 / 16 : Real) *
            (1 + Real.log ((X : Real) + 2)) ^ 2 +
          4 * (X : Real) ^ (15 / 16 : Real) := by
  classical
  choose C hC hBound using exists_uniform_prime_square_tail_upper
  refine Exists.intro C (And.intro hC ?_)
  intro p X R hp hpX hR hXR
  let T := tailSplit X
  let Y : Real := (X : Real) ^ (1 / 16 : Real)
  let V : Real := (X : Real) ^ (15 / 16 : Real)
  let B : Real := 1 + Real.log ((X : Real) + 2)
  let L : Real := 1 + Real.log (T ^ 2 : Nat) + Real.log ((X : Real) + 2)
  have hSplit := tailSplit_bounds R X hR hXR
  have hRT : R <= T := hSplit.1
  have hTpos : 0 < T := hSplit.2.1
  have hHalf : Y / 2 <= (T : Real) := hSplit.2.2.1
  have hTY : (T : Real) <= Y := hSplit.2.2.2.1
  have hTX : T <= X := hSplit.2.2.2.2
  have hXpos : (0 : Real) < X := by exact_mod_cast lt_of_lt_of_le hTpos hTX
  have hTrpos : (0 : Real) < T := by exact_mod_cast hTpos
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hXpos _
  have hV0 : 0 <= V := Real.rpow_nonneg hXpos.le _
  have hXlog : 0 <= Real.log ((X : Real) + 2) :=
    Real.log_nonneg (by linarith)
  have hTlog : 0 <= Real.log (T : Real) :=
    Real.log_nonneg (by exact_mod_cast (show 1 <= T by omega))
  have hLogPow : Real.log (T ^ 2 : Nat) = 2 * Real.log (T : Real) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hLogLe : Real.log (T : Real) <= Real.log ((X : Real) + 2) :=
    Real.log_le_log hTrpos (by exact_mod_cast (show T <= X + 2 by omega))
  have hL0 : 0 <= L := by
    dsimp only [L]
    rw [hLogPow]
    linarith
  have hB0 : 0 <= B := by dsimp only [B]; linarith
  have hLB : L <= 3 * B := by
    dsimp only [L, B]
    rw [hLogPow]
    linarith
  have hSq : L ^ 2 <= 9 * B ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hLB)
      (add_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 3) hB0) hL0)
    nlinarith only [h]
  have hProduct : Y * (X : Real) ^ (7 / 8 : Real) = V := by
    dsimp only [Y, V]
    rw [<- Real.rpow_add hXpos]
    norm_num
  have hLow : C * (T : Real) * (X : Real) ^ (7 / 8 : Real) * L ^ 2 <=
      9 * C * V * B ^ 2 := by
    calc
      _ <= C * Y * (X : Real) ^ (7 / 8 : Real) * L ^ 2 := by
        apply mul_le_mul_of_nonneg_right
        { exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hTY hC.le) (by positivity) }
        { exact sq_nonneg L }
      _ <= C * Y * (X : Real) ^ (7 / 8 : Real) * (9 * B ^ 2) :=
        mul_le_mul_of_nonneg_left hSq (by positivity)
      _ = 9 * C * (Y * (X : Real) ^ (7 / 8 : Real)) * B ^ 2 := by ring1
      _ = _ := by rw [hProduct]
  have hPower : Y * V = (X : Real) := by
    dsimp only [Y, V]
    rw [<- Real.rpow_add hXpos]
    norm_num
  have hDiv : (X : Real) / (T : Real) <= 2 * V := by
    calc
      _ <= (X : Real) / (Y / 2) :=
        div_le_div_of_nonneg_left hXpos.le (by positivity) hHalf
      _ = _ := by
        field_simp [hYpos.ne']
        nlinarith only [hPower]
  have hHigh : 2 * ((X / T : Nat) : Real) <= 4 * V := by
    have hNat : ((X / T : Nat) : Real) <= (X : Real) / (T : Real) :=
      Nat.cast_div_le
    linarith
  have hSource := hBound p X R T hp hpX hR hRT
  change (primeSquareTailCount p X R : Real) <=
    ((Nat.primesBelow (X + 1)).card : Real) / (R : Real) + 9 * C * V * B ^ 2 + 4 * V
  change (primeSquareTailCount p X R : Real) <=
    ((Nat.primesBelow (X + 1)).card : Real) / (R : Real) +
      C * (T : Real) * (X : Real) ^ (7 / 8 : Real) * L ^ 2 +
      2 * ((X / T : Nat) : Real) at hSource
  linarith

/-- For each fixed divisor cutoff, the tail is uniformly small at every moving prime. -/
theorem eventually_prime_square_tail_count_le (R : Nat) (hR : 2 <= R)
    {eps : Real} (heps : 0 < eps) :
    Filter.Eventually (fun X : Nat => forall p : Nat,
      Nat.Prime p -> p <= X ->
      (primeSquareTailCount p X R : Real) / ((oddPrimeVertices X).card : Real) <=
        1 / (R : Real) + eps) atTop := by
  classical
  choose C hC hBound using exists_uniform_prime_square_tail_power_upper
  let n : Nat -> Real := fun X => ((oddPrimeVertices X).card : Real)
  let err : Nat -> Real := fun X =>
    9 * C * (X : Real) ^ (15 / 16 : Real) *
      (1 + Real.log ((X : Real) + 2)) ^ 2 / n X +
      4 * (X : Real) ^ (15 / 16 : Real) / n X
  have hPos (X : Nat) (hX : 3 <= X) : 0 < n X := by
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    refine Exists.intro 3 ?_
    change Membership.mem ((Nat.primesBelow (X + 1)).erase 2) 3
    apply Finset.mem_erase.mpr
    exact And.intro (by decide)
      (Nat.mem_primesBelow.mpr (And.intro (by omega) Nat.prime_three))
  have hInv : Tendsto (fun X : Nat => 1 / n X) atTop (nhds (0 : Real)) := by
    simpa only [Real.rpow_zero, zero_add, pow_zero, one_mul, n] using
      tendsto_rpow_logshift_pow_div_oddPrimeCount 0 0 (by norm_num) (by norm_num) 0
  have hTotal : Tendsto (fun X : Nat =>
      ((Nat.primesBelow (X + 1)).card : Real) / n X)
      atTop (nhds (1 : Real)) := by
    have hc : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds (1 : Real)) :=
      tendsto_const_nhds
    have h := hc.add hInv
    apply (show Tendsto (fun X : Nat => 1 + 1 / n X)
        atTop (nhds (1 : Real)) from by simpa only [add_zero] using h).congr'
    filter_upwards [eventually_ge_atTop (3 : Nat)] with X hX
    have h2 : Membership.mem (Nat.primesBelow (X + 1)) 2 :=
      Nat.mem_primesBelow.mpr (And.intro (by omega) Nat.prime_two)
    have hCard : ((Nat.primesBelow (X + 1)).card : Real) = n X + 1 := by
      dsimp only [n, oddPrimeVertices]
      have hNat := (Finset.card_erase_add_one h2).symm
      exact_mod_cast hNat
    rw [hCard]
    field_simp [(hPos X hX).ne']
  have hLow : Tendsto (fun X : Nat =>
      (X : Real) ^ (15 / 16 : Real) *
        (1 + Real.log ((X : Real) + 2)) ^ 2 / n X)
      atTop (nhds (0 : Real)) :=
    tendsto_rpow_logshift_pow_div_oddPrimeCount (15 / 16) 1
      (by norm_num) (by norm_num) 2
  have hHigh : Tendsto (fun X : Nat =>
      (X : Real) ^ (15 / 16 : Real) / n X)
      atTop (nhds (0 : Real)) := by
    simpa only [pow_zero, mul_one, n] using
      tendsto_rpow_logshift_pow_div_oddPrimeCount (15 / 16) 0
        (by norm_num) (by norm_num) 0
  have hErr : Tendsto err atTop (nhds (0 : Real)) := by
    have h := (hLow.const_mul (9 * C)).add (hHigh.const_mul 4)
    apply (show Tendsto (fun X : Nat =>
        9 * C * ((X : Real) ^ (15 / 16 : Real) *
          (1 + Real.log ((X : Real) + 2)) ^ 2 / n X) +
          4 * ((X : Real) ^ (15 / 16 : Real) / n X))
        atTop (nhds (0 : Real)) from by simpa using h).congr'
    filter_upwards [] with X
    dsimp only [err]
    ring1
  have hEnvelope : Tendsto (fun X : Nat =>
      ((Nat.primesBelow (X + 1)).card : Real) / n X / (R : Real) + err X)
      atTop (nhds (1 / (R : Real))) := by
    simpa only [add_zero] using (hTotal.div_const (R : Real)).add hErr
  have hSmall := hEnvelope.eventually
    (gt_mem_nhds (show 1 / (R : Real) < 1 / (R : Real) + eps by linarith))
  filter_upwards [eventually_ge_atTop (max 3 ((R + 2) ^ 16)), hSmall]
    with X hX hError
  intro p hp hpX
  have hn := hPos X (le_trans (le_max_left _ _) hX)
  have hPower := hBound p X R hp hpX hR (le_trans (le_max_right _ _) hX)
  have hNorm := div_le_div_of_nonneg_right hPower hn.le
  have hIdentity :
      (((Nat.primesBelow (X + 1)).card : Real) / (R : Real) +
        9 * C * (X : Real) ^ (15 / 16 : Real) *
          (1 + Real.log ((X : Real) + 2)) ^ 2 +
        4 * (X : Real) ^ (15 / 16 : Real)) / n X =
      ((Nat.primesBelow (X + 1)).card : Real) / n X / (R : Real) + err X := by
    dsimp only [err]
    ring1
  rw [hIdentity] at hNorm
  exact hNorm.trans hError.le

end PrimeFactorOscillations.QRH
