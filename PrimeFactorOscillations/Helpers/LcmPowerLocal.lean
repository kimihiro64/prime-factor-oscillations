/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform lower bounds for the LCM-power local correction

The main local loss has coefficient k, uniformly for 1 <= k <= 2.
The remaining losses are explicit. This estimate will be consumed with the
actual prime-exponent product, its height, and its positive zeta tail.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations

def lcmPowerCorrection (k u v t : Real) : Real :=
  ((1 - u) ^ k - v * (1 - t) ^ k) / (1 - v)

theorem lcmPowerCorrection_log_lower
    (k u v t : Real) (hk : 1 <= k) (hkTwo : k <= 2)
    (hu : 0 <= u) (huSmall : u <= 1 / 8)
    (hv : 0 <= v) (hvHalf : v <= 1 / 2)
    (ht : 0 <= t) (htOne : t <= 1) :
    0 < lcmPowerCorrection k u v t /\
      -k * u - 4 * u * v - 32 * u ^ 2 <= Real.log (lcmPowerCorrection k u v t) := by
  have hDen : 0 < 1 - v := by linarith
  let z : Real := k * u / (1 - v)
  have hz : 0 <= z := by dsimp [z]; positivity
  have hZmul : z * (1 - v) = k * u := by dsimp [z]; field_simp
  have hZFour : z <= 4 * u := by
    have hNum : k * u <= 4 * u * (1 - v) := by
      nlinarith [mul_nonneg hu (show 0 <= 2 - k by linarith),
        mul_nonneg hu (show 0 <= 1 / 2 - v by linarith)]
    have hDiv := div_le_div_of_nonneg_right hNum hDen.le
    have hCancel : (4 * u * (1 - v)) / (1 - v) = 4 * u := by field_simp
    exact hDiv.trans_eq hCancel
  have hZHalf : z <= 1 / 2 := by linarith
  have hOneZ : 0 < 1 - z := by linarith
  have hZSharp : z <= k * u + 4 * u * v := by
    have hSlack := mul_nonneg (mul_nonneg hu hv)
      (show 0 <= 4 - k - 4 * v by linarith)
    have hNum : k * u <= (k * u + 4 * u * v) * (1 - v) := by
      nlinarith only [hSlack]
    have hDiv := div_le_div_of_nonneg_right hNum hDen.le
    have hCancel : ((k * u + 4 * u * v) * (1 - v)) / (1 - v) =
        k * u + 4 * u * v := by field_simp
    exact hDiv.trans_eq hCancel
  have hBernoulli : 1 - k * u <= (1 - u) ^ k := by
    have hs : -1 <= -u := by linarith
    have hB := one_add_mul_self_le_rpow_one_add hs hk
    simpa only [sub_eq_add_neg, mul_neg] using hB
  have hOther : (1 - t) ^ k <= 1 :=
    Real.rpow_le_one (by linarith) (by linarith) (by linarith)
  have hCorrection : 1 - z <= lcmPowerCorrection k u v t := by
    have hV := mul_le_mul_of_nonneg_left hOther hv
    have hNum : (1 - z) * (1 - v) <= (1 - u) ^ k - v * (1 - t) ^ k := by
      nlinarith only [hBernoulli, hV, hZmul]
    have hDiv := div_le_div_of_nonneg_right hNum hDen.le
    have hCancel : ((1 - z) * (1 - v)) / (1 - v) = 1 - z := by field_simp
    rw [hCancel] at hDiv
    exact hDiv
  have hPos : 0 < lcmPowerCorrection k u v t := hOneZ.trans_le hCorrection
  have hLog : -z - 2 * z ^ 2 <= Real.log (1 - z) := by
    have hInv : (1 - z) * Inv.inv (1 - z) = 1 := by field_simp
    have hSlack := mul_nonneg (sq_nonneg z) (show 0 <= 1 - 2 * z by linarith)
    have hLower : -z - 2 * z ^ 2 <= 1 - Inv.inv (1 - z) := by
      apply (mul_le_mul_iff_of_pos_right hOneZ).mp
      nlinarith only [hInv, hSlack]
    exact hLower.trans (Real.one_sub_inv_le_log_of_pos hOneZ)
  have hSquare : z ^ 2 <= 16 * u ^ 2 := by
    have h := mul_le_mul hZFour hZFour hz (show 0 <= 4 * u by positivity)
    nlinarith only [h]
  refine And.intro hPos ?_
  calc
    _ <= -z - 2 * z ^ 2 := by nlinarith only [hZSharp, hSquare]
    _ <= Real.log (1 - z) := hLog
    _ <= _ := Real.log_le_log hOneZ hCorrection

def lcmPowerLocalFactor (p : Real) (a : Nat) (k : Real) : Real :=
  lcmPowerCorrection k (p ^ (-((a : Real) + 1))) (p ^ (-k)) (p ^ (-(a : Real)))

theorem lcmPowerLocalFactor_log_lower
    (p : Real) (hp : 2 <= p) (a : Nat) (k : Real)
    (hk : 1 <= k) (hkTwo : k <= 2)
    (hSmall : p ^ (-((a : Real) + 1)) <= 1 / 8) :
    0 < lcmPowerLocalFactor p a k /\
      -k * p ^ (-((a : Real) + 1)) -
        4 * p ^ (-((a : Real) + 1)) * p ^ (-k) -
        32 * (p ^ (-((a : Real) + 1))) ^ 2 <= Real.log (lcmPowerLocalFactor p a k) := by
  have hpOne : 1 <= p := by linarith
  have hpPos : 0 < p := by linarith
  have hV : p ^ (-k) <= 1 / 2 := by
    calc
      _ <= p ^ (-1 : Real) := Real.rpow_le_rpow_of_exponent_le hpOne (by linarith)
      _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
      _ <= _ := one_div_le_one_div_of_le (by norm_num) hp
  have hT : p ^ (-(a : Real)) <= 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hpOne
      (show -(a : Real) <= 0 from neg_nonpos.mpr (Nat.cast_nonneg a))
  exact lcmPowerCorrection_log_lower k _ _ _ hk hkTwo
    (Real.rpow_nonneg hpPos.le _) hSmall (Real.rpow_nonneg hpPos.le _) hV
    (Real.rpow_nonneg hpPos.le _) hT

/-- The exact finite product has a k-independent remainder on the whole
interval 1 <= k <= 2; every prime-exponent factor is retained. -/
theorem lcmPowerLocal_product_log_lower
    {I : Type*} (S : Finset I) (p : I -> Real) (a : I -> Nat) (k : Real)
    (hk : 1 <= k) (hkTwo : k <= 2)
    (hp : forall i, Membership.mem S i -> 2 <= p i)
    (hSmall : forall i, Membership.mem S i ->
      (p i) ^ (-((a i : Real) + 1)) <= 1 / 8) :
    -k * S.sum (fun i => (p i) ^ (-((a i : Real) + 1))) -
      4 * S.sum (fun i => (p i) ^ (-((a i : Real) + 1)) / p i) -
      32 * S.sum (fun i => ((p i) ^ (-((a i : Real) + 1))) ^ 2) <=
        Real.log (S.prod (fun i => lcmPowerLocalFactor (p i) (a i) k)) := by
  have hLocal (i : I) (hi : Membership.mem S i) :=
    lcmPowerLocalFactor_log_lower (p i) (hp i hi) (a i) k hk hkTwo (hSmall i hi)
  rw [Real.log_prod (fun i hi => (hLocal i hi).1.ne')]
  have hSum := Finset.sum_le_sum (s := S) (fun i hi => by
    have hV : (p i) ^ (-k) <= 1 / p i := by
      have h := Real.rpow_le_rpow_of_exponent_le
        (show 1 <= p i by linarith [hp i hi]) (show -k <= (-1 : Real) by linarith)
      simpa only [Real.rpow_neg_one, one_div] using h
    have hu : 0 <= (p i) ^ (-((a i : Real) + 1)) :=
      Real.rpow_nonneg (by linarith [hp i hi]) _
    have hLoss := mul_le_mul_of_nonneg_left hV
      (show 0 <= 4 * (p i) ^ (-((a i : Real) + 1)) by positivity)
    have hPoint :
        -k * (p i) ^ (-((a i : Real) + 1)) -
          4 * ((p i) ^ (-((a i : Real) + 1)) / p i) -
          32 * ((p i) ^ (-((a i : Real) + 1))) ^ 2 <=
            Real.log (lcmPowerLocalFactor (p i) (a i) k) := by
      have hBound := (hLocal i hi).2
      simp only [div_eq_mul_inv, one_mul] at hLoss
      simp only [div_eq_mul_inv]
      nlinarith only [hBound, hLoss]
    exact hPoint)
  simpa only [Finset.sum_sub_distrib, <- Finset.mul_sum] using hSum

end PrimeFactorOscillations
