/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.ThreeLineHorizontalConvexity

/-! # Strict residual geometry and the complete nonlinear parity cost -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def threeLineHorizontalResidualProfile (x : Real) : Real :=
  threeLineHorizontalProfile x - threeLineHorizontalVarianceCoefficient * x ^ 2

def threeLineHorizontalResidualSlope (z : Real) : Real :=
  threeLineHorizontalSlope z - 2 * threeLineHorizontalVarianceCoefficient * z

def threeLineParityCost (N M : Real) : Real :=
  threeLineCharge + (N - 1) * threeLineHorizontalResidualProfile (M / (N - 1)) -
    N * threeLineHorizontalResidualProfile (M / N)

theorem threeLineHorizontalTangentCertificate_pos (X Z : Real)
    (hX : And (0 <= X) (X <= 1)) (hZ : And (0 <= Z) (Z <= 1))
    (hPos : Or (0 < X) (0 < Z)) :
    0 < threeLineHorizontalTangentCertificate X Z := by
  have hX0 := hX.1
  have hZ0 := hZ.1
  have hX1 : 0 <= 1 - X := by linarith [hX.2]
  have hZ1 : 0 <= 1 - Z := by linarith [hZ.2]
  rcases hPos with hXP | hZP
  . by_cases hZeq : Z = 1
    . have hZP : 0 < Z := by rw [hZeq]; norm_num
      unfold threeLineHorizontalTangentCertificate
      positivity
    . have hZlt : Z < 1 := by
        by_contra h
        exact hZeq (le_antisymm hZ.2 (le_of_not_gt h))
      have hZ1P : 0 < 1 - Z := by linarith
      unfold threeLineHorizontalTangentCertificate
      positivity
  . by_cases hXeq : X = 1
    . have hXP : 0 < X := by rw [hXeq]; norm_num
      unfold threeLineHorizontalTangentCertificate
      positivity
    . have hXlt : X < 1 := by
        by_contra h
        exact hXeq (le_antisymm hX.2 (le_of_not_gt h))
      have hX1P : 0 < 1 - X := by linarith
      unfold threeLineHorizontalTangentCertificate
      positivity

theorem threeLineHorizontalRemainder_gt (x z : Real)
    (hx : And (0 <= x) (x <= 9 / 64)) (hz : And (0 <= z) (z <= 9 / 64))
    (hPos : Or (0 < x) (0 < z)) :
    threeLineHorizontalVarianceCoefficient < threeLineHorizontalRemainder x z := by
  have hX : And (0 <= 64 * x / 9) (64 * x / 9 <= 1) := by
    constructor <;> linarith [hx.1, hx.2]
  have hZ : And (0 <= 64 * z / 9) (64 * z / 9 <= 1) := by
    constructor <;> linarith [hz.1, hz.2]
  have hXZ : Or (0 < 64 * x / 9) (0 < 64 * z / 9) := by
    rcases hPos with h | h
    . exact Or.inl (by linarith)
    . exact Or.inr (by linarith)
  have hc := threeLineHorizontalTangentCertificate_pos _ _ hX hZ hXZ
  rw [<- threeLineHorizontalTangentCertificate_identity x z] at hc
  have hd := threeLineHorizontalRemainderDen_pos x z hx.2 hz.2
  have hm := threeLineHorizontalRemainder_mul_den x z hx.2 hz.2
  nlinarith

theorem threeLineHorizontalResidualProfile_zero :
    threeLineHorizontalResidualProfile 0 = threeLineCharge := by
  simp [threeLineHorizontalResidualProfile, threeLineHorizontalProfile_zero]

theorem threeLineHorizontalResidual_tangent_identity (x z : Real)
    (hx : x <= 9 / 64) (hz : z <= 9 / 64) :
    threeLineHorizontalResidualProfile x - threeLineHorizontalResidualProfile z -
      threeLineHorizontalResidualSlope z * (x - z) =
      (threeLineHorizontalRemainder x z - threeLineHorizontalVarianceCoefficient) *
        (x - z) ^ 2 := by
  have h := threeLineHorizontal_tangent_identity x z hx hz
  calc
    _ = (threeLineHorizontalProfile x - threeLineHorizontalProfile z -
        threeLineHorizontalSlope z * (x - z)) -
          threeLineHorizontalVarianceCoefficient * (x - z) ^ 2 := by
      unfold threeLineHorizontalResidualProfile threeLineHorizontalResidualSlope
      ring
    _ = _ := by rw [h]; ring

theorem threeLineHorizontalResidual_tangent_le (x z : Real)
    (hx : And (0 <= x) (x <= 9 / 64)) (hz : And (0 <= z) (z <= 9 / 64)) :
    threeLineHorizontalResidualProfile z + threeLineHorizontalResidualSlope z * (x - z) <=
      threeLineHorizontalResidualProfile x := by
  have h := threeLineHorizontalResidual_tangent_identity x z hx.2 hz.2
  have hR := threeLineHorizontalRemainder_ge x z hx hz
  have hProduct := mul_nonneg (sub_nonneg.mpr hR) (sq_nonneg (x - z))
  nlinarith

theorem threeLineHorizontalResidual_tangent_lt (x z : Real)
    (hx : And (0 <= x) (x <= 9 / 64)) (hz : And (0 <= z) (z <= 9 / 64))
    (hNe : Not (x = z)) :
    threeLineHorizontalResidualProfile z + threeLineHorizontalResidualSlope z * (x - z) <
      threeLineHorizontalResidualProfile x := by
  have hPos : Or (0 < x) (0 < z) := by
    by_cases hXP : 0 < x
    . exact Or.inl hXP
    . apply Or.inr
      by_contra hZP
      have hX0 : x = 0 := le_antisymm (le_of_not_gt hXP) hx.1
      have hZ0 : z = 0 := le_antisymm (le_of_not_gt hZP) hz.1
      exact hNe (hX0.trans hZ0.symm)
  have hR := threeLineHorizontalRemainder_gt x z hx hz hPos
  have hSq : 0 < (x - z) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hNe)
  have hProduct := mul_pos (sub_pos.mpr hR) hSq
  have h := threeLineHorizontalResidual_tangent_identity x z hx.2 hz.2
  nlinarith

theorem threeLineHorizontalResidual_centered_charge {Iota : Type*} (S : Finset Iota)
    (x : Iota -> Real) (z : Real)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 9 / 64))
    (hz : And (0 <= z) (z <= 9 / 64))
    (hCenter : Finset.sum S x = (S.card : Real) * z) :
    (S.card : Real) * threeLineHorizontalResidualProfile z <=
      Finset.sum S (fun i => threeLineHorizontalResidualProfile (x i)) := by
  classical
  have hDeviation : Finset.sum S (fun i => x i - z) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hCenter]
    ring
  have hLocal : Finset.sum S (fun i => threeLineHorizontalResidualProfile z +
      threeLineHorizontalResidualSlope z * (x i - z)) <=
      Finset.sum S (fun i => threeLineHorizontalResidualProfile (x i)) :=
    Finset.sum_le_sum (fun i hi => threeLineHorizontalResidual_tangent_le (x i) z (hx i hi) hz)
  have hSum : Finset.sum S (fun i => threeLineHorizontalResidualProfile z +
      threeLineHorizontalResidualSlope z * (x i - z)) =
        (S.card : Real) * threeLineHorizontalResidualProfile z := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      <- Finset.mul_sum, hDeviation, mul_zero, add_zero]
  rw [hSum] at hLocal
  exact hLocal

theorem threeLineHorizontalResidual_jensen_eq_iff {Iota : Type*} (S : Finset Iota)
    (x : Iota -> Real) (z : Real)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 9 / 64))
    (hz : And (0 <= z) (z <= 9 / 64))
    (hCenter : Finset.sum S x = (S.card : Real) * z) :
    Finset.sum S (fun i => threeLineHorizontalResidualProfile (x i)) =
      (S.card : Real) * threeLineHorizontalResidualProfile z <->
        (forall i, Membership.mem S i -> x i = z) := by
  classical
  constructor
  case mp =>
    intro hEq
    let gap : Iota -> Real := fun i => threeLineHorizontalResidualProfile (x i) -
      (threeLineHorizontalResidualProfile z + threeLineHorizontalResidualSlope z * (x i - z))
    have hGap (i : Iota) (hi : Membership.mem S i) : 0 <= gap i :=
      sub_nonneg.mpr (threeLineHorizontalResidual_tangent_le (x i) z (hx i hi) hz)
    have hDeviation : Finset.sum S (fun i => x i - z) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hCenter]
      ring
    have hGapSum : Finset.sum S gap = 0 := by
      dsimp only [gap]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, <- Finset.mul_sum, hDeviation, mul_zero, add_zero]
      linarith
    intro i hi
    by_contra hNe
    have hStrict : 0 < gap i :=
      sub_pos.mpr (threeLineHorizontalResidual_tangent_lt (x i) z (hx i hi) hz hNe)
    have hOne : gap i <= Finset.sum S gap := Finset.single_le_sum hGap hi
    linarith
  case mpr =>
    intro h
    calc
      _ = Finset.sum S (fun _ => threeLineHorizontalResidualProfile z) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [h i hi]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

theorem threeLineHorizontalResidual_central_removal {Iota : Type*} [DecidableEq Iota]
    (S : Finset Iota)
    (x : Iota -> Real) (a : Iota) (ha : Membership.mem S a) (hZero : x a = 0)
    (z : Real)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 9 / 64))
    (hz : And (0 <= z) (z <= 9 / 64))
    (hCenter : Finset.sum (S.erase a) x = ((S.erase a).card : Real) * z) :
    threeLineCharge + ((S.erase a).card : Real) * threeLineHorizontalResidualProfile z <=
      Finset.sum S (fun i => threeLineHorizontalResidualProfile (x i)) := by
  classical
  have hLocal := threeLineHorizontalResidual_centered_charge (S.erase a) x z
    (fun i hi => hx i (Finset.mem_of_mem_erase hi)) hz hCenter
  have hSum := Finset.sum_erase_add S (fun i => threeLineHorizontalResidualProfile (x i)) ha
  rw [hZero, threeLineHorizontalResidualProfile_zero] at hSum
  linarith

theorem threeLineHorizontalResidual_mean_shift_nonneg (q z w : Real)
    (hq : 0 <= q) (hz : And (0 <= z) (z <= 9 / 64))
    (hw : And (0 <= w) (w <= 9 / 64)) (hBalance : q * w = (q + 1) * z) :
    0 <= threeLineCharge + q * threeLineHorizontalResidualProfile w -
      (q + 1) * threeLineHorizontalResidualProfile z := by
  have hW := threeLineHorizontalResidual_tangent_le w z hw hz
  have hZero := threeLineHorizontalResidual_tangent_le 0 z (by norm_num) hz
  rw [threeLineHorizontalResidualProfile_zero] at hZero
  have hMul := _root_.mul_le_mul_of_nonneg_left hW hq
  have hCentered := congrArg (fun r : Real => threeLineHorizontalResidualSlope z * r) hBalance
  nlinarith only [hMul, hZero, hCentered]

theorem threeLineHorizontalResidual_mean_shift_pos (q z w : Real)
    (hq : 0 <= q) (hz : And (0 <= z) (z <= 9 / 64))
    (hw : And (0 <= w) (w <= 9 / 64)) (hZpos : 0 < z)
    (hBalance : q * w = (q + 1) * z) :
    0 < threeLineCharge + q * threeLineHorizontalResidualProfile w -
      (q + 1) * threeLineHorizontalResidualProfile z := by
  have hW := threeLineHorizontalResidual_tangent_le w z hw hz
  have hZero := threeLineHorizontalResidual_tangent_lt 0 z (by norm_num) hz (ne_of_lt hZpos)
  rw [threeLineHorizontalResidualProfile_zero] at hZero
  have hMul := _root_.mul_le_mul_of_nonneg_left hW hq
  have hCentered := congrArg (fun r : Real => threeLineHorizontalResidualSlope z * r) hBalance
  nlinarith only [hMul, hZero, hCentered]

theorem threeLineHorizontal_central_optimizer {Iota : Type*} [DecidableEq Iota]
    (S : Finset Iota) (x : Iota -> Real) (a : Iota)
    (ha : Membership.mem S a) (hZero : x a = 0) (z : Real)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 9 / 64))
    (hz : And (0 <= z) (z <= 9 / 64))
    (hCenter : Finset.sum (S.erase a) x = ((S.erase a).card : Real) * z) :
    And (threeLineCharge + ((S.erase a).card : Real) * threeLineHorizontalProfile z <=
      Finset.sum S (fun i => threeLineHorizontalProfile (x i)))
      (Finset.sum S (fun i => threeLineHorizontalProfile (x i)) =
        threeLineCharge + ((S.erase a).card : Real) * threeLineHorizontalProfile z <->
          forall i, Membership.mem (S.erase a) i -> x i = z) := by
  classical
  have hxR (i : Iota) (hi : Membership.mem (S.erase a) i) := hx i (Finset.mem_of_mem_erase hi)
  have hStrong := threeLineHorizontal_centered_charge (S.erase a) x z hxR hz hCenter
  have hVariance : 0 <= Finset.sum (S.erase a) (fun i => (x i - z) ^ 2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (x i - z))
  have hVarCharge := mul_nonneg (le_of_lt threeLineHorizontalVarianceCoefficient_pos) hVariance
  have hSum := Finset.sum_erase_add S (fun i => threeLineHorizontalProfile (x i)) ha
  rw [hZero, threeLineHorizontalProfile_zero] at hSum
  have hEq := threeLineHorizontal_jensen_eq_iff (S.erase a) x z hxR hz hCenter
  constructor
  case left => linarith
  case right =>
    constructor
    case mp => intro h; apply hEq.mp; linarith
    case mpr => intro h; have hh := hEq.mpr h; linarith

theorem threeLineParityCost_means (N M : Real) (hN : 1 < N) (hM : 0 <= M)
    (hMax : M <= (9 / 64 : Real) * (N - 1)) :
    And (And (0 <= M / N) (M / N <= 9 / 64))
      (And (And (0 <= M / (N - 1)) (M / (N - 1) <= 9 / 64))
        ((N - 1) * (M / (N - 1)) = ((N - 1) + 1) * (M / N))) := by
  have hNp : 0 < N := by linarith
  have hQp : 0 < N - 1 := by linarith
  have hZBalance : N * (M / N) = M := by field_simp [ne_of_gt hNp]
  have hWBalance : (N - 1) * (M / (N - 1)) = M := by field_simp [ne_of_gt hQp]
  have hz : And (0 <= M / N) (M / N <= 9 / 64) := by
    constructor
    case left => exact div_nonneg hM (le_of_lt hNp)
    case right =>
      apply (_root_.mul_le_mul_iff_of_pos_left hNp).mp
      rw [hZBalance]
      nlinarith
  have hw : And (0 <= M / (N - 1)) (M / (N - 1) <= 9 / 64) := by
    constructor
    case left => exact div_nonneg hM (le_of_lt hQp)
    case right =>
      apply (_root_.mul_le_mul_iff_of_pos_left hQp).mp
      rw [hWBalance]
      nlinarith
  have hBalance : (N - 1) * (M / (N - 1)) = ((N - 1) + 1) * (M / N) := by
    rw [hWBalance]
    simpa only [sub_add_cancel] using hZBalance.symm
  exact And.intro hz (And.intro hw hBalance)

theorem threeLineParityCost_nonneg (N M : Real) (hN : 1 < N) (hM : 0 <= M)
    (hMax : M <= (9 / 64 : Real) * (N - 1)) :
    0 <= threeLineParityCost N M := by
  have hMeans := threeLineParityCost_means N M hN hM hMax
  have h := threeLineHorizontalResidual_mean_shift_nonneg (N - 1) (M / N) (M / (N - 1))
    (by linarith) hMeans.1 hMeans.2.1 hMeans.2.2
  unfold threeLineParityCost
  simpa only [sub_add_cancel] using h

theorem threeLineParityCost_pos (N M : Real) (hN : 1 < N) (hM : 0 < M)
    (hMax : M <= (9 / 64 : Real) * (N - 1)) :
    0 < threeLineParityCost N M := by
  have hMeans := threeLineParityCost_means N M hN (le_of_lt hM) hMax
  have hZpos : 0 < M / N := div_pos hM (by linarith)
  have h := threeLineHorizontalResidual_mean_shift_pos (N - 1) (M / N) (M / (N - 1))
    (by linarith) hMeans.1 hMeans.2.1 hZpos hMeans.2.2
  unfold threeLineParityCost
  simpa only [sub_add_cancel] using h

theorem threeLineParityCost_zero (N : Real) (_hN : 1 < N) :
    threeLineParityCost N 0 = 0 := by
  unfold threeLineParityCost
  simp only [zero_div, threeLineHorizontalResidualProfile_zero]
  ring

theorem threeLineParity_odd_model_cost (k : Nat) (hk : 0 < k) (r : Real) :
    threeLineHorizontalVarianceCoefficient * (2 * (k : Real) * r ^ 4) + threeLineCharge +
      ((2 * (k : Real) + 1) - 1) * threeLineHorizontalResidualProfile
        ((2 * (k : Real) * r ^ 2) / ((2 * (k : Real) + 1) - 1)) =
      threeLineHorizontalProfile 0 + (k : Real) * threeLineHorizontalProfile (r ^ 2) +
        (k : Real) * threeLineHorizontalProfile ((-r) ^ 2) := by
  have hK : 0 < (k : Real) := by exact_mod_cast hk
  have hD : Not (2 * (k : Real) = 0) := ne_of_gt (by positivity)
  have hRatio : (2 * (k : Real) * r ^ 2) / ((2 * (k : Real) + 1) - 1) = r ^ 2 := by
    rw [show (2 * (k : Real) + 1) - 1 = 2 * (k : Real) by ring]
    field_simp [hD]
  rw [hRatio, show (-r) ^ 2 = r ^ 2 by ring, threeLineHorizontalProfile_zero]
  unfold threeLineHorizontalResidualProfile
  ring

theorem threeLineParity_even_model_cost (k : Nat) (hk : 0 < k) (r : Real) :
    threeLineHorizontalVarianceCoefficient * (2 * (k : Real) * r ^ 4) +
      (2 * (k : Real)) * threeLineHorizontalResidualProfile
        ((2 * (k : Real) * r ^ 2) / (2 * (k : Real))) =
      (k : Real) * threeLineHorizontalProfile (r ^ 2) +
        (k : Real) * threeLineHorizontalProfile ((-r) ^ 2) := by
  have hK : 0 < (k : Real) := by exact_mod_cast hk
  have hD : Not (2 * (k : Real) = 0) := ne_of_gt (by positivity)
  have hRatio : (2 * (k : Real) * r ^ 2) / (2 * (k : Real)) = r ^ 2 := by field_simp [hD]
  rw [hRatio, show (-r) ^ 2 = r ^ 2 by ring]
  unfold threeLineHorizontalResidualProfile
  ring

end PrimeFactorOscillations
