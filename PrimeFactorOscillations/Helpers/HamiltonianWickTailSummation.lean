/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianWickSeriesCoefficients

/-! # Complete finite high-diagram coefficient summation

All supports, degree profiles, pairings and deformation coefficients through
the same cutoff are summed. The signed low-degree correction is excluded
explicitly. No infinite Wick expansion at parameter one is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem wick_nonnegative_power_le (a b : Real) (ha : 0 <= a) (hab : a <= b)
    (k : Nat) : a ^ k <= b ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (pow_nonneg (le_trans ha hab) k)

theorem wick_unit_power_le_one (u : Real) (hu0 : 0 <= u) (hu1 : u <= 1)
    (k : Nat) : u ^ k <= 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul ih hu1 hu0 (by norm_num : (0 : Real) <= 1)

theorem wick_unit_power_antitone (u : Real) (hu0 : 0 <= u) (hu1 : u <= 1)
    (p q : Nat) (hPQ : p <= q) : u ^ q <= u ^ p := by
  have h := mul_le_mul_of_nonneg_left (wick_unit_power_le_one u hu0 hu1 (q - p))
    (pow_nonneg hu0 p)
  rw [<- pow_add, Nat.add_sub_of_le hPQ, mul_one] at h
  exact h

theorem wick_exp_nat_power (e : Nat) : Real.exp (e : Real) = Real.exp 1 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Nat.cast_add, Nat.cast_one, Real.exp_add, ih, pow_succ]

theorem wick_degree_factor_geometric (n : Nat) (kappa u : Real) (e v : Nat)
    (hKappa : 0 <= kappa) (hu0 : 0 <= u) (hu1 : u <= 1)
    (hSupport : 3 * v <= 2 * e)
    (hCutoff : (e : Real) / (n : Real) <= u ^ 3) :
    (16 * kappa) ^ e * Real.exp (e : Real) *
        ((e : Real) / (n : Real)) ^ (e - v) <=
      (16 * Real.exp 1 * kappa * u) ^ e := by
  have hVE : v <= e := by omega
  have hExponent : e <= 3 * (e - v) := by omega
  have hPower : ((e : Real) / (n : Real)) ^ (e - v) <= u ^ e := by
    calc
      _ <= (u ^ 3) ^ (e - v) :=
        wick_nonnegative_power_le _ _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          hCutoff _
      _ = u ^ (3 * (e - v)) := (pow_mul _ _ _).symm
      _ <= _ := wick_unit_power_antitone u hu0 hu1 _ _ hExponent
  calc
    _ <= (16 * kappa) ^ e * Real.exp (e : Real) * u ^ e :=
      mul_le_mul_of_nonneg_left hPower
        (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hKappa) e) (Real.exp_pos _).le)
    _ = _ := by
      rw [wick_exp_nat_power, <- mul_pow, <- mul_pow]
      congr 1
      ring

theorem wick_half_weighted_sum (L : Nat) :
    Finset.sum (Finset.range L) (fun j =>
        ((j : Real) + 13) * (1 / 2 : Real) ^ j) =
      28 - 2 * ((L : Real) + 14) * (1 / 2 : Real) ^ L := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

theorem wick_high_geometric_sum (q : Real) (hq0 : 0 <= q) (hq1 : q <= 1 / 2)
    (L : Nat) :
    Finset.sum (Finset.range L) (fun j =>
        ((j : Real) + 13) * q ^ (j + 12)) <= 28 * q ^ 12 := by
  have hWeighted : Finset.sum (Finset.range L) (fun j =>
      ((j : Real) + 13) * q ^ j) <= 28 := by
    calc
      _ <= Finset.sum (Finset.range L) (fun j =>
          ((j : Real) + 13) * (1 / 2 : Real) ^ j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (wick_nonnegative_power_le q _ hq0 hq1 j)
          (by positivity)
      _ <= 28 := by
        rw [wick_half_weighted_sum]
        have hTerm : 0 <= 2 * ((L : Real) + 14) * (1 / 2 : Real) ^ L := by positivity
        linarith
  calc
    _ = Finset.sum (Finset.range L) (fun j => ((j : Real) + 13) * q ^ j) * q ^ 12 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_add]
      ring
    _ <= _ := mul_le_mul_of_nonneg_right hWeighted (pow_nonneg hq0 12)

variable {J : Type*} [Fintype J] [DecidableEq J]

def wickSeriesHighRemainder (G : Matrix J J (PowerSeries Complex)) (L : Nat) :
    PowerSeries Complex :=
  Finset.sum (Finset.range L) (fun j =>
    Finset.sum (Finset.range (j + 13)) (fun v =>
      wickSeriesDiagramCoefficient G (j + 12) v))

theorem wickSeriesHighRemainder_mass_bound
    (G : Matrix J J (PowerSeries Complex)) (H n L : Nat) (kappa u : Real)
    (hCard : Fintype.card J = 2 * n) (hn : 0 < n) (hKappa : 0 <= kappa)
    (hu0 : 0 <= u) (hu1 : u <= 1)
    (hSmall : 16 * Real.exp 1 * kappa * u <= 1 / 2)
    (hEntry : forall i j, finitePowerSeriesMass H (G i j) <= kappa / (n : Real))
    (hCutoff : forall j, Membership.mem (Finset.range L) j ->
      ((j + 12 : Nat) : Real) / (n : Real) <= u ^ 3) :
    finitePowerSeriesMass H (wickSeriesHighRemainder G L) <=
      28 * (16 * Real.exp 1 * kappa * u) ^ 12 := by
  let q : Real := 16 * Real.exp 1 * kappa * u
  have hq0 : 0 <= q := by
    dsimp only [q]
    positivity
  have hOne : forall j, Membership.mem (Finset.range L) j ->
      forall v, finitePowerSeriesMass H (wickSeriesDiagramCoefficient G (j + 12) v) <=
        q ^ (j + 12) := by
    intro j hj v
    by_cases hSupport : 3 * v <= 2 * (j + 12)
    case pos =>
      have hVE : v <= j + 12 := by omega
      exact le_trans
        (wickSeriesDiagramCoefficient_mass_envelope G H n kappa (j + 12) v
          hCard hn hKappa (by omega) hVE hEntry)
        (wick_degree_factor_geometric n kappa u (j + 12) v
          hKappa hu0 hu1 hSupport (hCutoff j hj))
    case neg =>
      rw [wickSeriesDiagramCoefficient_zero_of_support G _ _ (by omega),
        finitePowerSeriesMass_zero]
      exact pow_nonneg hq0 _
  unfold wickSeriesHighRemainder
  calc
    _ <= Finset.sum (Finset.range L) (fun j =>
        finitePowerSeriesMass H (Finset.sum (Finset.range (j + 13)) (fun v =>
          wickSeriesDiagramCoefficient G (j + 12) v))) :=
      finitePowerSeriesMass_sum H _ _
    _ <= Finset.sum (Finset.range L) (fun j => ((j : Real) + 13) * q ^ (j + 12)) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ <= Finset.sum (Finset.range (j + 13)) (fun v =>
            finitePowerSeriesMass H (wickSeriesDiagramCoefficient G (j + 12) v)) :=
          finitePowerSeriesMass_sum H _ _
        _ <= Finset.sum (Finset.range (j + 13)) (fun _ => q ^ (j + 12)) :=
          Finset.sum_le_sum (fun v _ => hOne j hj v)
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; rfl
    _ <= _ := wick_high_geometric_sum q hq0 hSmall L

theorem stochastic_wickSeriesHighRemainder_mass_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta b s u : Real) (H L : Nat)
    (hn : 0 < n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hb : 1 <= b) (hs : abs s <= b) (hTheta1 : b * (1 - delta / 2) < 1)
    (hu0 : 0 <= u) (hu1 : u <= 1)
    (hSmall : 32 * Real.exp 1 * b ^ 2 * a * u / (1 - b * (1 - delta / 2)) <= 1 / 2)
    (hCutoff : forall j, Membership.mem (Finset.range L) j ->
      ((j + 12 : Nat) : Real) / (n : Real) <= u ^ 3) :
    finitePowerSeriesMass H
        (wickSeriesHighRemainder
          (covarianceFormalSeries (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))) L) <=
      28 * (32 * Real.exp 1 * b ^ 2 * a * u / (1 - b * (1 - delta / 2))) ^ 12 := by
  letI : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 hn)
  let kappa : Real := 2 * b ^ 2 * a / (1 - b * (1 - delta / 2))
  have hGap : 0 < 1 - b * (1 - delta / 2) := sub_pos.mpr hTheta1
  have hKappa : 0 <= kappa := by
    dsimp only [kappa]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg b)) (by linarith only [ha])) hGap.le
  have hn0 : Not ((n : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hn)
  have hqEq : q = 1 / (n : Real) := by
    apply (eq_div_iff hn0).mpr
    simpa only [mul_comm] using hq
  have hCard : Fintype.card (Sum (Fin n) (Fin n)) = 2 * n := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hFactor : 16 * Real.exp 1 * kappa * u =
      32 * Real.exp 1 * b ^ 2 * a * u / (1 - b * (1 - delta / 2)) := by
    dsimp only [kappa]
    ring
  have hSmallK : 16 * Real.exp 1 * kappa * u <= 1 / 2 := by
    rw [hFactor]
    exact hSmall
  have hEntry : forall i j,
      finitePowerSeriesMass H
        (covarianceFormalSeries (HSMul.hSMul s (bipartiteLift (centeredKernel T q))) i j) <=
        kappa / (n : Real) := by
    intro i j
    have h := stochastic_covarianceFormalSeries_mass_bound T q a delta b s H
      (by simpa only [Fintype.card_fin] using hq) ha hRow hCol hNonneg hUpper
      hDelta0 hDelta1 hNorm hb hs hTheta1 i j
    calc
      _ <= _ := h
      _ = kappa / (n : Real) := by
        rw [hqEq]
        dsimp only [kappa]
        ring
  rw [<- hFactor]
  exact wickSeriesHighRemainder_mass_bound _ H n L kappa u
    hCard hn hKappa hu0 hu1 hSmallK hEntry hCutoff


theorem wick_high_power_budget (n H : Nat) (C u V : Real)
    (hn : 0 < n) (hCube : u ^ 3 = (H : Real) / (n : Real))
    (hLength : (H : Real) ^ 2 <= V * (n : Real)) :
    28 * (C * u) ^ 12 <= 28 * C ^ 12 * V ^ 2 / (n : Real) ^ 2 := by
  have hn0 : Not ((n : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hn)
  have hVn : 0 <= V * (n : Real) := le_trans (sq_nonneg (H : Real)) hLength
  have hSquare := mul_le_mul hLength hLength (sq_nonneg (H : Real)) hVn
  have hFourth : (H : Real) ^ 4 <= V ^ 2 * (n : Real) ^ 2 := by
    nlinarith only [hSquare]
  have hRatio : ((H : Real) / (n : Real)) ^ 4 <= V ^ 2 / (n : Real) ^ 2 := by
    calc
      _ = (H : Real) ^ 4 / (n : Real) ^ 4 := div_pow _ _ _
      _ <= (V ^ 2 * (n : Real) ^ 2) / (n : Real) ^ 4 :=
        div_le_div_of_nonneg_right hFourth (pow_nonneg (Nat.cast_nonneg n) 4)
      _ = _ := by field_simp
  have hTwelfth : u ^ 12 = ((H : Real) / (n : Real)) ^ 4 := by
    calc
      _ = (u ^ 3) ^ 4 := by ring
      _ = _ := by rw [hCube]
  rw [mul_pow, hTwelfth]
  calc
    _ <= 28 * C ^ 12 * (V ^ 2 / (n : Real) ^ 2) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hRatio
        (mul_nonneg (by norm_num) (by nlinarith [sq_nonneg (C ^ 6)] : 0 <= C ^ 12))
    _ = _ := by ring

theorem wickSeriesHighRemainder_two_power_bound
    (G : Matrix J J (PowerSeries Complex)) (H n L : Nat) (kappa u V : Real)
    (hCard : Fintype.card J = 2 * n) (hn : 0 < n) (hKappa : 0 <= kappa)
    (hu0 : 0 <= u) (hu1 : u <= 1)
    (hSmall : 16 * Real.exp 1 * kappa * u <= 1 / 2)
    (hEntry : forall i j, finitePowerSeriesMass H (G i j) <= kappa / (n : Real))
    (hCutoff : forall j, Membership.mem (Finset.range L) j -> j + 12 <= H)
    (hCube : u ^ 3 = (H : Real) / (n : Real))
    (hLength : (H : Real) ^ 2 <= V * (n : Real)) :
    finitePowerSeriesMass H (wickSeriesHighRemainder G L) <=
      28 * (16 * Real.exp 1 * kappa) ^ 12 * V ^ 2 / (n : Real) ^ 2 := by
  have hRatio : forall j, Membership.mem (Finset.range L) j ->
      ((j + 12 : Nat) : Real) / (n : Real) <= u ^ 3 := by
    intro j hj
    rw [hCube]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hCutoff j hj) (Nat.cast_nonneg n)
  exact le_trans
    (wickSeriesHighRemainder_mass_bound G H n L kappa u
      hCard hn hKappa hu0 hu1 hSmall hEntry hRatio)
    (wick_high_power_budget n H (16 * Real.exp 1 * kappa) u V hn hCube hLength)

theorem stochastic_wickSeriesHighRemainder_two_power_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta b s u V : Real) (H L : Nat)
    (hn : 0 < n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hb : 1 <= b) (hs : abs s <= b) (hTheta1 : b * (1 - delta / 2) < 1)
    (hu0 : 0 <= u) (hu1 : u <= 1)
    (hSmall : 32 * Real.exp 1 * b ^ 2 * a * u / (1 - b * (1 - delta / 2)) <= 1 / 2)
    (hCutoff : forall j, Membership.mem (Finset.range L) j -> j + 12 <= H)
    (hCube : u ^ 3 = (H : Real) / (n : Real))
    (hLength : (H : Real) ^ 2 <= V * (n : Real)) :
    finitePowerSeriesMass H
        (wickSeriesHighRemainder
          (covarianceFormalSeries (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))) L) <=
      28 * (32 * Real.exp 1 * b ^ 2 * a / (1 - b * (1 - delta / 2))) ^ 12 *
        V ^ 2 / (n : Real) ^ 2 := by
  let C : Real := 32 * Real.exp 1 * b ^ 2 * a / (1 - b * (1 - delta / 2))
  have hRatio : forall j, Membership.mem (Finset.range L) j ->
      ((j + 12 : Nat) : Real) / (n : Real) <= u ^ 3 := by
    intro j hj
    rw [hCube]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hCutoff j hj) (Nat.cast_nonneg n)
  have hHigh := stochastic_wickSeriesHighRemainder_mass_bound T q a delta b s u H L
    hn hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hb hs hTheta1
    hu0 hu1 hSmall hRatio
  have hFactor : 32 * Real.exp 1 * b ^ 2 * a * u / (1 - b * (1 - delta / 2)) =
      C * u := by dsimp only [C]; ring
  rw [hFactor] at hHigh
  exact le_trans hHigh (wick_high_power_budget n H C u V hn hCube hLength)

end PrimeFactorOscillations
