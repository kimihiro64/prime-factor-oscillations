/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianWickTailSummation

/-! # The complete moderate Wick remainder

Pair degrees four through eleven are summed with all supports, profiles,
pairings and coefficient convolutions. The lower signed correction is
excluded explicitly.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem wick_moderate_degree_factor (n e v : Nat) (kappa : Real)
    (hn : 11 <= n) (he0 : 4 <= e) (he1 : e <= 11)
    (hKappa : 0 <= kappa) (hSupport : 3 * v <= 2 * e) :
    (16 * kappa) ^ e * Real.exp (e : Real) *
        ((e : Real) / (n : Real)) ^ (e - v) <=
      121 * (1 + 16 * Real.exp 1 * kappa) ^ 11 / (n : Real) ^ 2 := by
  have hnPos : 0 < n := by omega
  have hnReal : 0 < (n : Real) := Nat.cast_pos.mpr hnPos
  have hnZero : Not ((n : Real) = 0) := ne_of_gt hnReal
  have hEN : (e : Real) <= (n : Real) := by exact_mod_cast (show e <= n by omega)
  have hE11 : (e : Real) <= 11 := by exact_mod_cast he1
  have hRatio0 : 0 <= (e : Real) / (n : Real) :=
    div_nonneg (Nat.cast_nonneg e) hnReal.le
  have hRatio1 : (e : Real) / (n : Real) <= 1 := by
    have h := div_le_div_of_nonneg_right hEN hnReal.le
    simpa only [div_self hnZero] using h
  have hExponent : 2 <= e - v := by omega
  have hPower := wick_unit_power_antitone _ hRatio0 hRatio1 2 (e - v) hExponent
  have hSquare : (e : Real) ^ 2 <= 121 := by
    nlinarith only [hE11, (Nat.cast_nonneg e : (0 : Real) <= (e : Real))]
  have hRatioSquare : ((e : Real) / (n : Real)) ^ 2 <=
      121 / (n : Real) ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right hSquare (sq_nonneg (n : Real))
  let C : Real := 16 * Real.exp 1 * kappa
  have hC : 0 <= C := by dsimp only [C]; positivity
  have hBase : 1 <= 1 + C := by linarith
  have hDegree : C ^ e <= (1 + C) ^ 11 := by
    have hRest : 1 <= (1 + C) ^ (11 - e) := by
      simpa only [one_pow] using
        wick_nonnegative_power_le 1 (1 + C) (by norm_num) hBase (11 - e)
    calc
      _ <= (1 + C) ^ e :=
        wick_nonnegative_power_le C (1 + C) hC (by linarith) e
      _ <= (1 + C) ^ e * (1 + C) ^ (11 - e) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hRest
          (pow_nonneg (by linarith : 0 <= 1 + C) e)
      _ = _ := by rw [<- pow_add, Nat.add_sub_of_le he1]
  have hFactor : (16 * kappa) ^ e * Real.exp (e : Real) = C ^ e := by
    rw [wick_exp_nat_power, <- mul_pow]
    dsimp only [C]
    congr 1
    ring
  rw [hFactor]
  calc
    _ <= (1 + C) ^ 11 * ((e : Real) / (n : Real)) ^ 2 :=
      mul_le_mul hDegree hPower (pow_nonneg hRatio0 _)
        (pow_nonneg (by linarith : 0 <= 1 + C) 11)
    _ <= (1 + C) ^ 11 * (121 / (n : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hRatioSquare
        (pow_nonneg (by linarith : 0 <= 1 + C) 11)
    _ = _ := by dsimp only [C]; ring

variable {J : Type*} [Fintype J] [DecidableEq J]

def wickSeriesModerateRemainder (G : Matrix J J (PowerSeries Complex)) :
    PowerSeries Complex :=
  Finset.sum (Finset.range 8) (fun j =>
    Finset.sum (Finset.range (j + 5)) (fun v =>
      wickSeriesDiagramCoefficient G (j + 4) v))

theorem wickSeriesModerateRemainder_mass_bound
    (G : Matrix J J (PowerSeries Complex)) (H n : Nat) (kappa : Real)
    (hCard : Fintype.card J = 2 * n) (hn : 11 <= n) (hKappa : 0 <= kappa)
    (hEntry : forall i j, finitePowerSeriesMass H (G i j) <= kappa / (n : Real)) :
    finitePowerSeriesMass H (wickSeriesModerateRemainder G) <=
      11616 * (1 + 16 * Real.exp 1 * kappa) ^ 11 / (n : Real) ^ 2 := by
  let E : Real := 121 * (1 + 16 * Real.exp 1 * kappa) ^ 11 / (n : Real) ^ 2
  have hE : 0 <= E := by dsimp only [E]; positivity
  have hOne : forall j, Membership.mem (Finset.range 8) j -> forall v,
      finitePowerSeriesMass H (wickSeriesDiagramCoefficient G (j + 4) v) <= E := by
    intro j hj v
    have hjLt : j < 8 := Finset.mem_range.mp hj
    by_cases hSupport : 3 * v <= 2 * (j + 4)
    case pos =>
      exact le_trans
        (wickSeriesDiagramCoefficient_mass_envelope G H n kappa (j + 4) v
          hCard (by omega) hKappa (by omega) (by omega) hEntry)
        (wick_moderate_degree_factor n (j + 4) v kappa hn (by omega) (by omega)
          hKappa hSupport)
    case neg =>
      rw [wickSeriesDiagramCoefficient_zero_of_support G _ _ (by omega),
        finitePowerSeriesMass_zero]
      exact hE
  unfold wickSeriesModerateRemainder
  calc
    _ <= Finset.sum (Finset.range 8) (fun j =>
        finitePowerSeriesMass H (Finset.sum (Finset.range (j + 5)) (fun v =>
          wickSeriesDiagramCoefficient G (j + 4) v))) :=
      finitePowerSeriesMass_sum _ _ _
    _ <= Finset.sum (Finset.range 8) (fun _ => 12 * E) := by
      apply Finset.sum_le_sum
      intro j hj
      have hJ : ((j + 5 : Nat) : Real) <= 12 := by
        exact_mod_cast (show j + 5 <= 12 by have := Finset.mem_range.mp hj; omega)
      calc
        _ <= Finset.sum (Finset.range (j + 5)) (fun v =>
            finitePowerSeriesMass H (wickSeriesDiagramCoefficient G (j + 4) v)) :=
          finitePowerSeriesMass_sum _ _ _
        _ <= Finset.sum (Finset.range (j + 5)) (fun _ => E) :=
          Finset.sum_le_sum (fun v _ => hOne j hj v)
        _ = ((j + 5 : Nat) : Real) * E := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ <= _ := mul_le_mul_of_nonneg_right hJ hE
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp only [E]
      norm_num
      ring

theorem stochastic_wickSeriesModerateRemainder_mass_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta b s : Real) (H : Nat)
    (hn : 11 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hb : 1 <= b) (hs : abs s <= b) (hTheta1 : b * (1 - delta / 2) < 1) :
    finitePowerSeriesMass H
        (wickSeriesModerateRemainder
          (covarianceFormalSeries (HSMul.hSMul s (bipartiteLift (centeredKernel T q))))) <=
      11616 * (1 + 32 * Real.exp 1 * b ^ 2 * a /
        (1 - b * (1 - delta / 2))) ^ 11 / (n : Real) ^ 2 := by
  have hnPos : 0 < n := by omega
  let : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 hnPos)
  let kappa : Real := 2 * b ^ 2 * a / (1 - b * (1 - delta / 2))
  have hGap : 0 < 1 - b * (1 - delta / 2) := sub_pos.mpr hTheta1
  have hKappa : 0 <= kappa := by
    dsimp only [kappa]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg b))
        (by linarith only [ha])) hGap.le
  have hn0 : Not ((n : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hnPos)
  have hqEq : q = 1 / (n : Real) := by
    apply (eq_div_iff hn0).mpr
    simpa only [mul_comm] using hq
  have hCard : Fintype.card (Sum (Fin n) (Fin n)) = 2 * n := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
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
      _ = _ := by rw [hqEq]; dsimp only [kappa]; ring
  have hFactor : 16 * Real.exp 1 * kappa =
      32 * Real.exp 1 * b ^ 2 * a / (1 - b * (1 - delta / 2)) := by
    dsimp only [kappa]
    ring
  rw [<- hFactor]
  exact wickSeriesModerateRemainder_mass_bound _ H n kappa hCard hn hKappa hEntry

end PrimeFactorOscillations
