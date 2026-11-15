/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedCauchyTail
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceTaylorSeries
import PrimeFactorOscillations.Helpers.HamiltonianWickModerateRemainder

/-! # Uniform assembly of the actual compensated permanent remainder

The complete low-degree signed Wick sum is retained. Only the explicit
moderate/high remainder and the Cauchy truncation tail are estimated.
The actual coefficient identification is consumed before any bound.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonianCauchyCoefficient_eq_taylor
    (f : Complex -> Complex) (R : NNReal)
    (hSeries : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 R)
    (k : Nat) :
    hamiltonianCauchyCoefficient f R k =
      PowerSeries.coeff k (wickTaylorSeries f) := by
  have h := hSeries.factorial_smul (1 : Complex) k
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] at h
  simp only [nsmul_eq_mul] at h
  change (k.factorial : Complex) * hamiltonianCauchyCoefficient f R k =
    iteratedDeriv k f 0 at h
  have hFac : Not ((k.factorial : Complex) = 0) := by
    exact_mod_cast Nat.factorial_ne_zero k
  rw [wickTaylorSeries_coeff, <- h]
  field_simp

def hamiltonianFiniteSeriesValue (H : Nat) (f : PowerSeries Complex) : Complex :=
  Finset.sum (Finset.range (H + 1)) (fun k => PowerSeries.coeff k f)

theorem hamiltonianFiniteSeriesValue_add (H : Nat) (f g : PowerSeries Complex) :
    hamiltonianFiniteSeriesValue H (f + g) =
      hamiltonianFiniteSeriesValue H f + hamiltonianFiniteSeriesValue H g := by
  simp only [hamiltonianFiniteSeriesValue, map_add, Finset.sum_add_distrib]

theorem hamiltonianFiniteSeriesValue_norm_bound (H : Nat) (f : PowerSeries Complex) :
    norm (hamiltonianFiniteSeriesValue H f) <= finitePowerSeriesMass H f := by
  exact norm_sum_le _ _

variable {J : Type*} [Fintype J] [DecidableEq J]

def wickSeriesTruncatedDiagrams (G : Matrix J J (PowerSeries Complex)) (H : Nat) :
    PowerSeries Complex :=
  Finset.sum (Finset.range (H + 1)) (fun e =>
    Finset.sum (Finset.range (e + 1)) (fun v => wickSeriesDiagramCoefficient G e v))

def wickSeriesLowDiagrams (G : Matrix J J (PowerSeries Complex)) : PowerSeries Complex :=
  Finset.sum (Finset.range 4) (fun e =>
    Finset.sum (Finset.range (e + 1)) (fun v => wickSeriesDiagramCoefficient G e v))

omit [DecidableEq J] in
theorem wickSeriesTruncatedDiagrams_partition
    (G : Matrix J J (PowerSeries Complex)) (H : Nat) (hH : 11 <= H) :
    wickSeriesTruncatedDiagrams G H =
      wickSeriesLowDiagrams G + wickSeriesModerateRemainder G +
        wickSeriesHighRemainder G (H - 11) := by
  let f := fun e => Finset.sum (Finset.range (e + 1))
    (fun v => wickSeriesDiagramCoefficient G e v)
  change Finset.sum (Finset.range (H + 1)) f =
    Finset.sum (Finset.range 4) f +
      Finset.sum (Finset.range 8) (fun j => f (j + 4)) +
        Finset.sum (Finset.range (H - 11)) (fun j => f (j + 12))
  have hSplit : H + 1 = 12 + (H - 11) := by omega
  rw [hSplit, Finset.sum_range_add]
  have hFirst : Finset.sum (Finset.range 12) f =
      Finset.sum (Finset.range 4) f +
        Finset.sum (Finset.range 8) (fun j => f (j + 4)) := by
    rw [show 12 = 4 + 8 by decide, Finset.sum_range_add]
    apply congrArg (fun z : PowerSeries Complex => Finset.sum (Finset.range 4) f + z)
    exact Finset.sum_congr rfl (fun j hj => congrArg f (Nat.add_comm 4 j))
  rw [hFirst]
  apply congrArg (fun z : PowerSeries Complex =>
    (Finset.sum (Finset.range 4) f +
      Finset.sum (Finset.range 8) (fun j => f (j + 4))) + z)
  exact Finset.sum_congr rfl (fun j hj => congrArg f (Nat.add_comm 12 j))

theorem wickSeriesTruncatedDiagrams_remainder_bound
    (G : Matrix J J (PowerSeries Complex)) (H n : Nat) (kappa u V : Real)
    (hCard : Fintype.card J = 2 * n) (hn : 11 <= n) (hH : 11 <= H)
    (hKappa : 0 <= kappa) (hu0 : 0 <= u) (hu1 : u <= 1)
    (hSmall : 16 * Real.exp 1 * kappa * u <= 1 / 2)
    (hEntry : forall i j, finitePowerSeriesMass H (G i j) <= kappa / (n : Real))
    (hCube : u ^ 3 = (H : Real) / (n : Real))
    (hLength : (H : Real) ^ 2 <= V * (n : Real)) :
    norm (hamiltonianFiniteSeriesValue H (wickSeriesTruncatedDiagrams G H) -
      hamiltonianFiniteSeriesValue H (wickSeriesLowDiagrams G)) <=
      (11616 * (1 + 16 * Real.exp 1 * kappa) ^ 11 +
        28 * (16 * Real.exp 1 * kappa) ^ 12 * V ^ 2) / (n : Real) ^ 2 := by
  have hnPos : 0 < n := by omega
  have hModerate := wickSeriesModerateRemainder_mass_bound G H n kappa
    hCard hn hKappa hEntry
  have hCutoff : forall j, Membership.mem (Finset.range (H - 11)) j -> j + 12 <= H := by
    intro j hj
    have hjLt := Finset.mem_range.mp hj
    omega
  have hHigh := wickSeriesHighRemainder_two_power_bound G H n (H - 11) kappa u V
    hCard hnPos hKappa hu0 hu1 hSmall hEntry hCutoff hCube hLength
  rw [wickSeriesTruncatedDiagrams_partition G H hH,
    hamiltonianFiniteSeriesValue_add, hamiltonianFiniteSeriesValue_add]
  have hCancel : hamiltonianFiniteSeriesValue H (wickSeriesLowDiagrams G) +
      hamiltonianFiniteSeriesValue H (wickSeriesModerateRemainder G) +
      hamiltonianFiniteSeriesValue H (wickSeriesHighRemainder G (H - 11)) -
      hamiltonianFiniteSeriesValue H (wickSeriesLowDiagrams G) =
    hamiltonianFiniteSeriesValue H (wickSeriesModerateRemainder G) +
      hamiltonianFiniteSeriesValue H (wickSeriesHighRemainder G (H - 11)) := by ring
  rw [hCancel]
  calc
    _ <= norm (hamiltonianFiniteSeriesValue H (wickSeriesModerateRemainder G)) +
      norm (hamiltonianFiniteSeriesValue H (wickSeriesHighRemainder G (H - 11))) :=
        norm_add_le _ _
    _ <= finitePowerSeriesMass H (wickSeriesModerateRemainder G) +
      finitePowerSeriesMass H (wickSeriesHighRemainder G (H - 11)) :=
        add_le_add (hamiltonianFiniteSeriesValue_norm_bound _ _)
          (hamiltonianFiniteSeriesValue_norm_bound _ _)
    _ <= _ := by
      have h := add_le_add hModerate hHigh
      simpa only [add_div] using h


theorem stochastic_compensated_finiteSeriesValue {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q rho : Real) (H : Nat)
    (hn : 0 < n) (hq : (n : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) :
    hamiltonianFiniteSeriesValue H
        (wickTaylorSeries (hamiltonianCompensatedRook (centeredKernel T q))) =
      hamiltonianFiniteSeriesValue H
        (wickSeriesTruncatedDiagrams
          (covarianceFormalSeries (bipartiteLift (centeredKernel T q))) H) := by
  unfold hamiltonianFiniteSeriesValue
  apply Finset.sum_congr rfl
  intro k hk
  exact stochastic_compensated_taylor_covariance_series T q rho H k
    hn hq hRow hCol hNorm (by have h := Finset.mem_range.mp hk; omega)

theorem stochastic_compensated_lowSeries_remainder {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta u V : Real)
    (R : NNReal) (H : Nat)
    (hn : 11 <= n) (hH : 11 <= H) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hR : 1 < (R : Real)) (hGap : (R : Real) * (1 - delta) < 1)
    (hu0 : 0 <= u) (hu1 : u <= 1)
    (hSmall : 16 * Real.exp 1 * (4 * a / delta) * u <= 1 / 2)
    (hCube : u ^ 3 = (H : Real) / (n : Real))
    (hLength : (H : Real) ^ 2 <= V * (n : Real)) :
    norm (hamiltonianCompensatedRook (centeredKernel T q) 1 -
      hamiltonianFiniteSeriesValue H
        (wickSeriesLowDiagrams
          (covarianceFormalSeries (bipartiteLift (centeredKernel T q))))) <=
      Real.exp (2 * (R : Real) / (1 - (R : Real) * (1 - delta)) *
        Real.sqrt ((n : Real) * (a - 1)) + (R : Real) ^ 2 * (a - 1) / 2) *
          (Inv.inv (R : Real)) ^ (H + 1) / (1 - (Inv.inv (R : Real))) +
      (11616 * (1 + 16 * Real.exp 1 * (4 * a / delta)) ^ 11 +
        28 * (16 * Real.exp 1 * (4 * a / delta)) ^ 12 * V ^ 2) / (n : Real) ^ 2 := by
  have hnPos : 0 < n := by omega
  have : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 hnPos)
  let F := hamiltonianCompensatedRook (centeredKernel T q)
  let G := covarianceFormalSeries (bipartiteLift (centeredKernel T q))
  let kappa : Real := 4 * a / delta
  have hKappa : 0 <= kappa := by dsimp only [kappa]; positivity
  have hn0 : Not ((n : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hnPos)
  have hqEq : q = 1 / (n : Real) := by
    apply (eq_div_iff hn0).mpr
    simpa only [mul_comm] using hq
  have hDeltaNe : Not (delta = 0) := ne_of_gt hDelta0
  have hTheta : 1 * (1 - delta / 2) < 1 := by linarith
  have hEntry : forall i j, finitePowerSeriesMass H (G i j) <= kappa / (n : Real) := by
    intro i j
    have h := stochastic_covarianceFormalSeries_mass_bound T q a delta 1 1 H
      (by simpa only [Fintype.card_fin] using hq) ha hRow hCol hNonneg hUpper
      hDelta0 hDelta1 hNorm (le_refl _) (by norm_num) hTheta i j
    simp only [one_smul, one_pow, one_mul] at h
    calc
      _ <= _ := h
      _ = _ := by rw [hqEq]; dsimp only [kappa]; field_simp [hDeltaNe, hn0]; ring
  have hCard : Fintype.card (Sum (Fin n) (Fin n)) = 2 * n := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hDiagrams := wickSeriesTruncatedDiagrams_remainder_bound G H n kappa u V
    hCard hn hH hKappa hu0 hu1 hSmall hEntry hCube hLength
  have hCauchy := stochastic_compensated_cauchy_tail_bound T q a (1 - delta) R (H + 1)
    hq ha hRow hCol hNonneg hUpper hNorm hR hGap
  have hR0 : 0 < R := by exact_mod_cast lt_trans (by norm_num : (0 : Real) < 1) hR
  have hSeries := hamiltonianCompensatedRook_hasFPowerSeriesOnBall
    (centeredKernel T q) (1 - delta) R hNorm hR0 hGap
  have hCoeff : forall k, hamiltonianCauchyCoefficient F R k =
      PowerSeries.coeff k (wickTaylorSeries F) := by
    intro k
    exact hamiltonianCauchyCoefficient_eq_taylor F R hSeries k
  change norm (F 1 - Finset.sum (Finset.range (H + 1))
    (hamiltonianCauchyCoefficient F R)) <= _ at hCauchy
  simp_rw [hCoeff] at hCauchy
  change norm (F 1 - hamiltonianFiniteSeriesValue H (wickTaylorSeries F)) <= _ at hCauchy
  rw [stochastic_compensated_finiteSeriesValue T q (1 - delta) H
    hnPos hq hRow hCol hNorm] at hCauchy
  let S := hamiltonianFiniteSeriesValue H (wickSeriesTruncatedDiagrams G H)
  let L := hamiltonianFiniteSeriesValue H (wickSeriesLowDiagrams G)
  change norm (F 1 - L) <= _
  have hSplit : F 1 - L = (F 1 - S) + (S - L) := by ring
  rw [hSplit]
  exact le_trans (norm_add_le _ _) (add_le_add hCauchy hDiagrams)

end PrimeFactorOscillations
