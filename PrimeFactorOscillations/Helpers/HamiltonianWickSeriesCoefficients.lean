/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceSeries
import PrimeFactorOscillations.Helpers.HamiltonianPowerSeriesMass

/-! # Complete Wick coefficient convolutions in the deformation parameter

The actual covariance inverse series is used coefficient by coefficient.
Every pairing is retained. Finite coefficient mass controls all convolution
frequencies through the same cutoff, rather than replacing it by a degree tail.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota J : Type*}

theorem finitePowerSeriesMass_one (H : Nat) :
    finitePowerSeriesMass H (1 : PowerSeries Complex) = 1 := by
  simp [finitePowerSeriesMass, PowerSeries.coeff_one, apply_ite]

def wickSeriesPairMoment (G : Matrix J J (PowerSeries Complex)) :
    Nat -> List J -> PowerSeries Complex
  | 0, [] => 1
  | 0, _ :: _ => 0
  | _ + 1, [] => 0
  | e + 1, i :: xs =>
    Finset.sum (Finset.range xs.length) (fun k =>
      G i (xs.getD k i) * wickSeriesPairMoment G e (xs.eraseIdx k))

theorem wickSeriesPairMoment_coeff_zero_of_lt
    (G : Matrix J J (PowerSeries Complex))
    (hZero : forall i j, PowerSeries.coeff 0 (G i j) = 0)
    (e k : Nat) (xs : List J) (hk : k < e) :
    PowerSeries.coeff k (wickSeriesPairMoment G e xs) = 0 := by
  induction e generalizing xs k with
  | zero => omega
  | succ e ih =>
    cases xs with
    | nil => simp only [wickSeriesPairMoment, map_zero]
    | cons i xs =>
      rw [wickSeriesPairMoment, map_sum]
      apply Finset.sum_eq_zero
      intro r hr
      rw [PowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      have hP := Finset.mem_antidiagonal.mp hp
      by_cases hFirst : p.1 = 0
      case pos => rw [hFirst, hZero, zero_mul]
      case neg =>
        rw [ih p.2 (xs.eraseIdx r) (by omega), mul_zero]

theorem wickSeriesPairMoment_mass_zero_of_lt
    (G : Matrix J J (PowerSeries Complex))
    (hZero : forall i j, PowerSeries.coeff 0 (G i j) = 0)
    (e H : Nat) (xs : List J) (hH : H < e) :
    finitePowerSeriesMass H (wickSeriesPairMoment G e xs) = 0 := by
  unfold finitePowerSeriesMass
  apply Finset.sum_eq_zero
  intro k hk
  rw [wickSeriesPairMoment_coeff_zero_of_lt G hZero e k xs
    (by have hK := Finset.mem_range.mp hk; omega), norm_zero]

theorem wickSeriesPairMoment_mass_bound (G : Matrix J J (PowerSeries Complex))
    (H : Nat) (c : Real) (hc : 0 <= c)
    (hEntry : forall i j, finitePowerSeriesMass H (G i j) <= c)
    (e : Nat) (xs : List J) (hLen : xs.length = 2 * e) :
    finitePowerSeriesMass H (wickSeriesPairMoment G e xs) <=
      (wickPairCount e : Real) * c ^ e := by
  induction e generalizing xs with
  | zero =>
    cases xs with
    | nil => simp only [wickSeriesPairMoment, finitePowerSeriesMass_one,
        wickPairCount, Nat.cast_one, pow_zero, mul_one, le_refl]
    | cons i xs => simp only [List.length_cons] at hLen; omega
  | succ e ih =>
    cases xs with
    | nil => simp only [List.length_nil] at hLen; omega
    | cons i xs =>
      have hXs : xs.length = 2 * e + 1 := by
        simp only [List.length_cons] at hLen
        omega
      rw [wickSeriesPairMoment]
      calc
        _ <= Finset.sum (Finset.range xs.length) (fun k =>
            finitePowerSeriesMass H (G i (xs.getD k i) *
              wickSeriesPairMoment G e (xs.eraseIdx k))) :=
          finitePowerSeriesMass_sum H _ _
        _ <= Finset.sum (Finset.range xs.length)
            (fun _ => c * ((wickPairCount e : Real) * c ^ e)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hErase := List.length_eraseIdx_add_one (Finset.mem_range.mp hk)
          have hEraseLen : (xs.eraseIdx k).length = 2 * e := by omega
          exact le_trans (finitePowerSeriesMass_mul H _ _)
            (mul_le_mul (hEntry _ _) (ih (xs.eraseIdx k) hEraseLen)
              (finitePowerSeriesMass_nonnegative H _) hc)
        _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            hXs, wickPairCount, pow_succ]
          push_cast
          ring

theorem wickVertexProfileCoefficient_bound {k : Nat} (d : Composition k) :
    norm (Finset.prod Finset.univ
      (fun i => wickVertexCoefficient (d.blocksFun i))) <= 1 := by
  have hAll : forall S : Finset (Fin d.length),
      norm (Finset.prod S (fun i => wickVertexCoefficient (d.blocksFun i))) <= 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, norm_mul]
      have hVertex := wickVertexCoefficient_norm_le_one (d.blocksFun i)
      nlinarith [norm_nonneg (wickVertexCoefficient (d.blocksFun i)),
        norm_nonneg (Finset.prod S (fun j => wickVertexCoefficient (d.blocksFun j)))]
  exact hAll Finset.univ

def wickSeriesProfile (G : Matrix J J (PowerSeries Complex)) (e : Nat)
    (d : Composition (2 * e)) (label : Fin d.length -> J) : PowerSeries Complex :=
  PowerSeries.C (Finset.prod Finset.univ
      (fun i => wickVertexCoefficient (d.blocksFun i))) *
    wickSeriesPairMoment G e (wickProfileList d label)

theorem wickSeriesProfile_mass_bound (G : Matrix J J (PowerSeries Complex))
    (H : Nat) (c : Real) (hc : 0 <= c)
    (hEntry : forall i j, finitePowerSeriesMass H (G i j) <= c)
    (e : Nat) (d : Composition (2 * e)) (label : Fin d.length -> J) :
    finitePowerSeriesMass H (wickSeriesProfile G e d label) <=
      (wickPairCount e : Real) * c ^ e := by
  unfold wickSeriesProfile
  rw [finitePowerSeriesMass_const_mul]
  calc
    _ <= 1 * ((wickPairCount e : Real) * c ^ e) :=
      mul_le_mul (wickVertexProfileCoefficient_bound d)
        (wickSeriesPairMoment_mass_bound G H c hc hEntry e _
          (wickProfileList_length d label))
        (finitePowerSeriesMass_nonnegative H _) (by norm_num)
    _ = _ := one_mul _

variable [Fintype Iota] [DecidableEq Iota]

def covarianceFormalSeries (Q : Matrix Iota Iota Real)
    (i j : Iota) : PowerSeries Complex :=
  PowerSeries.mk (fun k => match k with
    | 0 => 0
    | k + 1 => (covarianceSeriesCoefficient Q k i j : Complex))

theorem covarianceFormalSeries_coeff_zero (Q : Matrix Iota Iota Real) (i j : Iota) :
    PowerSeries.coeff 0 (covarianceFormalSeries Q i j) = 0 := by
  simp only [covarianceFormalSeries, PowerSeries.coeff_mk]

theorem covarianceFormalSeries_coeff_succ (Q : Matrix Iota Iota Real)
    (k : Nat) (i j : Iota) :
    PowerSeries.coeff (k + 1) (covarianceFormalSeries Q i j) =
      (covarianceSeriesCoefficient Q k i j : Complex) := by
  simp only [covarianceFormalSeries, PowerSeries.coeff_mk]

theorem covarianceFormalSeries_mass_bound (Q : Matrix Iota Iota Real)
    (H : Nat) (c theta : Real)
    (hc : 0 <= c) (hTheta0 : 0 <= theta) (hTheta1 : theta < 1)
    (hCoeff : forall k i j, norm (covarianceSeriesCoefficient Q k i j) <= c * theta ^ k)
    (i j : Iota) :
    finitePowerSeriesMass H (covarianceFormalSeries Q i j) <= c / (1 - theta) := by
  apply finitePowerSeriesMass_geometric H _ c theta hc hTheta0 hTheta1
    (covarianceFormalSeries_coeff_zero Q i j)
  intro k
  rw [covarianceFormalSeries_coeff_succ, Complex.norm_real]
  exact hCoeff k i j

variable [Nonempty Iota]

theorem stochastic_covarianceFormalSeries_mass_bound
    (T : Matrix Iota Iota Real) (q a delta b s : Real) (H : Nat)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hb : 1 <= b) (hs : abs s <= b) (hTheta1 : b * (1 - delta / 2) < 1)
    (i j : Sum Iota Iota) :
    finitePowerSeriesMass H
        (covarianceFormalSeries (HSMul.hSMul s (bipartiteLift (centeredKernel T q))) i j) <=
      2 * b ^ 2 * a * q / (1 - b * (1 - delta / 2)) := by
  have hData := stochastic_covariance_series_data T q a delta b s
    hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hb hs hTheta1
  have hCard : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hCard]
  have hc : 0 <= 2 * b ^ 2 * a * q :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg b))
      (by linarith only [ha])) hq0
  have hTheta0 : 0 <= b * (1 - delta / 2) :=
    mul_nonneg (by linarith only [hb]) (by linarith only [hDelta1])
  exact covarianceFormalSeries_mass_bound _ H _ _ hc hTheta0 hTheta1 hData.2 i j


variable [Fintype J] [DecidableEq J]

def wickSeriesSupportProfile (G : Matrix J J (PowerSeries Complex))
    (e : Nat) (S : Finset J) (d : Composition (2 * e)) : PowerSeries Complex :=
  if h : d.length = S.card then
    wickSeriesProfile G e d (fun i => wickSupportLabel S (Fin.cast h i))
  else 0

def wickSeriesDiagramCoefficient (G : Matrix J J (PowerSeries Complex))
    (e v : Nat) : PowerSeries Complex :=
  Finset.sum ((Finset.univ : Finset J).powersetCard v) (fun S =>
    Finset.sum (wickVertexProfiles e v) (fun d => wickSeriesSupportProfile G e S d))

theorem wickSeriesSupportProfile_mass_bound (G : Matrix J J (PowerSeries Complex))
    (H : Nat) (c : Real) (hc : 0 <= c)
    (hEntry : forall i j, finitePowerSeriesMass H (G i j) <= c)
    (e : Nat) (S : Finset J) (d : Composition (2 * e)) :
    finitePowerSeriesMass H (wickSeriesSupportProfile G e S d) <=
      (wickPairCount e : Real) * c ^ e := by
  unfold wickSeriesSupportProfile
  split_ifs
  case pos h => exact wickSeriesProfile_mass_bound G H c hc hEntry e d _
  case neg h =>
    rw [finitePowerSeriesMass_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc e)

theorem wickSeriesDiagramCoefficient_mass_bound (G : Matrix J J (PowerSeries Complex))
    (H : Nat) (c : Real) (hc : 0 <= c)
    (hEntry : forall i j, finitePowerSeriesMass H (G i j) <= c)
    (e v : Nat) :
    finitePowerSeriesMass H (wickSeriesDiagramCoefficient G e v) <=
      ((Fintype.card J).choose v : Real) * (2 : Real) ^ (2 * e - 1) *
        ((wickPairCount e : Real) * c ^ e) := by
  let W : Real := (wickPairCount e : Real) * c ^ e
  have hW : 0 <= W := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc e)
  have hCard : ((wickVertexProfiles e v).card : Real) <=
      (2 : Real) ^ (2 * e - 1) := by
    exact_mod_cast wickVertexProfiles_card_le e v
  unfold wickSeriesDiagramCoefficient
  calc
    _ <= Finset.sum ((Finset.univ : Finset J).powersetCard v) (fun S =>
        finitePowerSeriesMass H (Finset.sum (wickVertexProfiles e v)
          (fun d => wickSeriesSupportProfile G e S d))) :=
      finitePowerSeriesMass_sum H _ _
    _ <= Finset.sum ((Finset.univ : Finset J).powersetCard v)
        (fun _ => ((wickVertexProfiles e v).card : Real) * W) := by
      apply Finset.sum_le_sum
      intro S hS
      calc
        _ <= Finset.sum (wickVertexProfiles e v)
            (fun d => finitePowerSeriesMass H (wickSeriesSupportProfile G e S d)) :=
          finitePowerSeriesMass_sum H _ _
        _ <= Finset.sum (wickVertexProfiles e v) (fun _ => W) :=
          Finset.sum_le_sum (fun d _ =>
            wickSeriesSupportProfile_mass_bound G H c hc hEntry e S d)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((Fintype.card J).choose v : Real) *
        ((wickVertexProfiles e v).card : Real) * W := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ]
      ring
    _ <= _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCard (Nat.cast_nonneg _)) hW

theorem wickSeriesDiagramCoefficient_mass_envelope (G : Matrix J J (PowerSeries Complex))
    (H n : Nat) (kappa : Real) (e v : Nat)
    (hCard : Fintype.card J = 2 * n) (hn : 0 < n) (hKappa : 0 <= kappa)
    (he : 0 < e) (hVE : v <= e)
    (hEntry : forall i j, finitePowerSeriesMass H (G i j) <= kappa / (n : Real)) :
    finitePowerSeriesMass H (wickSeriesDiagramCoefficient G e v) <=
      (16 * kappa) ^ e * Real.exp (e : Real) *
        ((e : Real) / (n : Real)) ^ (e - v) := by
  have hBase := wickSeriesDiagramCoefficient_mass_bound G H (kappa / (n : Real))
    (div_nonneg hKappa (Nat.cast_nonneg n)) hEntry e v
  have hChoose : ((Fintype.card J).choose v : Real) <=
      (Fintype.card J : Real) ^ v / (v.factorial : Real) :=
    Nat.choose_le_pow_div v (Fintype.card J)
  have hFactorial := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hChoose
      (pow_nonneg (by norm_num : (0 : Real) <= 2) (2 * e - 1)))
    (mul_nonneg (Nat.cast_nonneg (wickPairCount e))
      (pow_nonneg (div_nonneg hKappa (Nat.cast_nonneg n)) e))
  rw [hCard] at hBase hFactorial
  push_cast at hBase hFactorial
  exact le_trans (le_trans hBase hFactorial)
    (wick_support_envelope_bound n kappa e v hn hKappa he hVE)

theorem wickSeriesDiagramCoefficient_zero_of_support
    (G : Matrix J J (PowerSeries Complex)) (e v : Nat) (h : 2 * e < 3 * v) :
    wickSeriesDiagramCoefficient G e v = 0 := by
  unfold wickSeriesDiagramCoefficient
  rw [wickVertexProfiles_empty_of_support e v h]
  simp only [Finset.sum_empty, Finset.sum_const_zero]

end PrimeFactorOscillations
