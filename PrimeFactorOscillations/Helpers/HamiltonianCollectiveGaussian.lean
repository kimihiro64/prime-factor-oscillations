/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Collective zero-sum Gaussian-product bounds

The sum of the complex linear terms is cancelled exactly before any
absolute product estimate. The AM-GM form cancels the Gamma density's
power, allowing the original rook polynomial to be bounded outside the
local determinant window. These are deterministic vector inequalities;
the Gaussian representation is a separate, still-required consumer.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

private theorem collective_power_mono (a b : Real) (ha : 0 <= a)
    (hab : a <= b) (n : Nat) : a ^ n <= b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (pow_nonneg (le_trans ha hab) n)

theorem collective_nonnegative_prod_bound {Iota : Type*} (S : Finset Iota)
    (f : Iota -> Real) (hS : S.Nonempty) (hf : forall i, Membership.mem S i -> 0 <= f i) :
    Finset.prod S f <= (Finset.sum S f / (S.card : Real)) ^ S.card := by
  have hCard : 0 < S.card := Finset.card_pos.mpr hS
  have hProd : 0 <= Finset.prod S f := Finset.prod_nonneg (fun i hi => hf i hi)
  have hGM := Real.geom_mean_le_arith_mean S (fun _ => 1) f (fun _ _ => by norm_num)
    (show (0 : Real) < Finset.sum S (fun _ => 1) by
      simpa using (Nat.cast_pos.mpr hCard : (0 : Real) < (S.card : Real))) hf
  have hMean : (Finset.prod S f) ^ (Inv.inv (S.card : Real)) <=
      Finset.sum S f / (S.card : Real) := by
    simpa only [Real.rpow_one, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] using hGM
  have hPower := collective_power_mono
    ((Finset.prod S f) ^ (Inv.inv (S.card : Real)))
    (Finset.sum S f / (S.card : Real)) (Real.rpow_nonneg hProd _) hMean S.card
  rw [Real.rpow_inv_natCast_pow hProd (Nat.ne_of_gt hCard)] at hPower
  exact hPower

theorem collective_one_add_norm_square (z : Complex) :
    norm (1 + z) ^ 2 = 1 + 2 * z.re + norm z ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im]
  ring

variable {Iota : Type*} [DecidableEq Iota] [Fintype Iota] [Nonempty Iota]

def collectiveSquareMass (Y : Iota -> Complex) : Real :=
  Finset.sum Finset.univ (fun i => norm (Y i) ^ 2)

theorem collectiveSquareMass_nonnegative (Y : Iota -> Complex) :
    0 <= collectiveSquareMass Y :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (norm (Y i)))

theorem collective_zero_sum_norm_square (Y : Iota -> Complex) (c : Complex)
    (hZero : Finset.sum Finset.univ Y = 0) :
    Finset.sum Finset.univ (fun i => norm (1 + c * Y i) ^ 2) =
      (Fintype.card Iota : Real) + norm c ^ 2 * collectiveSquareMass Y := by
  have hScaled : Finset.sum Finset.univ (fun i => c * Y i) = 0 := by
    rw [<- Finset.mul_sum, hZero, mul_zero]
  have hReal : Finset.sum Finset.univ (fun i => (c * Y i).re) = 0 := by
    have h := congrArg (fun z : Complex => Complex.reCLM z) hScaled
    change Finset.sum Finset.univ (fun i => Complex.reCLM (c * Y i)) = 0
    simpa only [map_sum, map_zero] using h
  calc
    _ = Finset.sum Finset.univ
        (fun i => 1 + 2 * (c * Y i).re + norm c ^ 2 * norm (Y i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [collective_one_add_norm_square, norm_mul, mul_pow]
    _ = (Fintype.card Iota : Real) +
        2 * Finset.sum Finset.univ (fun i => (c * Y i).re) +
        norm c ^ 2 * collectiveSquareMass Y := by
      simp only [collectiveSquareMass, Finset.sum_add_distrib,
        <- Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
    _ = _ := by rw [hReal]; ring

theorem collective_zero_sum_product_bound (Y : Iota -> Complex) (c : Complex)
    (hZero : Finset.sum Finset.univ Y = 0) :
    (Finset.prod Finset.univ (fun i => norm (1 + c * Y i))) ^ 2 <=
      (1 + norm c ^ 2 * collectiveSquareMass Y / (Fintype.card Iota : Real)) ^
        Fintype.card Iota := by
  have hCardPos : 0 < (Fintype.card Iota : Real) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hProd := collective_nonnegative_prod_bound Finset.univ
    (fun i => norm (1 + c * Y i) ^ 2) Finset.univ_nonempty (fun i _ => sq_nonneg _)
  rw [Finset.prod_pow, collective_zero_sum_norm_square Y c hZero, Finset.card_univ] at hProd
  have hAverage :
      ((Fintype.card Iota : Real) + norm c ^ 2 * collectiveSquareMass Y) /
        (Fintype.card Iota : Real) =
      1 + norm c ^ 2 * collectiveSquareMass Y / (Fintype.card Iota : Real) := by
    field_simp [ne_of_gt hCardPos]
  rw [hAverage] at hProd
  exact hProd

theorem collective_gamma_product_bound (Y : Sum Iota Iota -> Complex)
    (hZero : Finset.sum Finset.univ Y = 0) (t : Real) (ht : 0 < t) :
    Finset.prod Finset.univ (fun i =>
      norm (1 + (Real.sqrt ((Fintype.card Iota : Real) / t) : Complex) * Y i)) <=
      (1 + collectiveSquareMass Y / (2 * t)) ^ Fintype.card Iota := by
  let c : Complex := (Real.sqrt ((Fintype.card Iota : Real) / t) : Complex)
  have hCardPos : 0 < (Fintype.card Iota : Real) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hC : norm c ^ 2 = (Fintype.card Iota : Real) / t := by
    change norm ((Real.sqrt ((Fintype.card Iota : Real) / t) : Real) : Complex) ^ 2 = _
    rw [Complex.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) (le_of_lt ht))]
  have h := collective_zero_sum_product_bound Y c hZero
  have hCard : (Fintype.card (Sum Iota Iota) : Real) =
      2 * (Fintype.card Iota : Real) := by
    simp only [Fintype.card_sum, Nat.cast_add]
    ring
  have hBase :
      1 + norm c ^ 2 * collectiveSquareMass Y / (Fintype.card (Sum Iota Iota) : Real) =
        1 + collectiveSquareMass Y / (2 * t) := by
    rw [hC, hCard]
    field_simp [ne_of_gt hCardPos, ne_of_gt ht]
  rw [hBase] at h
  have hCardNat : Fintype.card (Sum Iota Iota) = Fintype.card Iota * 2 := by
    simp only [Fintype.card_sum]
    ring
  rw [hCardNat, pow_mul] at h
  have hProductNonnegative : 0 <= Finset.prod Finset.univ (fun i => norm (1 + c * Y i)) :=
    Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have hRightNonnegative : 0 <=
      (1 + collectiveSquareMass Y / (2 * t)) ^ Fintype.card Iota := by
    apply pow_nonneg
    exact add_nonneg (by norm_num)
      (div_nonneg (collectiveSquareMass_nonnegative Y) (by positivity))
  change Finset.prod Finset.univ (fun i => norm (1 + c * Y i)) <= _
  nlinarith only [h, hProductNonnegative, hRightNonnegative]


theorem collective_gamma_density_bound (Y : Sum Iota Iota -> Complex)
    (hZero : Finset.sum Finset.univ Y = 0) (t : Real) (ht : 0 < t) :
    (Inv.inv ((Fintype.card Iota).factorial : Real)) * Real.exp (-t) *
      t ^ Fintype.card Iota * Finset.prod Finset.univ (fun i =>
        norm (1 + (Real.sqrt ((Fintype.card Iota : Real) / t) : Complex) * Y i)) <=
    Real.exp (collectiveSquareMass Y / 2) *
      (Inv.inv ((Fintype.card Iota).factorial : Real)) *
      (Real.exp (-(t + collectiveSquareMass Y / 2)) *
        (t + collectiveSquareMass Y / 2) ^ Fintype.card Iota) := by
  have hProd := collective_gamma_product_bound Y hZero t ht
  have hWeight : 0 <= (Inv.inv ((Fintype.card Iota).factorial : Real)) *
      Real.exp (-t) * t ^ Fintype.card Iota := by positivity
  have hPolynomial :
      t ^ Fintype.card Iota *
        (1 + collectiveSquareMass Y / (2 * t)) ^ Fintype.card Iota =
      (t + collectiveSquareMass Y / 2) ^ Fintype.card Iota := by
    rw [<- mul_pow]
    congr 1
    field_simp [ne_of_gt ht]
    <;> ring
  have hExponential : Real.exp (-t) = Real.exp (collectiveSquareMass Y / 2) *
      Real.exp (-(t + collectiveSquareMass Y / 2)) := by
    rw [<- Real.exp_add]
    congr 1
    ring
  calc
    _ <= ((Inv.inv ((Fintype.card Iota).factorial : Real)) * Real.exp (-t) *
        t ^ Fintype.card Iota) *
        (1 + collectiveSquareMass Y / (2 * t)) ^ Fintype.card Iota :=
      mul_le_mul_of_nonneg_left hProd hWeight
    _ = ((Inv.inv ((Fintype.card Iota).factorial : Real)) * Real.exp (-t)) *
        (t + collectiveSquareMass Y / 2) ^ Fintype.card Iota := by
      rw [mul_assoc, hPolynomial]
    _ = _ := by rw [hExponential]; ring

theorem collective_one_add_norm_exp_bound (z : Complex) :
    norm (1 + z) <= Real.exp (z.re + norm z ^ 2 / 2) := by
  have hNorm := collective_one_add_norm_square z
  have hScalar := Real.add_one_le_exp (2 * z.re + norm z ^ 2)
  have hExponential :
      (Real.exp (z.re + norm z ^ 2 / 2)) ^ 2 = Real.exp (2 * z.re + norm z ^ 2) := by
    rw [pow_two, <- Real.exp_add]
    congr 1
    ring
  nlinarith only [hNorm, hScalar, hExponential, norm_nonneg (1 + z),
    le_of_lt (Real.exp_pos (z.re + norm z ^ 2 / 2))]

theorem collective_zero_sum_exponential_bound (Y : Iota -> Complex) (c : Complex)
    (hZero : Finset.sum Finset.univ Y = 0) :
    Finset.prod Finset.univ (fun i => norm (1 + c * Y i)) <=
      Real.exp (norm c ^ 2 * collectiveSquareMass Y / 2) := by
  have hScaled : Finset.sum Finset.univ (fun i => c * Y i) = 0 := by
    rw [<- Finset.mul_sum, hZero, mul_zero]
  have hReal : Finset.sum Finset.univ (fun i => (c * Y i).re) = 0 := by
    have h := congrArg (fun z : Complex => Complex.reCLM z) hScaled
    change Finset.sum Finset.univ (fun i => Complex.reCLM (c * Y i)) = 0
    simpa only [map_sum, map_zero] using h
  have hExponent : Finset.sum Finset.univ
      (fun i => (c * Y i).re + norm (c * Y i) ^ 2 / 2) =
        norm c ^ 2 * collectiveSquareMass Y / 2 := by
    calc
      _ = Finset.sum Finset.univ (fun i => (c * Y i).re) +
          (Finset.sum Finset.univ (fun i => norm c ^ 2 * norm (Y i) ^ 2)) / 2 := by
        simp only [norm_mul, mul_pow, Finset.sum_add_distrib, Finset.sum_div]
      _ = _ := by rw [hReal, zero_add, <- Finset.mul_sum]; rfl
  have hFinite : forall S : Finset Iota,
      Finset.prod S (fun i => norm (1 + c * Y i)) <=
        Finset.prod S (fun i => Real.exp ((c * Y i).re + norm (c * Y i) ^ 2 / 2)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact mul_le_mul (collective_one_add_norm_exp_bound (c * Y i)) ih
        (Finset.prod_nonneg (fun j _ => norm_nonneg _)) (le_of_lt (Real.exp_pos _))
  calc
    _ <= Finset.prod Finset.univ
        (fun i => Real.exp ((c * Y i).re + norm (c * Y i) ^ 2 / 2)) := hFinite Finset.univ
    _ = Real.exp (Finset.sum Finset.univ
        (fun i => (c * Y i).re + norm (c * Y i) ^ 2 / 2)) := by rw [Real.exp_sum]
    _ = _ := congrArg Real.exp hExponent

end PrimeFactorOscillations
