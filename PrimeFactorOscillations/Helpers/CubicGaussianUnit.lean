/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicPairRadius
import PrimeFactorOscillations.Helpers.CubicReciprocalGaussian
/-!
# Actual reciprocal Gaussian unit lattice packet

Proves convergence and native Poisson reflection of the actual four-Gaussian
window, without a Schwartz-profile premise on the negative half-line. Its
zero origin gives an explicit decaying unit-lattice tail. The exact four-term
compensation is retained. This does not estimate the arithmetic Abel unit C_G
or assert a new zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false


noncomputable section
namespace PrimeFactorOscillations.CubicGaussianUnit
open OAI OAI.SevenEighths
open ActualEisensteinCubic ConcreteTraceCRT ProbeRadialMellin
open CubicReciprocalGaussian
local notation "Eis" => ActualEisensteinCubic.O

theorem exp_weight_bound (u : Real) (hu : 0 <= u) :
    (1 + u) ^ 2 * Real.exp (-u) <= 5 := by
  have h1 := Real.pow_div_factorial_le_exp u hu 1
  have h2 := Real.pow_div_factorial_le_exp u hu 2
  norm_num at h1 h2
  have he : Real.exp u * Real.exp (-u) = 1 := by
    rw [<- Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hp : 0 <= Real.exp (-u) := (Real.exp_pos _).le
  have h0m : Real.exp (-u) <= 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have h1m := mul_le_mul_of_nonneg_right h1 hp
  have h2m := mul_le_mul_of_nonneg_right h2 hp
  rw [he] at h1m h2m
  nlinarith only [h0m, h1m, h2m]

theorem gaussian_lattice_summable (a M : Real) (ha : 0 < a) (hM : 0 < M) :
    Summable (fun z : Eis => gaussian (a / M) (eisEmbedding z)) := by
  let K : Real := paperConstant * a / M
  have hK : 0 < K := by
    exact div_pos (mul_pos paperConstant_pos ha) hM
  apply (CubicPairRadius.dominated_lattice_sum
    (fun z : Eis => gaussian (a / M) (eisEmbedding z)) K 5 hK (by norm_num) ?_).1
  intro z
  have hEq : gaussian (a / M) (eisEmbedding z) =
      Complex.exp ((-(K * norm (eisEmbedding z) ^ 2) : Real) : Complex) := by
    unfold gaussian
    congr 1
    dsimp [K]
    push_cast
    ring
  rw [hEq, Complex.norm_exp, Complex.ofReal_re]
  exact exp_weight_bound _ (by positivity)

def theta (a : Real) : Complex :=
  tsum (fun z : Eis => gaussian a (eisEmbedding z))

theorem poisson_prefactor (a : Real) (ha : 0 < a) :
    (1 / ((2 * a / Real.sqrt 3 : Real) : Complex) ^ (1 / 2 : Complex)) *
      (1 / ((3 * (2 * a / Real.sqrt 3) / 4 : Real) : Complex) ^
        (1 / 2 : Complex)) = 1 / (a : Complex) := by
  let t : Real := 2 * a / Real.sqrt 3
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have ht : 0 < t := div_pos (mul_pos (by norm_num) ha) hs
  have hd : 0 < 3 * t / 4 := by positivity
  have hm : t * (3 * t / 4) = a * a := by
    dsimp [t]
    have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith only [hs2]
  have hc : (t : Complex) * ((3 * t / 4 : Real) : Complex) =
      (a : Complex) * (a : Complex) := by exact_mod_cast hm
  have ha0 : Not ((a : Complex) = 0) := by exact_mod_cast ha.ne'
  have hprod :
      (t : Complex) ^ (1 / 2 : Complex) *
        ((3 * t / 4 : Real) : Complex) ^ (1 / 2 : Complex) = (a : Complex) := by
    rw [<- Complex.mul_cpow_ofReal_nonneg ht.le hd.le, hc,
      Complex.mul_cpow_ofReal_nonneg ha.le ha.le,
      <- Complex.cpow_add _ _ ha0]
    norm_num
  change (1 / (t : Complex) ^ (1 / 2 : Complex)) *
    (1 / ((3 * t / 4 : Real) : Complex) ^ (1 / 2 : Complex)) = _
  simpa only [one_div, mul_inv] using congrArg Inv.inv hprod

theorem gaussian_coordinates (a : Real) (z : Prod Int Int) :
    gaussian a (eisEmbedding (latticeCoordEquiv.symm z)) =
      RankTwoPoisson.eisGauss (2 * a / Real.sqrt 3) z := by
  change gaussian a (eisEmbedding (ActualEisensteinCoordinates.eval z.1 z.2)) = _
  unfold gaussian RankTwoPoisson.eisGauss RankTwoPoisson.eisQ
  rw [<- Complex.ofReal_pow, eisEmbedding_eval_norm_sq]
  congr 1
  unfold paperConstant
  push_cast
  ring

theorem gaussian_theta_poisson (a : Real) (ha : 0 < a) :
    theta a = (1 / (a : Complex)) * theta (1 / a) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have ht : 0 < 2 * a / Real.sqrt 3 := div_pos (mul_pos (by norm_num) ha) hs
  have hd : 4 / (3 * (2 * a / Real.sqrt 3)) =
      2 * (1 / a) / Real.sqrt 3 := by
    have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith only [hs2]
  have hreindex (b : Real) :
      theta b = tsum (RankTwoPoisson.eisGauss (2 * b / Real.sqrt 3)) := by
    unfold theta
    rw [<- latticeCoordEquiv.symm.tsum_eq]
    apply tsum_congr
    exact gaussian_coordinates b
  rw [hreindex, RankTwoPoisson.eisenstein_gaussian_poisson ht,
    poisson_prefactor a ha, hd, <- hreindex]

def unitPacket (M : Real) : Complex :=
  tsum (fun z : Eis => carrierProfile (norm (eisEmbedding z) ^ 2 / M))

theorem window_lattice_hasSum (M : Real) (hM : 0 < M) :
    HasSum (fun z : Eis => carrierProfile (norm (eisEmbedding z) ^ 2 / M))
      (Finset.univ.sum (fun i : Fin 4 =>
        coefficients i * theta (scales i / M))) := by
  classical
  have hfin (S : Finset (Fin 4)) :
      HasSum (fun z : Eis => S.sum (fun i =>
        coefficients i * gaussian (scales i / M) (eisEmbedding z)))
        (S.sum (fun i => coefficients i * theta (scales i / M))) := by
    induction S using Finset.induction_on with
    | empty =>
      have hz : HasSum (fun _ : Eis => (0 : Complex)) 0 := hasSum_zero
      simpa only [Finset.sum_empty] using hz
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      have hh := (gaussian_lattice_summable (scales i) M (scales_pos i) hM).hasSum
      change HasSum (fun z : Eis => gaussian (scales i / M) (eisEmbedding z))
        (theta (scales i / M)) at hh
      exact (hh.mul_left (coefficients i)).add ih
  have he (z : Eis) :
      carrierProfile (norm (eisEmbedding z) ^ 2 / M) =
        Finset.univ.sum (fun i : Fin 4 =>
          coefficients i * gaussian (scales i / M) (eisEmbedding z)) := by
    unfold carrierProfile
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    unfold gaussian
    congr 1
    push_cast
    ring
  simpa only [<- he] using hfin Finset.univ

theorem unitPacket_eq_theta (M : Real) (hM : 0 < M) :
    unitPacket M = Finset.univ.sum (fun i : Fin 4 =>
      coefficients i * theta (scales i / M)) :=
  (window_lattice_hasSum M hM).tsum_eq

theorem unitPacket_anti_reflection (M : Real) (hM : 0 < M) :
    unitPacket M = -(M : Complex) * unitPacket (1 / M) := by
  rw [unitPacket_eq_theta M hM,
    unitPacket_eq_theta (1 / M) (one_div_pos.mpr hM)]
  have hp (i : Fin 4) := gaussian_theta_poisson (scales i / M)
    (div_pos (scales_pos i) hM)
  simp_rw [hp, one_div_div]
  norm_num [coefficients, scales, Fin.sum_univ_succ, div_eq_mul_inv, mul_comm]
  ring

theorem exp_weight3_bound (u : Real) (hu : 0 <= u) :
    (1 + u) ^ 3 * Real.exp (-u) <= 16 := by
  have h1 := Real.pow_div_factorial_le_exp u hu 1
  have h2 := Real.pow_div_factorial_le_exp u hu 2
  have h3 := Real.pow_div_factorial_le_exp u hu 3
  norm_num at h1 h2 h3
  have he : Real.exp u * Real.exp (-u) = 1 := by
    rw [<- Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hp : 0 <= Real.exp (-u) := (Real.exp_pos _).le
  have h0m : Real.exp (-u) <= 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have h1m := mul_le_mul_of_nonneg_right h1 hp
  have h2m := mul_le_mul_of_nonneg_right h2 hp
  have h3m := mul_le_mul_of_nonneg_right h3 hp
  rw [he] at h1m h2m h3m
  nlinarith only [h0m, h1m, h2m, h3m]

theorem scaled_exp_weight3_bound (K v : Real) (hK : 0 < K) (hv : 0 <= v) :
    (1 + v) ^ 3 * Real.exp (-K * v) <=
      16 * (1 + 1 / K) ^ 3 := by
  let u : Real := K * v
  let A : Real := 1 + v
  let B : Real := (1 + 1 / K) * (1 + u)
  have hu : 0 <= u := mul_nonneg hK.le hv
  have hA : 0 <= A := by dsimp [A]; positivity
  have hB : 0 <= B := by dsimp [B]; positivity
  have hAB : A <= B := by
    have he : B - A = u + 1 / K := by dsimp [A, B, u]; field_simp; ring
    have hh : 0 <= B - A := by rw [he]; positivity
    linarith
  have hcube : A ^ 3 <= B ^ 3 := by
    have hh := mul_nonneg (sub_nonneg.mpr hAB)
      (show 0 <= B ^ 2 + B * A + A ^ 2 by positivity)
    nlinarith only [hh]
  have hw := exp_weight3_bound u hu
  calc
    _ <= B ^ 3 * Real.exp (-u) := by
      convert mul_le_mul_of_nonneg_right hcube (Real.exp_pos (-u)).le using 1
      dsimp [A, u]
      congr 2
      ring
    _ = (1 + 1 / K) ^ 3 * ((1 + u) ^ 3 * Real.exp (-u)) := by dsimp [B]; ring
    _ <= (1 + 1 / K) ^ 3 * 16 :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

def windowConstant : Real :=
  Finset.univ.sum (fun i : Fin 4 =>
    norm (coefficients i) * (16 * (1 + 1 / (paperConstant * scales i)) ^ 3))

theorem windowConstant_nonneg : 0 <= windowConstant := by
  unfold windowConstant
  apply Finset.sum_nonneg
  intro i hi
  have hK : 0 < paperConstant * scales i := mul_pos paperConstant_pos (scales_pos i)
  positivity

theorem carrierProfile_weight3 (v : Real) (hv : 0 <= v) :
    (1 + v) ^ 3 * norm (carrierProfile v) <= windowConstant := by
  unfold carrierProfile windowConstant
  calc
    _ <= (1 + v) ^ 3 * Finset.univ.sum (fun i : Fin 4 =>
        norm (coefficients i * Complex.exp
          (-((paperConstant * scales i : Real) : Complex) * (v : Complex)))) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = Finset.univ.sum (fun i : Fin 4 =>
        norm (coefficients i) * ((1 + v) ^ 3 *
          Real.exp (-(paperConstant * scales i) * v))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, Complex.norm_exp]
      have he : (-((paperConstant * scales i : Real) : Complex) *
          (v : Complex)).re = -(paperConstant * scales i) * v := by simp
      rw [he]
      ring
    _ <= _ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (scaled_exp_weight3_bound (paperConstant * scales i) v
          (mul_pos paperConstant_pos (scales_pos i)) hv) (norm_nonneg _)

open EisensteinSchwartzPoisson

def nonzeroTail (M : Real) : Complex :=
  tsum (fun z : {z : Eis // Not (z = 0)} =>
    carrierProfile (M * norm (eisEmbedding z.val) ^ 2))

theorem nonzero_tail_bound (M : Real) (hM : 1 <= M) :
    norm (nonzeroTail M) <=
      nonzeroLatticeEnvelopeConstant * windowConstant / M ^ 2 := by
  have hMp : 0 < M := by linarith
  have hC : 0 <= windowConstant / M :=
    div_nonneg windowConstant_nonneg hMp.le
  have hb (z : {z : Eis // Not (z = 0)}) :
      (1 + M * norm (eisEmbedding z.val) ^ 2) ^ 2 *
        norm (carrierProfile (M * norm (eisEmbedding z.val) ^ 2)) <=
          windowConstant / M := by
    let u : Real := M * norm (eisEmbedding z.val) ^ 2
    have hQ : 1 <= norm (eisEmbedding z.val) ^ 2 :=
      one_le_eisenstein_norm_sq z.val z.property
    have hu : 0 <= u := by dsimp [u]; positivity
    have hMu : M <= u := by dsimp [u]; nlinarith
    have hw := carrierProfile_weight3 u hu
    have hm := mul_nonneg (sub_nonneg.mpr (show M <= 1 + u by linarith))
      (mul_nonneg (sq_nonneg (1 + u)) (norm_nonneg (carrierProfile u)))
    have hmul : ((1 + u) ^ 2 * norm (carrierProfile u)) * M <= windowConstant := by
      nlinarith only [hw, hm]
    change (1 + u) ^ 2 * norm (carrierProfile u) <= _
    calc
      _ = (((1 + u) ^ 2 * norm (carrierProfile u)) * M) / M := by field_simp
      _ <= windowConstant / M := div_le_div_of_nonneg_right hmul hMp.le
  have hs := nonzero_lattice_envelope_sum M (windowConstant / M) hMp hC
    (fun z : {z : Eis // Not (z = 0)} =>
      norm (carrierProfile (M * norm (eisEmbedding z.val) ^ 2)))
    (fun _ => norm_nonneg _) hb
  have hn := norm_tsum_le_tsum_norm hs.1
  have hmul := (mul_le_mul_of_nonneg_left hn hMp.le).trans hs.2
  calc
    _ = (M * norm (nonzeroTail M)) / M := by field_simp
    _ <= (nonzeroLatticeEnvelopeConstant * (windowConstant / M)) / M :=
      div_le_div_of_nonneg_right hmul hMp.le
    _ = _ := by ring

theorem unit_zero_mode (M : Real) (hM : 0 < M) :
    unitPacket M = -(M : Complex) * nonzeroTail M := by
  classical
  let f : Eis -> Complex := fun z =>
    carrierProfile (M * norm (eisEmbedding z) ^ 2)
  have hscale (z : Eis) :
      carrierProfile (norm (eisEmbedding z) ^ 2 / (1 / M)) = f z := by
    dsimp [f]
    congr 1
    field_simp
  have hs : Summable f :=
    (window_lattice_hasSum (1 / M) (one_div_pos.mpr hM)).summable.congr hscale
  let e : Equiv {z : Eis // Not (Membership.mem ({0} : Finset Eis) z)}
      {z : Eis // Not (z = 0)} :=
    Equiv.subtypeEquivRight (fun _ => Finset.notMem_singleton)
  have hindex :
      (tsum fun z : {z : Eis // Not (Membership.mem ({0} : Finset Eis) z)} => f z.val) =
      (tsum fun z : {z : Eis // Not (z = 0)} => f z.val) :=
    Equiv.tsum_eq e (fun z => f z.val)
  have he :
      (tsum fun z : {z : Eis // Not (z = 0)} => f z.val) = tsum f := by
    have hh := hs.sum_add_tsum_subtype_compl ({0} : Finset Eis)
    rw [hindex] at hh
    simpa only [Finset.sum_singleton, f, map_zero, norm_zero, zero_pow
      (by norm_num : Not (2 = 0)), mul_zero, carrierProfile_zero, zero_add] using hh
  have hp := unitPacket_anti_reflection M hM
  change unitPacket M = -(M : Complex) *
    (tsum fun z : Eis => carrierProfile (norm (eisEmbedding z) ^ 2 / (1 / M))) at hp
  simp_rw [hscale] at hp
  rw [<- he] at hp
  exact hp

theorem unitPacket_bound (M : Real) (hM : 1 <= M) :
    norm (unitPacket M) <=
      nonzeroLatticeEnvelopeConstant * windowConstant / M := by
  have hMp : 0 < M := by linarith
  rw [unit_zero_mode M hMp, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMp]
  calc
    _ <= M * (nonzeroLatticeEnvelopeConstant * windowConstant / M ^ 2) :=
      mul_le_mul_of_nonneg_left (nonzero_tail_bound M hM) hMp.le
    _ = _ := by field_simp

theorem compensated_unit_identity (c : Complex) (Maa Mab Mba Mbb : Real)
    (haa : 0 < Maa) (hab : 0 < Mab) (hba : 0 < Mba) (hbb : 0 < Mbb) :
    unitPacket Maa - star c * unitPacket Mab -
      c * unitPacket Mba + c * star c * unitPacket Mbb =
    -(Maa : Complex) * nonzeroTail Maa +
      star c * (Mab : Complex) * nonzeroTail Mab +
      c * (Mba : Complex) * nonzeroTail Mba -
      c * star c * (Mbb : Complex) * nonzeroTail Mbb := by
  rw [unit_zero_mode Maa haa, unit_zero_mode Mab hab,
    unit_zero_mode Mba hba, unit_zero_mode Mbb hbb]
  ring

end PrimeFactorOscillations.CubicGaussianUnit
