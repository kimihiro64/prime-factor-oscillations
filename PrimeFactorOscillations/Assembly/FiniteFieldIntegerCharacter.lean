/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticCharacter
import PrimeFactorOscillations.Assembly.FiniteFieldFrozenGrowth
import PrimeFactorOscillations.Helpers.QRHPrimePrefix

/-!
# Actual quadratic-character tails at bounded integer height

The finite-field pair law's two characters are identified with numerator
Jacobi characters on rational primes, including all zero values. Their
nonprincipality follows constructively from a prime factor and CRT.
The installed uniform QRH estimate then bounds both signed tails on the
natural integer-height packet branch. No new zero-free boundary or
positive short-height packet mass is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.FiniteFieldIntegerCharacter

open IntegerQuadraticCharacter
open FiniteFieldIntegerMass

theorem integer_characterA (h n p : Nat) [Fact (Nat.Prime p)] (hp2 : Not (p = 2)) :
    ((FiniteField.QuadraticPairTwistEuler.characterA (n : ZMod p) (h : ZMod p) : Real) : Complex) =
      numeratorKernel (-((h : Int) * (n : Int))) p := by
  rw [numerator_kernel_prime _ p hp2]
  simp only [FiniteField.QuadraticPairTwistEuler.characterA,
    Int.cast_neg, Int.cast_mul, Int.cast_natCast, neg_mul]
  norm_cast

theorem integer_characterB (h n p : Nat) [Fact (Nat.Prime p)] (hp2 : Not (p = 2)) :
    ((FiniteField.QuadraticPairTwistEuler.characterB (n : ZMod p) (h : ZMod p) : Real) : Complex) =
      numeratorKernel ((h : Int) * ((n + h : Nat) : Int)) p := by
  rw [numerator_kernel_prime _ p hp2]
  simp only [FiniteField.QuadraticPairTwistEuler.characterB,
    Int.cast_mul, Int.cast_natCast, Nat.cast_add]
  norm_cast


theorem exists_prime_factor_numerator_tail_bound :
    exists C : Real, And (0 < C)
      (forall h P : Nat, 0 < h -> Nat.Prime P -> 2 < P -> h < P ->
        forall D : Int,
          Or (D = (h : Int) * (P : Int)) (D = -((h : Int) * (P : Int))) ->
        forall Y X : Nat, 1 <= Y ->
          norm (Finset.sum ((Finset.Ico Y X).filter Nat.Prime)
            (fun p => HSMul.hSMul (1 / (p : Real)) (numeratorKernel D p))) <=
            C * (3 + Real.log ((4 * h * P : Nat) : Real)) ^ 2 *
              (Y : Real) ^ (-1 / 32 : Real)) := by
  let C : Real := Classical.choose QRH.exists_primeCharacter_reciprocal_tail_bound
  have hSpec := Classical.choose_spec QRH.exists_primeCharacter_reciprocal_tail_bound
  refine Exists.intro C (And.intro hSpec.1 ?_)
  intro h P hh hP hP2 hhP D hSign Y X hY
  have hAbs : D.natAbs = h * P := by
    cases hSign with
    | inl hs => simp only [hs, Int.natAbs_mul, Int.natAbs_natCast]
    | inr hs => simp only [hs, Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast]
  have hprod : 0 < h * P := Nat.mul_pos hh hP.pos
  have hD : Not (D = 0) := by
    intro hz
    rw [hz, Int.natAbs_zero] at hAbs
    omega
  have : NeZero (4 * D.natAbs) := NeZero.mk (by
    apply ne_of_gt
    apply Nat.mul_pos (by decide : 0 < (4 : Nat))
    rw [hAbs]
    exact hprod)
  have hlevel : 4 * D.natAbs = 4 * h * P := by rw [hAbs, Nat.mul_assoc]
  have hn := numerator_character_ne_one_at_prime_factor h P hh hP hP2 hhP D hD hSign
  have ht := hSpec.2 (numeratorCharacter D hD) hn Y X hY
  simpa only [numerator_character_natCast, hlevel] using ht

theorem exists_natural_height_joint_tail_bound :
    exists C : Real, And (0 < C)
      (forall h Q n : Nat, 0 < h -> 2 <= Q -> h < Q -> Q < n ->
        n + h <= Q * Q -> 0 < actualPacket (h : Int) Q n ->
        forall Y X : Nat, 1 <= Y ->
          norm (Finset.sum ((Finset.Ico Y X).filter Nat.Prime)
            (fun p => HSMul.hSMul (1 / (p : Real))
              (numeratorKernel (-((h : Int) * (n : Int))) p +
                numeratorKernel ((h : Int) * ((n + h : Nat) : Int)) p))) <=
            2 * C * (3 + Real.log ((4 * h * (Q * Q) : Nat) : Real)) ^ 2 *
              (Y : Real) ^ (-1 / 32 : Real)) := by
  let C : Real := Classical.choose exists_prime_factor_numerator_tail_bound
  have hSpec := Classical.choose_spec exists_prime_factor_numerator_tail_bound
  have hC : 0 < C := hSpec.1
  refine Exists.intro C (And.intro hC ?_)
  intro h Q n hh hQ hhQ hQn hnQ hpos Y X hY
  have hpair := FiniteFieldIntegerPrimes.actual_packet_positive_gives_prime_pair
    h Q n (by omega) hQn hnQ hpos
  have hBound (P : Nat) (hp : Nat.Prime P) (hp2 : 2 < P) (hhP : h < P)
      (hPQ : P <= Q * Q) (D : Int)
      (hSign : Or (D = (h : Int) * (P : Int)) (D = -((h : Int) * (P : Int)))) :
      norm (Finset.sum ((Finset.Ico Y X).filter Nat.Prime)
        (fun p => HSMul.hSMul (1 / (p : Real)) (numeratorKernel D p))) <=
        C * (3 + Real.log ((4 * h * (Q * Q) : Nat) : Real)) ^ 2 *
          (Y : Real) ^ (-1 / 32 : Real) := by
    have ht := hSpec.2 h P hh hp hp2 hhP D hSign Y X hY
    have hl : (4 * h * P : Nat) <= 4 * h * (Q * Q) :=
      Nat.mul_le_mul_left (4 * h) hPQ
    have hlpos : (0 : Real) < ((4 * h * P : Nat) : Real) := by
      exact_mod_cast Nat.mul_pos (Nat.mul_pos (by decide : 0 < (4 : Nat)) hh) hp.pos
    have hlone : (1 : Real) <= ((4 * h * P : Nat) : Real) := by
      have htN : 1 <= 4 * h * P := Nat.one_le_iff_ne_zero.mpr
        (ne_of_gt (Nat.mul_pos (Nat.mul_pos (by decide : 0 < (4 : Nat)) hh) hp.pos))
      exact_mod_cast htN
    have hlog := Real.log_le_log hlpos (Nat.cast_le.mpr hl)
    have hlow : 0 <= 3 + Real.log ((4 * h * P : Nat) : Real) := by
      have htL := Real.log_nonneg hlone
      linarith only [htL]
    have hsq : (3 + Real.log ((4 * h * P : Nat) : Real)) ^ 2 <=
        (3 + Real.log ((4 * h * (Q * Q) : Nat) : Real)) ^ 2 := by
      nlinarith only [hlog, hlow]
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq hC.le) (Real.rpow_nonneg (Nat.cast_nonneg Y) _))
  have hleft := hBound n hpair.1 (by omega) (by omega) (by omega)
    (-((h : Int) * (n : Int))) (Or.inr rfl)
  have hright := hBound (n + h) hpair.2 (by omega) (by omega) hnQ
    ((h : Int) * ((n + h : Nat) : Int)) (Or.inl rfl)
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib]
  calc
    _ <= _ := norm_add_le _ _
    _ <= _ := add_le_add hleft hright
    _ = _ := by ring


theorem power_cutoff_decay_le_one (L x : Real) (hL : 0 < L) (hcut : L ^ 64 <= x) :
    L ^ 2 * x ^ (-1 / 32 : Real) <= 1 := by
  have hid : L ^ 2 * (L ^ 64) ^ (-1 / 32 : Real) = 1 := by
    rw [<- Real.rpow_natCast L (64 : Nat), <- Real.rpow_mul hL.le]
    norm_num only [Nat.cast_ofNat]
    rw [<- Real.rpow_natCast L (2 : Nat), <- Real.rpow_add hL]
    norm_num
  calc
    _ <= L ^ 2 * (L ^ 64) ^ (-1 / 32 : Real) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (pow_pos hL 64) hcut (by norm_num)) (sq_nonneg L)
    _ = 1 := hid

theorem exists_natural_height_joint_tail_bounded :
    exists C : Real, And (0 < C)
      (forall h Q n : Nat, 0 < h -> 2 <= Q -> h < Q -> Q < n ->
        n + h <= Q * Q -> 0 < actualPacket (h : Int) Q n ->
        forall Y X : Nat, 1 <= Y ->
          (3 + Real.log ((4 * h * (Q * Q) : Nat) : Real)) ^ 64 <= (Y : Real) ->
          norm (Finset.sum ((Finset.Ico Y X).filter Nat.Prime)
            (fun p => HSMul.hSMul (1 / (p : Real))
              (numeratorKernel (-((h : Int) * (n : Int))) p +
                numeratorKernel ((h : Int) * ((n + h : Nat) : Int)) p))) <= 2 * C) := by
  let C : Real := Classical.choose exists_natural_height_joint_tail_bound
  have hSpec := Classical.choose_spec exists_natural_height_joint_tail_bound
  have hC : 0 < C := hSpec.1
  refine Exists.intro C (And.intro hC ?_)
  intro h Q n hh hQ hhQ hQn hnQ hpos Y X hY hcut
  have ht := hSpec.2 h Q n hh hQ hhQ hQn hnQ hpos Y X hY
  have hQN : 0 < Q := by omega
  have hlevel : 1 <= 4 * h * (Q * Q) := Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt (Nat.mul_pos (Nat.mul_pos (by decide : 0 < (4 : Nat)) hh)
      (Nat.mul_pos hQN hQN)))
  have hL : 0 < 3 + Real.log ((4 * h * (Q * Q) : Nat) : Real) := by
    have hlevelR : (1 : Real) <= ((4 * h * (Q * Q) : Nat) : Real) := by
      exact_mod_cast hlevel
    have hLog := Real.log_nonneg hlevelR
    linarith only [hLog]
  have hscale := power_cutoff_decay_le_one _ _ hL hcut
  calc
    _ <= 2 * C * (3 + Real.log ((4 * h * (Q * Q) : Nat) : Real)) ^ 2 *
        (Y : Real) ^ (-1 / 32 : Real) := ht
    _ = (2 * C) * ((3 + Real.log ((4 * h * (Q * Q) : Nat) : Real)) ^ 2 *
        (Y : Real) ^ (-1 / 32 : Real)) := by ring
    _ <= 2 * C := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale (by positivity : 0 <= 2 * C)

end PrimeFactorOscillations.FiniteFieldIntegerCharacter
