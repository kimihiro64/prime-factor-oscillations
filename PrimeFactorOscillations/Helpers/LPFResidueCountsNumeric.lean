/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPrimePrefixNumeric
import PrimeFactorOscillations.Helpers.LPFResidueCounts

/-!
# Numerical smooth-number and largest-factor residue bounds

The fifteen-sixteenths prime-prefix estimate gives the explicit coefficient
8388608 with saving y^(-1/16). Smooth counts retain their coprime centering;
the largest-factor full mean requires a y-smooth modulus. These bounds count
ordinary integers and do not assert distributions for generated states.
-/


set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def lpfNumericCharacterError (N X y : Nat) : Real :=
  8388608 * (X : Real) * (y : Real) ^ (-(1 / 16 : Real)) *
    (1 + Real.log N + Real.log ((X : Real) + 2)) ^ 2

theorem lpf_numeric_character_error_nonneg (N X y : Nat) :
    0 <= lpfNumericCharacterError N X y := by
  unfold lpfNumericCharacterError
  positivity

theorem lpf_uniform_character_bounds_numeric
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (hchi : Not (chi = 1)) (X y : Nat) (hX : 0 < X) (hy : 0 < y) :
    And
      (norm (Finset.sum (Nat.smoothNumbersUpTo X (y + 1))
        (fun n => chi (n : ZMod N))) <= (N : Real) + lpfNumericCharacterError N X y)
      (norm (Finset.sum ((Finset.Icc 1 X).filter
        (fun n => y < Nat.largestPrimeFactor n))
        (fun n => chi (Nat.largestPrimeFactor n : ZMod N))) <=
          lpfNumericCharacterError N X y) := by
  let B : Real := 262144
  have hB : 0 < B := by norm_num [B]
  let L : Real := 1 + Real.log N + Real.log ((X : Real) + 2)
  have hN := BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hNR : (1 : Real) <= (N : Real) := by exact_mod_cast (by omega : 1 <= N)
  have hLN := Real.log_nonneg hNR
  have hFrozen : 0 <= B * L ^ 2 := mul_nonneg hB.le (sq_nonneg L)
  have hPrefix : forall t, t <= X ->
      norm (Finset.sum (Nat.primesBelow (t + 1)) (fun p => chi (p : ZMod N))) <=
        (B * L ^ 2) * (t : Real) ^ (15 / 16 : Real) := by
    intro t ht
    have htR : (t : Real) <= (X : Real) := Nat.cast_le.mpr ht
    have hLog : Real.log ((t : Real) + 2) <= Real.log ((X : Real) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hLt : 0 <= Real.log ((t : Real) + 2) :=
      Real.log_nonneg (by have h : (0 : Real) <= (t : Real) := Nat.cast_nonneg t; linarith)
    have hLX : 0 <= Real.log ((X : Real) + 2) :=
      Real.log_nonneg (by have h : (0 : Real) <= (X : Real) := Nat.cast_nonneg X; linarith)
    have hSq : (1 + Real.log N + Real.log ((t : Real) + 2)) ^ 2 <= L ^ 2 := by
      dsimp [L]
      nlinarith
    calc
      _ <= B * (t : Real) ^ (15 / 16 : Real) *
          (1 + Real.log N + Real.log ((t : Real) + 2)) ^ 2 := QRH.lpf_primeCharacterSum_numeric chi hchi t
      _ <= B * (t : Real) ^ (15 / 16 : Real) * L ^ 2 :=
        mul_le_mul_of_nonneg_left hSq (mul_nonneg hB.le (Real.rpow_nonneg (Nat.cast_nonneg t) _))
      _ = (B * L ^ 2) * (t : Real) ^ (15 / 16 : Real) := by ring
  have hMul : forall m p : Nat, chi ((m * p : Nat) : ZMod N) =
      chi (m : ZMod N) * chi (p : ZMod N) := by
    intro m p
    simp only [Nat.cast_mul, map_mul]
  have hSmooth := Nat.norm_sum_smoothNumbersUpTo_le_rpow
    (fun n => chi (n : ZMod N)) hMul X y hX hy
    (15 / 16) (B * L ^ 2) (by norm_num) (by norm_num) hFrozen
    (fun m hm => chi.norm_le_one _) hPrefix
  have hLargest := Nat.norm_sum_largePrimeFactor_twist_le_rpow
    (fun n => chi (n : ZMod N)) X y hX hy
    (15 / 16) (B * L ^ 2) (by norm_num) (by norm_num) hFrozen hPrefix
  have hOrdinary := chi.norm_sum_Icc_le_modulus hchi X
  have hCoeff : (2 * (B * L ^ 2) / (1 - (15 / 16 : Real))) *
      (X : Real) * (y : Real) ^ ((15 / 16 : Real) - 1) =
      lpfNumericCharacterError N X y := by
    unfold lpfNumericCharacterError
    rw [show (15 / 16 : Real) - 1 = -(1 / 16 : Real) by norm_num]
    dsimp [B, L]
    norm_num <;> ring
  rw [hCoeff] at hSmooth hLargest
  exact And.intro (hSmooth.trans (_root_.add_le_add hOrdinary le_rfl)) hLargest


theorem lpf_uniform_residue_bounds_numeric :
    forall {N : Nat} [NeZero N] (a : Units (ZMod N)) (X y : Nat),
        0 < X -> 0 < y -> And
          (abs ((((Nat.smoothNumbersUpTo X (y + 1)).filter
              (fun (n : Nat) => (n : ZMod N) = (a : ZMod N))).card : Real) -
            (((Nat.smoothNumbersUpTo X (y + 1)).filter
              (fun n => Nat.Coprime n N)).card : Real) / (N.totient : Real)) <=
            (N : Real) + lpfNumericCharacterError N X y)
          (Nat.largestPrimeFactor N <= y ->
            abs (((((Finset.Icc 1 X).filter (fun n => y < Nat.largestPrimeFactor n)).filter
                (fun n => (Nat.largestPrimeFactor n : ZMod N) = (a : ZMod N))).card : Real) -
              ((X : Real) - ((Nat.smoothNumbersUpTo X (y + 1)).card : Real)) /
                (N.totient : Real)) <= lpfNumericCharacterError N X y) := by
  intro N inst a X y hX hy
  have hE := lpf_numeric_character_error_nonneg N X y
  refine And.intro ?_ ?_
  next =>
    have h := DirichletCharacter.abs_residue_count_sub_unit_mean_le
      (Nat.smoothNumbersUpTo X (y + 1)) (fun (n : Nat) => (n : ZMod N)) a
      ((N : Real) + lpfNumericCharacterError N X y) (add_nonneg (Nat.cast_nonneg N) hE)
      (fun chi hchi => (lpf_uniform_character_bounds_numeric chi hchi X y hX hy).1)
    simpa only [ZMod.isUnit_iff_coprime] using h
  next =>
    intro hN
    let S := (Finset.Icc 1 X).filter (fun n => y < Nat.largestPrimeFactor n)
    have h := DirichletCharacter.abs_residue_count_sub_unit_mean_le
      S (fun n => (Nat.largestPrimeFactor n : ZMod N)) a
      (lpfNumericCharacterError N X y) hE (fun chi hchi => (lpf_uniform_character_bounds_numeric chi hchi X y hX hy).2)
    have hSupport : S.filter (fun n => IsUnit (Nat.largestPrimeFactor n : ZMod N)) = S := by
      apply Finset.filter_eq_self.mpr
      intro n hn
      have hmem := Finset.mem_filter.mp hn
      exact Nat.isUnit_largestPrimeFactor_of_le_cutoff
        (Finset.mem_Icc.mp hmem.1).1 hN hmem.2
    rw [hSupport] at h
    have hPartition := Nat.card_smoothNumbersUpTo_add_largePrimeFactor X y hy
    have hReal : ((Nat.smoothNumbersUpTo X (y + 1)).card : Real) + (S.card : Real) =
        (X : Real) := by exact_mod_cast hPartition
    have hCenter : (S.card : Real) =
        (X : Real) - ((Nat.smoothNumbersUpTo X (y + 1)).card : Real) := by linarith
    rw [hCenter] at h
    exact h

end PrimeFactorOscillations.LPF
