/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMajorCharacterNumeric
import PrimeFactorOscillations.Helpers.QRHPrimeRows

/-!
# Numerical prime prefixes and all largest-prime-factor rows

Remove higher prime powers, use exact finite partial summation, and take the
difference of two prime prefixes. The respective coefficients are 131072,
262144, and 524288, uniformly in the modulus, nonprincipal character and row.
Small endpoints are handled explicitly. The reusable transports retain their
input hypotheses; the final three bounds consume the proved Chebyshev bound.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

theorem lpf_characterPrimeLogSum_trivial {N : Nat}
    (chi : DirichletCharacter Complex N) {x : Nat} (hx : 1 <= x) :
    norm (characterPrimeLogSum x chi) <= (x : Real) * Real.log (x : Real) := by
  have hX : 1 <= (x : Real) := by exact_mod_cast hx
  have hLogX : 0 <= Real.log (x : Real) := Real.log_nonneg hX
  have hEach : forall n, Membership.mem (Finset.Icc 1 x) n ->
      norm (if Nat.Prime n then
        HSMul.hSMul (Real.log (n : Real)) (chi (n : ZMod N)) else 0) <=
      Real.log (x : Real) := by
    intro n hn
    have hRange := Finset.mem_Icc.mp hn
    have hN : 1 <= (n : Real) := by exact_mod_cast hRange.1
    have hLogN : 0 <= Real.log (n : Real) := Real.log_nonneg hN
    have hLog := Real.log_le_log (zero_lt_one.trans_le hN)
      (show (n : Real) <= (x : Real) by exact_mod_cast hRange.2)
    by_cases hp : Nat.Prime n
    next =>
      rw [if_pos hp, norm_smul, Real.norm_eq_abs, abs_of_nonneg hLogN]
      nlinarith [chi.norm_le_one (n : ZMod N)]
    next => simpa only [if_neg hp, norm_zero] using hLogX
  calc
    _ <= Finset.sum (Finset.Icc 1 x) (fun n =>
        norm (if Nat.Prime n then
          HSMul.hSMul (Real.log (n : Real)) (chi (n : ZMod N)) else 0)) :=
      norm_sum_le _ _
    _ <= Finset.sum (Finset.Icc 1 x) (fun _ => Real.log (x : Real)) :=
      Finset.sum_le_sum hEach
    _ = _ := by simp

theorem lpf_characterPrimeLogSum_numeric_of_chebyshev
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hchi : Not (chi = 1))
    (hPsi : forall x : Nat, 4 <= x ->
      norm (BombieriVinogradov.SiegelWalfisz.characterChebyshevSum x chi) <=
        65536 * (x : Real) ^ (15 / 16 : Real) *
          (1 + Real.log (N : Real) + Real.log ((x : Real) + 2)) ^ 2)
    {x : Nat} (hx : 2 <= x) :
    norm (characterPrimeLogSum x chi) <=
      131072 * (x : Real) ^ (15 / 16 : Real) *
        (1 + Real.log (N : Real) + Real.log ((x : Real) + 2)) ^ 2 := by
  have hx1 : 1 <= x := by omega
  have hxR : 1 <= (x : Real) := by exact_mod_cast hx1
  have hNR : 1 <= (N : Real) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hLN := Real.log_nonneg hNR
  have hLx := Real.log_nonneg hxR
  have hLx2 : 0 <= Real.log ((x : Real) + 2) := Real.log_nonneg (by linarith)
  have hLogs : Real.log (x : Real) <= Real.log ((x : Real) + 2) :=
    Real.log_le_log (zero_lt_one.trans_le hxR) (by linarith)
  let L : Real := 1 + Real.log (N : Real) + Real.log ((x : Real) + 2)
  let R : Real := (x : Real) ^ (15 / 16 : Real)
  have hL : 1 <= L := by dsimp [L]; linarith
  have hL2 : 1 <= L ^ 2 := by nlinarith
  have hR : 1 <= R := Real.one_le_rpow hxR (by norm_num)
  have hUnit : 1 <= R * L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hL2)]
  change norm (characterPrimeLogSum x chi) <= 131072 * R * L ^ 2
  by_cases hx4 : 4 <= x
  next =>
    have hLog : Real.log (x : Real) <= L ^ 2 := by
      have h : Real.log (x : Real) <= L := by dsimp [L]; linarith
      nlinarith
    have hSqrt : Real.sqrt (x : Real) <= R := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hxR (by norm_num)
    have hError : 2 * Real.sqrt (x : Real) * Real.log (x : Real) <= 2 * R * L ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hSqrt (by norm_num)) hLog hLx
        (by positivity)
    have hPsi' := hPsi x hx4
    have hTheta := norm_characterPrimeLogSum_le_psi chi hx1
    change norm (BombieriVinogradov.SiegelWalfisz.characterChebyshevSum x chi) <=
      65536 * R * L ^ 2 at hPsi'
    nlinarith
  next =>
    have hSmall : (x : Real) <= 3 := by exact_mod_cast (show x <= 3 by omega)
    have hLogSmall : Real.log (x : Real) <= 3 := by
      have h := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hxR)
      linarith
    have hTrivial := lpf_characterPrimeLogSum_trivial chi hx1
    have hNine : (x : Real) * Real.log (x : Real) <= 9 := by
      convert mul_le_mul hSmall hLogSmall hLx (by norm_num : (0 : Real) <= 3) using 1 <;> norm_num
    nlinarith

theorem lpf_primeCharacterSum_of_weighted_bound
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (C delta : Real) (hC : 0 <= C) (hDelta : 0 <= delta)
    (hTheta : forall {t : Nat}, 2 <= t ->
      norm (characterPrimeLogSum t chi) <= C * (t : Real) ^ delta *
        (1 + Real.log (N : Real) + Real.log ((t : Real) + 2)) ^ 2)
    (x : Nat) :
    norm (Finset.sum (Nat.primesBelow (x + 1)) (fun p => chi (p : ZMod N))) <=
      (C / Real.log (2 : Real)) * (x : Real) ^ delta *
        (1 + Real.log (N : Real) + Real.log ((x : Real) + 2)) ^ 2 := by
  have hNR : 1 <= (N : Real) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hLN := Real.log_nonneg hNR
  let L : Real := 1 + Real.log (N : Real) + Real.log ((x : Real) + 2)
  let E : Real := C * (x : Real) ^ delta * L ^ 2
  have hE : 0 <= E := by dsimp [E]; positivity
  have hPrefixes : forall t, t <= x -> norm (characterPrimeLogSum t chi) <= E := by
    intro t htx
    by_cases ht : 2 <= t
    next =>
      have htR : (t : Real) <= (x : Real) := Nat.cast_le.mpr htx
      have hPow : (t : Real) ^ delta <= (x : Real) ^ delta :=
        Real.rpow_le_rpow (Nat.cast_nonneg t) htR hDelta
      have hLog : Real.log ((t : Real) + 2) <= Real.log ((x : Real) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have hLt0 : 0 <= Real.log ((t : Real) + 2) := Real.log_nonneg
        (by have h : (0 : Real) <= (t : Real) := Nat.cast_nonneg t; linarith)
      have hLx0 : 0 <= Real.log ((x : Real) + 2) := Real.log_nonneg
        (by have h : (0 : Real) <= (x : Real) := Nat.cast_nonneg x; linarith)
      have hSq : (1 + Real.log (N : Real) + Real.log ((t : Real) + 2)) ^ 2 <= L ^ 2 := by
        dsimp [L]
        nlinarith
      exact (hTheta ht).trans (mul_le_mul
        (mul_le_mul_of_nonneg_left hPow hC) hSq (sq_nonneg _)
        (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg x) _)))
    next =>
      have hsmall : Or (t = 0) (t = 1) := by omega
      rcases hsmall with h0 | h1
      next => simpa [characterPrimeLogSum, h0] using hE
      next => simpa [characterPrimeLogSum, h1] using hE
  have h := Nat.norm_sum_primesBelow_le_of_weighted_prefix
    (fun p => chi (p : ZMod N)) x E hPrefixes
  calc
    _ <= E / Real.log (2 : Real) := h
    _ = _ := by dsimp [E, L]; ring

theorem lpf_prime_row_of_prefix_bound
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (C delta : Real) (hC : 0 <= C) (hDelta : 0 <= delta)
    (hPrefix : forall t : Nat,
      norm (Finset.sum (Nat.primesBelow (t + 1)) (fun r => chi (r : ZMod N))) <=
        C * (t : Real) ^ delta *
          (1 + Real.log (N : Real) + Real.log ((t : Real) + 2)) ^ 2)
    (X y m : Nat) :
    norm (Finset.sum (Nat.largestPrimeFactorRow X y m) (fun r => chi (r : ZMod N))) <=
      (2 * C) * (X : Real) ^ delta *
        (1 + Real.log (N : Real) + Real.log ((X : Real) + 2)) ^ 2 := by
  let E := C * (X : Real) ^ delta *
    (1 + Real.log (N : Real) + Real.log ((X : Real) + 2)) ^ 2
  have hN : 1 <= (N : Real) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hLN := Real.log_nonneg hN
  have hUniform : forall t, t <= X ->
      norm (Finset.sum (Nat.primesBelow (t + 1)) (fun r => chi (r : ZMod N))) <= E := by
    intro t ht
    have htX : (t : Real) <= (X : Real) := Nat.cast_le.mpr ht
    have hLog := Real.log_le_log (by positivity : 0 < (t : Real) + 2)
      (show (t : Real) + 2 <= (X : Real) + 2 by linarith)
    have hLt : 0 <= Real.log ((t : Real) + 2) := Real.log_nonneg
      (by have h : (0 : Real) <= (t : Real) := Nat.cast_nonneg t; linarith)
    have hLX : 0 <= Real.log ((X : Real) + 2) := Real.log_nonneg
      (by have h : (0 : Real) <= (X : Real) := Nat.cast_nonneg X; linarith)
    have hSq : (1 + Real.log (N : Real) + Real.log ((t : Real) + 2)) ^ 2 <=
        (1 + Real.log (N : Real) + Real.log ((X : Real) + 2)) ^ 2 := by nlinarith
    have hPow : (t : Real) ^ delta <= (X : Real) ^ delta :=
      Real.rpow_le_rpow (Nat.cast_nonneg t) htX hDelta
    exact (hPrefix t).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hPow hC) hSq (sq_nonneg _)
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg X) _)))
  have hRow := Nat.norm_sum_largestPrimeFactorRow_le (fun r => chi (r : ZMod N))
    (fun _ => E) X y m (fun _ _ _ => le_refl E) hUniform
  calc
    _ <= 2 * E := hRow
    _ = _ := by dsimp [E]; ring

theorem lpf_characterPrimeLogSum_numeric {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (hchi : Not (chi = 1))
    {x : Nat} (hx : 2 <= x) :
    norm (characterPrimeLogSum x chi) <=
      131072 * (x : Real) ^ (15 / 16 : Real) *
        (1 + Real.log (N : Real) + Real.log ((x : Real) + 2)) ^ 2 := by
  classical
  apply lpf_characterPrimeLogSum_numeric_of_chebyshev chi hchi _ hx
  intro t ht
  simpa only [if_neg hchi, sub_zero] using lpf_character_chebyshev_numeric chi ht

theorem lpf_primeCharacterSum_numeric {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (hchi : Not (chi = 1)) (x : Nat) :
    norm (Finset.sum (Nat.primesBelow (x + 1)) (fun p => chi (p : ZMod N))) <=
      262144 * (x : Real) ^ (15 / 16 : Real) *
        (1 + Real.log (N : Real) + Real.log ((x : Real) + 2)) ^ 2 := by
  have h := lpf_primeCharacterSum_of_weighted_bound chi 131072 (15 / 16)
    (by norm_num) (by norm_num) (fun ht => lpf_characterPrimeLogSum_numeric chi hchi ht) x
  have hLog : (1 / 2 : Real) <= Real.log (2 : Real) := by
    have hi := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < (2 : Real) ^ (-1 : Int))
    rw [zpow_neg_one, Real.log_inv] at hi
    norm_num at hi
    linarith
  have hLog0 : 0 < Real.log (2 : Real) := by linarith
  have hC : (131072 : Real) / Real.log (2 : Real) <= 262144 := by
    apply (mul_le_mul_iff_of_pos_right hLog0).mp
    have hCancel : ((131072 : Real) / Real.log (2 : Real)) * Real.log (2 : Real) = 131072 := by
      field_simp
    rw [hCancel]
    linarith
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Nat.cast_nonneg x) _))
    (sq_nonneg _))

theorem lpf_prime_row_numeric {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (hchi : Not (chi = 1))
    (X y m : Nat) :
    norm (Finset.sum (Nat.largestPrimeFactorRow X y m) (fun r => chi (r : ZMod N))) <=
      524288 * (X : Real) ^ (15 / 16 : Real) *
        (1 + Real.log (N : Real) + Real.log ((X : Real) + 2)) ^ 2 := by
  have h := lpf_prime_row_of_prefix_bound chi 262144 (15 / 16)
    (by norm_num) (by norm_num) (lpf_primeCharacterSum_numeric chi hchi) X y m
  simpa only [show (2 : Real) * 262144 = 524288 by norm_num] using h

end PrimeFactorOscillations.QRH

