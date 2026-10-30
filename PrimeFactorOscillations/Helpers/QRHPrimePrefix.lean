/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.QRHCharacterChebyshev
import PrimeFactorOscillations.Mathlib.NumberTheory.Chebyshev.WeightedPrimePower
import PrimeFactorOscillations.Mathlib.NumberTheory.PrimeCounting.WeightedPrefix

/-!
# Uniform seven-eighths bounds for prime-character prefixes

The higher prime powers are removed with their full square-root mass.
Finite partial summation then removes the logarithm without losing a power.
The final bound includes every natural endpoint, including zero and one.
Uniform reciprocal-prime tails are bounded after a polylogarithmic cutoff,
with one constant before the modulus and character. Finite Abel summation
retains both boundary terms.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

open BombieriVinogradov.SiegelWalfisz

noncomputable def characterPrimeLogSum {N : Nat} (x : Nat)
    (chi : DirichletCharacter Complex N) : Complex :=
  Finset.sum (Finset.Icc 1 x)
    (fun n => if Nat.Prime n then HSMul.hSMul (Real.log (n : Real)) (chi (n : ZMod N)) else 0)

theorem norm_characterPrimeLogSum_le_psi {N : Nat}
    (chi : DirichletCharacter Complex N) {x : Nat} (hx : 1 <= x) :
    norm (characterPrimeLogSum x chi) <= norm (characterChebyshevSum x chi) +
      2 * Real.sqrt (x : Real) * Real.log (x : Real) := by
  have h := Chebyshev.norm_weighted_primeLog_sum_le
    (fun n => chi (n : ZMod N)) x hx (fun n hn => chi.norm_le_one (n : ZMod N))
  have hId : Finset.sum (Finset.Icc 1 x)
      (fun n => ((if Nat.Prime n then Real.log (n : Real) else 0 : Real) : Complex) *
        chi (n : ZMod N)) = characterPrimeLogSum x chi := by
    unfold characterPrimeLogSum
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : Nat.Prime n
    next =>
      simp only [hp, if_pos]
      exact (Algebra.smul_def (Real.log (n : Real)) (chi (n : ZMod N))).symm
    next => simp [hp]
  rw [hId] at h
  exact h

theorem exists_characterPrimeLogSum_le_seven_eighths :
    exists A : Real, And (0 < A)
      (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        Not (chi = 1) -> forall {x : Nat}, 2 <= x ->
          norm (characterPrimeLogSum x chi) <=
            A * (x : Real) ^ (7 / 8 : Real) *
              (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2) := by
  let A : Real := Classical.choose exists_characterChebyshevSum_le_seven_eighths
  have hAAll := Classical.choose_spec exists_characterChebyshevSum_le_seven_eighths
  have hA : 0 < A := hAAll.1
  refine Exists.intro (A + 2) (And.intro (by positivity) ?_)
  intro N inst chi hchi x hx
  have hx1 : 1 <= x := by omega
  have hxR : (1 : Real) <= (x : Real) := by exact_mod_cast hx1
  have hN := BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hNR : (1 : Real) <= (N : Real) := by exact_mod_cast (by omega : 1 <= N)
  have hLN := Real.log_nonneg hNR
  have hLx := Real.log_nonneg hxR
  have hLx2 : 0 <= Real.log ((x : Real) + 2) := Real.log_nonneg (by linarith)
  have hLogs : Real.log x <= Real.log ((x : Real) + 2) :=
    Real.log_le_log (zero_lt_one.trans_le hxR) (by linarith)
  let L : Real := 1 + Real.log N + Real.log ((x : Real) + 2)
  have hL : 1 <= L := by dsimp [L]; linarith
  have hLog : Real.log x <= L ^ 2 := by
    have h : Real.log x <= L := by dsimp [L]; linarith
    nlinarith
  have hSqrt : Real.sqrt (x : Real) <= (x : Real) ^ (7 / 8 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hxR (by norm_num)
  have hError : 2 * Real.sqrt (x : Real) * Real.log x <=
      2 * (x : Real) ^ (7 / 8 : Real) * L ^ 2 := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hSqrt (by norm_num))
      hLog hLx (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg x) _))
  have hPsi := hAAll.2 chi hchi hx
  have hTheta := norm_characterPrimeLogSum_le_psi chi hx1
  change norm (characterPrimeLogSum x chi) <= (A + 2) * (x : Real) ^ (7 / 8 : Real) * L ^ 2
  change norm (characterChebyshevSum x chi) <= A * (x : Real) ^ (7 / 8 : Real) * L ^ 2 at hPsi
  nlinarith

theorem exists_primeCharacterSum_le_seven_eighths :
    exists B : Real, And (0 < B)
      (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        Not (chi = 1) -> forall x : Nat,
          norm (Finset.sum (Nat.primesBelow (x + 1)) (fun p => chi (p : ZMod N))) <=
            B * (x : Real) ^ (7 / 8 : Real) *
              (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2) := by
  let A : Real := Classical.choose exists_characterPrimeLogSum_le_seven_eighths
  have hAAll := Classical.choose_spec exists_characterPrimeLogSum_le_seven_eighths
  have hA : 0 < A := hAAll.1
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  refine Exists.intro (A / Real.log (2 : Real)) (And.intro (div_pos hA hLogTwo) ?_)
  intro N inst chi hchi x
  have hN := BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hNR : (1 : Real) <= (N : Real) := by exact_mod_cast (by omega : 1 <= N)
  have hLN := Real.log_nonneg hNR
  let L : Real := 1 + Real.log N + Real.log ((x : Real) + 2)
  have hLx2 : 0 <= Real.log ((x : Real) + 2) :=
    Real.log_nonneg (by have h : (0 : Real) <= (x : Real) := Nat.cast_nonneg x; linarith)
  have hL : 1 <= L := by dsimp [L]; linarith
  let M : Real := A * (x : Real) ^ (7 / 8 : Real) * L ^ 2
  have hM : 0 <= M := by dsimp [M]; positivity
  have hPrefixes : forall t, t <= x -> norm (characterPrimeLogSum t chi) <= M := by
    intro t htx
    by_cases ht : 2 <= t
    next =>
      have htR : (t : Real) <= (x : Real) := Nat.cast_le.mpr htx
      have hPow : (t : Real) ^ (7 / 8 : Real) <= (x : Real) ^ (7 / 8 : Real) :=
        Real.rpow_le_rpow (Nat.cast_nonneg t) htR (by norm_num)
      have hLog : Real.log ((t : Real) + 2) <= Real.log ((x : Real) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have hLt0 : 0 <= Real.log ((t : Real) + 2) :=
        Real.log_nonneg (by have h : (0 : Real) <= (t : Real) := Nat.cast_nonneg t; linarith)
      have hSq : (1 + Real.log N + Real.log ((t : Real) + 2)) ^ 2 <= L ^ 2 := by
        dsimp [L]
        nlinarith
      calc
        _ <= A * (t : Real) ^ (7 / 8 : Real) *
            (1 + Real.log N + Real.log ((t : Real) + 2)) ^ 2 := hAAll.2 chi hchi ht
        _ <= M := mul_le_mul (mul_le_mul_of_nonneg_left hPow hA.le) hSq (sq_nonneg _)
          (mul_nonneg hA.le (Real.rpow_nonneg (Nat.cast_nonneg x) _))
    next =>
      have hsmall : Or (t = 0) (t = 1) := by omega
      rcases hsmall with h0 | h1
      next => simpa [characterPrimeLogSum, h0] using hM
      next => simpa [characterPrimeLogSum, h1] using hM
  have h := Nat.norm_sum_primesBelow_le_of_weighted_prefix
    (fun p => chi (p : ZMod N)) x M hPrefixes
  calc
    _ <= M / Real.log (2 : Real) := h
    _ = (A / Real.log (2 : Real)) * (x : Real) ^ (7 / 8 : Real) *
        (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2 := by dsimp [M, L]; ring

theorem log_square_absorption (x : Real) (hx : 1 <= x) :
    (1 + Real.log x) ^ 2 <= 1089 * x ^ (1 / 16 : Real) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hr := Real.log_le_rpow_div (le_of_lt hx0) (by norm_num : (0 : Real) < 1 / 32)
  have hpow : 1 <= x ^ (1 / 32 : Real) :=
    Real.one_le_rpow hx (by norm_num)
  have hlog : 0 <= Real.log x := Real.log_nonneg hx
  have hlin : 1 + Real.log x <= 33 * x ^ (1 / 32 : Real) := by
    norm_num only [div_eq_mul_inv, inv_div, inv_one, mul_one] at hr
    linarith only [hr, hpow]
  have hsq := mul_self_le_mul_self (by linarith only [hlog] : 0 <= 1 + Real.log x) hlin
  have hid : (x ^ (1 / 32 : Real)) ^ 2 = x ^ (1 / 16 : Real) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (le_of_lt hx0)]
    norm_num
  nlinarith only [hsq, hid]

theorem successor_power_bound (x : Real) (hx : 1 <= x) :
    (x + 1) ^ (15 / 16 : Real) <= 2 * x ^ (15 / 16 : Real) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxn : 0 < x + 1 := by linarith only [hx]
  have hmono := Real.rpow_le_rpow_of_nonpos hx0
    (show x <= x + 1 by linarith) (by norm_num : (-1 / 16 : Real) <= 0)
  have hid (t : Real) (ht : 0 < t) :
      t ^ (15 / 16 : Real) = t * t ^ (-1 / 16 : Real) := by
    calc
      _ = t ^ ((1 : Real) + (-1 / 16 : Real)) := by norm_num
      _ = t ^ (1 : Real) * t ^ (-1 / 16 : Real) := Real.rpow_add ht _ _
      _ = _ := by rw [Real.rpow_one]
  calc
    _ = (x + 1) * (x + 1) ^ (-1 / 16 : Real) := hid _ hxn
    _ <= (x + 1) * x ^ (-1 / 16 : Real) :=
      mul_le_mul_of_nonneg_left hmono (le_of_lt hxn)
    _ <= (2 * x) * x ^ (-1 / 16 : Real) :=
      mul_le_mul_of_nonneg_right (by linarith only [hx]) (Real.rpow_nonneg (le_of_lt hx0) _)
    _ = _ := by rw [hid x hx0]; ring

theorem exists_primeCharacterSum_power_bound :
    exists C : Real, And (0 < C)
      (forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
        Not (chi = 1) -> forall x : Nat,
          norm (Finset.sum (Nat.primesBelow (x + 1)) (fun p => chi (p : ZMod q))) <=
            C * (3 + Real.log q) ^ 2 * (x : Real) ^ (15 / 16 : Real)) := by
  let B : Real := Classical.choose exists_primeCharacterSum_le_seven_eighths
  have hSpec := Classical.choose_spec exists_primeCharacterSum_le_seven_eighths
  have hB : 0 < B := hSpec.1
  refine Exists.intro (1089 * B) (And.intro (by positivity) ?_)
  intro q inst chi hchi x
  have hq := BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hqR : (1 : Real) <= (q : Real) := by exact_mod_cast (by omega : 1 <= q)
  have hlq : 0 <= Real.log q := Real.log_nonneg hqR
  by_cases hx : x = 0
  . subst x
    simp
  . have hxN : 1 <= x := by omega
    have hxR : (1 : Real) <= (x : Real) := by exact_mod_cast hxN
    have hx0 : 0 < (x : Real) := lt_of_lt_of_le zero_lt_one hxR
    have hlogx := Real.log_nonneg hxR
    have hlog3 : Real.log (3 : Real) <= 2 := by
      have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 3)
      norm_num at ht
      exact ht
    have hlog : Real.log ((x : Real) + 2) <= 2 + Real.log x := by
      calc
        _ <= Real.log (3 * (x : Real)) :=
          Real.log_le_log (by positivity) (by linarith only [hxR])
        _ = Real.log (3 : Real) + Real.log x := Real.log_mul (by norm_num) (ne_of_gt hx0)
        _ <= _ := by linarith only [hlog3]
    have hlin : 1 + Real.log q + Real.log ((x : Real) + 2) <=
        (3 + Real.log q) * (1 + Real.log x) := by
      nlinarith only [hlog, hlogx, mul_nonneg hlq hlogx]
    have hlo : 0 <= 1 + Real.log q + Real.log ((x : Real) + 2) := by
      have ht := Real.log_nonneg (show 1 <= (x : Real) + 2 by linarith only [hxR])
      linarith only [hlq, ht]
    have hsq := mul_self_le_mul_self hlo hlin
    have habs := log_square_absorption (x : Real) hxR
    have hlogs : (1 + Real.log q + Real.log ((x : Real) + 2)) ^ 2 <=
        (3 + Real.log q) ^ 2 * (1089 * (x : Real) ^ (1 / 16 : Real)) := by
      nlinarith only [hsq, mul_le_mul_of_nonneg_left habs (sq_nonneg (3 + Real.log q))]
    have hid : (x : Real) ^ (7 / 8 : Real) * (x : Real) ^ (1 / 16 : Real) =
        (x : Real) ^ (15 / 16 : Real) := by
      rw [<- Real.rpow_add hx0]
      norm_num
    calc
      _ <= B * (x : Real) ^ (7 / 8 : Real) *
          (1 + Real.log q + Real.log ((x : Real) + 2)) ^ 2 := hSpec.2 chi hchi x
      _ <= B * (x : Real) ^ (7 / 8 : Real) *
          ((3 + Real.log q) ^ 2 * (1089 * (x : Real) ^ (1 / 16 : Real))) :=
        mul_le_mul_of_nonneg_left hlogs (by positivity)
      _ = _ := by rw [show B * (x : Real) ^ (7 / 8 : Real) *
            ((3 + Real.log q) ^ 2 * (1089 * (x : Real) ^ (1 / 16 : Real))) =
          (1089 * B) * (3 + Real.log q) ^ 2 *
            ((x : Real) ^ (7 / 8 : Real) * (x : Real) ^ (1 / 16 : Real)) by ring, hid]


noncomputable def harmonicTailBudget : Real :=
  3 + 2 * (tsum fun n : Nat => (n : Real) ^ (-33 / 32 : Real))

theorem harmonic_tail_budget_pos : 0 < harmonicTailBudget := by
  have ht : 0 <= tsum (fun n : Nat => (n : Real) ^ (-33 / 32 : Real)) :=
    tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  dsimp [harmonicTailBudget]
  linarith only [ht]

theorem reciprocal_power_identity (x : Real) (hx : 0 < x) :
    x ^ (15 / 16 : Real) / x = x ^ (-1 / 16 : Real) := by
  calc
    _ = x ^ (15 / 16 : Real) / x ^ (1 : Real) := by rw [Real.rpow_one]
    _ = x ^ ((15 / 16 : Real) - 1) := (Real.rpow_sub hx _ _).symm
    _ = _ := by norm_num

theorem inverse_square_power_identity (x : Real) (hx : 0 < x) :
    x ^ (-2 : Real) * x ^ (15 / 16 : Real) = x ^ (-17 / 16 : Real) := by
  rw [<- Real.rpow_add hx]
  norm_num

theorem reciprocal_step_bound (x : Real) (hx : 1 <= x) :
    abs (1 / (x + 1) - 1 / x) <= x ^ (-2 : Real) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx1 : 0 < x + 1 := by linarith only [hx]
  have hanti : 1 / (x + 1) <= 1 / x :=
    one_div_le_one_div_of_le hx0 (by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr hanti), neg_sub]
  have hid : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
    field_simp
    ring
  rw [hid]
  calc
    _ <= 1 / x ^ 2 := one_div_le_one_div_of_le (pow_pos hx0 2) (by nlinarith only [hx0])
    _ = _ := by
      rw [show (-2 : Real) = -(2 : Real) by norm_num, Real.rpow_neg (le_of_lt hx0)]
      norm_num only [Real.rpow_ofNat, one_div]

theorem norm_reciprocal_Ico_le_of_power_prefix
    (f : Nat -> Complex) (C : Real) (hC : 0 <= C)
    (hp : forall n : Nat, norm (Finset.sum (Finset.range n) f) <=
      C * (n : Real) ^ (15 / 16 : Real))
    (Y X : Nat) (hY : 1 <= Y) :
    norm (Finset.sum (Finset.Ico Y X) (fun n => HSMul.hSMul (1 / (n : Real)) (f n))) <=
      harmonicTailBudget * C * (Y : Real) ^ (-1 / 32 : Real) := by
  have hYreal : (1 : Real) <= (Y : Real) := by exact_mod_cast hY
  have hY0 : 0 < (Y : Real) := lt_of_lt_of_le zero_lt_one hYreal
  have hdecay : (Y : Real) ^ (-1 / 16 : Real) <= (Y : Real) ^ (-1 / 32 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hYreal (by norm_num)
  have hT : 0 <= harmonicTailBudget := le_of_lt harmonic_tail_budget_pos
  by_cases hYX : Y < X
  . have hXm : Y <= X - 1 := by omega
    have hXmR : (Y : Real) <= ((X - 1 : Nat) : Real) := Nat.cast_le.mpr hXm
    have hXm1 : (1 : Real) <= ((X - 1 : Nat) : Real) := hYreal.trans hXmR
    have hXm0 : 0 < ((X - 1 : Nat) : Real) := lt_of_lt_of_le zero_lt_one hXm1
    have hcast : (X : Real) = ((X - 1 : Nat) : Real) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : 1 <= X)).symm
    have hlast :
        norm (HSMul.hSMul (1 / ((X - 1 : Nat) : Real))
          (Finset.sum (Finset.range X) f)) <=
        2 * C * (Y : Real) ^ (-1 / 32 : Real) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hXm0)]
      calc
        _ <= (1 / ((X - 1 : Nat) : Real)) * (C * (X : Real) ^ (15 / 16 : Real)) :=
          mul_le_mul_of_nonneg_left (hp X) (by positivity)
        _ <= (1 / ((X - 1 : Nat) : Real)) *
            (C * (2 * ((X - 1 : Nat) : Real) ^ (15 / 16 : Real))) := by
          apply mul_le_mul_of_nonneg_left
          . exact mul_le_mul_of_nonneg_left (by rw [hcast]; exact successor_power_bound _ hXm1) hC
          . positivity
        _ = 2 * C * ((X - 1 : Nat) : Real) ^ (-1 / 16 : Real) := by
          rw [show (1 / ((X - 1 : Nat) : Real)) *
                (C * (2 * ((X - 1 : Nat) : Real) ^ (15 / 16 : Real))) =
              2 * C * (((X - 1 : Nat) : Real) ^ (15 / 16 : Real) /
                ((X - 1 : Nat) : Real)) by ring,
            reciprocal_power_identity _ hXm0]
        _ <= 2 * C * (Y : Real) ^ (-1 / 16 : Real) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hY0 hXmR (by norm_num)) (by positivity)
        _ <= _ := mul_le_mul_of_nonneg_left hdecay (by positivity)
    have hfirst :
        norm (HSMul.hSMul (1 / (Y : Real)) (Finset.sum (Finset.range Y) f)) <=
        C * (Y : Real) ^ (-1 / 32 : Real) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hY0)]
      calc
        _ <= (1 / (Y : Real)) * (C * (Y : Real) ^ (15 / 16 : Real)) :=
          mul_le_mul_of_nonneg_left (hp Y) (by positivity)
        _ = C * (Y : Real) ^ (-1 / 16 : Real) := by
          rw [show (1 / (Y : Real)) * (C * (Y : Real) ^ (15 / 16 : Real)) =
            C * ((Y : Real) ^ (15 / 16 : Real) / (Y : Real)) by ring,
            reciprocal_power_identity _ hY0]
        _ <= _ := mul_le_mul_of_nonneg_left hdecay hC
    have hterm (i : Nat) (hi : Membership.mem (Finset.Ico Y (X - 1)) i) :
        norm (HSMul.hSMul (1 / ((i + 1 : Nat) : Real) - 1 / (i : Real))
          (Finset.sum (Finset.range (i + 1)) f)) <=
        2 * C * (Y : Real) ^ (-1 / 32 : Real) * (i : Real) ^ (-33 / 32 : Real) := by
      have hiY := (Finset.mem_Ico.mp hi).1
      have hiYR : (Y : Real) <= (i : Real) := Nat.cast_le.mpr hiY
      have hi1 : (1 : Real) <= (i : Real) := hYreal.trans hiYR
      have hi0 : 0 < (i : Real) := lt_of_lt_of_le zero_lt_one hi1
      rw [norm_smul, Real.norm_eq_abs]
      have hpow := successor_power_bound (i : Real) hi1
      have hpre := hp (i + 1)
      simp only [Nat.cast_add, Nat.cast_one] at hpre
      calc
        _ <= (i : Real) ^ (-2 : Real) * (C * (2 * (i : Real) ^ (15 / 16 : Real))) := by
          apply mul_le_mul
          . simpa only [Nat.cast_add, Nat.cast_one] using reciprocal_step_bound (i : Real) hi1
          . exact hpre.trans (mul_le_mul_of_nonneg_left hpow hC)
          . exact norm_nonneg _
          . exact Real.rpow_nonneg (Nat.cast_nonneg i) _
        _ = 2 * C * (i : Real) ^ (-17 / 16 : Real) := by
          rw [show (i : Real) ^ (-2 : Real) * (C * (2 * (i : Real) ^ (15 / 16 : Real))) =
            2 * C * ((i : Real) ^ (-2 : Real) * (i : Real) ^ (15 / 16 : Real)) by ring,
            inverse_square_power_identity _ hi0]
        _ = 2 * C * ((i : Real) ^ (-1 / 32 : Real) * (i : Real) ^ (-33 / 32 : Real)) := by
          rw [<- Real.rpow_add hi0]
          norm_num
        _ <= _ := by
          have hdec := Real.rpow_le_rpow_of_nonpos hY0 hiYR (by norm_num : (-1 / 32 : Real) <= 0)
          calc
            _ <= 2 * C * ((Y : Real) ^ (-1 / 32 : Real) * (i : Real) ^ (-33 / 32 : Real)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hdec
                  (Real.rpow_nonneg (Nat.cast_nonneg i) (-33 / 32 : Real))) (by positivity)
            _ = _ := by ring
    have hsum : Finset.sum (Finset.Ico Y (X - 1))
        (fun i => norm (HSMul.hSMul (1 / ((i + 1 : Nat) : Real) - 1 / (i : Real))
          (Finset.sum (Finset.range (i + 1)) f))) <=
        2 * C * (Y : Real) ^ (-1 / 32 : Real) *
          (tsum fun i : Nat => (i : Real) ^ (-33 / 32 : Real)) := by
      calc
        _ <= Finset.sum (Finset.Ico Y (X - 1)) (fun i =>
            2 * C * (Y : Real) ^ (-1 / 32 : Real) * (i : Real) ^ (-33 / 32 : Real)) :=
          Finset.sum_le_sum hterm
        _ = 2 * C * (Y : Real) ^ (-1 / 32 : Real) *
            Finset.sum (Finset.Ico Y (X - 1)) (fun i => (i : Real) ^ (-33 / 32 : Real)) :=
          (Finset.mul_sum _ _ _).symm
        _ <= _ := by
          apply mul_le_mul_of_nonneg_left
          . apply Summable.sum_le_tsum
            . intro i hi
              exact Real.rpow_nonneg (Nat.cast_nonneg i) _
            . exact Real.summable_nat_rpow.mpr (by norm_num)
          . positivity
    rw [Finset.sum_Ico_by_parts (fun i => 1 / (i : Real)) f hYX]
    calc
      _ <= (norm (HSMul.hSMul (1 / ((X - 1 : Nat) : Real))
            (Finset.sum (Finset.range X) f)) +
          norm (HSMul.hSMul (1 / (Y : Real)) (Finset.sum (Finset.range Y) f))) +
          Finset.sum (Finset.Ico Y (X - 1)) (fun i =>
            norm (HSMul.hSMul (1 / ((i + 1 : Nat) : Real) - 1 / (i : Real))
              (Finset.sum (Finset.range (i + 1)) f))) :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sum_le _ _))
      _ <= (2 * C * (Y : Real) ^ (-1 / 32 : Real) +
          C * (Y : Real) ^ (-1 / 32 : Real)) +
          2 * C * (Y : Real) ^ (-1 / 32 : Real) *
            (tsum fun i : Nat => (i : Real) ^ (-33 / 32 : Real)) :=
        add_le_add (add_le_add hlast hfirst) hsum
      _ = _ := by dsimp [harmonicTailBudget]; ring
  . have hEmpty : Finset.Ico Y X = (EmptyCollection.emptyCollection : Finset Nat) :=
      Finset.Ico_eq_empty_of_le (by omega)
    simp only [hEmpty, Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg hT hC) (Real.rpow_nonneg (Nat.cast_nonneg Y) _)


/-- Uniform reciprocal-prime cancellation, with the modulus chosen after the constant. -/
theorem exists_primeCharacter_reciprocal_tail_bound :
    exists C : Real, And (0 < C)
      (forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
        Not (chi = 1) -> forall Y X : Nat, 1 <= Y ->
          norm (Finset.sum ((Finset.Ico Y X).filter Nat.Prime)
            (fun p => HSMul.hSMul (1 / (p : Real)) (chi (p : ZMod q)))) <=
            C * (3 + Real.log q) ^ 2 * (Y : Real) ^ (-1 / 32 : Real)) := by
  let A : Real := Classical.choose exists_primeCharacterSum_power_bound
  have hSpec := Classical.choose_spec exists_primeCharacterSum_power_bound
  have hA : 0 < A := hSpec.1
  refine Exists.intro (harmonicTailBudget * A)
    (And.intro (mul_pos harmonic_tail_budget_pos hA) ?_)
  intro q inst chi hchi Y X hY
  let f : Nat -> Complex := fun n => if Nat.Prime n then chi (n : ZMod q) else 0
  have hp (n : Nat) : norm (Finset.sum (Finset.range n) f) <=
      (A * (3 + Real.log q) ^ 2) * (n : Real) ^ (15 / 16 : Real) := by
    cases n with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
        positivity
    | succ m =>
        have hid : Finset.sum (Finset.range (m + 1)) f =
            Finset.sum (Nat.primesBelow (m + 1)) (fun p => chi (p : ZMod q)) := by
          unfold Nat.primesBelow
          rw [Finset.sum_filter]
        rw [hid]
        calc
          _ <= A * (3 + Real.log q) ^ 2 * (m : Real) ^ (15 / 16 : Real) :=
            hSpec.2 chi hchi m
          _ <= _ := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast Nat.le_succ m)
              (by norm_num)) (by positivity)
  have h := norm_reciprocal_Ico_le_of_power_prefix f
    (A * (3 + Real.log q) ^ 2) (by positivity) hp Y X hY
  have hid :
      Finset.sum (Finset.Ico Y X) (fun n => HSMul.hSMul (1 / (n : Real)) (f n)) =
      Finset.sum ((Finset.Ico Y X).filter Nat.Prime)
        (fun p => HSMul.hSMul (1 / (p : Real)) (chi (p : ZMod q))) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hnP : Nat.Prime n
    . simp only [f, ite_eq_left hnP]
    . simp only [f, ite_eq_right hnP, smul_zero]
  rw [hid] at h
  convert h using 1
  ring

/-- Every nonprincipal character has a bounded harmonic tail after a polylogarithmic cutoff. -/
theorem exists_primeCharacter_reciprocal_tail_bounded :
    exists C : Real, And (0 < C)
      (forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
        Not (chi = 1) -> forall Y X : Nat, 1 <= Y ->
          (3 + Real.log q) ^ 64 <= (Y : Real) ->
          norm (Finset.sum ((Finset.Ico Y X).filter Nat.Prime)
            (fun p => HSMul.hSMul (1 / (p : Real)) (chi (p : ZMod q)))) <= C) := by
  let C : Real := Classical.choose exists_primeCharacter_reciprocal_tail_bound
  have hSpec := Classical.choose_spec exists_primeCharacter_reciprocal_tail_bound
  have hC : 0 < C := hSpec.1
  refine Exists.intro C (And.intro hC ?_)
  intro q inst chi hchi Y X hY hCut
  have hq := BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hqR : (1 : Real) <= (q : Real) := by exact_mod_cast (by omega : 1 <= q)
  have hH : 0 < 3 + Real.log q := by
    have ht := Real.log_nonneg hqR
    linarith only [ht]
  have hid : (3 + Real.log q) ^ 2 *
      ((3 + Real.log q) ^ 64) ^ (-1 / 32 : Real) = 1 := by
    rw [<- Real.rpow_natCast (3 + Real.log q) (64 : Nat),
      <- Real.rpow_mul (le_of_lt hH)]
    norm_num only [Nat.cast_ofNat]
    rw [<- Real.rpow_natCast (3 + Real.log q) (2 : Nat), <- Real.rpow_add hH]
    norm_num
  have hscale : (3 + Real.log q) ^ 2 * (Y : Real) ^ (-1 / 32 : Real) <= 1 := by
    calc
      _ <= (3 + Real.log q) ^ 2 *
          ((3 + Real.log q) ^ 64) ^ (-1 / 32 : Real) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (pow_pos hH 64) hCut (by norm_num)) (sq_nonneg _)
      _ = 1 := hid
  calc
    _ <= C * (3 + Real.log q) ^ 2 * (Y : Real) ^ (-1 / 32 : Real) :=
      hSpec.2 chi hchi Y X hY
    _ = C * ((3 + Real.log q) ^ 2 * (Y : Real) ^ (-1 / 32 : Real)) := by ring
    _ <= C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale hC.le

end PrimeFactorOscillations.QRH
