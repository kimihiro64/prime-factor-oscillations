/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPrimeTargetFull

/-! # Uniform full prime-target moments at the prime-count scale -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

private theorem pow_mono_nonneg (a b : Real) (ha : 0 <= a) (hab : a <= b) (q : Nat) :
    a ^ q <= b ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (pow_nonneg (ha.trans hab) q)

private theorem cutoff_weight_le (M : Nat) (hM : 4 <= M)
    (hLog : 4 <= Real.log (M : Real)) (hLL : 1 <= Real.log (Real.log (M : Real))) :
    Finset.prod (primeTargetCutoff M) singularFactor <=
      (2 * Real.exp singularMertensBound) * Real.log (Real.log (M : Real)) := by
  let N := Nat.floor (Real.log (M : Real)) + 1
  have hFloor4 : 4 <= Nat.floor (Real.log (M : Real)) := Nat.le_floor hLog
  have hN2 : 2 <= N := by dsimp [N]; omega
  have hBound := singular_prime_product_le (primeTargetCutoff M) N hN2 (by
    intro p hp
    have h := (primeTargetCutoff_mem M p (by omega)).mp hp
    have hpFloor := Nat.le_floor h.2.2
    exact And.intro h.1 (And.intro (by omega) (by dsimp [N]; omega)))
  have hNPos : (0 : Real) < (N : Real) := by exact_mod_cast (show 0 < N by omega)
  have hNUpper : (N : Real) <= 2 * Real.log (M : Real) := by
    have hFloor := Nat.floor_le (show 0 <= Real.log (M : Real) by linarith)
    dsimp [N]
    push_cast
    linarith
  have hLogN : Real.log (N : Real) <= 2 * Real.log (Real.log (M : Real)) := by
    calc
      _ <= Real.log (2 * Real.log (M : Real)) := Real.log_le_log hNPos hNUpper
      _ = Real.log 2 + Real.log (Real.log (M : Real)) :=
        Real.log_mul (by norm_num) (by linarith)
      _ <= _ := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
        linarith
  calc
    _ <= Real.exp singularMertensBound * Real.log (N : Real) := hBound
    _ <= Real.exp singularMertensBound * (2 * Real.log (Real.log (M : Real))) :=
      mul_le_mul_of_nonneg_left hLogN (Real.exp_pos _).le
    _ = _ := by ring

private theorem cutoff_conductor_le (M : Nat) (hM : 4 <= M)
    (hLog : 4 <= Real.log (M : Real)) :
    (1 + Real.log ((Finset.prod (primeTargetCutoff M) (fun p => p) : Nat) : Real) +
      Real.log (((5 * M / 4 : Nat) : Real) + 2)) ^ 2 <= 64 * Real.log (M : Real) ^ 4 := by
  let N := Nat.floor (Real.log (M : Real))
  let D := Finset.prod (primeTargetCutoff M) (fun p => p)
  have hCut : forall p, Membership.mem (primeTargetCutoff M) p -> And (1 <= p) (p <= N) := by
    intro p hp
    have h := (primeTargetCutoff_mem M p (by omega)).mp hp
    exact And.intro (by omega) (Nat.le_floor h.2.2)
  have hDPos : 0 < D := Finset.prod_pos (fun p hp => by have h := (hCut p hp).1; omega)
  have hDLog0 : 0 <= Real.log (D : Real) := Real.log_nonneg (by
    exact_mod_cast (show 1 <= D by omega))
  have hDLog : Real.log (D : Real) <= 4 * Real.log (M : Real) ^ 2 := by
    have h := log_cutoff_product_le_square (primeTargetCutoff M) N hCut
    have hN : (N : Real) <= Real.log (M : Real) :=
      Nat.floor_le (show 0 <= Real.log (M : Real) by linarith)
    have hN0 : (0 : Real) <= (N : Real) := Nat.cast_nonneg N
    change Real.log (D : Real) <= _ at h
    nlinarith only [h, hN, hN0, hLog]
  have hX : ((5 * M / 4 : Nat) : Real) <= 2 * (M : Real) := by
    exact_mod_cast (show 5 * M / 4 <= 2 * M by omega)
  have hX0 : (0 : Real) <= ((5 * M / 4 : Nat) : Real) := Nat.cast_nonneg _
  have hMR : (4 : Real) <= (M : Real) := by exact_mod_cast hM
  have hXLog0 : 0 <= Real.log (((5 * M / 4 : Nat) : Real) + 2) :=
    Real.log_nonneg (by linarith)
  have hXLog : Real.log (((5 * M / 4 : Nat) : Real) + 2) <= 2 * Real.log (M : Real) := by
    calc
      _ <= Real.log (4 * (M : Real)) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 4 + Real.log (M : Real) := Real.log_mul (by norm_num) (by linarith)
      _ <= _ := by
        have h : Real.log 4 <= Real.log (M : Real) :=
          Real.log_le_log (by norm_num) hMR
        linarith
  have hA0 : 0 <= 1 + Real.log (D : Real) +
      Real.log (((5 * M / 4 : Nat) : Real) + 2) := by linarith
  have hA : 1 + Real.log (D : Real) + Real.log (((5 * M / 4 : Nat) : Real) + 2) <=
      8 * Real.log (M : Real) ^ 2 := by
    nlinarith only [hDLog, hXLog, hLog]
  change (1 + Real.log (D : Real) + Real.log (((5 * M / 4 : Nat) : Real) + 2)) ^ 2 <= _
  calc
    _ = (1 + Real.log (D : Real) + Real.log (((5 * M / 4 : Nat) : Real) + 2)) *
        (1 + Real.log (D : Real) + Real.log (((5 * M / 4 : Nat) : Real) + 2)) := by ring
    _ <= (8 * Real.log (M : Real) ^ 2) * (8 * Real.log (M : Real) ^ 2) :=
      mul_le_mul hA hA hA0 (by positivity)
    _ = _ := by ring

private theorem window_rpow_le (M : Nat) :
    ((5 * M / 4 : Nat) : Real) ^ (7 / 8 : Real) <=
      (2 : Real) ^ (7 / 8 : Real) * (M : Real) ^ (7 / 8 : Real) := by
  have hX : ((5 * M / 4 : Nat) : Real) <= 2 * (M : Real) := by
    exact_mod_cast (show 5 * M / 4 <= 2 * M by omega)
  calc
    _ <= (2 * (M : Real)) ^ (7 / 8 : Real) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hX (by norm_num)
    _ = _ := Real.mul_rpow (by norm_num) (Nat.cast_nonneg M)

private theorem eventually_error_scale_le_main :
    Filter.Eventually (fun M : Nat =>
      (M : Real) ^ (15 / 16 : Real) <= (M : Real) / Real.log (M : Real)) Filter.atTop := by
  have hNat : Filter.Tendsto (fun M : Nat => (M : Real)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hBudget := hNat.eventually (eventually_complete_moment_error_log_power_le 1 1 (by norm_num))
  have hLL := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hNat)).eventually
    (Filter.eventually_ge_atTop (1 : Real))
  filter_upwards [hBudget, hLL, Filter.eventually_ge_atTop (2 : Nat)] with M hBudget hLL hM
  change 1 <= Real.log (Real.log (M : Real)) at hLL
  have hMpos : (0 : Real) < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  have hLog : 0 < Real.log (M : Real) := Real.log_pos (by
    exact_mod_cast (show 1 < M by omega))
  have h := hBudget 0 (by norm_num; linarith)
  simp only [one_mul, pow_one, pow_zero, mul_one] at h
  have hScaled := mul_le_mul_of_nonneg_right h
    (Real.rpow_nonneg hMpos.le (1 / 16 : Real))
  have hLeft : ((M : Real) ^ (7 / 8 : Real) * Real.log (M : Real)) *
      (M : Real) ^ (1 / 16 : Real) =
      (M : Real) ^ (15 / 16 : Real) * Real.log (M : Real) := by
    calc
      _ = ((M : Real) ^ (7 / 8 : Real) * (M : Real) ^ (1 / 16 : Real)) *
          Real.log (M : Real) := by ring
      _ = _ := by rw [<- Real.rpow_add hMpos]; norm_num
  have hRight : (M : Real) ^ (15 / 16 : Real) * (M : Real) ^ (1 / 16 : Real) =
      (M : Real) := by rw [<- Real.rpow_add hMpos]; norm_num
  rw [hLeft, hRight] at hScaled
  have hDivide := div_le_div_of_nonneg_right hScaled hLog.le
  have hCancel : ((M : Real) ^ (15 / 16 : Real) * Real.log (M : Real)) /
      Real.log (M : Real) = (M : Real) ^ (15 / 16 : Real) := by field_simp
  rw [hCancel] at hDivide
  exact hDivide

private theorem nine_le_pow (q : Nat) (hq : 1 <= q) : (9 : Real) <= 9 ^ q := by
  cases q with
  | zero => omega
  | succ k =>
    have h := pow_mono_nonneg 1 9 (by norm_num) (by norm_num) k
    simp only [one_pow] at h
    rw [pow_succ]
    linarith

/-- The full prime-target moment, uniformly in r and in growing moment order q. -/
theorem exists_uniform_primeTarget_moment :
    exists C0 : Real, And (0 < C0)
      (Filter.Eventually (fun M : Nat => forall r q : Nat,
        Membership.mem (nextPrimeWindow M) r -> 1 <= q ->
        (q : Real) <= 10 * Real.log (Real.log (M : Real)) ->
        Finset.sum ((nextPrimeWindow M).erase r) (fun s =>
          singularDivisorProduct (primeTargetSeparation r s) ^ q) <=
          ((M : Real) / Real.log (M : Real)) *
            (C0 * Real.log ((q : Real) + 2)) ^ q) Filter.atTop) := by
  classical
  let C : Real := Classical.choose exists_primeTarget_full_finite_bound
  have hC := Classical.choose_spec exists_primeTarget_full_finite_bound
  have hCpos : 0 < C := hC.1
  let K : Real := 2 * Real.exp 4
  let A0 : Real := 2 * Real.exp (singularMertensBound + 12)
  let A : Real := K * A0
  let W : Real := K * (2 * Real.exp singularMertensBound)
  let E0 : Real := C * 64 * (2 : Real) ^ (7 / 8 : Real)
  let B : Real := E0 + W + 1
  let Aplus : Real := A + 1 / Real.log 2
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hA0pos : 0 < A0 := by dsimp [A0]; positivity
  have hApos : 0 < A := mul_pos hKpos hA0pos
  have hWpos : 0 < W := by dsimp [W]; positivity
  have hE0pos : 0 < E0 := by dsimp [E0]; positivity
  have hBpos : 0 < B := by dsimp [B]; linarith
  have hE0B : E0 <= B := by dsimp [B]; linarith
  have hWB : W <= B := by dsimp [B]; linarith
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hAplus : A <= Aplus := by
    have hInv : 0 <= 1 / Real.log 2 := one_div_nonneg.mpr hLogTwo.le
    dsimp [Aplus]
    linarith only [hInv]
  have hAplusPos : 0 < Aplus := hApos.trans_le hAplus
  refine Exists.intro (9 * Aplus) (And.intro (mul_pos (by norm_num) hAplusPos) ?_)
  have hNat : Filter.Tendsto (fun M : Nat => (M : Real)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hLogEvent := (Real.tendsto_log_atTop.comp hNat).eventually
    (Filter.eventually_ge_atTop (4 : Real))
  have hLLEvent := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hNat)).eventually
    (Filter.eventually_ge_atTop (1 : Real))
  have hErrorEvent := hNat.eventually (eventually_complete_moment_error_log_power_le 4 B hBpos)
  filter_upwards [Filter.eventually_ge_atTop (4 : Nat), hLogEvent, hLLEvent,
    eventually_nextPrimeWindow_card_le, hErrorEvent, eventually_error_scale_le_main]
    with M hM hLog hLL hCard hError hScale
  change 4 <= Real.log (M : Real) at hLog
  change 1 <= Real.log (Real.log (M : Real)) at hLL
  intro r q hr hq hqMax
  let X : Nat := 5 * M / 4
  let F : Real := Finset.prod (primeTargetCutoff M) singularFactor
  let J : Real := 1 + Real.log ((Finset.prod (primeTargetCutoff M) (fun p => p) : Nat) : Real) +
    Real.log ((X : Real) + 2)
  let U : Real := (M : Real) / Real.log (M : Real)
  let T : Real := Real.log ((q : Real) + 2)
  have hM0 : (0 : Real) <= (M : Real) := Nat.cast_nonneg M
  have hLogPos : 0 < Real.log (M : Real) := by linarith
  have hLL0 : 0 <= Real.log (Real.log (M : Real)) := by linarith
  have hU0 : 0 <= U := div_nonneg hM0 hLogPos.le
  have hq0 : (0 : Real) <= (q : Real) := Nat.cast_nonneg q
  have hTpos : 0 < T := Real.log_pos (by linarith)
  have hTTwo : Real.log 2 <= T := Real.log_le_log (by norm_num) (by linarith)
  have hF0 : 0 <= F := by
    apply Finset.prod_nonneg
    intro p hp
    have hc := (primeTargetCutoff_mem M p (by omega)).mp hp
    have h := singular_moment_weight_nonneg p 1 (by omega)
    simp only [pow_one] at h
    linarith
  have hFull := hC.2 M r q hM hLog hLL hr hq
  change Finset.sum ((nextPrimeWindow M).erase r) (fun s =>
    singularDivisorProduct (primeTargetSeparation r s) ^ q) <=
    K ^ q * (2 * ((nextPrimeWindow M).card : Real) * (A0 * T) ^ q +
      C * (X : Real) ^ (7 / 8 : Real) * J ^ 2 * F ^ q) at hFull
  have hKF : K * F <= B * Real.log (Real.log (M : Real)) := by
    calc
      _ <= K * ((2 * Real.exp singularMertensBound) * Real.log (Real.log (M : Real))) :=
        mul_le_mul_of_nonneg_left (cutoff_weight_le M hM hLog hLL) hKpos.le
      _ = W * Real.log (Real.log (M : Real)) := by dsimp [W]; ring
      _ <= _ := mul_le_mul_of_nonneg_right hWB hLL0
  have hPowError := pow_mono_nonneg (K * F) (B * Real.log (Real.log (M : Real)))
    (mul_nonneg hKpos.le hF0) hKF q
  have hErrorBound : K ^ q *
      (C * (X : Real) ^ (7 / 8 : Real) * J ^ 2 * F ^ q) <= U := by
    have hX := window_rpow_le M
    have hJ := cutoff_conductor_le M hM hLog
    have hUpper : C * (X : Real) ^ (7 / 8 : Real) * J ^ 2 * (K * F) ^ q <=
        C * ((2 : Real) ^ (7 / 8 : Real) * (M : Real) ^ (7 / 8 : Real)) *
          (64 * Real.log (M : Real) ^ 4) * (B * Real.log (Real.log (M : Real))) ^ q := by
      exact mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left hX hCpos.le) hJ (sq_nonneg J) (by positivity))
        hPowError (by positivity) (by positivity)
    calc
      _ = C * (X : Real) ^ (7 / 8 : Real) * J ^ 2 * (K * F) ^ q := by
        simp only [mul_pow] <;> ring
      _ <= C * ((2 : Real) ^ (7 / 8 : Real) * (M : Real) ^ (7 / 8 : Real)) *
          (64 * Real.log (M : Real) ^ 4) * (B * Real.log (Real.log (M : Real))) ^ q := hUpper
      _ = E0 * ((M : Real) ^ (7 / 8 : Real) * Real.log (M : Real) ^ 4 *
          (B * Real.log (Real.log (M : Real))) ^ q) := by dsimp [E0]; ring
      _ <= B * ((M : Real) ^ (7 / 8 : Real) * Real.log (M : Real) ^ 4 *
          (B * Real.log (Real.log (M : Real))) ^ q) :=
        mul_le_mul_of_nonneg_right hE0B (by positivity)
      _ = B * (M : Real) ^ (7 / 8 : Real) * Real.log (M : Real) ^ 4 *
          (B * Real.log (Real.log (M : Real))) ^ q := by ring
      _ <= (M : Real) ^ (15 / 16 : Real) := hError q hqMax
      _ <= U := hScale
  have hBasePow : (A * T) ^ q <= (Aplus * T) ^ q :=
    pow_mono_nonneg _ _ (mul_nonneg hApos.le hTpos.le)
      (mul_le_mul_of_nonneg_right hAplus hTpos.le) q
  have hMainBound : K ^ q * (2 * ((nextPrimeWindow M).card : Real) * (A0 * T) ^ q) <=
      8 * U * (Aplus * T) ^ q := by
    calc
      _ = 2 * ((nextPrimeWindow M).card : Real) * (A * T) ^ q := by
        dsimp [A]
        simp only [mul_pow] <;> ring
      _ <= (2 * (4 * (M : Real) / Real.log (M : Real))) * (A * T) ^ q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCard (by norm_num)) (pow_nonneg (by positivity) q)
      _ = 8 * U * (A * T) ^ q := by dsimp [U]; ring
      _ <= _ := mul_le_mul_of_nonneg_left hBasePow (by positivity)
  have hInvA : 1 / Real.log 2 <= Aplus := by dsimp [Aplus]; linarith only [hApos]
  have hBaseOne : 1 <= Aplus * T := by
    calc
      _ = (1 / Real.log 2) * Real.log 2 := by field_simp
      _ <= (1 / Real.log 2) * T :=
        mul_le_mul_of_nonneg_left hTTwo (one_div_nonneg.mpr hLogTwo.le)
      _ <= _ := mul_le_mul_of_nonneg_right hInvA hTpos.le
  have hOnePow : 1 <= (Aplus * T) ^ q := by
    simpa only [one_pow] using pow_mono_nonneg 1 (Aplus * T) zero_le_one hBaseOne q
  have hUle : U <= U * (Aplus * T) ^ q := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hOnePow hU0
  rw [mul_add] at hFull
  calc
    _ <= 8 * U * (Aplus * T) ^ q + U :=
      hFull.trans (_root_.add_le_add hMainBound hErrorBound)
    _ <= 8 * U * (Aplus * T) ^ q + U * (Aplus * T) ^ q :=
      _root_.add_le_add (le_refl _) hUle
    _ = U * (9 * (Aplus * T) ^ q) := by ring
    _ <= U * (9 ^ q * (Aplus * T) ^ q) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (nine_le_pow q hq) (pow_nonneg (by positivity) q)) hU0
    _ = _ := by simp only [mul_pow] <;> ring

end PrimeFactorOscillations.LPF
