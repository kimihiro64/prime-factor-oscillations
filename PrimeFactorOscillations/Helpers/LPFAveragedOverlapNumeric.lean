/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFOverlapOnsetNumeric

/-!
# Explicit averaged prime-target overlap

The growing moment estimate gives constant 6144 for every target subset above
M / log(M)^4 once log(M) is at least 32768. The maximum in the logarithm keeps
the bound valid without an additional eventual prime-counting cutoff.
-/


set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

private theorem numeric_sum_le_of_log_moment (S : Finset Nat) (f : Nat -> Real)
    (b N A : Real) (q : Nat) (hb : 0 < b) (hN : 0 < N) (hA : 0 <= A)
    (hcard : (S.card : Real) <= b) (hq : 1 <= q)
    (hlog : Real.log (N / b) <= (q : Real))
    (hf : forall i, Membership.mem S i -> 0 <= f i)
    (hMoment : Finset.sum S (fun i => f i ^ q) <= N * A ^ q) :
    Finset.sum S f <= b * Real.exp 1 * A := by
  have hqR : (1 : Real) <= (q : Real) := by exact_mod_cast hq
  have hqpos : (0 : Real) < (q : Real) := by linarith
  have hSum : 0 <= Finset.sum S f := Finset.sum_nonneg hf
  have hMean := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S hqR hf
  simp only [Real.rpow_natCast] at hMean
  have hCardPow : (S.card : Real) ^ ((q : Real) - 1) <= b ^ ((q : Real) - 1) :=
    Real.rpow_le_rpow (Nat.cast_nonneg S.card) hcard (by linarith)
  have hSumPow : 0 <= Finset.sum S (fun i => f i ^ q) := by
    exact Finset.sum_nonneg (fun i hi => pow_nonneg (hf i hi) q)
  have hFirst : (Finset.sum S f) ^ q <=
      b ^ ((q : Real) - 1) * (N * A ^ q) := by
    exact hMean.trans (mul_le_mul hCardPow hMoment hSumPow
      (Real.rpow_nonneg hb.le _))
  have hExp := (Real.log_le_iff_le_exp (div_pos hN hb)).mp hlog
  have hExpEq : Real.exp (q : Real) = Real.exp 1 ^ q := by
    simpa only [mul_one] using Real.exp_nat_mul 1 q
  rw [hExpEq] at hExp
  have hNexp : N <= b * Real.exp 1 ^ q := by
    have h := mul_le_mul_of_nonneg_right hExp hb.le
    have hCancel : (N / b) * b = N := by field_simp
    rw [hCancel] at h
    simpa only [mul_comm] using h
  have hBPow : b ^ ((q : Real) - 1) * b = b ^ q := by
    calc
      _ = b ^ ((q : Real) - 1) * b ^ (1 : Real) := by rw [Real.rpow_one]
      _ = b ^ ((q : Real) - 1 + 1) := (Real.rpow_add hb _ _).symm
      _ = b ^ q := by rw [sub_add_cancel, Real.rpow_natCast]
  have hSecond : b ^ ((q : Real) - 1) * (N * A ^ q) <=
      (b * Real.exp 1 * A) ^ q := by
    calc
      _ <= b ^ ((q : Real) - 1) * ((b * Real.exp 1 ^ q) * A ^ q) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hNexp (pow_nonneg hA q))
          (Real.rpow_nonneg hb.le _)
      _ = (b ^ ((q : Real) - 1) * b) * Real.exp 1 ^ q * A ^ q := by ring
      _ = (b * Real.exp 1 * A) ^ q := by rw [hBPow, mul_pow, mul_pow]
  have hTargetNonneg : 0 <= b * Real.exp 1 * A := by positivity
  apply (Real.rpow_le_rpow_iff hSum hTargetNonneg hqpos).mp
  simpa only [Real.rpow_natCast] using hFirst.trans hSecond

private theorem numeric_singularDivisorProduct_nonneg (v : Nat) :
    0 <= singularDivisorProduct v := by
  apply Finset.prod_nonneg
  intro p hp
  have hp3 : 3 <= p := (Finset.mem_filter.mp hp).2
  have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast hp3
  have hDen : 0 < (p : Real) - 2 := by linarith
  unfold singularFactor
  positivity


private theorem numeric_overlap_order_bounds (M : Nat) (b : Real)
    (hM : 4 <= M) (hLog : 32768 <= Real.log (M : Real))
    (hbLower : (M : Real) / Real.log (M : Real) ^ 4 <= b) :
    let N := (M : Real) / Real.log (M : Real)
    let t := Real.log (max 1 (N / b))
    let q := max 5 (Nat.ceil t)
    And (0 < b) (And (5 <= q)
      (And ((q : Real) <= 10 * Real.log (Real.log (M : Real)))
        (And (Real.log (N / b) <= (q : Real))
          (Real.log ((q : Real) + 2) <= 2 * Real.log (3 + t))))) := by
  let L := Real.log (M : Real)
  let N := (M : Real) / L
  let z := max 1 (N / b)
  let t := Real.log z
  let q := max 5 (Nat.ceil t)
  have hMp : 0 < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  have hL : 32768 <= L := hLog
  have hLp : 0 < L := by linarith
  have hN : 0 < N := div_pos hMp hLp
  have hb : 0 < b := (div_pos hMp (pow_pos hLp 4)).trans_le hbLower
  have hLL : 1 <= Real.log L := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ <= _ := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
  have hPower : (M : Real) <= b * L ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hbLower (pow_nonneg hLp.le 4)
    have hEq : ((M : Real) / L ^ 4) * L ^ 4 = (M : Real) := by field_simp
    change ((M : Real) / L ^ 4) * L ^ 4 <= b * L ^ 4 at h
    rwa [hEq] at h
  have hNUpper : N <= b * L ^ 3 := by
    apply le_of_mul_le_mul_right (a := L)
    next =>
      have hEq : N * L = (M : Real) := by dsimp [N]; field_simp
      rw [hEq]
      nlinarith only [hPower]
    next => exact hLp
  have hRatioUpper : N / b <= L ^ 3 := by
    have h := div_le_div_of_nonneg_right hNUpper hb.le
    have hEq : (b * L ^ 3) / b = L ^ 3 := by field_simp
    rwa [hEq] at h
  have hL3 : 1 <= L ^ 3 := by
    calc
      1 <= L ^ ((3 : Nat) : Real) := Real.one_le_rpow
        (show 1 <= L by linarith) (by norm_num)
      _ = L ^ (3 : Nat) := Real.rpow_natCast L 3
  have hz : 1 <= z := le_max_left _ _
  have hzUpper : z <= L ^ 3 := max_le hL3 hRatioUpper
  have ht : 0 <= t := Real.log_nonneg hz
  have htUpper : t <= 3 * Real.log L := by
    have h := Real.log_le_log (by linarith : 0 < z) hzUpper
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hq : 5 <= q := le_max_left _ _
  have hCeil : t <= (q : Real) := (Nat.le_ceil t).trans
    (by exact_mod_cast (show Nat.ceil t <= q from le_max_right _ _))
  have hqUpper : (q : Real) <= t + 5 := by
    by_cases h : Nat.ceil t <= 5
    next =>
      change ((max 5 (Nat.ceil t) : Nat) : Real) <= t + 5
      rw [max_eq_left h]
      norm_num only [Nat.cast_ofNat]
      linarith
    next =>
      have h5 : 5 <= Nat.ceil t := by omega
      change ((max 5 (Nat.ceil t) : Nat) : Real) <= t + 5
      rw [max_eq_right h5]
      have hC := Nat.ceil_lt_add_one ht
      linarith
  have hOrderUpper : (q : Real) <= 10 * Real.log L := by
    linarith only [hqUpper, htUpper, hLL]
  have hLogRatio : Real.log (N / b) <= (q : Real) :=
    (Real.log_le_log (div_pos hN hb) (le_max_right 1 (N / b))).trans hCeil
  have hShape : (q : Real) + 2 <= (3 + t) ^ 2 := by
    nlinarith only [hqUpper, ht, sq_nonneg t]
  have hShapeLog : Real.log ((q : Real) + 2) <= 2 * Real.log (3 + t) := by
    have hQ0 : (0 : Real) <= (q : Real) := Nat.cast_nonneg q
    have h := Real.log_le_log (by linarith : 0 < (q : Real) + 2) hShape
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  exact And.intro hb (And.intro hq
    (And.intro hOrderUpper (And.intro hLogRatio hShapeLog)))

theorem lpf_primeTarget_overlap_numeric (M : Nat) (B : Finset Nat)
    (hM : 4 <= M) (hLog : 32768 <= Real.log (M : Real))
    (hB : B <= nextPrimeWindow M)
    (hbLower : (M : Real) / Real.log (M : Real) ^ 4 <= (B.card : Real)) :
    Finset.sum B (fun r => Finset.sum (B.erase r) (fun s =>
      singularDivisorProduct (primeTargetSeparation r s))) <=
      6144 * (B.card : Real) ^ 2 *
        Real.log (3 + Real.log (max 1
          (((M : Real) / Real.log (M : Real)) / (B.card : Real)))) := by
  classical
  let b : Real := (B.card : Real)
  let N : Real := (M : Real) / Real.log (M : Real)
  let t := Real.log (max 1 (N / b))
  let q := max 5 (Nat.ceil t)
  have hOrder := numeric_overlap_order_bounds M b hM hLog hbLower
  change And (0 < b) (And (5 <= q)
    (And ((q : Real) <= 10 * Real.log (Real.log (M : Real)))
      (And (Real.log (N / b) <= (q : Real))
        (Real.log ((q : Real) + 2) <= 2 * Real.log (3 + t))))) at hOrder
  have hNpos : 0 < N := div_pos (by exact_mod_cast (show 0 < M by omega))
    (by linarith : 0 < Real.log (M : Real))
  have ht : 0 <= t := Real.log_nonneg (le_max_left _ _)
  have hF : 0 <= Real.log (3 + t) := Real.log_nonneg (by linarith)
  have hQ0 : 0 <= Real.log ((q : Real) + 2) := Real.log_nonneg
    (by have hq0 : (0 : Real) <= (q : Real) := Nat.cast_nonneg q; linarith)
  have hRow : forall r, Membership.mem B r ->
      Finset.sum (B.erase r) (fun s => singularDivisorProduct (primeTargetSeparation r s)) <=
        b * 6144 * Real.log (3 + t) := by
    intro r hr
    let f : Nat -> Real := fun s => singularDivisorProduct (primeTargetSeparation r s)
    have hf : forall s, 0 <= f s := fun s => numeric_singularDivisorProduct_nonneg _
    have hErase : B.erase r <= (nextPrimeWindow M).erase r := by
      intro s hs
      have h := Finset.mem_erase.mp hs
      exact Finset.mem_erase.mpr (And.intro h.1 (hB h.2))
    have hRestricted : Finset.sum (B.erase r) (fun s => f s ^ q) <=
        N * (1024 * Real.log ((q : Real) + 2)) ^ q := by
      calc
        _ <= Finset.sum ((nextPrimeWindow M).erase r) (fun s => f s ^ q) :=
          Finset.sum_le_sum_of_subset_of_nonneg hErase (fun s _ _ => pow_nonneg (hf s) q)
        _ <= _ := lpf_overlap_full_moment_numeric M r q hM hLog
          (hB hr) hOrder.2.1 hOrder.2.2.1
    have hEraseCard : ((B.erase r).card : Real) <= b := by
      dsimp [b]
      exact_mod_cast Finset.card_le_card (Finset.erase_subset r B)
    have h := numeric_sum_le_of_log_moment (B.erase r) f b N
      (1024 * Real.log ((q : Real) + 2)) q hOrder.1 hNpos
      (by positivity) hEraseCard (by omega : 1 <= q)
      hOrder.2.2.2.1 (fun s _ => hf s) hRestricted
    calc
      _ <= b * Real.exp 1 * (1024 * Real.log ((q : Real) + 2)) := h
      _ = (b * (1024 * Real.log ((q : Real) + 2))) * Real.exp 1 := by ring
      _ <= (b * (1024 * Real.log ((q : Real) + 2))) * 3 :=
        mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le (by positivity)
      _ = (b * 3072) * Real.log ((q : Real) + 2) := by ring
      _ <= (b * 3072) * (2 * Real.log (3 + t)) :=
        mul_le_mul_of_nonneg_left hOrder.2.2.2.2 (by positivity)
      _ = _ := by ring
  calc
    _ <= Finset.sum B (fun _ => b * 6144 * Real.log (3 + t)) := Finset.sum_le_sum hRow
    _ = 6144 * b ^ 2 * Real.log (3 + t) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      change b * (b * 6144 * Real.log (3 + t)) = _
      ring

end PrimeFactorOscillations.LPF
