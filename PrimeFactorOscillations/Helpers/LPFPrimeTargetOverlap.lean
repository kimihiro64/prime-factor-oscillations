/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPrimeTargetAsymptotic
import PrimeFactorOscillations.Helpers.ThetaEndpointAsymptotic

/-! # Averaged full difference multipliers over subsets of prime targets -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

/-- The margin needed for q=ceil(log(N/b)), with N=M/log M. -/
theorem eventually_nextPrimeWindow_card_le_half :
    Filter.Eventually (fun M : Nat =>
      ((nextPrimeWindow M).card : Real) <= ((M : Real) / Real.log (M : Real)) / 2)
      Filter.atTop := by
  classical
  have hNat : Filter.Tendsto (fun M : Nat => (M : Real)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hUpper := ((tendsto_primeCounting_scaled_mainTerm (5 / 4) (by norm_num)).comp hNat).eventually
    (gt_mem_nhds (show (5 / 4 : Real) < 11 / 8 by norm_num))
  have hLower := tendsto_primeCounting_div_mainTerm.eventually
    (lt_mem_nhds (show (7 / 8 : Real) < 1 by norm_num))
  filter_upwards [hUpper, hLower, Filter.eventually_ge_atTop (2 : Nat)] with M hUpper hLower hM
  let N : Real := (M : Real) / Real.log (M : Real)
  have hMR : (1 : Real) < (M : Real) := by exact_mod_cast (show 1 < M by omega)
  have hNpos : 0 < N := div_pos (by linarith) (Real.log_pos hMR)
  change (Nat.primeCounting (Nat.floor ((5 / 4 : Real) * (M : Real))) : Real) / N < 11 / 8 at hUpper
  change (7 / 8 : Real) < (Nat.primeCounting M : Real) / N at hLower
  have hDisjoint : Disjoint (nextPrimeWindow M) (Nat.primesLE M) := by
    apply Finset.disjoint_left.mpr
    intro p hp hOld
    have h := nextPrimeWindow_spec M p hp
    have hOld' := Nat.mem_primesLE.mp hOld
    omega
  have hUnion : Union.union (nextPrimeWindow M) (Nat.primesLE M) <=
      Nat.primesLE (Nat.floor ((5 / 4 : Real) * (M : Real))) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hNew | hOld
    next =>
      have h := nextPrimeWindow_spec M p hNew
      have hMul : 4 * p <= 5 * M := by omega
      have hMulR : (4 : Real) * (p : Real) <= 5 * (M : Real) := by exact_mod_cast hMul
      exact Nat.mem_primesLE.mpr (And.intro (Nat.le_floor (by linarith)) h.1)
    next =>
      have h := Nat.mem_primesLE.mp hOld
      have hpR : (p : Real) <= (M : Real) := by exact_mod_cast h.1
      exact Nat.mem_primesLE.mpr (And.intro (Nat.le_floor (by linarith)) h.2)
  have hCardNat := Finset.card_le_card hUnion
  rw [Finset.card_union_of_disjoint hDisjoint, Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_card_eq_primeCounting] at hCardNat
  have hCard : ((nextPrimeWindow M).card : Real) + (Nat.primeCounting M : Real) <=
      (Nat.primeCounting (Nat.floor ((5 / 4 : Real) * (M : Real))) : Real) := by
    exact_mod_cast hCardNat
  have hU := mul_lt_mul_of_pos_right hUpper hNpos
  have hL := mul_lt_mul_of_pos_right hLower hNpos
  have hCancelU :
      ((Nat.primeCounting (Nat.floor ((5 / 4 : Real) * (M : Real))) : Real) / N) * N =
        (Nat.primeCounting (Nat.floor ((5 / 4 : Real) * (M : Real))) : Real) := by field_simp
  have hCancelL : ((Nat.primeCounting M : Real) / N) * N = (Nat.primeCounting M : Real) := by
    field_simp
  rw [hCancelU] at hU
  rw [hCancelL] at hL
  change ((nextPrimeWindow M).card : Real) <= N / 2
  linarith only [hCard, hU, hL]

private theorem sum_le_of_log_moment (S : Finset Nat) (f : Nat -> Real)
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

private theorem overlap_order_bounds (M : Nat) (b : Real)
    (hM : 2 <= M) (hLL : 1 <= Real.log (Real.log (M : Real)))
    (hbLower : (M : Real) / Real.log (M : Real) ^ 4 <= b)
    (hbUpper : b <= ((M : Real) / Real.log (M : Real)) / 2) :
    let N := (M : Real) / Real.log (M : Real)
    let q := Nat.ceil (Real.log (N / b))
    And (0 < b) (And (1 <= q)
      (And ((q : Real) <= 10 * Real.log (Real.log (M : Real)))
        ((q : Real) + 2 <= 3 + Real.log (N / b)))) := by
  let L := Real.log (M : Real)
  let N := (M : Real) / L
  let q := Nat.ceil (Real.log (N / b))
  have hMR : (1 : Real) < (M : Real) := by exact_mod_cast (show 1 < M by omega)
  have hL : 0 < L := Real.log_pos hMR
  have hN : 0 < N := div_pos (by linarith) hL
  have hb : 0 < b := (div_pos (by linarith : (0 : Real) < (M : Real))
    (pow_pos hL 4)).trans_le hbLower
  have hCancel : (N / b) * b = N := by field_simp
  have hRatio : 1 < N / b := by
    change b <= N / 2 at hbUpper
    nlinarith only [hb, hbUpper, hCancel]
  have hLog : 0 < Real.log (N / b) := Real.log_pos hRatio
  have hq : 1 <= q := Nat.ceil_pos.mpr hLog
  have hqUpper : (q : Real) < Real.log (N / b) + 1 := Nat.ceil_lt_add_one hLog.le
  have hPower : (M : Real) <= b * L ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hbLower (pow_nonneg hL.le 4)
    have hEq : ((M : Real) / L ^ 4) * L ^ 4 = (M : Real) := by field_simp
    change ((M : Real) / L ^ 4) * L ^ 4 <= b * L ^ 4 at h
    rwa [hEq] at h
  have hNUpper : N <= b * L ^ 3 := by
    apply le_of_mul_le_mul_right (a := L)
    next =>
      have hEq : N * L = (M : Real) := by dsimp [N]; field_simp
      rw [hEq]
      nlinarith only [hPower]
    next => exact hL
  have hRatioUpper : N / b <= L ^ 3 := by
    have h := div_le_div_of_nonneg_right hNUpper hb.le
    have hEq : (b * L ^ 3) / b = L ^ 3 := by field_simp
    rwa [hEq] at h
  have hLogUpper : Real.log (N / b) <= 3 * Real.log L := by
    have h := Real.log_le_log (by linarith : 0 < N / b) hRatioUpper
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  refine And.intro hb (And.intro hq (And.intro ?_ ?_))
  next => change (q : Real) <= 10 * Real.log L; change 1 <= Real.log L at hLL; linarith
  next => change (q : Real) + 2 <= 3 + Real.log (N / b); linarith

private theorem singularDivisorProduct_nonneg (v : Nat) :
    0 <= singularDivisorProduct v := by
  apply Finset.prod_nonneg
  intro p hp
  have hp3 : 3 <= p := (Finset.mem_filter.mp hp).2
  have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast hp3
  have hDen : 0 < (p : Real) - 2 := by linarith
  unfold singularFactor
  positivity

/-- Uniform overlap for every target subset above the discarded error scale. -/
theorem exists_uniform_primeTarget_overlap :
    exists C : Real, And (0 < C)
      (Filter.Eventually (fun M : Nat => forall B : Finset Nat,
        B <= nextPrimeWindow M ->
        (M : Real) / Real.log (M : Real) ^ 4 <= (B.card : Real) ->
        Finset.sum B (fun r => Finset.sum (B.erase r) (fun s =>
          singularDivisorProduct (primeTargetSeparation r s))) <=
          C * (B.card : Real) ^ 2 *
            Real.log (3 + Real.log (((M : Real) / Real.log (M : Real)) / (B.card : Real))))
        Filter.atTop) := by
  classical
  choose C0 hC0pos hMomentEvent using exists_uniform_primeTarget_moment
  refine Exists.intro (Real.exp 1 * C0) (And.intro (mul_pos (Real.exp_pos 1) hC0pos) ?_)
  have hNat : Filter.Tendsto (fun M : Nat => (M : Real)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hLLEvent := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hNat)).eventually
    (Filter.eventually_ge_atTop (1 : Real))
  filter_upwards [hMomentEvent, eventually_nextPrimeWindow_card_le_half, hLLEvent,
    Filter.eventually_ge_atTop (2 : Nat)] with M hMoment hCard hLL hM
  change 1 <= Real.log (Real.log (M : Real)) at hLL
  intro B hB hbLower
  let b : Real := (B.card : Real)
  let N : Real := (M : Real) / Real.log (M : Real)
  let q : Nat := Nat.ceil (Real.log (N / b))
  have hbUpper : b <= N / 2 := by
    exact (show (B.card : Real) <= ((nextPrimeWindow M).card : Real) by
      exact_mod_cast Finset.card_le_card hB).trans hCard
  have hOrder := overlap_order_bounds M b hM hLL hbLower hbUpper
  change And (0 < b) (And (1 <= q) (And ((q : Real) <=
    10 * Real.log (Real.log (M : Real))) ((q : Real) + 2 <= 3 + Real.log (N / b)))) at hOrder
  have hNpos : 0 < N := by
    apply div_pos
    next => exact_mod_cast (show 0 < M by omega)
    next => exact Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hRow : forall r, Membership.mem B r ->
      Finset.sum (B.erase r) (fun s => singularDivisorProduct (primeTargetSeparation r s)) <=
        b * (Real.exp 1 * C0) * Real.log (3 + Real.log (N / b)) := by
    intro r hr
    let f : Nat -> Real := fun s => singularDivisorProduct (primeTargetSeparation r s)
    have hf : forall s, 0 <= f s := fun s => singularDivisorProduct_nonneg _
    have hErase : B.erase r <= (nextPrimeWindow M).erase r := by
      intro s hs
      have h := Finset.mem_erase.mp hs
      exact Finset.mem_erase.mpr (And.intro h.1 (hB h.2))
    have hRestricted : Finset.sum (B.erase r) (fun s => f s ^ q) <=
        N * (C0 * Real.log ((q : Real) + 2)) ^ q := by
      calc
        _ <= Finset.sum ((nextPrimeWindow M).erase r) (fun s => f s ^ q) :=
          Finset.sum_le_sum_of_subset_of_nonneg hErase (fun s _ _ => pow_nonneg (hf s) q)
        _ <= _ := hMoment r q (hB hr) hOrder.2.1 hOrder.2.2.1
    have hLogPos : 0 < Real.log ((q : Real) + 2) := by
      apply Real.log_pos
      have hq0 : (0 : Real) <= (q : Real) := Nat.cast_nonneg q
      linarith
    have hEraseCard : ((B.erase r).card : Real) <= b := by
      dsimp [b]
      exact_mod_cast Finset.card_le_card (Finset.erase_subset r B)
    have h := sum_le_of_log_moment (B.erase r) f b N
      (C0 * Real.log ((q : Real) + 2)) q hOrder.1 hNpos
      (mul_nonneg hC0pos.le hLogPos.le) hEraseCard hOrder.2.1
      (Nat.le_ceil _) (fun s _ => hf s) hRestricted
    have hLogUpper : Real.log ((q : Real) + 2) <= Real.log (3 + Real.log (N / b)) :=
      Real.log_le_log (by have hq0 : (0 : Real) <= (q : Real) := Nat.cast_nonneg q; linarith) hOrder.2.2.2
    calc
      _ <= b * Real.exp 1 * (C0 * Real.log ((q : Real) + 2)) := h
      _ = b * (Real.exp 1 * C0) * Real.log ((q : Real) + 2) := by ring
      _ <= _ := mul_le_mul_of_nonneg_left hLogUpper (by positivity)
  calc
    _ <= Finset.sum B (fun _ => b * (Real.exp 1 * C0) * Real.log (3 + Real.log (N / b))) :=
      Finset.sum_le_sum hRow
    _ = (Real.exp 1 * C0) * b ^ 2 * Real.log (3 + Real.log (N / b)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      change b * (b * (Real.exp 1 * C0) * Real.log (3 + Real.log (N / b))) = _
      ring

end PrimeFactorOscillations.LPF
