/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFOverlapCutoffNumeric
import PrimeFactorOscillations.Helpers.LPFOverlapFullNumeric

/-!
# Numerical onset for the complete prime-target overlap moments

Both residue branches and every off-diagonal target are retained. The explicit
cutoff controls moment orders up to ten times log log M. This is an overlap
component bound, not a complete LPF orbit-entry threshold.
-/


set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_overlap_cutoff_data_numeric :
    And (1 <= Real.log (32768 : Real))
      (And (lpfOverlapLogDeficit ((2 : Real) ^ (30 : Nat)) 216 (1 / 16) 32768 <= 0)
        ((15 + 10 * Real.log (216 : Real) +
          10 * Real.log (Real.log (32768 : Real))) / 32768 <= (1 / 16 : Real))) := by
  have hHalf : (1 / 2 : Real) <= Real.log (2 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < (2 : Real) ^ (-1 : Int))
    rw [zpow_neg_one, Real.log_inv] at h
    norm_num at h
    linarith
  have hOne : Real.log (2 : Real) <= 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith
  have hL : And (1 <= Real.log (32768 : Real)) (Real.log (32768 : Real) <= 15) := by
    rw [show (32768 : Real) = 2 ^ (15 : Nat) by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    constructor <;> linarith
  have hC : Real.log ((2 : Real) ^ (30 : Nat)) <= 30 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hW : Real.log (216 : Real) <= 8 := by
    calc
      _ <= Real.log ((2 : Real) ^ (8 : Nat)) :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 8 * Real.log (2 : Real) := by rw [Real.log_pow]; norm_num
      _ <= 8 := by linarith
  have hLL : Real.log (Real.log (32768 : Real)) <= 4 := by
    calc
      _ <= Real.log (16 : Real) := Real.log_le_log (by linarith only [hL.1]) (by linarith only [hL.2])
      _ = 4 * Real.log (2 : Real) := by
        rw [show (16 : Real) = 2 ^ (4 : Nat) by norm_num, Real.log_pow]
        norm_num
      _ <= 4 := by linarith
  have hLL0 := Real.log_nonneg hL.1
  have hW0 := Real.log_nonneg (by norm_num : (1 : Real) <= 216)
  have hProduct := mul_le_mul hL.2
    (show Real.log (216 : Real) + Real.log (Real.log (32768 : Real)) <= 12 by linarith)
    (add_nonneg hW0 hLL0) (by norm_num : (0 : Real) <= 15)
  have hStart : lpfOverlapLogDeficit ((2 : Real) ^ (30 : Nat)) 216 (1 / 16) 32768 <= 0 := by
    unfold lpfOverlapLogDeficit
    have hSum := _root_.add_le_add
      (_root_.add_le_add hC
        (mul_le_mul_of_nonneg_left hL.2 (by norm_num : (0 : Real) <= 5)))
      (mul_le_mul_of_nonneg_left hProduct (by norm_num : (0 : Real) <= 10))
    calc
      _ = (Real.log ((2 : Real) ^ (30 : Nat)) + 5 * Real.log (32768 : Real) +
          10 * (Real.log (32768 : Real) *
            (Real.log (216 : Real) + Real.log (Real.log (32768 : Real))))) -
          (1 / 16 : Real) * 32768 := by ring
      _ <= (30 + 5 * 15 + 10 * (15 * 12) : Real) - (1 / 16 : Real) * 32768 :=
        _root_.sub_le_sub_right hSum _
      _ <= 0 := by norm_num
  have hSlope :
      (15 + 10 * Real.log (216 : Real) +
        10 * Real.log (Real.log (32768 : Real))) / 32768 <= (1 / 16 : Real) := by
    calc
      _ <= (135 : Real) / 32768 := div_le_div_of_nonneg_right
        (by linarith only [hW, hLL]) (by norm_num)
      _ <= _ := by norm_num
  exact And.intro hL.1 (And.intro hStart hSlope)

theorem lpf_overlap_scalar_error_numeric (M : Real) (q : Nat)
    (hM : 0 < M) (hLog : 32768 <= Real.log M)
    (hq : (q : Real) <= 10 * Real.log (Real.log M)) :
    (2 : Real) ^ (30 : Nat) * M ^ (15 / 16 : Real) * Real.log M ^ 4 *
      (216 * Real.log (Real.log M)) ^ q <= M / Real.log M := by
  have hData := lpf_overlap_cutoff_data_numeric
  have h := lpf_overlap_full_moment_error_cutoff ((2 : Real) ^ (30 : Nat)) 216
    (1 / 16) 32768 M q (by positivity) (by norm_num) (by norm_num)
    hData.1 hData.2.1 hData.2.2 hM hLog hq
  simpa only [show (1 - (1 / 16 : Real)) = (15 / 16 : Real) by norm_num] using h

theorem lpf_overlap_log_factor_numeric (M : Nat) (hM : 4 <= M)
    (hLog : 4 <= Real.log (M : Real)) :
    And (0 <= 1 + Real.log ((Finset.prod (primeTargetCutoff M) (fun p => p) : Nat) : Real) +
      Real.log (((5 * M / 4 : Nat) : Real) + 2))
      (1 + Real.log ((Finset.prod (primeTargetCutoff M) (fun p => p) : Nat) : Real) +
        Real.log (((5 * M / 4 : Nat) : Real) + 2) <= 4 * Real.log (M : Real)) := by
  classical
  let P := primeTargetCutoff M
  let L : Real := Real.log (M : Real)
  let X : Nat := 5 * M / 4
  have hMp : 0 < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  have hL : 4 <= L := hLog
  have hP : forall p, Membership.mem P p ->
      And (Nat.Prime p) (And (3 < p) ((p : Real) <= L)) := by
    intro p hp
    exact (primeTargetCutoff_mem M p (by omega)).mp hp
  have hProd : Real.log ((Finset.prod P (fun p => p) : Nat) : Real) =
      Finset.sum P (fun p => Real.log (p : Real)) := by
    rw [Nat.cast_prod]
    apply Real.log_prod
    intro p hp
    exact_mod_cast (ne_of_gt (hP p hp).1.pos)
  have hSub : P <= (Finset.Ioc 0 (Nat.floor L)).filter Nat.Prime := by
    intro p hp
    exact Finset.mem_filter.mpr (And.intro
      (Finset.mem_Ioc.mpr (And.intro (hP p hp).1.pos (Nat.le_floor (hP p hp).2.2)))
      (hP p hp).1)
  have hTheta : Finset.sum P (fun p => Real.log (p : Real)) <= Chebyshev.theta L := by
    rw [Chebyshev.theta.eq_1]
    apply Finset.sum_le_sum_of_subset_of_nonneg hSub
    intro p hp _
    have hPrime := (Finset.mem_filter.mp hp).2
    exact Real.log_nonneg (by exact_mod_cast hPrime.one_lt.le)
  have hFour : Real.log (4 : Real) <= 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hMod : Real.log ((Finset.prod P (fun p => p) : Nat) : Real) <= 2 * L :=
    hProd.le.trans (hTheta.trans ((Chebyshev.theta_le_log4_mul_x (by linarith : 0 <= L)).trans
      (mul_le_mul_of_nonneg_right hFour (by linarith))))
  have hNatProd : 1 <= Finset.prod P (fun p => p) := by
    apply Finset.one_le_prod
    intro p hp
    exact (hP p hp).1.one_lt.le
  have hMod0 : 0 <= Real.log ((Finset.prod P (fun p => p) : Nat) : Real) :=
    Real.log_nonneg (by exact_mod_cast hNatProd)
  have hX : X <= 2 * M := by dsimp [X]; omega
  have hXr : (X : Real) <= 2 * (M : Real) := by exact_mod_cast hX
  have hMr : (4 : Real) <= (M : Real) := by exact_mod_cast hM
  have hX0 : 0 <= (X : Real) := Nat.cast_nonneg X
  have hXL : Real.log ((X : Real) + 2) <= 2 + L := by
    calc
      _ <= Real.log (3 * (M : Real)) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log (3 : Real) + L := Real.log_mul (by norm_num) hMp.ne'
      _ <= _ := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 3)
        linarith
  have hXL0 : 0 <= Real.log ((X : Real) + 2) := Real.log_nonneg (by linarith)
  change And (0 <= 1 + Real.log ((Finset.prod P (fun p => p) : Nat) : Real) +
      Real.log ((X : Real) + 2)) _
  exact And.intro (by linarith) (by linarith)

theorem lpf_overlap_cutoff_product_numeric (M : Nat) (hM : 4 <= M)
    (hLog : 5 <= Real.log (M : Real)) :
    And (0 <= Finset.prod (primeTargetCutoff M) singularFactor)
      (Finset.prod (primeTargetCutoff M) singularFactor <=
        36 * Real.log (Real.log (M : Real))) := by
  classical
  let P := primeTargetCutoff M
  let L : Real := Real.log (M : Real)
  let n : Nat := Nat.ceil L
  have hL : 5 <= L := hLog
  have hP : forall p, Membership.mem P p ->
      And (Nat.Prime p) (And (5 <= p) ((p : Real) <= L)) := by
    intro p hp
    have h := (primeTargetCutoff_mem M p (by omega)).mp hp
    have hNot4 : Not (p = 4) := by intro he; subst p; norm_num at h
    exact And.intro h.1 (And.intro (by omega) h.2.2)
  have hCeil : L <= (n : Real) := Nat.le_ceil L
  have hn : 5 <= n := by
    have h : (5 : Real) <= (n : Real) := by linarith
    exact_mod_cast h
  have hProduct := lpf_singular_prime_product_numeric P n hn
    (fun p hp => And.intro (hP p hp).1 (And.intro (hP p hp).2.1
      (by exact_mod_cast ((hP p hp).2.2.trans hCeil))))
  have hCeilUpper : (n : Real) <= 2 * L := by
    have h := Nat.ceil_lt_add_one (show 0 <= L by linarith)
    change (n : Real) < L + 1 at h
    linarith
  have hLogL : 1 <= Real.log L := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ <= Real.log L := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
  have hLogN : Real.log (n : Real) <= 2 * Real.log L := by
    calc
      _ <= Real.log (2 * L) := Real.log_le_log
        (by exact_mod_cast (show 0 < n by omega)) hCeilUpper
      _ = Real.log (2 : Real) + Real.log L :=
        Real.log_mul (by norm_num) (by linarith)
      _ <= _ := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
        linarith
  have hNonneg : 0 <= Finset.prod P singularFactor := by
    apply Finset.prod_nonneg
    intro p hp
    have hpr : (5 : Real) <= (p : Real) := by exact_mod_cast (hP p hp).2.1
    have hDen : 0 <= (p : Real) - 2 := by linarith
    exact add_nonneg zero_le_one (one_div_nonneg.mpr hDen)
  change And (0 <= Finset.prod P singularFactor)
    (Finset.prod P singularFactor <= 36 * Real.log L)
  exact And.intro hNonneg (hProduct.trans (by linarith))

theorem lpf_overlap_full_error_normalized_numeric (M r q : Nat)
    (hM : 4 <= M) (hLog : 32768 <= Real.log (M : Real))
    (hr : Membership.mem (nextPrimeWindow M) r) (hq : 5 <= q) :
    Finset.sum ((nextPrimeWindow M).erase r) (fun s =>
      singularDivisorProduct (primeTargetSeparation r s) ^ q) <=
      2 * ((nextPrimeWindow M).card : Real) *
        (432 * Real.log ((q : Real) + 2)) ^ q +
      (2 : Real) ^ (30 : Nat) * (M : Real) ^ (15 / 16 : Real) *
        Real.log (M : Real) ^ 4 * (216 * Real.log (Real.log (M : Real))) ^ q := by
  classical
  let L : Real := Real.log (M : Real)
  let X : Nat := 5 * M / 4
  let P := primeTargetCutoff M
  let S := Finset.prod P singularFactor
  let J := 1 + Real.log ((Finset.prod P (fun p => p) : Nat) : Real) +
    Real.log ((X : Real) + 2)
  have hL : 32768 <= L := hLog
  have hLL : 3 <= Real.log L := by
    have hHalf : (1 / 2 : Real) <= Real.log (2 : Real) := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < (2 : Real) ^ (-1 : Int))
      rw [zpow_neg_one, Real.log_inv] at h
      norm_num at h
      linarith
    have hBase : 3 <= Real.log (64 : Real) := by
      rw [show (64 : Real) = 2 ^ (6 : Nat) by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith
    exact hBase.trans (Real.log_le_log (by norm_num) (by linarith))
  have hM0 : 0 < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  have hPower0 : 0 <= (M : Real) ^ (15 / 16 : Real) := Real.rpow_nonneg hM0.le _
  have hJ := lpf_overlap_log_factor_numeric M hM (by linarith : 4 <= Real.log (M : Real))
  change And (0 <= J) (J <= 4 * L) at hJ
  have hJ2 : J ^ 2 <= 16 * L ^ 2 := by
    have h := mul_le_mul hJ.2 hJ.2 hJ.1 (show 0 <= 4 * L by linarith)
    nlinarith only [h]
  have hS := lpf_overlap_cutoff_product_numeric M hM (by linarith : 5 <= Real.log (M : Real))
  change And (0 <= S) (S <= 36 * Real.log L) at hS
  have hS0 : 0 <= S := hS.1
  have hSPow : (6 * S) ^ q <= (216 * Real.log L) ^ q := by
    calc
      _ = (6 * S) ^ (q : Real) := (Real.rpow_natCast _ _).symm
      _ <= (216 * Real.log L) ^ (q : Real) := Real.rpow_le_rpow
        (by positivity) (by linarith only [hS.2]) (Nat.cast_nonneg q)
      _ = _ := Real.rpow_natCast _ _
  have hXP : X <= 2 * M := by dsimp [X]; omega
  have hXPow : (X : Real) ^ (15 / 16 : Real) <= 2 * (M : Real) ^ (15 / 16 : Real) := by
    have h := Real.rpow_le_rpow (Nat.cast_nonneg X)
      (show (X : Real) <= 2 * (M : Real) by exact_mod_cast hXP)
      (by norm_num : (0 : Real) <= 15 / 16)
    rw [Real.mul_rpow (by norm_num : (0 : Real) <= 2) hM0.le] at h
    have hTwo : (2 : Real) ^ (15 / 16 : Real) <= 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 2)
        (by norm_num : (15 / 16 : Real) <= 1)
      simpa only [Real.rpow_one] using h
    exact h.trans (mul_le_mul_of_nonneg_right hTwo hPower0)
  have hLL0 : 0 <= Real.log L := by linarith only [hLL]
  have hQ0 : 0 <= (216 * Real.log L) ^ q := by positivity
  have hErr : 1048576 * (X : Real) ^ (15 / 16 : Real) * J ^ 2 * (6 * S) ^ q <=
      (2 : Real) ^ (30 : Nat) * (M : Real) ^ (15 / 16 : Real) *
        L ^ 4 * (216 * Real.log L) ^ q := by
    have h1 := mul_le_mul_of_nonneg_left hXPow (by norm_num : (0 : Real) <= 1048576)
    have h2 := mul_le_mul h1 hJ2 (sq_nonneg J)
      (by positivity : 0 <= 1048576 * (2 * (M : Real) ^ (15 / 16 : Real)))
    have h3 := mul_le_mul h2 hSPow (by positivity : 0 <= (6 * S) ^ q)
      (by positivity : 0 <= 1048576 * (2 * (M : Real) ^ (15 / 16 : Real)) * (16 * L ^ 2))
    have hLift : L ^ 2 <= L ^ 4 := by
      calc
        _ = L ^ (2 : Real) := (Real.rpow_natCast _ _).symm
        _ <= L ^ (4 : Real) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = _ := Real.rpow_natCast _ _
    have hCoef := mul_le_mul
      (show (33554432 : Real) <= (2 : Real) ^ (30 : Nat) by norm_num)
      hLift (sq_nonneg L) (by positivity : 0 <= (2 : Real) ^ (30 : Nat))
    have h4 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCoef hPower0) hQ0
    exact h3.trans (by convert h4 using 1 <;> ring)
  have hFinite := lpf_primeTarget_full_finite_power_numeric M r q hM
    (by linarith : 4 <= Real.log (M : Real)) hLL hr hq
  change Finset.sum ((nextPrimeWindow M).erase r) (fun s =>
    singularDivisorProduct (primeTargetSeparation r s) ^ q) <=
    (6 : Real) ^ q * (2 * ((nextPrimeWindow M).card : Real) *
      (72 * Real.log ((q : Real) + 2)) ^ q +
      1048576 * (X : Real) ^ (15 / 16 : Real) * J ^ 2 * S ^ q) at hFinite
  have hExact : (6 : Real) ^ q * (2 * ((nextPrimeWindow M).card : Real) *
      (72 * Real.log ((q : Real) + 2)) ^ q +
      1048576 * (X : Real) ^ (15 / 16 : Real) * J ^ 2 * S ^ q) =
      2 * ((nextPrimeWindow M).card : Real) * (432 * Real.log ((q : Real) + 2)) ^ q +
        1048576 * (X : Real) ^ (15 / 16 : Real) * J ^ 2 * (6 * S) ^ q := by
    rw [show (432 : Real) * Real.log ((q : Real) + 2) =
      6 * (72 * Real.log ((q : Real) + 2)) by ring]
    simp only [mul_pow]
    ring
  rw [hExact] at hFinite
  exact hFinite.trans (_root_.add_le_add (le_refl _) hErr)

theorem lpf_overlap_full_moment_numeric (M r q : Nat)
    (hM : 4 <= M) (hLog : 32768 <= Real.log (M : Real))
    (hr : Membership.mem (nextPrimeWindow M) r) (hq : 5 <= q)
    (hqUpper : (q : Real) <= 10 * Real.log (Real.log (M : Real))) :
    Finset.sum ((nextPrimeWindow M).erase r) (fun s =>
      singularDivisorProduct (primeTargetSeparation r s) ^ q) <=
      ((M : Real) / Real.log (M : Real)) *
        (1024 * Real.log ((q : Real) + 2)) ^ q := by
  let N : Real := (M : Real) / Real.log (M : Real)
  let U : Real := (432 * Real.log ((q : Real) + 2)) ^ q
  let V : Real := (1024 * Real.log ((q : Real) + 2)) ^ q
  have hMp : 0 < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  have hLogPos : 0 < Real.log (M : Real) := by linarith
  have hN : 0 <= N := div_nonneg hMp.le hLogPos.le
  have hQ : (5 : Real) <= (q : Real) := by exact_mod_cast hq
  have hQL : 1 <= Real.log ((q : Real) + 2) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ <= _ := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
  have hQL0 : 0 <= Real.log ((q : Real) + 2) := by linarith only [hQL]
  have hBase : 1 <= 432 * Real.log ((q : Real) + 2) := by linarith
  have hU : 1 <= U := by
    have h := Real.one_le_rpow hBase (Nat.cast_nonneg q)
    simpa only [Real.rpow_natCast] using h
  have hTwo : (8 : Real) <= (2 : Real) ^ q := by
    calc
      _ = (2 : Real) ^ (3 : Nat) := by norm_num
      _ = (2 : Real) ^ (3 : Real) := (Real.rpow_natCast _ _).symm
      _ <= (2 : Real) ^ (q : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := Real.rpow_natCast _ _
  have hUV : (2 * (432 * Real.log ((q : Real) + 2))) ^ q <=
      (1024 * Real.log ((q : Real) + 2)) ^ q := by
    calc
      _ = (2 * (432 * Real.log ((q : Real) + 2))) ^ (q : Real) :=
        (Real.rpow_natCast _ _).symm
      _ <= (1024 * Real.log ((q : Real) + 2)) ^ (q : Real) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (Nat.cast_nonneg q)
      _ = _ := Real.rpow_natCast _ _
  have h8U : 8 * U <= V := by
    calc
      _ <= (2 : Real) ^ q * U := mul_le_mul_of_nonneg_right hTwo (by linarith)
      _ <= V := by simpa only [U, V, mul_pow] using hUV
  have hCoefficient : (25 / 7 : Real) * U + 1 <= V := by
    linarith only [h8U, hU]
  have hCard := lpf_nextPrimeWindow_card_numeric M (by omega : 2 <= M)
  have hCount : 2 * ((nextPrimeWindow M).card : Real) * U <= (25 / 7 : Real) * N * U := by
    have h := mul_le_mul_of_nonneg_right hCard (show 0 <= 2 * U by linarith)
    convert h using 1 <;> (try dsimp only [N]) <;> ring
  have hRaw := lpf_overlap_full_error_normalized_numeric M r q hM hLog hr hq
  have hError := lpf_overlap_scalar_error_numeric (M : Real) q hMp hLog hqUpper
  have hRaw' : Finset.sum ((nextPrimeWindow M).erase r) (fun s =>
      singularDivisorProduct (primeTargetSeparation r s) ^ q) <=
      2 * ((nextPrimeWindow M).card : Real) * U + N := by
    exact hRaw.trans (_root_.add_le_add (le_refl _) hError)
  have hScaled := mul_le_mul_of_nonneg_right hCoefficient hN
  change Finset.sum ((nextPrimeWindow M).erase r) (fun s =>
    singularDivisorProduct (primeTargetSeparation r s) ^ q) <= N * V
  nlinarith only [hRaw', hCount, hScaled]

end PrimeFactorOscillations.LPF
