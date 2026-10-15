/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.LPFGridPhase
import PrimeFactorOscillations.Helpers.LPFGridScale

/-!
# Uniform arithmetic major-packet envelope at the small denominator q
The complete consumer retains the minor, kernel and singular-tail packets.
This lemma supplies no equidistribution assertion for generated states.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

theorem lpfPhaseAllowance_le_major_cap (A : Real) (M P q X : Nat)
    (hA : 0 <= A) (hM : 1 <= M) (hP : 1 <= P) (hq : 1 <= q)
    (hX : 1 <= X) (hqP : q <= P) (hPM : P <= M) (hXM : X <= 2 * M) :
    lpfPhaseAllowance A q X <=
      (18 * A + 1 / Real.log 2) * Real.sqrt (P : Real) *
        (M : Real) ^ (15 / 16 : Real) * (1 + Real.log (M : Real)) ^ 2 := by
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hM
  have hPR : (1 : Real) <= (P : Real) := by exact_mod_cast hP
  have hQR : (1 : Real) <= (q : Real) := by exact_mod_cast hq
  have hXR : (1 : Real) <= (X : Real) := by exact_mod_cast hX
  have hqPR : (q : Real) <= (P : Real) := by exact_mod_cast hqP
  have hPMR : (P : Real) <= (M : Real) := by exact_mod_cast hPM
  have hXMR : (X : Real) <= 2 * (M : Real) := by exact_mod_cast hXM
  have hM0 : (0 : Real) < (M : Real) := by linarith
  have hq0 : (0 : Real) < (q : Real) := by linarith
  have hX0 : (0 : Real) < (X : Real) := by linarith
  have hLogM : 0 <= Real.log (M : Real) := Real.log_nonneg hMR
  have hLogQ : 0 <= Real.log (q : Real) := Real.log_nonneg hQR
  have hLogX : 0 <= Real.log (X : Real) := Real.log_nonneg hXR
  have hLog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hLog2le : Real.log (2 : Real) <= 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith
  have hLogQle : Real.log (q : Real) <= Real.log (M : Real) :=
    Real.log_le_log hq0 (le_trans hqPR hPMR)
  have hLogXle : Real.log (X : Real) <= 1 + Real.log (M : Real) := by
    have h := Real.log_le_log hX0 hXMR
    rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt hM0)] at h
    linarith
  have hLog4 : Real.log (4 : Real) <= 2 := by
    have h : Real.log (4 : Real) = 2 * Real.log (2 : Real) := by
      rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num, Real.log_pow]
      norm_num
    linarith
  have hLogPlus : Real.log ((X : Real) + 2) <= 2 + Real.log (M : Real) := by
    have h := Real.log_le_log (by linarith : 0 < (X : Real) + 2)
      (by linarith : (X : Real) + 2 <= 4 * (M : Real))
    rw [Real.log_mul (by norm_num : Not ((4 : Real) = 0)) (ne_of_gt hM0)] at h
    linarith
  have hRow0 : 0 <= 1 + Real.log (q : Real) + Real.log ((X : Real) + 2) := by
    have h := Real.log_nonneg (by linarith : (1 : Real) <= (X : Real) + 2)
    linarith
  have hRow : 1 + Real.log (q : Real) + Real.log ((X : Real) + 2) <=
      3 * (1 + Real.log (M : Real)) := by linarith
  have hRowSq : (1 + Real.log (q : Real) + Real.log ((X : Real) + 2)) ^ 2 <=
      9 * (1 + Real.log (M : Real)) ^ 2 := by nlinarith
  have hTot : (q.totient : Real) <= (P : Real) := by
    exact_mod_cast le_trans (Nat.totient_le q) hqP
  have hSqrt := Real.sqrt_le_sqrt hTot
  have hPow0 : 0 <= (M : Real) ^ (15 / 16 : Real) := Real.rpow_nonneg (le_of_lt hM0) _
  have hPow : (X : Real) ^ (15 / 16 : Real) <=
      2 * (M : Real) ^ (15 / 16 : Real) := by
    have h := Real.rpow_le_rpow (le_of_lt hX0) hXMR (by norm_num : (0 : Real) <= 15 / 16)
    rw [Real.mul_rpow (by norm_num : (0 : Real) <= 2) (le_of_lt hM0)] at h
    have h2 : (2 : Real) ^ (15 / 16 : Real) <= 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 2)
        (by norm_num : (15 / 16 : Real) <= 1)
      simpa using h
    exact le_trans h (mul_le_mul_of_nonneg_right h2 hPow0)
  have hLead : A * Real.sqrt (q.totient : Real) * (X : Real) ^ (15 / 16 : Real) *
      (1 + Real.log (q : Real) + Real.log ((X : Real) + 2)) ^ 2 <=
      18 * A * Real.sqrt (P : Real) * (M : Real) ^ (15 / 16 : Real) *
        (1 + Real.log (M : Real)) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hSqrt hA
    have h2 := mul_le_mul h1 hPow (Real.rpow_nonneg (le_of_lt hX0) _)
      (mul_nonneg hA (Real.sqrt_nonneg _))
    have h3 := mul_le_mul h2 hRowSq (sq_nonneg _)
      (mul_nonneg (mul_nonneg hA (Real.sqrt_nonneg _)) (mul_nonneg (by norm_num) hPow0))
    convert h3 using 1 <;> ring
  have hLogs : Real.log (q : Real) * Real.log (X : Real) <=
      (1 + Real.log (M : Real)) ^ 2 := by
    have h := mul_le_mul (by linarith : Real.log (q : Real) <= 1 + Real.log (M : Real))
      hLogXle hLogX (by linarith : 0 <= 1 + Real.log (M : Real))
    simpa only [pow_two] using h
  have hUnit : 1 <= Real.sqrt (P : Real) * (M : Real) ^ (15 / 16 : Real) := by
    have hs : 1 <= Real.sqrt (P : Real) := by
      have h := Real.sqrt_le_sqrt hPR
      simpa using h
    have hp : 1 <= (M : Real) ^ (15 / 16 : Real) := Real.one_le_rpow hMR (by norm_num)
    nlinarith
  have hRest : Real.log (q : Real) * Real.log (X : Real) / Real.log 2 <=
      (1 / Real.log 2) * Real.sqrt (P : Real) * (M : Real) ^ (15 / 16 : Real) *
        (1 + Real.log (M : Real)) ^ 2 := by
    have h1 := div_le_div_of_nonneg_right hLogs (le_of_lt hLog2)
    have h2 := mul_le_mul_of_nonneg_right hUnit
      (mul_nonneg (le_of_lt (one_div_pos.mpr hLog2)) (sq_nonneg (1 + Real.log (M : Real))))
    calc
      _ <= (1 + Real.log (M : Real)) ^ 2 / Real.log 2 := h1
      _ <= _ := by convert h2 using 1 <;> ring
  unfold lpfPhaseAllowance
  calc
    _ <= 18 * A * Real.sqrt (P : Real) * (M : Real) ^ (15 / 16 : Real) *
      (1 + Real.log (M : Real)) ^ 2 +
      (1 / Real.log 2) * Real.sqrt (P : Real) * (M : Real) ^ (15 / 16 : Real) *
      (1 + Real.log (M : Real)) ^ 2 := add_le_add hLead hRest
    _ = _ := by ring

theorem lpfGridRadians_le_major_cap {N : Nat} [NeZero N] (M P : Nat) (k : Int)
    (hM : 0 < M) (hDiv : Dvd.dvd M N)
    (hk : Membership.mem (Finset.Icc (-(((N / M) * P : Nat) : Int))
      (((N / M) * P : Nat) : Int)) k) :
    abs (lpfGridRadians N k) <= 8 * (P : Real) / (M : Real) := by
  have hNr : (0 : Real) < (N : Real) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hMr : (0 : Real) < (M : Real) := by exact_mod_cast hM
  have hKI : abs k <= (((N / M) * P : Nat) : Int) := abs_le.mpr (Finset.mem_Icc.mp hk)
  have hKR : abs (k : Real) <= (((N / M) * P : Nat) : Real) := by
    have h : ((abs k : Int) : Real) <= (((((N / M) * P : Nat) : Int) : Real)) :=
      Int.cast_le.mpr hKI
    simpa only [Int.cast_abs, Int.cast_natCast] using h
  have hD : ((N / M : Nat) : Real) * (M : Real) = (N : Real) := by
    exact_mod_cast Nat.div_mul_cancel hDiv
  have hPi : 2 * Real.pi <= (8 : Real) := by linarith [Real.pi_lt_four]
  have hPi0 : 0 <= 2 * Real.pi := by linarith [Real.pi_pos]
  unfold lpfGridRadians
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2),
    abs_of_pos Real.pi_pos, abs_of_pos hNr]
  calc
    _ <= 2 * Real.pi * (((N / M) * P : Nat) : Real) / (N : Real) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hKR hPi0) hNr.le
    _ <= 8 * (((N / M) * P : Nat) : Real) / (N : Real) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hPi (Nat.cast_nonneg _)) hNr.le
    _ = _ := by
      push_cast
      field_simp
      nlinarith [hD]

theorem exists_primeGridInterval_uniform_point_bound :
    exists K : Real, And (0 < K)
      (forall {N : Nat} [NeZero N] {q : Nat} [NeZero q] (a : Units (ZMod q)),
        forall (M P s L : Nat) (k : Int),
          0 < P -> 8 * P <= M -> Dvd.dvd M N -> Dvd.dvd q N -> q <= P ->
          65536 <= s -> L <= M -> s + L <= 2 * M ->
          Membership.mem (Finset.Icc (-(((N / M) * P : Nat) : Int))
            (((N / M) * P : Nat) : Int)) k ->
          norm (lpfGridIntervalWeight N s L (lpfRationalGridPoint N q (a : ZMod q).val k) -
            lpfRationalCoefficient q * lpfGridIntervalKernel N s L k) <=
            K * (P : Real) * Real.sqrt (P : Real) * (M : Real) ^ (15 / 16 : Real) *
              (1 + Real.log (M : Real)) ^ 2) := by
  choose A hA hSource using exists_primeGridInterval_point_power_bound
  let C : Real := 18 * A + 1 / Real.log 2
  have hC : 0 < C := by
    have hLog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
    dsimp [C]
    positivity
  refine Exists.intro (34 * C) (And.intro (by positivity) ?_)
  intro N instN q instQ a M P s L k hP hEight hDivM hDivQ hqP hs hL hX hk
  have hM : 0 < M := by omega
  have hMr : (0 : Real) < (M : Real) := by exact_mod_cast hM
  have hPr : (1 : Real) <= (P : Real) := by exact_mod_cast hP
  have hLr : (L : Real) <= (M : Real) := by exact_mod_cast hL
  have hEightR : 8 * (P : Real) <= (M : Real) := by exact_mod_cast hEight
  have hBeta := lpfGridRadians_le_major_cap M P k hM hDivM hk
  have hB1 : abs (lpfGridRadians N k) <= 1 := by
    have h := div_le_div_of_nonneg_right hEightR hMr.le
    simpa only [div_self (ne_of_gt hMr)] using hBeta.trans h
  have hB0 : 0 <= 8 * (P : Real) / (M : Real) := by positivity
  have hLB : (L : Real) * abs (lpfGridRadians N k) <= 8 * (P : Real) := by
    have h := mul_le_mul hLr hBeta (abs_nonneg _) hMr.le
    calc
      _ <= (M : Real) * (8 * (P : Real) / (M : Real)) := h
      _ = _ := by field_simp
  have hFactor : 2 * (1 + 2 * (L : Real) * abs (lpfGridRadians N k)) <=
      34 * (P : Real) := by nlinarith
  have hCap := lpfPhaseAllowance_le_major_cap A M P q (s + L) hA.le
    (by omega) (by omega) (Nat.pos_of_ne_zero (NeZero.ne q)) (by omega) hqP (by omega) hX
  have hEnvelope0 : 0 <= C * Real.sqrt (P : Real) * (M : Real) ^ (15 / 16 : Real) *
      (1 + Real.log (M : Real)) ^ 2 := by positivity
  have hFactor0 : 0 <= 2 * (1 + 2 * (L : Real) * abs (lpfGridRadians N k)) := by positivity
  have hProduct := mul_le_mul_of_nonneg_right hFactor hEnvelope0
  have hSourceBound := (hSource a s L k hDivQ hs hB1).trans
    (mul_le_mul_of_nonneg_left hCap hFactor0)
  calc
    _ <= 34 * (P : Real) *
      (C * Real.sqrt (P : Real) * (M : Real) ^ (15 / 16 : Real) *
        (1 + Real.log (M : Real)) ^ 2) := hSourceBound.trans hProduct
    _ = _ := by ring

theorem exists_primeGridInterval_uniform_error_bound :
    exists K : Real, And (0 < K)
      (forall {N : Nat} [NeZero N] (M P s L : Nat),
        0 < P -> 8 * P <= M -> Dvd.dvd M N ->
        (forall q, 0 < q -> q <= P -> Dvd.dvd q N) -> 2 * P ^ 3 < M ->
        65536 <= s -> L <= M -> s + L <= 2 * M ->
        forall x, Membership.mem (lpfRationalGrid N P ((N / M) * P)) x ->
          norm (lpfGridIntervalWeight N s L x -
            lpfRationalGridReference N P ((N / M) * P) (lpfGridIntervalKernel N s L) x) <=
            K * (P : Real) * Real.sqrt (P : Real) * (M : Real) ^ (15 / 16 : Real) *
              (1 + Real.log (M : Real)) ^ 2) := by
  choose K hK hPoint using exists_primeGridInterval_uniform_point_bound
  refine Exists.intro K (And.intro hK ?_)
  intro N instN M P s L hP hEight hDivM hDiv hSmall hs hL hX x hx
  have hM : 0 < M := by omega
  have hWidth := lpfRationalGrid_scaled_width M P hM hDivM hSmall
  have hInj := lpfRationalPacketPoint_injective P ((N / M) * P) hDiv hWidth
  choose u hu hux using Finset.mem_image.mp hx
  have hOffset := (Finset.mem_product.mp hu).2
  have hqP : u.1.1.val + 1 <= P := by have h := u.1.1.isLt; omega
  have hRef : lpfRationalGridReference N P ((N / M) * P) (lpfGridIntervalKernel N s L) x =
      lpfRationalCoefficient (u.1.1.val + 1) * lpfGridIntervalKernel N s L u.2 := by
    rw [<- hux]
    exact lpfGridReference_at _ _ _ hInj u hu
  rw [hRef, <- hux]
  exact hPoint u.1.2 M P s L u.2 hP hEight hDivM
    (hDiv _ (Nat.succ_pos _) hqP) hqP hs hL hX hOffset

theorem exists_primeGridInterval_complete_major_bound :
    exists K : Real, And (0 < K)
      (forall {N : Nat} [NeZero N] (M P s L : Nat) (T : Finset (ZMod N)),
        0 < P -> 8 * P <= M -> Dvd.dvd M N ->
        (forall q, 0 < q -> q <= P -> Dvd.dvd q N) -> 2 * P ^ 3 < M ->
        65536 <= s -> L <= M -> s + L <= 2 * M -> s + L < N ->
        Finset.sum T (fun t => Complex.normSq (lpfCyclicInverse
          (fun x => if Membership.mem (lpfRationalGrid N P ((N / M) * P)) x then
            (lpfGridIntervalWeight N s L x) ^ 2 -
            (lpfRationalGridReference N P ((N / M) * P) (lpfGridIntervalKernel N s L) x) ^ 2
            else 0) t)) <=
          8 * K ^ 2 * (P : Real) ^ 4 * ((M : Real) ^ (15 / 16 : Real)) ^ 2 *
            (M : Real) * (1 + Real.log (M : Real)) ^ 4 +
          6 * K ^ 4 * (P : Real) ^ 9 * ((M : Real) ^ (15 / 16 : Real)) ^ 4 *
            (1 + Real.log (M : Real)) ^ 8 / (M : Real)) := by
  choose K hK hError using exists_primeGridInterval_uniform_error_bound
  refine Exists.intro K (And.intro hK ?_)
  intro N instN M P s L T hP hEight hDivM hDiv hSmall hs hL hX hNoWrap
  have hM : 0 < M := by omega
  let E : Real := K * (P : Real) * Real.sqrt (P : Real) *
    (M : Real) ^ (15 / 16 : Real) * (1 + Real.log (M : Real)) ^ 2
  have hE : 0 <= E := by dsimp [E]; positivity
  have hCard : (lpfGridIntervalInputs s L).card <= M := by
    rw [lpfGridIntervalInputs_card]
    exact hL
  have hInputs : forall n, Membership.mem (lpfGridIntervalInputs s L) n -> n < N := by
    intro n hn
    exact (lpfGridIntervalInputs_le s L n hn).trans_lt hNoWrap
  have hErr : forall x, Membership.mem (lpfRationalGrid N P ((N / M) * P)) x ->
      norm (lpfGridIntervalWeight N s L x -
        lpfRationalGridReference N P ((N / M) * P)
          (fun k => lpfFiniteTransform (lpfGridIntervalInputs s L)
            (fun n => (n : ZMod N)) (fun _ => (1 : Complex)) (k : ZMod N)) x) <= E := by
    intro x hx
    simpa only [<- lpfGridIntervalKernel_eq_transform] using
      hError M P s L hP hEight hDivM hDiv hSmall hs hL hX x hx
  have hBound := lpfRationalGrid_complete_major_bound M P (lpfGridIntervalInputs s L)
    (lpfGridIntervalWeight N s L) T E hM hP hE hDivM hDiv hSmall hCard hInputs hErr
  simp only [<- lpfGridIntervalKernel_eq_transform] at hBound
  have hSqrt : Real.sqrt (P : Real) ^ 2 = (P : Real) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hSqrt4 : Real.sqrt (P : Real) ^ 4 = (P : Real) ^ 2 := by
    calc
      _ = (Real.sqrt (P : Real) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hSqrt]
  have hAlg : 8 * E ^ 2 * (P : Real) * (M : Real) +
      6 * E ^ 4 * (P : Real) ^ 3 / (M : Real) =
      8 * K ^ 2 * (P : Real) ^ 4 * ((M : Real) ^ (15 / 16 : Real)) ^ 2 *
        (M : Real) * (1 + Real.log (M : Real)) ^ 4 +
      6 * K ^ 4 * (P : Real) ^ 9 * ((M : Real) ^ (15 / 16 : Real)) ^ 4 *
        (1 + Real.log (M : Real)) ^ 8 / (M : Real) := by
    dsimp [E]
    ring_nf
    simp only [hSqrt4, hSqrt]
    ring
  exact hBound.trans_eq hAlg

end PrimeFactorOscillations.LPF
