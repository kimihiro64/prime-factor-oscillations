/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMajorPhaseNumeric

/-!
# Numerical complete arithmetic major packet

The phase coefficient 65536 yields
34*(18*65536 + 1/log(2)) <= 67108864 = 2^26.
This one constant controls the complete interval/grid square difference,
including the quadratic and quartic error contributions. The denominator
and grid ranges are retained, and no orbit equidistribution is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

theorem lpf_primeGridInterval_uniform_point_numeric :
    forall {N : Nat} [NeZero N] {q : Nat} [NeZero q] (a : Units (ZMod q)),
        forall (M P s L : Nat) (k : Int),
          0 < P -> 8 * P <= M -> Dvd.dvd M N -> Dvd.dvd q N -> q <= P ->
          65536 <= s -> L <= M -> s + L <= 2 * M ->
          Membership.mem (Finset.Icc (-(((N / M) * P : Nat) : Int))
            (((N / M) * P : Nat) : Int)) k ->
          norm (lpfGridIntervalWeight N s L (lpfRationalGridPoint N q (a : ZMod q).val k) -
            lpfRationalCoefficient q * lpfGridIntervalKernel N s L k) <=
            67108864 * (P : Real) * Real.sqrt (P : Real) * (M : Real) ^ (15 / 16 : Real) *
              (1 + Real.log (M : Real)) ^ 2 := by
  let A : Real := 65536
  have hA : 0 < A := by norm_num [A]
  let C : Real := 18 * A + 1 / Real.log 2
  have hC : 0 < C := by
    have hLog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
    dsimp [C]
    positivity
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
  have hSourceBound := (lpf_primeGridInterval_point_numeric a s L k hDivQ hs hB1).trans
    (mul_le_mul_of_nonneg_left hCap hFactor0)
  calc
    _ <= 34 * (P : Real) *
      (C * Real.sqrt (P : Real) * (M : Real) ^ (15 / 16 : Real) *
        (1 + Real.log (M : Real)) ^ 2) := hSourceBound.trans hProduct
    _ = (34 * C) * ((P : Real) * Real.sqrt (P : Real) *
        (M : Real) ^ (15 / 16 : Real) * (1 + Real.log (M : Real)) ^ 2) := by ring
    _ <= 67108864 * ((P : Real) * Real.sqrt (P : Real) *
        (M : Real) ^ (15 / 16 : Real) * (1 + Real.log (M : Real)) ^ 2) := by
      have hLog : (1 / 2 : Real) <= Real.log (2 : Real) := by
        have hi := Real.log_le_sub_one_of_pos
          (by norm_num : (0 : Real) < (2 : Real) ^ (-1 : Int))
        rw [zpow_neg_one, Real.log_inv] at hi
        norm_num at hi
        linarith
      have hLog0 : 0 < Real.log (2 : Real) := by linarith
      have hTwo : (1 : Real) / Real.log (2 : Real) <= 2 := by
        apply (mul_le_mul_iff_of_pos_right hLog0).mp
        have hCancel : ((1 : Real) / Real.log (2 : Real)) * Real.log (2 : Real) = 1 := by
          field_simp
        rw [hCancel]
        linarith
      have hK : 34 * C <= 67108864 := by dsimp [C, A]; linarith
      exact mul_le_mul_of_nonneg_right hK (by positivity)
    _ = _ := by ring

theorem lpf_primeGridInterval_uniform_error_numeric :
    forall {N : Nat} [NeZero N] (M P s L : Nat),
        0 < P -> 8 * P <= M -> Dvd.dvd M N ->
        (forall q, 0 < q -> q <= P -> Dvd.dvd q N) -> 2 * P ^ 3 < M ->
        65536 <= s -> L <= M -> s + L <= 2 * M ->
        forall x, Membership.mem (lpfRationalGrid N P ((N / M) * P)) x ->
          norm (lpfGridIntervalWeight N s L x -
            lpfRationalGridReference N P ((N / M) * P) (lpfGridIntervalKernel N s L) x) <=
            67108864 * (P : Real) * Real.sqrt (P : Real) * (M : Real) ^ (15 / 16 : Real) *
              (1 + Real.log (M : Real)) ^ 2 := by
  classical
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
  exact lpf_primeGridInterval_uniform_point_numeric u.1.2 M P s L u.2 hP hEight hDivM
    (hDiv _ (Nat.succ_pos _) hqP) hqP hs hL hX hOffset

theorem lpf_primeGridInterval_complete_major_numeric :
    forall {N : Nat} [NeZero N] (M P s L : Nat) (T : Finset (ZMod N)),
        0 < P -> 8 * P <= M -> Dvd.dvd M N ->
        (forall q, 0 < q -> q <= P -> Dvd.dvd q N) -> 2 * P ^ 3 < M ->
        65536 <= s -> L <= M -> s + L <= 2 * M -> s + L < N ->
        Finset.sum T (fun t => Complex.normSq (lpfCyclicInverse
          (fun x => if Membership.mem (lpfRationalGrid N P ((N / M) * P)) x then
            (lpfGridIntervalWeight N s L x) ^ 2 -
            (lpfRationalGridReference N P ((N / M) * P) (lpfGridIntervalKernel N s L) x) ^ 2
            else 0) t)) <=
          8 * 67108864 ^ 2 * (P : Real) ^ 4 * ((M : Real) ^ (15 / 16 : Real)) ^ 2 *
            (M : Real) * (1 + Real.log (M : Real)) ^ 4 +
          6 * 67108864 ^ 4 * (P : Real) ^ 9 * ((M : Real) ^ (15 / 16 : Real)) ^ 4 *
            (1 + Real.log (M : Real)) ^ 8 / (M : Real) := by
  classical
  intro N instN M P s L T hP hEight hDivM hDiv hSmall hs hL hX hNoWrap
  have hM : 0 < M := by omega
  let E : Real := 67108864 * (P : Real) * Real.sqrt (P : Real) *
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
      lpf_primeGridInterval_uniform_error_numeric M P s L hP hEight hDivM hDiv hSmall hs hL hX x hx
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
      8 * 67108864 ^ 2 * (P : Real) ^ 4 * ((M : Real) ^ (15 / 16 : Real)) ^ 2 *
        (M : Real) * (1 + Real.log (M : Real)) ^ 4 +
      6 * 67108864 ^ 4 * (P : Real) ^ 9 * ((M : Real) ^ (15 / 16 : Real)) ^ 4 *
        (1 + Real.log (M : Real)) ^ 8 / (M : Real) := by
    dsimp [E]
    ring_nf
    simp only [hSqrt4, hSqrt]
    ring
  exact hBound.trans_eq hAlg

end PrimeFactorOscillations.LPF

