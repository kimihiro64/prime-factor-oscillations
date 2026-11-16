/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimePrefixMinor
import PrimeFactorOscillations.Helpers.LPFUniformMajorNumeric

/-! # Independent major-arc denominator and width, with the whole prefix

The existing all-character arithmetic estimate is applied with denominator
cutoff Q and independently chosen offset width T. The initial 65536 terms
and their reference contribution are retained in an explicit constant.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_major_grid_point :
    forall {N : Nat} [NeZero N] {q : Nat} [NeZero q] (a : Units (ZMod q)),
        forall (M Q T s L : Nat) (k : Int),
          0 < Q -> Q <= M -> 0 < T -> 8 * T <= M -> Dvd.dvd M N -> Dvd.dvd q N -> q <= Q ->
          65536 <= s -> L <= M -> s + L <= 2 * M ->
          Membership.mem (Finset.Icc (-(((N / M) * T : Nat) : Int))
            (((N / M) * T : Nat) : Int)) k ->
          norm (lpfGridIntervalWeight N s L (lpfRationalGridPoint N q (a : ZMod q).val k) -
            lpfRationalCoefficient q * lpfGridIntervalKernel N s L k) <=
            67108864 * (T : Real) * Real.sqrt (Q : Real) * (M : Real) ^ (15 / 16 : Real) *
              (1 + Real.log (M : Real)) ^ 2 := by
  let A : Real := 65536
  have hA : 0 < A := by norm_num [A]
  let C : Real := 18 * A + 1 / Real.log 2
  have hC : 0 < C := by
    have hLog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
    dsimp [C]
    positivity
  intro N instN q instQ a M Q T s L k hQ hQM hP hEight hDivM hDivQ hqP hs hL hX hk
  have hM : 0 < M := by omega
  have hMr : (0 : Real) < (M : Real) := by exact_mod_cast hM
  have hPr : (1 : Real) <= (T : Real) := by exact_mod_cast hP
  have hLr : (L : Real) <= (M : Real) := by exact_mod_cast hL
  have hEightR : 8 * (T : Real) <= (M : Real) := by exact_mod_cast hEight
  have hBeta := lpfGridRadians_le_major_cap M T k hM hDivM hk
  have hB1 : abs (lpfGridRadians N k) <= 1 := by
    have h := div_le_div_of_nonneg_right hEightR hMr.le
    simpa only [div_self (ne_of_gt hMr)] using hBeta.trans h
  have hB0 : 0 <= 8 * (T : Real) / (M : Real) := by positivity
  have hLB : (L : Real) * abs (lpfGridRadians N k) <= 8 * (T : Real) := by
    have h := mul_le_mul hLr hBeta (abs_nonneg _) hMr.le
    calc
      _ <= (M : Real) * (8 * (T : Real) / (M : Real)) := h
      _ = _ := by field_simp
  have hFactor : 2 * (1 + 2 * (L : Real) * abs (lpfGridRadians N k)) <=
      34 * (T : Real) := by nlinarith
  have hCap := lpfPhaseAllowance_le_major_cap A M Q q (s + L) hA.le
    (by omega) (by omega) (Nat.pos_of_ne_zero (NeZero.ne q)) (by omega) hqP (by omega) hX
  have hEnvelope0 : 0 <= C * Real.sqrt (Q : Real) * (M : Real) ^ (15 / 16 : Real) *
      (1 + Real.log (M : Real)) ^ 2 := by positivity
  have hFactor0 : 0 <= 2 * (1 + 2 * (L : Real) * abs (lpfGridRadians N k)) := by positivity
  have hProduct := mul_le_mul_of_nonneg_right hFactor hEnvelope0
  have hSourceBound := (lpf_primeGridInterval_point_numeric a s L k hDivQ hs hB1).trans
    (mul_le_mul_of_nonneg_left hCap hFactor0)
  calc
    _ <= 34 * (T : Real) *
      (C * Real.sqrt (Q : Real) * (M : Real) ^ (15 / 16 : Real) *
        (1 + Real.log (M : Real)) ^ 2) := hSourceBound.trans hProduct
    _ = (34 * C) * ((T : Real) * Real.sqrt (Q : Real) *
        (M : Real) ^ (15 / 16 : Real) * (1 + Real.log (M : Real)) ^ 2) := by ring
    _ <= 67108864 * ((T : Real) * Real.sqrt (Q : Real) *
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

theorem hamiltonian_interval_kernel_add {N : Nat} [NeZero N]
    (s A B : Nat) (k : Int) :
    lpfGridIntervalKernel N s (A + B) k =
      lpfGridIntervalKernel N s A k + lpfGridIntervalKernel N (s + A) B k := by
  unfold lpfGridIntervalKernel
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hIndex : s + 1 + (A + i) = (s + A) + 1 + i := by omega
  rw [hIndex]

theorem hamiltonian_interval_kernel_trivial {N : Nat} [NeZero N]
    (s L : Nat) (k : Int) :
    norm (lpfGridIntervalKernel N s L k) <= (L : Real) := by
  unfold lpfGridIntervalKernel
  calc
    _ <= (Finset.range L).sum (fun i =>
        norm (ZMod.stdAddChar (N := N) ((k : ZMod N) * ((s + 1 + i : Nat) : ZMod N)))) :=
      norm_sum_le _ _
    _ = _ := by
      simp only [ZMod.stdAddChar_apply, Circle.norm_coe, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one]

theorem hamiltonian_prime_prefix_major {N : Nat} [NeZero N]
    {q : Nat} [NeZero q] (a : Units (ZMod q))
    (M Q T : Nat) (k : Int)
    (hM : 65536 <= M) (hQ : 0 < Q) (hQM : Q <= M) (hT : 0 < T) (hEight : 8 * T <= M)
    (hDivM : Dvd.dvd M N) (hDivQ : Dvd.dvd q N) (hqQ : q <= Q)
    (hk : Membership.mem (Finset.Icc (-(((N / M) * T : Nat) : Int))
      (((N / M) * T : Nat) : Int)) k) :
    norm (lpfGridIntervalWeight N 0 M (lpfRationalGridPoint N q (a : ZMod q).val k) -
      lpfRationalCoefficient q * lpfGridIntervalKernel N 0 M k) <=
      65536 * (Real.log 65536 + 1) +
        67108864 * (T : Real) * Real.sqrt (Q : Real) * (M : Real) ^ (15 / 16 : Real) *
          (1 + Real.log (M : Real)) ^ 2 := by
  let B : Nat := 65536
  let x := lpfRationalGridPoint N q (a : ZMod q).val k
  let rho := lpfRationalCoefficient q
  have hTotal : B + (M - B) = M := by dsimp [B]; omega
  have hTail := hamiltonian_prime_major_grid_point a M Q T B (M - B) k
    hQ hQM hT hEight hDivM hDivQ hqQ (le_refl B) (by omega) (by omega) hk
  have hSplit : lpfGridIntervalWeight N 0 M x =
      lpfGridIntervalWeight N 0 B x + lpfGridIntervalWeight N B (M - B) x := by
    have h := hamiltonian_prime_grid_interval_add (N := N) 0 B (M - B) (x.val : Int)
    simpa only [hTotal, Nat.zero_add, Int.cast_natCast, ZMod.natCast_zmod_val] using h
  have hKernel : lpfGridIntervalKernel N 0 M k =
      lpfGridIntervalKernel N 0 B k + lpfGridIntervalKernel N B (M - B) k := by
    have h := hamiltonian_interval_kernel_add (N := N) 0 B (M - B) k
    simpa only [hTotal, Nat.zero_add] using h
  have hHead := hamiltonian_prime_grid_interval_trivial (N := N) 0 B B
    (by norm_num [B]) (by omega) (x.val : Int)
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at hHead
  have hPhi : (1 : Real) <= (q.totient : Real) := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)))
  have hRho : norm rho <= 1 := by
    have h := norm_lpfRationalCoefficient_le q (Nat.pos_of_ne_zero (NeZero.ne q))
    apply h.trans
    exact (div_le_one (by linarith : (0 : Real) < (q.totient : Real))).mpr hPhi
  have hReference : norm (rho * lpfGridIntervalKernel N 0 B k) <= (B : Real) := by
    rw [norm_mul]
    exact (mul_le_mul hRho (hamiltonian_interval_kernel_trivial 0 B k)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hHeadError : norm (lpfGridIntervalWeight N 0 B x -
      rho * lpfGridIntervalKernel N 0 B k) <= 65536 * (Real.log 65536 + 1) := by
    calc
      _ <= norm (lpfGridIntervalWeight N 0 B x) +
        norm (rho * lpfGridIntervalKernel N 0 B k) := norm_sub_le _ _
      _ <= (B : Real) * Real.log (B : Real) + (B : Real) := add_le_add hHead hReference
      _ = _ := by norm_num [B]; ring
  have hExact : lpfGridIntervalWeight N 0 M x - rho * lpfGridIntervalKernel N 0 M k =
      (lpfGridIntervalWeight N 0 B x - rho * lpfGridIntervalKernel N 0 B k) +
        (lpfGridIntervalWeight N B (M - B) x - rho * lpfGridIntervalKernel N B (M - B) k) := by
    rw [hSplit, hKernel]
    ring
  change norm (lpfGridIntervalWeight N 0 M x - rho * lpfGridIntervalKernel N 0 M k) <= _
  rw [hExact]
  exact (norm_add_le _ _).trans (add_le_add hHeadError hTail)

end PrimeFactorOscillations.LPF
