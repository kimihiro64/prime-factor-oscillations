/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFAveragedCorrections
import PrimeFactorOscillations.Helpers.LPFMinorMeanSquare
import PrimeFactorOscillations.Helpers.LPFSourcePower

/-!
# Complete averaged fixed-interval source budget

All four exact signed packets are retained. The minor, kernel and weighted
singular tail have explicit constants. The major-arc constant K is the sole
unspecified source constant. With the floor cutoff, the complete energy has
exponent 119/40 and logarithmic power twelve. This is a source estimate, not
an entry certificate for the orbit from two.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_fixed_source_mean_four_packet_budget :
    exists K : Real, And (0 < K)
      (forall {N : Nat} [NeZero N] (M P s L : Nat) (T : Finset Nat),
        2 ^ 18 <= M -> 0 < P ->
        (P : Real) <= (M : Real) ^ ((1 : Real) / 40) ->
        Dvd.dvd M N -> (forall q, 0 < q -> q <= P -> Dvd.dvd q N) ->
        (M : Real) / 4 <= (s : Real) -> s + L <= 2 * M -> L <= M -> s + L < N ->
        2 * M < N -> (forall n, Membership.mem T n -> And (0 < n) (n <= 2 * M)) ->
        Finset.sum T (fun n => norm (lpfFixedSourceError N s L n) ^ 2) <=
          4 * ((8 * K ^ 2 * (1 + Real.log (M : Real)) ^ 4 +
                6 * K ^ 4 * (1 + Real.log (M : Real)) ^ 8) * (M : Real) ^ (119 / 40 : Real) +
            32768 * ((M : Real) ^ 3 / (P : Real) + (M : Real) ^ (13 / 5 : Real)) *
              (1 + Real.log (2 * (M : Real))) ^ 12 +
            (289 / 2 : Real) * (M : Real) ^ 3 *
              (1 + Real.log (2 * (M : Real))) ^ 3 / (P : Real) ^ 2 +
            512 * (M : Real) ^ 3 * (1 + Real.log (2 * (M : Real))) ^ 3 / (P : Real))) := by
  classical
  choose K hK hMajor using exists_primeGridInterval_major_power_bound
  refine Exists.intro K (And.intro hK ?_)
  intro N instN M P s L T hM hP hPower hDivM hDiv hStart hTop hL hInput hNTop hT
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hMPos : 0 < M := by omega
  have hPOne : 1 <= P := by omega
  have hMajorConditions := lpf_warm_major_conditions M P hM hP hPower
  have hMReal : (262144 : Real) <= (M : Real) := by exact_mod_cast hM
  have hStartReal : (65536 : Real) <= (s : Real) := by linarith only [hMReal, hStart]
  have hStartNat : 65536 <= s := by exact_mod_cast hStartReal
  have hQuot : 0 < N / M := Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hDivM) hMPos
  have hWidth : 2 * ((N / M) * P) * P ^ 2 < N := by
    calc
      _ = (N / M) * (2 * P ^ 3) := by ring
      _ < (N / M) * M := Nat.mul_lt_mul_of_pos_left hMajorConditions.2 hQuot
      _ = _ := Nat.div_mul_cancel hDivM
  let G : Finset (ZMod N) := lpfRationalGrid N P ((N / M) * P)
  let A : ZMod N -> Complex := lpfRationalGridReference N P ((N / M) * P) (lpfGridIntervalKernel N s L)
  let F : ZMod N -> Complex := fun t => lpfCyclicInverse
    (fun x => if Membership.mem G x then lpfGridIntervalWeight N s L x ^ 2 - A x ^ 2 else 0) t
  let H : ZMod N -> Complex := fun t => lpfCyclicInverse
    (fun x => if Membership.mem G x then 0 else lpfGridIntervalWeight N s L x ^ 2) t
  have hTargetInput (n : Nat) (hn : Membership.mem T n) : n < N := (hT n hn).2.trans_lt hNTop
  have hMaj := hMajor (N := N) M P s L (T.image (fun n : Nat => (n : ZMod N)))
    hP hMajorConditions.1 hDivM hDiv hMajorConditions.2 hStartNat hL hTop hInput hPower
  rw [<- lpf_nat_grid_square_sum_eq_image T F hTargetInput] at hMaj
  have hMin := lpf_grid_minor_meanSquare_explicit_bound (N := N) M P s L hM hP hPower hDivM hDiv hStart hTop hL hInput
    (T.image (fun n : Nat => (n : ZMod N)))
  rw [<- lpf_nat_grid_square_sum_eq_image T H hTargetInput] at hMin
  have hKer := lpf_kernel_correction_physical_mean_bound (N := N) M P s L T hMPos hP hDivM hT
  let w : Nat -> Complex := fun n => lpfIntervalPairCount N s L (n : ZMod N)
  have hWeight (n : Nat) (_hn : Membership.mem T n) : norm (w n) <= (M : Real) :=
    (norm_lpfIntervalPairCount_le s L (n : ZMod N) hInput).trans
      (by exact_mod_cast hL)
  have hTailBudget := lpf_weighted_singular_tail_physical_mean_bound M P T w hMPos hPOne hT hWeight
  have hSign (n : Nat) : norm (w n * (lpfSingularPartial P n - lpfSingularSeries n)) ^ 2 =
      norm (w n * (lpfSingularSeries n - lpfSingularPartial P n)) ^ 2 := by
    rw [show w n * (lpfSingularPartial P n - lpfSingularSeries n) =
      -(w n * (lpfSingularSeries n - lpfSingularPartial P n)) by ring, norm_neg]
  have hTailOriginal : Finset.sum T (fun n =>
      norm (lpfIntervalPairCount N s L (n : ZMod N) *
        (lpfSingularPartial P n - lpfSingularSeries n)) ^ 2) <=
      512 * (M : Real) ^ 3 * (1 + Real.log (2 * (M : Real))) ^ 3 / (P : Real) := by
    change Finset.sum T (fun n => norm (w n * (lpfSingularPartial P n - lpfSingularSeries n)) ^ 2) <= _
    simp_rw [hSign]
    exact hTailBudget
  have hExact (n : Nat) : lpfFixedSourceError N s L n =
      F (n : ZMod N) + H (n : ZMod N) + lpfIntervalKernelCorrection N M P s L n +
        lpfIntervalPairCount N s L (n : ZMod N) * (lpfSingularPartial P n - lpfSingularSeries n) := by
    have h := lpf_fixed_interval_source_four_packets P ((N / M) * P) s L n hP hDiv hWidth
    unfold lpfIntervalKernelCorrection
    rw [lpfIntervalFrequencyKernel_inverse_square]
    exact h
  calc
    _ <= Finset.sum T (fun n => 4 * (norm (F (n : ZMod N)) ^ 2 + norm (H (n : ZMod N)) ^ 2 +
        norm (lpfIntervalKernelCorrection N M P s L n) ^ 2 +
        norm (lpfIntervalPairCount N s L (n : ZMod N) *
          (lpfSingularPartial P n - lpfSingularSeries n)) ^ 2)) := by
      apply Finset.sum_le_sum
      intro n _
      rw [hExact n]
      exact lpf_norm_four_add_sq_le _ _ _ _
    _ = 4 * (Finset.sum T (fun n => norm (F (n : ZMod N)) ^ 2) +
        Finset.sum T (fun n => norm (H (n : ZMod N)) ^ 2) +
        Finset.sum T (fun n => norm (lpfIntervalKernelCorrection N M P s L n) ^ 2) +
        Finset.sum T (fun n => norm (lpfIntervalPairCount N s L (n : ZMod N) *
          (lpfSingularPartial P n - lpfSingularSeries n)) ^ 2)) := by
      rw [<- Finset.mul_sum]
      simp only [Finset.sum_add_distrib]
    _ <= _ := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add hMaj hMin) hKer) hTailOriginal) (by norm_num)

theorem lpf_source_log_power_le_twelve (M k : Nat) (hM : 1 <= M) (hk : k <= 12) :
    (1 + Real.log (M : Real)) ^ k <= (1 + Real.log (2 * (M : Real))) ^ 12 := by
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hM
  have hPos : (0 : Real) < (M : Real) := by linarith only [hMR]
  have hLog := Real.log_nonneg hMR
  have hLogLe : Real.log (M : Real) <= Real.log (2 * (M : Real)) :=
    Real.log_le_log hPos (by linarith only [hMR])
  have hEll : 1 <= 1 + Real.log (2 * (M : Real)) := by linarith only [hLog, hLogLe]
  calc
    _ <= (1 + Real.log (2 * (M : Real))) ^ k := by gcongr
    _ = (1 + Real.log (2 * (M : Real))) ^ (k : Real) := (Real.rpow_natCast _ _).symm
    _ <= (1 + Real.log (2 * (M : Real))) ^ (12 : Real) :=
      Real.rpow_le_rpow_of_exponent_le hEll (by exact_mod_cast hk)
    _ = _ := Real.rpow_natCast _ 12

theorem lpf_source_mean_four_packet_envelope (M P : Nat) (K C B D : Real)
    (hM : 1 <= M) (hP : 0 < P) (hC : 0 <= C) (hB : 0 <= B) (hD : 0 <= D)
    (hLower : (M : Real) ^ ((1 : Real) / 40) / 2 <= (P : Real)) :
    (8 * K ^ 2 * (1 + Real.log (M : Real)) ^ 4 +
        6 * K ^ 4 * (1 + Real.log (M : Real)) ^ 8) * (M : Real) ^ (119 / 40 : Real) +
      C * ((M : Real) ^ 3 / (P : Real) + (M : Real) ^ (13 / 5 : Real)) *
        (1 + Real.log (2 * (M : Real))) ^ 12 +
      B * (M : Real) ^ 3 * (1 + Real.log (2 * (M : Real))) ^ 3 / (P : Real) ^ 2 +
      D * (M : Real) ^ 3 * (1 + Real.log (2 * (M : Real))) ^ 3 / (P : Real) <=
    (8 * K ^ 2 + 6 * K ^ 4 + 3 * C + 4 * B + 2 * D) *
      (M : Real) ^ (119 / 40 : Real) * (1 + Real.log (2 * (M : Real))) ^ 12 := by
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hM
  have hMPos : 0 < M := by omega
  have hPos : (0 : Real) < (M : Real) := by linarith only [hMR]
  have hPR : (0 : Real) < (P : Real) := by exact_mod_cast hP
  have hExp (a b : Real) (hab : a <= b) : (M : Real) ^ a <= (M : Real) ^ b :=
    Real.rpow_le_rpow_of_exponent_le hMR hab
  have hDiv3 := lpf_source_cutoff_div_rpow_le M P hMPos hP hLower 3
  have hDiv119 := lpf_source_cutoff_div_rpow_le M P hMPos hP hLower (119 / 40)
  norm_num at hDiv3 hDiv119
  have hCScale : (M : Real) ^ 3 / (P : Real) + (M : Real) ^ (13 / 5 : Real) <=
      3 * (M : Real) ^ (119 / 40 : Real) := by
    have hSmall := hExp (13 / 5) (119 / 40) (by norm_num)
    linarith only [hDiv3, hSmall]
  have hBScale : (M : Real) ^ 3 / (P : Real) ^ 2 <=
      4 * (M : Real) ^ (119 / 40 : Real) := by
    have hTwice := div_le_div_of_nonneg_right hDiv3 hPR.le
    have hSmall := hExp (59 / 20) (119 / 40) (by norm_num)
    calc
      _ = ((M : Real) ^ 3 / (P : Real)) / (P : Real) := by rw [div_div, pow_two]
      _ <= (2 * (M : Real) ^ (119 / 40 : Real)) / (P : Real) := hTwice
      _ = 2 * ((M : Real) ^ (119 / 40 : Real) / (P : Real)) := by ring
      _ <= 4 * (M : Real) ^ (59 / 20 : Real) := by linarith only [hDiv119]
      _ <= _ := by linarith only [hSmall]
  have h4 := lpf_source_log_power_le_twelve M 4 hM (by norm_num)
  have h8 := lpf_source_log_power_le_twelve M 8 hM (by norm_num)
  have h3 := lpf_source_log_power_le_twelve M 3 hM (by norm_num)
  have hLog : 0 <= Real.log (2 * (M : Real)) :=
    Real.log_nonneg (by linarith only [hMR])
  have hLog3 : (1 + Real.log (2 * (M : Real))) ^ 3 <=
      (1 + Real.log (2 * (M : Real))) ^ 12 := by
    have hEll : 1 <= 1 + Real.log (2 * (M : Real)) := by linarith only [hLog]
    calc
      _ = (1 + Real.log (2 * (M : Real))) ^ (3 : Real) := (Real.rpow_natCast _ _).symm
      _ <= (1 + Real.log (2 * (M : Real))) ^ (12 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hEll (by norm_num)
      _ = _ := Real.rpow_natCast _ _
  have hMajor :
      (8 * K ^ 2 * (1 + Real.log (M : Real)) ^ 4 +
        6 * K ^ 4 * (1 + Real.log (M : Real)) ^ 8) * (M : Real) ^ (119 / 40 : Real) <=
      (8 * K ^ 2 + 6 * K ^ 4) * (M : Real) ^ (119 / 40 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 12 := by
    calc
      _ <= (8 * K ^ 2 * (1 + Real.log (2 * (M : Real))) ^ 12 +
        6 * K ^ 4 * (1 + Real.log (2 * (M : Real))) ^ 12) *
          (M : Real) ^ (119 / 40 : Real) := by gcongr
      _ = _ := by ring
  have hMinor : C * ((M : Real) ^ 3 / (P : Real) + (M : Real) ^ (13 / 5 : Real)) *
      (1 + Real.log (2 * (M : Real))) ^ 12 <=
      3 * C * (M : Real) ^ (119 / 40 : Real) * (1 + Real.log (2 * (M : Real))) ^ 12 := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCScale hC)
      (by positivity : 0 <= (1 + Real.log (2 * (M : Real))) ^ 12)
    nlinarith only [h]
  have hKernel : B * (M : Real) ^ 3 * (1 + Real.log (2 * (M : Real))) ^ 3 / (P : Real) ^ 2 <=
      4 * B * (M : Real) ^ (119 / 40 : Real) * (1 + Real.log (2 * (M : Real))) ^ 12 := by
    calc
      _ = B * ((M : Real) ^ 3 / (P : Real) ^ 2) * (1 + Real.log (2 * (M : Real))) ^ 3 := by ring
      _ <= B * (4 * (M : Real) ^ (119 / 40 : Real)) * (1 + Real.log (2 * (M : Real))) ^ 12 := by gcongr
      _ = _ := by ring
  have hTail : D * (M : Real) ^ 3 * (1 + Real.log (2 * (M : Real))) ^ 3 / (P : Real) <=
      2 * D * (M : Real) ^ (119 / 40 : Real) * (1 + Real.log (2 * (M : Real))) ^ 12 := by
    calc
      _ = D * ((M : Real) ^ 3 / (P : Real)) * (1 + Real.log (2 * (M : Real))) ^ 3 := by ring
      _ <= D * (2 * (M : Real) ^ (119 / 40 : Real)) * (1 + Real.log (2 * (M : Real))) ^ 12 := by gcongr
      _ = _ := by ring
  have hTotal := add_le_add (add_le_add (add_le_add hMajor hMinor) hKernel) hTail
  nlinarith only [hTotal]

theorem lpf_fixed_source_mean_log_power_bound :
    exists K : Real, And (0 < K)
      (forall {N : Nat} [NeZero N] (M s L : Nat) (T : Finset Nat),
        2 ^ 18 <= M -> Dvd.dvd M N ->
        (forall q, 0 < q -> q <= lpfSourceCutoff M -> Dvd.dvd q N) ->
        (M : Real) / 4 <= (s : Real) -> s + L <= 2 * M -> L <= M -> s + L < N ->
        2 * M < N -> (forall n, Membership.mem T n -> And (0 < n) (n <= 2 * M)) ->
        Finset.sum T (fun n => norm (lpfFixedSourceError N s L n) ^ 2) <=
          4 * (8 * K ^ 2 + 6 * K ^ 4 + 99906) *
            (M : Real) ^ (119 / 40 : Real) * (1 + Real.log (2 * (M : Real))) ^ 12) := by
  choose K hK hBudget using lpf_fixed_source_mean_four_packet_budget
  refine Exists.intro K (And.intro hK ?_)
  intro N instN M s L T hM hDivM hDiv hStart hTop hL hInput hNTop hT
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hCut := lpf_source_cutoff_bounds M hOne
  have h := hBudget M (lpfSourceCutoff M) s L T hM hCut.1 hCut.2.1
    hDivM hDiv hStart hTop hL hInput hNTop hT
  have hEnvelope := lpf_source_mean_four_packet_envelope M (lpfSourceCutoff M)
    K 32768 (289 / 2) 512 hOne hCut.1 (by norm_num) (by norm_num) (by norm_num) hCut.2.2
  have hFinal := h.trans (mul_le_mul_of_nonneg_left hEnvelope (show (0 : Real) <= 4 by norm_num))
  calc
    _ <= 4 * ((8 * K ^ 2 + 6 * K ^ 4 + 3 * 32768 + 4 * (289 / 2) + 2 * 512) *
      (M : Real) ^ (119 / 40 : Real) * (1 + Real.log (2 * (M : Real))) ^ 12) := hFinal
    _ = _ := by norm_num; ring

end PrimeFactorOscillations.LPF
