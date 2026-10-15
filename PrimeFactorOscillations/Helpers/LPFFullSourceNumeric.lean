/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFAveragedSourceBudget
import PrimeFactorOscillations.Helpers.LPFUniformMajorNumeric

/-!
# Fully numerical complete fixed-interval source energy

The major constant 2^26, minor constant 32768, kernel correction 289/2,
and singular tail constant 512 enter the same four-packet inequality.
At the floor cutoff P=floor(M^(1/40)), their complete coefficient is
4*(8*(2^26)^2 + 6*(2^26)^4 + 99906), bounded by 2^109.
The result retains every interval, divisibility and no-wrap premise.
A numerical full orbit-entry threshold is a separate remaining obligation.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_primeGridInterval_major_power_numeric :
    forall {N : Nat} [NeZero N] (M P s L : Nat) (T : Finset (ZMod N)),
        0 < P -> 8 * P <= M -> Dvd.dvd M N ->
        (forall q, 0 < q -> q <= P -> Dvd.dvd q N) -> 2 * P ^ 3 < M ->
        65536 <= s -> L <= M -> s + L <= 2 * M -> s + L < N ->
        (P : Real) <= (M : Real) ^ (1 / 40 : Real) ->
        Finset.sum T (fun t => Complex.normSq (lpfCyclicInverse
          (fun x => if Membership.mem (lpfRationalGrid N P ((N / M) * P)) x then
            (lpfGridIntervalWeight N s L x) ^ 2 -
            (lpfRationalGridReference N P ((N / M) * P) (lpfGridIntervalKernel N s L) x) ^ 2
            else 0) t)) <=
          (8 * 67108864 ^ 2 * (1 + Real.log (M : Real)) ^ 4 +
            6 * 67108864 ^ 4 * (1 + Real.log (M : Real)) ^ 8) * (M : Real) ^ (119 / 40 : Real) := by
  classical
  intro N instN M P s L T hP hEight hDivM hDiv hSmall hs hL hX hNoWrap hPower
  have hM : (1 : Real) <= (M : Real) := by exact_mod_cast (show 1 <= M by omega)
  exact (lpf_primeGridInterval_complete_major_numeric M P s L T hP hEight hDivM hDiv hSmall hs hL hX hNoWrap).trans
    (lpfMajorEnvelope_le_power 67108864 (M : Real) (P : Real) hM (Nat.cast_nonneg _) hPower)

theorem lpf_fixed_source_mean_four_packet_numeric :
    forall {N : Nat} [NeZero N] (M P s L : Nat) (T : Finset Nat),
        2 ^ 18 <= M -> 0 < P ->
        (P : Real) <= (M : Real) ^ ((1 : Real) / 40) ->
        Dvd.dvd M N -> (forall q, 0 < q -> q <= P -> Dvd.dvd q N) ->
        (M : Real) / 4 <= (s : Real) -> s + L <= 2 * M -> L <= M -> s + L < N ->
        2 * M < N -> (forall n, Membership.mem T n -> And (0 < n) (n <= 2 * M)) ->
        Finset.sum T (fun n => norm (lpfFixedSourceError N s L n) ^ 2) <=
          4 * ((8 * 67108864 ^ 2 * (1 + Real.log (M : Real)) ^ 4 +
                6 * 67108864 ^ 4 * (1 + Real.log (M : Real)) ^ 8) * (M : Real) ^ (119 / 40 : Real) +
            32768 * ((M : Real) ^ 3 / (P : Real) + (M : Real) ^ (13 / 5 : Real)) *
              (1 + Real.log (2 * (M : Real))) ^ 12 +
            (289 / 2 : Real) * (M : Real) ^ 3 *
              (1 + Real.log (2 * (M : Real))) ^ 3 / (P : Real) ^ 2 +
            512 * (M : Real) ^ 3 * (1 + Real.log (2 * (M : Real))) ^ 3 / (P : Real)) := by
  classical
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
  have hMaj := lpf_primeGridInterval_major_power_numeric (N := N) M P s L (T.image (fun n : Nat => (n : ZMod N)))
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

theorem lpf_fixed_source_mean_log_power_numeric :
    forall {N : Nat} [NeZero N] (M s L : Nat) (T : Finset Nat),
        2 ^ 18 <= M -> Dvd.dvd M N ->
        (forall q, 0 < q -> q <= lpfSourceCutoff M -> Dvd.dvd q N) ->
        (M : Real) / 4 <= (s : Real) -> s + L <= 2 * M -> L <= M -> s + L < N ->
        2 * M < N -> (forall n, Membership.mem T n -> And (0 < n) (n <= 2 * M)) ->
        Finset.sum T (fun n => norm (lpfFixedSourceError N s L n) ^ 2) <=
          4 * (8 * 67108864 ^ 2 + 6 * 67108864 ^ 4 + 99906) *
            (M : Real) ^ (119 / 40 : Real) * (1 + Real.log (2 * (M : Real))) ^ 12 := by
  classical
  intro N instN M s L T hM hDivM hDiv hStart hTop hL hInput hNTop hT
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hCut := lpf_source_cutoff_bounds M hOne
  have h := lpf_fixed_source_mean_four_packet_numeric M (lpfSourceCutoff M) s L T hM hCut.1 hCut.2.1
    hDivM hDiv hStart hTop hL hInput hNTop hT
  have hEnvelope := lpf_source_mean_four_packet_envelope M (lpfSourceCutoff M)
    67108864 32768 (289 / 2) 512 hOne hCut.1 (by norm_num) (by norm_num) (by norm_num) hCut.2.2
  have hFinal := h.trans (mul_le_mul_of_nonneg_left hEnvelope (show (0 : Real) <= 4 by norm_num))
  calc
    _ <= 4 * ((8 * 67108864 ^ 2 + 6 * 67108864 ^ 4 + 3 * 32768 + 4 * (289 / 2) + 2 * 512) *
      (M : Real) ^ (119 / 40 : Real) * (1 + Real.log (2 * (M : Real))) ^ 12) := hFinal
    _ = _ := by norm_num; ring

theorem lpf_fixed_source_mean_log_power_numeric_coarse
    {N : Nat} [NeZero N] (M s L : Nat) (T : Finset Nat)
    (hM : 2 ^ 18 <= M) (hDivM : Dvd.dvd M N)
    (hDiv : forall q, 0 < q -> q <= lpfSourceCutoff M -> Dvd.dvd q N)
    (hStart : (M : Real) / 4 <= (s : Real)) (hTop : s + L <= 2 * M)
    (hL : L <= M) (hInput : s + L < N) (hNTop : 2 * M < N)
    (hT : forall n, Membership.mem T n -> And (0 < n) (n <= 2 * M)) :
    Finset.sum T (fun n => norm (lpfFixedSourceError N s L n) ^ 2) <=
      (2 : Real) ^ (109 : Nat) * (M : Real) ^ (119 / 40 : Real) *
        (1 + Real.log (2 * (M : Real))) ^ 12 := by
  have h := lpf_fixed_source_mean_log_power_numeric M s L T hM hDivM hDiv
    hStart hTop hL hInput hNTop hT
  have hC : 4 * (8 * (67108864 : Real) ^ 2 + 6 * (67108864 : Real) ^ 4 + 99906) <=
      (2 : Real) ^ (109 : Nat) := by norm_num
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Nat.cast_nonneg M) _))
    (by positivity))

end PrimeFactorOscillations.LPF

