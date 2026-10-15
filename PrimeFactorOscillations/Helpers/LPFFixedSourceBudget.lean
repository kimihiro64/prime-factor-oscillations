/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFKernelMoment
import PrimeFactorOscillations.Helpers.LPFMajorFactorization
import PrimeFactorOscillations.Helpers.LPFMajorPower
import PrimeFactorOscillations.Helpers.LPFMinorParseval

/-!
# Complete fixed-interval squared-error budget

The four exact signed packets are bounded on the same physical interval and
natural target set. Major and minor outputs are reindexed without multiplicity
loss, and kernel and singular corrections retain their actual pair weights.
All four constants precede every scale, grid, interval and target set. The
error is centered at the infinite singular series; its positive arithmetic
identification and the actual generated-state entry remain open.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_norm_four_add_sq_le (a b c d : Complex) :
    norm (a + b + c + d) ^ 2 <= 4 * (norm a ^ 2 + norm b ^ 2 + norm c ^ 2 + norm d ^ 2) := by
  have hNorm : norm (a + b + c + d) <= norm a + norm b + norm c + norm d := by
    calc
      _ <= norm (a + b + c) + norm d := norm_add_le _ _
      _ <= norm (a + b) + norm c + norm d := add_le_add (norm_add_le _ _) (le_refl _)
      _ <= _ := add_le_add (add_le_add (norm_add_le _ _) (le_refl _)) (le_refl _)
  have hSq : norm (a + b + c + d) ^ 2 <= (norm a + norm b + norm c + norm d) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hNorm hNorm (norm_nonneg _) (by positivity)
  have hYoung : (norm a + norm b + norm c + norm d) ^ 2 <=
      4 * (norm a ^ 2 + norm b ^ 2 + norm c ^ 2 + norm d ^ 2) := by
    nlinarith only [sq_nonneg (norm a - norm b), sq_nonneg (norm a - norm c),
      sq_nonneg (norm a - norm d), sq_nonneg (norm b - norm c),
      sq_nonneg (norm b - norm d), sq_nonneg (norm c - norm d)]
  exact hSq.trans hYoung

theorem lpf_nat_grid_square_sum_eq_image {N : Nat} [NeZero N]
    (T : Finset Nat) (F : ZMod N -> Complex)
    (hInput : forall n, Membership.mem T n -> n < N) :
    Finset.sum T (fun n => norm (F (n : ZMod N)) ^ 2) =
      Finset.sum (T.image (fun n : Nat => (n : ZMod N))) (fun x => Complex.normSq (F x)) := by
  classical
  have hInj : Set.InjOn (fun n : Nat => (n : ZMod N)) (T : Set Nat) := by
    intro n hn m hm hEq
    have h := congrArg (fun x : ZMod N => x.val) hEq
    simpa only [ZMod.val_natCast_of_lt (hInput n hn), ZMod.val_natCast_of_lt (hInput m hm)] using h
  simp_rw [Complex.sq_norm]
  exact (Finset.sum_image (f := fun x => Complex.normSq (F x)) hInj).symm

theorem lpf_warm_major_conditions (M P : Nat) (hM : 2 ^ 18 <= M) (hP : 0 < P)
    (hPower : (P : Real) <= (M : Real) ^ ((1 : Real) / 40)) :
    And (8 * P <= M) (2 * P ^ 3 < M) := by
  have hMNonneg : (0 : Real) <= (M : Real) := by positivity
  have hPPos : (0 : Real) < (P : Real) := by exact_mod_cast hP
  have h8 := lpf_warm_multiple_rpow_le M 3 hM ((1 : Real) / 40) (by norm_num) (by norm_num)
  have h4 := lpf_warm_multiple_rpow_le M 2 hM (3 / 40) (by norm_num) (by norm_num)
  norm_num at h8 h4
  have h8P : 8 * (P : Real) <= (M : Real) := by linarith only [hPower, h8]
  have hP3 : (P : Real) ^ 3 <= (M : Real) ^ (3 / 40 : Real) := by
    calc
      _ <= ((M : Real) ^ ((1 : Real) / 40)) ^ 3 := by gcongr
      _ = ((M : Real) ^ ((1 : Real) / 40)) ^ (3 : Real) := (Real.rpow_natCast _ 3).symm
      _ = (M : Real) ^ (((1 : Real) / 40) * 3) := (Real.rpow_mul hMNonneg _ _).symm
      _ = _ := by norm_num
  have hStrong : 4 * (P : Real) ^ 3 <= (M : Real) := by linarith only [hP3, h4]
  have hStrict : 2 * (P : Real) ^ 3 < (M : Real) := by
    have hPos : (0 : Real) < (P : Real) ^ 3 := by positivity
    linarith only [hStrong, hPos]
  exact And.intro (by exact_mod_cast h8P) (by exact_mod_cast hStrict)

noncomputable def lpfFixedSourceError (N : Nat) [NeZero N] (s L n : Nat) : Complex :=
  lpfCyclicInverse (fun x => lpfGridIntervalWeight N s L x ^ 2) (n : ZMod N) -
    lpfIntervalPairCount N s L (n : ZMod N) * lpfSingularSeries n

theorem lpf_fixed_source_four_packet_budget :
    exists K C B D : Real, And (0 < K) (And (0 < C) (And (0 < B) (And (0 < D)
      (forall {N : Nat} [NeZero N] (M P s L : Nat) (T : Finset Nat),
        2 ^ 18 <= M -> 0 < P ->
        (P : Real) <= (M : Real) ^ ((1 : Real) / 40) ->
        Dvd.dvd M N -> (forall q, 0 < q -> q <= P -> Dvd.dvd q N) ->
        (M : Real) / 4 <= (s : Real) -> s + L <= 2 * M -> L <= M -> s + L < N ->
        2 * M < N -> (forall n, Membership.mem T n -> And (0 < n) (n <= 2 * M)) ->
        T.card <= 2 * M ->
        Finset.sum T (fun n => norm (lpfFixedSourceError N s L n) ^ 2) <=
          4 * ((8 * K ^ 2 * (1 + Real.log (M : Real)) ^ 4 +
                6 * K ^ 4 * (1 + Real.log (M : Real)) ^ 8) * (M : Real) ^ (119 / 40 : Real) +
            C * (M : Real) ^ ((1 : Real) / 160) *
              ((M : Real) ^ 3 / (P : Real) + (M : Real) ^ (13 / 5 : Real)) *
              (1 + Real.log (2 * (M : Real))) ^ 9 +
            B * (M : Real) ^ (481 / 160 : Real) / (P : Real) ^ 2 +
            D * (M : Real) ^ (481 / 160 : Real) / (P : Real)))))) := by
  classical
  choose K hK hMajor using exists_primeGridInterval_major_power_bound
  choose C hC hMinor using lpf_grid_minor_meanSquare_bound
  choose B hB hKernel using exists_lpfIntervalKernelCorrection_physical_power_bound
  choose D hD hTail using exists_lpfIntervalPair_singular_tail_bound
  refine Exists.intro K (Exists.intro C (Exists.intro B (Exists.intro D
    (And.intro hK (And.intro hC (And.intro hB (And.intro hD ?_)))))))
  intro N instN M P s L T hM hP hPower hDivM hDiv hStart hTop hL hInput hNTop hT hCard
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
  have hMin := hMinor (N := N) M P s L hM hP hPower hDivM hDiv hStart hTop hL hInput
    (T.image (fun n : Nat => (n : ZMod N)))
  rw [<- lpf_nat_grid_square_sum_eq_image T H hTargetInput] at hMin
  have hKer := hKernel (N := N) M P s L T hMPos hP hDivM hT hCard
  have hTailBudget := hTail (N := N) M P s L T hMPos hPOne hL hInput hT hCard
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
      (add_le_add (add_le_add (add_le_add hMaj hMin) hKer) hTailBudget) (by norm_num)

end PrimeFactorOscillations.LPF
