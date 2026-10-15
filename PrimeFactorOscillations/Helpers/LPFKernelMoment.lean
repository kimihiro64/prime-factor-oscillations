/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFCyclicKernel
import PrimeFactorOscillations.Helpers.LPFDivisorMoment

/-!
# Complete interval-kernel correction in mean square

The retained packet is (J-L)*S_P, with the actual cyclic inverse truncation
J and full interval-pair inverse L. Its bound is uniform in the auxiliary
N, both physical cutoffs H,M, P, shifts and lengths. Divisor subpower
control gives A*M^2*H^(161/160)/P^2. For H=2*M this is
B*M^(481/160)/P^2; at P comparable to M^(1/40), exponent 473/160.
The other retained tail L*(S_P-S) is also bounded with the actual cyclic
interval pair count, by B*M^(481/160)/P under input non-wrap and L<=M.
No complete prime-pair source bound or generated-state density is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def lpfIntervalKernelCorrection (N : Nat) [NeZero N] (M P s L n : Nat) : Complex :=
  (lpfCyclicInverse (fun x => if Membership.mem (lpfIntervalOffsetGrid N ((N / M) * P)) x then
      (lpfIntervalFrequencyKernel N s L x) ^ 2 else 0) (n : ZMod N) -
    lpfCyclicInverse (fun x => (lpfIntervalFrequencyKernel N s L x) ^ 2) (n : ZMod N)) *
      lpfSingularPartial P n

theorem lpfIntervalKernelCorrection_square_le {N : Nat} [NeZero N]
    (M P s L n : Nat) (hM : 0 < M) (hP : 0 < P) (hDiv : Dvd.dvd M N) (hn : 0 < n) :
    norm (lpfIntervalKernelCorrection N M P s L n) ^ 2 <=
      (289 * (M : Real) ^ 2 / (4 * (P : Real) ^ 2)) * (n.divisors.card : Real) ^ 2 := by
  have hK := norm_lpfIntervalKernel_scaled_truncation M P s L (n : ZMod N) hM hP hDiv
  have hS := norm_lpfSingularPartial_le P n hn
  unfold lpfIntervalKernelCorrection
  rw [norm_mul]
  have hProd := mul_le_mul hK hS (norm_nonneg (lpfSingularPartial P n))
    (by positivity : (0 : Real) <= (M : Real) / (2 * (P : Real)))
  calc
    _ <= (((M : Real) / (2 * (P : Real))) * (17 * (n.divisors.card : Real))) ^ 2 := by
      gcongr
    _ = _ := by field_simp <;> ring

theorem lpfIntervalKernelCorrection_square_sum (C : Real) (hC : 0 <= C)
    (hPoint : forall n : Nat, (n.divisors.card : Real) ^ 2 <= C * (n : Real) ^ (1 / 160 : Real))
    {N : Nat} [NeZero N] (H M P s L : Nat) (T : Finset Nat)
    (hM : 0 < M) (hP : 0 < P) (hDiv : Dvd.dvd M N)
    (hT : forall n, Membership.mem T n -> And (0 < n) (n <= H)) (hCard : T.card <= H) :
    Finset.sum T (fun n => norm (lpfIntervalKernelCorrection N M P s L n) ^ 2) <=
      (289 * C / 4) * (M : Real) ^ 2 * (H : Real) ^ (161 / 160 : Real) / (P : Real) ^ 2 := by
  have hPointwise : forall n, Membership.mem T n ->
      norm (lpfIntervalKernelCorrection N M P s L n) ^ 2 <=
        (289 * (M : Real) ^ 2 / (4 * (P : Real) ^ 2)) * (n.divisors.card : Real) ^ 2 := by
    intro n hn
    exact lpfIntervalKernelCorrection_square_le M P s L n hM hP hDiv (hT n hn).1
  have hSum := lpf_divisors_square_sum_of_power_bound C hC hPoint H T (fun n hn => (hT n hn).2) hCard
  calc
    _ <= Finset.sum T (fun n => (289 * (M : Real) ^ 2 / (4 * (P : Real) ^ 2)) * (n.divisors.card : Real) ^ 2) :=
      Finset.sum_le_sum hPointwise
    _ = (289 * (M : Real) ^ 2 / (4 * (P : Real) ^ 2)) * Finset.sum T (fun n => (n.divisors.card : Real) ^ 2) :=
      (Finset.mul_sum _ _ _).symm
    _ <= (289 * (M : Real) ^ 2 / (4 * (P : Real) ^ 2)) * (C * (H : Real) ^ (161 / 160 : Real)) :=
      mul_le_mul_of_nonneg_left hSum (by positivity)
    _ = _ := by ring

theorem exists_lpfIntervalKernelCorrection_square_sum :
    exists A : Real, And (0 < A)
      (forall {N : Nat} [NeZero N] (H M P s L : Nat) (T : Finset Nat),
        0 < M -> 0 < P -> Dvd.dvd M N ->
        (forall n, Membership.mem T n -> And (0 < n) (n <= H)) -> T.card <= H ->
        Finset.sum T (fun n => norm (lpfIntervalKernelCorrection N M P s L n) ^ 2) <=
          A * (M : Real) ^ 2 * (H : Real) ^ (161 / 160 : Real) / (P : Real) ^ 2) := by
  choose C hC hPoint using exists_lpf_divisors_square_power_bound
  refine Exists.intro (289 * C / 4) (And.intro (by positivity) ?_)
  intro N inst H M P s L T hM hP hDiv hT hCard
  exact lpfIntervalKernelCorrection_square_sum C hC.le hPoint H M P s L T hM hP hDiv hT hCard

theorem exists_lpfIntervalKernelCorrection_physical_power_bound :
    exists B : Real, And (0 < B)
      (forall {N : Nat} [NeZero N] (M P s L : Nat) (T : Finset Nat),
        0 < M -> 0 < P -> Dvd.dvd M N ->
        (forall n, Membership.mem T n -> And (0 < n) (n <= 2 * M)) -> T.card <= 2 * M ->
        Finset.sum T (fun n => norm (lpfIntervalKernelCorrection N M P s L n) ^ 2) <=
          B * (M : Real) ^ (481 / 160 : Real) / (P : Real) ^ 2) := by
  choose A hA hSource using exists_lpfIntervalKernelCorrection_square_sum
  refine Exists.intro (A * (2 : Real) ^ (161 / 160 : Real)) (And.intro (by positivity) ?_)
  intro N inst M P s L T hM hP hDiv hT hCard
  have hMreal : (0 : Real) < (M : Real) := Nat.cast_pos.mpr hM
  have hBound := hSource (2 * M) M P s L T hM hP hDiv hT hCard
  have hPower : (M : Real) ^ 2 * (M : Real) ^ (161 / 160 : Real) = (M : Real) ^ (481 / 160 : Real) := by
    rw [<- Real.rpow_natCast]
    norm_num only [Nat.cast_ofNat]
    rw [<- Real.rpow_add hMreal]
    norm_num
  have hCast : ((2 * M : Nat) : Real) = 2 * (M : Real) := by simp
  rw [hCast, Real.mul_rpow (by norm_num : (0 : Real) <= 2) hMreal.le] at hBound
  calc
    _ <= A * (M : Real) ^ 2 * ((2 : Real) ^ (161 / 160 : Real) * (M : Real) ^ (161 / 160 : Real)) / (P : Real) ^ 2 := hBound
    _ = A * (2 : Real) ^ (161 / 160 : Real) * ((M : Real) ^ 2 * (M : Real) ^ (161 / 160 : Real)) / (P : Real) ^ 2 := by ring
    _ = _ := by rw [hPower]

theorem exists_lpfIntervalPair_singular_tail_bound :
    exists B : Real, And (0 < B)
      (forall {N : Nat} [NeZero N] (M P s L : Nat) (T : Finset Nat),
        0 < M -> 1 <= P -> L <= M -> s + L < N ->
        (forall n, Membership.mem T n -> And (0 < n) (n <= 2 * M)) -> T.card <= 2 * M ->
        Finset.sum T (fun n => norm (lpfIntervalPairCount N s L (n : ZMod N) *
          (lpfSingularPartial P n - lpfSingularSeries n)) ^ 2) <=
            B * (M : Real) ^ (481 / 160 : Real) / (P : Real)) := by
  choose A hA hSource using exists_lpfSingularSeries_weighted_tail_square_sum
  refine Exists.intro (A * (2 : Real) ^ (481 / 160 : Real)) (And.intro (by positivity) ?_)
  intro N inst M P s L T hM hP hL hNoWrap hT hCard
  let w := fun n : Nat => lpfIntervalPairCount N s L (n : ZMod N)
  have hWeight : forall n, Membership.mem T n -> norm (w n) <= ((2 * M : Nat) : Real) := by
    intro n hn
    exact (norm_lpfIntervalPairCount_le s L (n : ZMod N) hNoWrap).trans
      (by exact_mod_cast (show L <= 2 * M by omega))
  have hBound := hSource (2 * M) P T w hP hT hCard hWeight
  have hCast : ((2 * M : Nat) : Real) = 2 * (M : Real) := by simp
  rw [hCast, Real.mul_rpow (by norm_num : (0 : Real) <= 2) (Nat.cast_nonneg M)] at hBound
  have hSign : forall n, norm (w n * (lpfSingularPartial P n - lpfSingularSeries n)) ^ 2 =
      norm (w n * (lpfSingularSeries n - lpfSingularPartial P n)) ^ 2 := by
    intro n
    rw [show w n * (lpfSingularPartial P n - lpfSingularSeries n) =
      -(w n * (lpfSingularSeries n - lpfSingularPartial P n)) by ring, norm_neg]
  change Finset.sum T (fun n => norm (w n * (lpfSingularPartial P n - lpfSingularSeries n)) ^ 2) <= _
  simp_rw [hSign]
  convert hBound using 1 <;> ring

end PrimeFactorOscillations.LPF
