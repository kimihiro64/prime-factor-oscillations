/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFGoldbachFixedSubwindows
import PrimeFactorOscillations.Helpers.LPFGoldbachPrimePowers
import PrimeFactorOscillations.Helpers.LPFSingularPositive
import PrimeFactorOscillations.Helpers.LPFSourcePower

/-!
# One-sided positive source from fixed subwindows

The complete fixed-interval squared error is charged to insufficient targets
in the actual moving window. The exact integer pair adapter retains all prime
powers and diagonals. The finite cover keeps its real kernel floor, uses the
correct physical scale for each pool, and eliminates the auxiliary modulus.
One constant bounds the bad target count by M^(79/80) for every M >= 2^19.
This is a full-input source theorem, not density entry of a generated orbit.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def lpfCoverWidth (M : Nat) : Nat := M / 128
def lpfCoverIndex (M t : Nat) : Nat := t / (2 * lpfCoverWidth M)
def lpfCoverCenter (M b : Nat) : Nat := b * lpfCoverWidth M
def lpfCoverStart (M b : Nat) : Nat := lpfCoverCenter M b - lpfCoverWidth M
def lpfCoverLength (M : Nat) : Nat := 3 * lpfCoverWidth M - 1

theorem lpf_positive_cover_geometry (M m t : Nat) (hM : 256 <= M)
    (hmTop : m <= M) (hmHalf : M <= 2 * m + 1)
    (ht : Membership.mem (goldbachEvenTargets m) t) :
    let b := lpfCoverIndex M t
    let c := lpfCoverCenter M b
    let s := lpfCoverStart M b
    let L := lpfCoverLength M
    And (b <= 256) (And (lpfCoverWidth M <= c)
      (And (2 * c <= t) (And (t < 2 * c + 2 * lpfCoverWidth M)
        (And (s + L = c + 2 * lpfCoverWidth M - 1)
          (And ((m : Real) / 4 <= (s : Real))
            (And (s + L <= 2 * m) (And (L <= m)
              (And (goldbachFixedSubwindow (lpfCoverWidth M) c <= goldbachWindowInputs M t)
                ((M : Real) / 256 <=
                  ((Finset.sumPartners (goldbachFixedSubwindow (lpfCoverWidth M) c) t).card : Real)))))))))) := by
  let h := lpfCoverWidth M
  let b := lpfCoverIndex M t
  let c := lpfCoverCenter M b
  have hTarget := Finset.mem_Ioo.mp (Finset.mem_filter.mp ht).1
  have hPos : 0 < h := by dsimp [h, lpfCoverWidth]; omega
  have hLow : 128 * h <= M := by dsimp [h, lpfCoverWidth]; omega
  have hHigh : M <= 128 * h + 127 := by dsimp [h, lpfCoverWidth]; omega
  have hScale : M <= 256 * h := by omega
  have hmLow : 64 * h <= m := by omega
  have hWidth : 2 * h <= M / 64 := by dsimp [h, lpfCoverWidth]; omega
  have hRem : t % (2 * h) < 2 * h := Nat.mod_lt _ (by omega)
  have hDecomp : t = 2 * c + t % (2 * h) := by
    change t = 2 * (t / (2 * h) * h) + t % (2 * h)
    nlinarith only [Nat.mod_add_div t (2 * h)]
  have hLower : 2 * c <= t := by omega
  have hUpper : t < 2 * c + 2 * h := by omega
  have hbPos : 1 <= b := by
    by_contra hNot
    have hb : b = 0 := by omega
    have hc : c = 0 := by dsimp [c, lpfCoverCenter]; rw [hb]; simp
    omega
  have hCenter : h <= c := by
    have hMul := Nat.mul_le_mul_right (lpfCoverWidth M) hbPos
    simpa only [Nat.one_mul, c, lpfCoverCenter, h] using hMul
  have hbTop : b <= 256 := by
    by_contra hNot
    have hb : 257 <= b := by omega
    have hMul := Nat.mul_le_mul_right (lpfCoverWidth M) hb
    change 257 * h <= c at hMul
    omega
  have hEnd : lpfCoverStart M b + lpfCoverLength M = c + 2 * h - 1 := by
    change c - h + (3 * h - 1) = c + 2 * h - 1
    omega
  have hStart : m <= 4 * lpfCoverStart M b := by
    change m <= 4 * (c - h)
    omega
  have hStartR : (m : Real) / 4 <= (lpfCoverStart M b : Real) := by
    have hCast : (m : Real) <= 4 * (lpfCoverStart M b : Real) := by exact_mod_cast hStart
    linarith only [hCast]
  have hTop : lpfCoverStart M b + lpfCoverLength M <= 2 * m := by rw [hEnd]; omega
  have hLength : lpfCoverLength M <= m := by change 3 * h - 1 <= m; omega
  have hSubset := goldbachFixedSubwindow_subset M h c t hWidth hCenter hLower hUpper
  have hCore := goldbachFixedSubwindow_main_card h c t hCenter hLower hUpper
  have hScaleR : (M : Real) <= 256 * (h : Real) := by exact_mod_cast hScale
  have hCoreR : (h : Real) <=
      ((Finset.sumPartners (goldbachFixedSubwindow h c) t).card : Real) := by exact_mod_cast hCore
  have hKernel : (M : Real) / 256 <=
      ((Finset.sumPartners (goldbachFixedSubwindow h c) t).card : Real) := by
    linarith only [hScaleR, hCoreR]
  exact And.intro hbTop (And.intro hCenter (And.intro hLower (And.intro hUpper
    (And.intro hEnd (And.intro hStartR (And.intro hTop (And.intro hLength
      (And.intro hSubset hKernel))))))))

theorem lpf_positive_cover_inputs_eq (M b : Nat) (hPos : 0 < lpfCoverWidth M)
    (hCenter : lpfCoverWidth M <= lpfCoverCenter M b) :
    goldbachFixedSubwindow (lpfCoverWidth M) (lpfCoverCenter M b) =
      Finset.Ioc (lpfCoverStart M b) (lpfCoverStart M b + lpfCoverLength M) := by
  apply Finset.ext
  intro p
  simp only [goldbachFixedSubwindow, Finset.mem_Ioo, Finset.mem_Ioc,
    lpfCoverStart, lpfCoverLength]
  omega

theorem lpf_finite_pair_collapse (A : Finset Nat) (w : Nat -> Complex) (t : Nat) :
    Finset.sum A (fun p => Finset.sum A (fun q => if p + q = t then w p * w q else 0)) =
      Finset.sum (Finset.sumPartners A t) (fun p => w p * w (t - p)) := by
  classical
  rw [Finset.sumPartners, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hGood : And (Membership.mem A (t - p)) (p <= t)
  next =>
    rw [ite_eq_left hGood]
    calc
      _ = if p + (t - p) = t then w p * w (t - p) else 0 := by
        apply Finset.sum_eq_single_of_mem (t - p) hGood.1
        intro q _ hNe
        have hSum : Not (p + q = t) := by intro h; apply hNe; omega
        simp [hSum]
      _ = _ := by
        have hSum : p + (t - p) = t := by omega
        simp [hSum]
  next =>
    rw [ite_eq_right hGood]
    apply Finset.sum_eq_zero
    intro q hq
    have hSum : Not (p + q = t) := by
      intro h
      apply hGood
      have hQ : q = t - p := by omega
      exact And.intro (by simpa only [<- hQ] using hq) (by omega)
    simp [hSum]

theorem lpf_range_interval_transform {N : Nat} [NeZero N]
    (s L : Nat) (w : Nat -> Complex) (x : ZMod N) :
    Finset.sum (Finset.range L) (fun i => w (s + 1 + i) *
      ZMod.stdAddChar (x * ((s + 1 + i : Nat) : ZMod N))) =
      lpfFiniteTransform (Finset.Ioc s (s + L)) (fun p => (p : ZMod N)) w x := by
  unfold lpfFiniteTransform
  apply Finset.sum_bij (fun i _ => s + 1 + i)
  next => intro i hi; apply Finset.mem_Ioc.mpr; have h := Finset.mem_range.mp hi; omega
  next => intro i _ j _ hEq; omega
  next =>
    intro p hp
    have h := Finset.mem_Ioc.mp hp
    refine Exists.intro (p - s - 1) (Exists.intro ?_ ?_)
    next => apply Finset.mem_range.mpr; omega
    next => omega
  next => intro i _; rfl

theorem lpf_nat_cyclic_weighted_pairs {N : Nat} [NeZero N]
    (A : Finset Nat) (w : Nat -> Complex) (t : Nat)
    (hPairs : forall p, Membership.mem A p -> forall q, Membership.mem A q -> p + q < N)
    (hTarget : t < N) :
    lpfCyclicInverse (fun x => lpfFiniteTransform A (fun p => (p : ZMod N)) w x ^ 2) (t : ZMod N) =
      Finset.sum (Finset.sumPartners A t) (fun p => w p * w (t - p)) := by
  have h := lpfCyclicInverse_finite_product A A (fun p => (p : ZMod N))
    (fun p => (p : ZMod N)) w w (t : ZMod N)
  simp_rw [pow_two]
  rw [h]
  rw [<- lpf_finite_pair_collapse A w t]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  have hEq : (p : ZMod N) + (q : ZMod N) = (t : ZMod N) <-> p + q = t := by
    rw [<- Nat.cast_add]
    constructor
    next =>
      intro h
      have hVal := congrArg (fun a : ZMod N => a.val) h
      simpa only [ZMod.val_natCast_of_lt (hPairs p hp q hq), ZMod.val_natCast_of_lt hTarget] using hVal
    next => intro h; rw [h]
  simp only [hEq]

noncomputable def lpfWeightedPartners (A : Finset Nat) (t : Nat) : Real :=
  Finset.sum (Finset.sumPartners A t) (fun p =>
    ArithmeticFunction.vonMangoldt p * ArithmeticFunction.vonMangoldt (t - p))

theorem lpf_grid_interval_inverse_weighted {N : Nat} [NeZero N] (s L t : Nat)
    (hNoWrap : 2 * (s + L) < N) (hTarget : t < N) :
    lpfCyclicInverse (fun x => lpfGridIntervalWeight N s L x ^ 2) (t : ZMod N) =
      (lpfWeightedPartners (Finset.Ioc s (s + L)) t : Complex) := by
  let A := Finset.Ioc s (s + L)
  let w : Nat -> Complex := fun p => (ArithmeticFunction.vonMangoldt p : Complex)
  have hPairs : forall p, Membership.mem A p -> forall q, Membership.mem A q -> p + q < N := by
    intro p hp q hq
    have hP := Finset.mem_Ioc.mp hp
    have hQ := Finset.mem_Ioc.mp hq
    omega
  have hTransform (x : ZMod N) : lpfGridIntervalWeight N s L x =
      lpfFiniteTransform A (fun p => (p : ZMod N)) w x :=
    lpf_range_interval_transform s L w x
  calc
    _ = lpfCyclicInverse (fun x => lpfFiniteTransform A (fun p => (p : ZMod N)) w x ^ 2) (t : ZMod N) := by
      congr 1
      funext x
      rw [hTransform x]
    _ = Finset.sum (Finset.sumPartners A t) (fun p => w p * w (t - p)) :=
      lpf_nat_cyclic_weighted_pairs A w t hPairs hTarget
    _ = _ := by unfold lpfWeightedPartners; dsimp [w, A]; push_cast <;> rfl

theorem lpf_interval_pairCount_sumPartners {N : Nat} [NeZero N] (s L t : Nat)
    (hNoWrap : 2 * (s + L) < N) (hTarget : t < N) :
    lpfIntervalPairCount N s L (t : ZMod N) =
      ((Finset.sumPartners (Finset.Ioc s (s + L)) t).card : Complex) := by
  let A := Finset.Ioc s (s + L)
  let w : Nat -> Complex := fun _ => 1
  have hPairs : forall p, Membership.mem A p -> forall q, Membership.mem A q -> p + q < N := by
    intro p hp q hq
    have hP := Finset.mem_Ioc.mp hp
    have hQ := Finset.mem_Ioc.mp hq
    omega
  have hTransform (x : ZMod N) : lpfIntervalFrequencyKernel N s L x =
      lpfFiniteTransform A (fun p => (p : ZMod N)) w x := by
    simpa only [lpfIntervalFrequencyKernel, w, A, one_mul] using lpf_range_interval_transform s L w x
  calc
    _ = lpfCyclicInverse (fun x => lpfIntervalFrequencyKernel N s L x ^ 2) (t : ZMod N) :=
      (lpfIntervalFrequencyKernel_inverse_square s L (t : ZMod N)).symm
    _ = lpfCyclicInverse (fun x => lpfFiniteTransform A (fun p => (p : ZMod N)) w x ^ 2) (t : ZMod N) := by
      congr 1
      funext x
      rw [hTransform x]
    _ = _ := by
      have h := lpf_nat_cyclic_weighted_pairs A w t hPairs hTarget
      simpa only [w, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] using h

theorem lpf_weightedPartners_le_mangoldt (A : Finset Nat) (t : Nat) :
    lpfWeightedPartners A t <= goldbachMangoldtWeight A t := by
  unfold lpfWeightedPartners goldbachMangoldtWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p _ _
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg

theorem lpf_mangoldtWeight_mono {A B : Finset Nat} (h : A <= B) (t : Nat) :
    goldbachMangoldtWeight A t <= goldbachMangoldtWeight B t := by
  unfold goldbachMangoldtWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro p _ _
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg

theorem lpf_fixed_cover_bad_error {N : Nat} [NeZero N] (M m b t : Nat)
    (hM : 256 <= M) (hmTop : m <= M) (hmHalf : M <= 2 * m + 1)
    (ht : Membership.mem (goldbachEvenTargets m) t) (hIndex : lpfCoverIndex M t = b)
    (hN : 4 * M < N)
    (hBad : goldbachMangoldtWeight (goldbachWindowInputs M t) t <
      (M : Real) * singularDivisorProduct t / 512) :
    (M : Real) / 512 <= norm (lpfFixedSourceError N (lpfCoverStart M b) (lpfCoverLength M) t) := by
  have hGeom := lpf_positive_cover_geometry M m t hM hmTop hmHalf ht
  dsimp only at hGeom
  rw [hIndex] at hGeom
  have hPos : 0 < lpfCoverWidth M := by unfold lpfCoverWidth; omega
  have hInputs := lpf_positive_cover_inputs_eq M b hPos hGeom.2.1
  have hTarget := Finset.mem_Ioo.mp (Finset.mem_filter.mp ht).1
  have hTop := hGeom.2.2.2.2.2.2.1
  have hNoWrap : 2 * (lpfCoverStart M b + lpfCoverLength M) < N := by omega
  have hTN : t < N := by omega
  have htPos : 0 < t := by omega
  have hEven : Dvd.dvd 2 t := Nat.dvd_of_mod_eq_zero (Finset.mem_filter.mp ht).2
  let A := Finset.Ioc (lpfCoverStart M b) (lpfCoverStart M b + lpfCoverLength M)
  have hSubset : A <= goldbachWindowInputs M t := by
    dsimp [A]
    rw [<- hInputs]
    exact hGeom.2.2.2.2.2.2.2.2.1
  have hFixed : (lpfCyclicInverse (fun x =>
      lpfGridIntervalWeight N (lpfCoverStart M b) (lpfCoverLength M) x ^ 2) (t : ZMod N)).re <=
      goldbachMangoldtWeight (goldbachWindowInputs M t) t := by
    rw [lpf_grid_interval_inverse_weighted _ _ _ hNoWrap hTN, Complex.ofReal_re]
    exact (lpf_weightedPartners_le_mangoldt A t).trans (lpf_mangoldtWeight_mono hSubset t)
  have hCard : (M : Real) / 256 <= ((Finset.sumPartners A t).card : Real) := by
    dsimp [A]
    rw [<- hInputs]
    exact hGeom.2.2.2.2.2.2.2.2.2
  have hSeries := lpf_singular_series_re_lower_bound t htPos hEven
  have hG := sieve_singularDivisorProduct_one_le t
  have hMain := mul_le_mul hCard hSeries (zero_le_one.trans hG)
    (Nat.cast_nonneg ((Finset.sumPartners A t).card))
  have hRe : (lpfFixedSourceError N (lpfCoverStart M b) (lpfCoverLength M) t).re =
      (lpfCyclicInverse (fun x => lpfGridIntervalWeight N (lpfCoverStart M b) (lpfCoverLength M) x ^ 2)
        (t : ZMod N)).re - ((Finset.sumPartners A t).card : Real) * (lpfSingularSeries t).re := by
    unfold lpfFixedSourceError
    rw [lpf_interval_pairCount_sumPartners _ _ _ hNoWrap hTN]
    simp only [Complex.sub_re, Complex.mul_re]
    simp [A]
  have hAllowance : (M : Real) / 512 <= (M : Real) / 512 * singularDivisorProduct t := by
    have h := mul_le_mul_of_nonneg_left hG (by positivity : 0 <= (M : Real) / 512)
    simpa only [mul_one] using h
  have hNorm : -(lpfFixedSourceError N (lpfCoverStart M b) (lpfCoverLength M) t).re <=
      norm (lpfFixedSourceError N (lpfCoverStart M b) (lpfCoverLength M) t) :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  nlinarith only [hFixed, hMain, hRe, hBad, hAllowance, hNorm]

theorem lpf_fixed_cover_bad_card_bound :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N] (M m b : Nat) (T : Finset Nat),
        2 ^ 19 <= M -> m <= M -> M <= 2 * m + 1 -> Dvd.dvd m N ->
        (forall q, 0 < q -> q <= lpfSourceCutoff m -> Dvd.dvd q N) -> 4 * M < N ->
        (forall t, Membership.mem T t -> And (Membership.mem (goldbachEvenTargets m) t)
          (And (lpfCoverIndex M t = b)
            (goldbachMangoldtWeight (goldbachWindowInputs M t) t <
              (M : Real) * singularDivisorProduct t / 512))) ->
        (T.card : Real) <= C * (M : Real) ^ (79 / 80 : Real)) := by
  classical
  choose A hA hBound using lpf_fixed_source_power_bound
  let C : Real := (512 : Real) ^ 2 * A
  refine Exists.intro C (And.intro (by dsimp [C]; positivity) ?_)
  intro N instN M m b T hM hmTop hmHalf hDivM hDiv hN hTargets
  have hM256 : 256 <= M := (by decide : 256 <= 2 ^ 19).trans hM
  have hmWarm : 2 ^ 18 <= m := by
    norm_num at hM
    norm_num
    omega
  have hMR : (0 : Real) < (M : Real) := by exact_mod_cast (by omega : 0 < M)
  by_cases hEmpty : T = Finset.empty
  next =>
    have hZero : T.card = 0 := Finset.card_eq_zero.mpr hEmpty
    rw [hZero, Nat.cast_zero]
    dsimp [C]
    positivity
  choose t0 ht0 using Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hGeom := lpf_positive_cover_geometry M m t0 hM256 hmTop hmHalf (hTargets t0 ht0).1
  dsimp only at hGeom
  rw [(hTargets t0 ht0).2.1] at hGeom
  have hStart := hGeom.2.2.2.2.2.1
  have hTop := hGeom.2.2.2.2.2.2.1
  have hLength := hGeom.2.2.2.2.2.2.2.1
  have hInput : lpfCoverStart M b + lpfCoverLength M < N := by omega
  have hOutput : 2 * m < N := by omega
  have hT (t : Nat) (ht : Membership.mem T t) : And (0 < t) (t <= 2 * m) := by
    have h := Finset.mem_Ioo.mp (Finset.mem_filter.mp (hTargets t ht).1).1
    constructor <;> omega
  have hSub : T <= Finset.Icc 1 (2 * m) := by
    intro t ht
    have h := hT t ht
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  have hCard : T.card <= 2 * m := by
    have h := Finset.card_le_card hSub
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using h
  have hBudget := hBound m (lpfCoverStart M b) (lpfCoverLength M) T
    hmWarm hDivM hDiv hStart hTop hLength hInput hOutput hT hCard
  have hPower : (m : Real) ^ (239 / 80 : Real) <= (M : Real) ^ (239 / 80 : Real) :=
    Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmTop) (by norm_num)
  have hNorm (t : Nat) (ht : Membership.mem T t) :
      ((M : Real) / 512) ^ 2 <=
        norm (lpfFixedSourceError N (lpfCoverStart M b) (lpfCoverLength M) t) ^ 2 := by
    have h := lpf_fixed_cover_bad_error M m b t hM256 hmTop hmHalf
      (hTargets t ht).1 (hTargets t ht).2.1 hN (hTargets t ht).2.2
    simpa only [pow_two] using mul_le_mul h h (by positivity : 0 <= (M : Real) / 512) (norm_nonneg _)
  have hEnergy : (T.card : Real) * ((M : Real) / 512) ^ 2 <= A * (M : Real) ^ (239 / 80 : Real) := by
    calc
      _ = Finset.sum T (fun _ => ((M : Real) / 512) ^ 2) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ <= Finset.sum T (fun t => norm (lpfFixedSourceError N (lpfCoverStart M b) (lpfCoverLength M) t) ^ 2) :=
        Finset.sum_le_sum hNorm
      _ <= A * (m : Real) ^ (239 / 80 : Real) := hBudget
      _ <= _ := mul_le_mul_of_nonneg_left hPower hA.le
  have hRpow : (M : Real) ^ (79 / 80 : Real) * (M : Real) ^ 2 =
      (M : Real) ^ (239 / 80 : Real) := by
    rw [<- Real.rpow_natCast (M : Real) 2, <- Real.rpow_add hMR]
    norm_num
  have hRight : (C * (M : Real) ^ (79 / 80 : Real)) * ((M : Real) / 512) ^ 2 =
      A * (M : Real) ^ (239 / 80 : Real) := by
    calc
      _ = A * ((M : Real) ^ (79 / 80 : Real) * (M : Real) ^ 2) := by dsimp [C]; ring
      _ = _ := by rw [hRpow]
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < ((M : Real) / 512) ^ 2)).mp
  rw [hRight]
  exact hEnergy

theorem lpf_source_cutoff_le_self (m : Nat) (hm : 1 <= m) : lpfSourceCutoff m <= m := by
  have hmR : (1 : Real) <= (m : Real) := by exact_mod_cast hm
  have hCut := (lpf_source_cutoff_bounds m hm).2.1
  have hPower := Real.rpow_le_rpow_of_exponent_le hmR (show (1 : Real) / 40 <= 1 by norm_num)
  rw [Real.rpow_one] at hPower
  have h := hCut.trans hPower
  exact_mod_cast h

def lpfPositiveGrid (M : Nat) : Nat := (4 * M + 1) * M.factorial

theorem lpf_positive_grid_large (M : Nat) : 4 * M < lpfPositiveGrid M := by
  have hOne : 1 <= M.factorial := Nat.factorial_pos M
  have h := Nat.mul_le_mul_left (4 * M + 1) hOne
  simpa only [Nat.mul_one, lpfPositiveGrid] using
    (show 4 * M < (4 * M + 1) * M.factorial by omega)

theorem lpf_positive_grid_divisible (M m : Nat) (hm : 0 < m) (hTop : m <= M) :
    Dvd.dvd m (lpfPositiveGrid M) := by
  exact dvd_mul_of_dvd_right (Nat.dvd_factorial (by omega) hTop) (4 * M + 1)

def lpfCoverFiber (M : Nat) (T : Finset Nat) (b : Nat) : Finset Nat :=
  T.filter (fun t => lpfCoverIndex M t = b)

noncomputable def lpfBadWindowTargets (M m : Nat) : Finset Nat :=
  (goldbachEvenTargets m).filter (fun t => goldbachMangoldtWeight (goldbachWindowInputs M t) t <
    (M : Real) * singularDivisorProduct t / 512)

set_option maxRecDepth 4096 in
theorem lpf_bad_window_targets_card_bound :
    exists D : Real, And (0 < D)
      (forall M m : Nat, 2 ^ 19 <= M -> m <= M -> M <= 2 * m + 1 ->
        ((lpfBadWindowTargets M m).card : Real) <= D * (M : Real) ^ (79 / 80 : Real)) := by
  classical
  choose C hC hSingle using lpf_fixed_cover_bad_card_bound
  let D : Real := 257 * C
  refine Exists.intro D (And.intro (by dsimp [D]; positivity) ?_)
  intro M m hM hmTop hmHalf
  have hM256 : 256 <= M := (by decide : 256 <= 2 ^ 19).trans hM
  have hmOne : 1 <= m := by have h := (by decide : 256 <= 2 ^ 19).trans hM; omega
  let N := lpfPositiveGrid M
  have hN : 4 * M < N := lpf_positive_grid_large M
  letI : NeZero N := NeZero.mk (by omega)
  have hDivM : Dvd.dvd m N := lpf_positive_grid_divisible M m (by omega) hmTop
  have hDiv (q : Nat) (hq : 0 < q) (hqCut : q <= lpfSourceCutoff m) : Dvd.dvd q N :=
    lpf_positive_grid_divisible M q hq ((hqCut.trans (lpf_source_cutoff_le_self m hmOne)).trans hmTop)
  let T := lpfBadWindowTargets M m
  have hCovered : T <= (Finset.range 257).biUnion (fun b => lpfCoverFiber M T b) := by
    intro t ht
    have hTarget := (Finset.mem_filter.mp ht).1
    have hGeom := lpf_positive_cover_geometry M m t hM256 hmTop hmHalf hTarget
    have hB : Membership.mem (Finset.range 257) (lpfCoverIndex M t) :=
      Finset.mem_range.mpr (by have h := hGeom.1; omega)
    exact Finset.mem_biUnion.mpr (Exists.intro (lpfCoverIndex M t)
      (And.intro hB (Finset.mem_filter.mpr (And.intro ht rfl))))
  have hCardNat : T.card <= Finset.sum (Finset.range 257) (fun b => (lpfCoverFiber M T b).card) :=
    (Finset.card_le_card hCovered).trans (Finset.card_biUnion_le)
  have hCardReal : (T.card : Real) <= Finset.sum (Finset.range 257)
      (fun b => ((lpfCoverFiber M T b).card : Real)) := by exact_mod_cast hCardNat
  have hFiber (b : Nat) : ((lpfCoverFiber M T b).card : Real) <= C * (M : Real) ^ (79 / 80 : Real) := by
    apply hSingle (N := N) M m b (lpfCoverFiber M T b) hM hmTop hmHalf hDivM hDiv hN
    intro t ht
    have h := Finset.mem_filter.mp ht
    have hRaw := Finset.mem_filter.mp h.1
    exact And.intro hRaw.1 (And.intro h.2 hRaw.2)
  calc
    _ <= Finset.sum (Finset.range 257) (fun b => ((lpfCoverFiber M T b).card : Real)) := hCardReal
    _ <= Finset.sum (Finset.range 257) (fun _ => C * (M : Real) ^ (79 / 80 : Real)) :=
      Finset.sum_le_sum (fun b _ => hFiber b)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; dsimp [D]; ring

noncomputable def lpfBadSourceTargets (M : Nat) : Finset Nat :=
  Union.union (lpfBadWindowTargets M (M / 2)) (lpfBadWindowTargets M M)

theorem lpf_bad_source_targets_card_bound :
    exists C : Real, And (0 < C) (forall M : Nat, 2 ^ 19 <= M ->
      ((lpfBadSourceTargets M).card : Real) <= C * (M : Real) ^ (79 / 80 : Real)) := by
  choose D hD hPool using lpf_bad_window_targets_card_bound
  refine Exists.intro (2 * D) (And.intro (by positivity) ?_)
  intro M hM
  have hHalf := hPool M (M / 2) hM (Nat.div_le_self M 2) (by omega)
  have hFull := hPool M M hM le_rfl (by omega)
  have hCard : ((lpfBadSourceTargets M).card : Real) <=
      ((lpfBadWindowTargets M (M / 2)).card : Real) + ((lpfBadWindowTargets M M).card : Real) := by
    unfold lpfBadSourceTargets
    exact_mod_cast (Finset.card_union_le (s := lpfBadWindowTargets M (M / 2)) (t := lpfBadWindowTargets M M))
  calc
    _ <= _ := hCard
    _ <= D * (M : Real) ^ (79 / 80 : Real) + D * (M : Real) ^ (79 / 80 : Real) := add_le_add hHalf hFull
    _ = _ := by ring

theorem lpf_good_source_target_weight (M t : Nat)
    (ht : Membership.mem (Union.union (goldbachEvenTargets (M / 2)) (goldbachEvenTargets M)) t)
    (hGood : Not (Membership.mem (lpfBadSourceTargets M) t)) :
    (M : Real) * singularDivisorProduct t / 512 <=
      goldbachMangoldtWeight (goldbachWindowInputs M t) t := by
  classical
  apply le_of_not_gt
  intro hBad
  apply hGood
  rcases Finset.mem_union.mp ht with h | h
  next => exact Finset.mem_union_left _ (Finset.mem_filter.mpr (And.intro h hBad))
  next => exact Finset.mem_union_right _ (Finset.mem_filter.mpr (And.intro h hBad))


end PrimeFactorOscillations.LPF
