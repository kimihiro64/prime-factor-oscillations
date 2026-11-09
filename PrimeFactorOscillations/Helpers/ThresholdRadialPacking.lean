/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Sort
import PrimeFactorOscillations.Helpers.ThresholdRadialCard
import PrimeFactorOscillations.Helpers.ThresholdSeparatedSpectrum
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.SeparatedGrid

/-! # Sharp separated-level packing for finite weighted moment profiles -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdRadialFiberMass {Iota : Type*} (S : Finset Iota)
    (w y : Iota -> Real) (z : Real) : Real := by
  classical
  exact Finset.sum ((S.filter (fun i => 0 < w i)).filter (fun i => y i = z)) w

theorem finiteWeighted_radial_fiber_sum {Iota : Type*} (S : Finset Iota)
    (w y : Iota -> Real) (hw : forall i, Membership.mem S i -> 0 <= w i)
    (phi : Real -> Real) :
    Finset.sum (thresholdRadialSupport S w y)
      (fun z => thresholdRadialFiberMass S w y z * phi z) =
      Finset.sum S (fun i => w i * phi (y i)) := by
  classical
  let T := S.filter (fun i => 0 < w i)
  let R := thresholdRadialSupport S w y
  have hMap : forall i, Membership.mem T i -> Membership.mem R (y i) := by
    intro i hi
    have h := Finset.mem_filter.mp hi
    exact (thresholdRadialSupport_mem S w y (y i)).mpr
      (Exists.intro i (And.intro h.1 (And.intro h.2 rfl)))
  have hGroup := Finset.sum_fiberwise_of_maps_to hMap (fun i => w i * phi (y i))
  have hEach : forall z, Membership.mem R z ->
      thresholdRadialFiberMass S w y z * phi z =
        Finset.sum (T.filter (fun i => y i = z)) (fun i => w i * phi (y i)) := by
    intro z _
    dsimp only [thresholdRadialFiberMass]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  have hRestrict : Finset.sum T (fun i => w i * phi (y i)) =
      Finset.sum S (fun i => w i * phi (y i)) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hn
    have hNot : Not (0 < w i) := by
      intro hp
      exact hn (Finset.mem_filter.mpr (And.intro hi hp))
    have hz : w i = 0 := le_antisymm (le_of_not_gt hNot) (hw i hi)
    rw [hz, zero_mul]
  exact (Finset.sum_congr rfl hEach).trans (hGroup.trans hRestrict)

theorem finiteWeighted_radial_fiber_quantum {Iota : Type*} (S : Finset Iota)
    (w y : Iota -> Real) (q : Real)
    (hw : forall i, Membership.mem S i -> 0 <= w i)
    (hq : forall i, Membership.mem S i -> 0 < w i -> q <= w i)
    (z : Real) (hz : Membership.mem (thresholdRadialSupport S w y) z) :
    q <= thresholdRadialFiberMass S w y z := by
  classical
  choose i hi using (thresholdRadialSupport_mem S w y z).mp hz
  have hMem : Membership.mem
      ((S.filter (fun i => 0 < w i)).filter (fun i => y i = z)) i :=
    Finset.mem_filter.mpr (And.intro
      (Finset.mem_filter.mpr (And.intro hi.1 hi.2.1)) hi.2.2)
  apply le_trans (hq i hi.1 hi.2.1)
  apply Finset.single_le_sum _ hMem
  intro j hj
  exact hw j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1

theorem finiteWeighted_radial_packing_lower {Iota : Type*} (S : Finset Iota)
    (w y : Iota -> Real) (q g : Real) (hq : 0 < q) (hg : 0 <= g)
    (hw : forall i, Membership.mem S i -> 0 <= w i)
    (hQuantum : forall i, Membership.mem S i -> 0 < w i -> q <= w i)
    (hK : 0 < Finset.sum S w)
    (hSep : forall x, Membership.mem (thresholdRadialSupport S w y) x ->
      forall z, Membership.mem (thresholdRadialSupport S w y) z ->
        x < z -> g <= z - x) :
    let K := Finset.sum S w
    let H := Finset.sum S (fun i => w i * y i)
    g ^ 2 * Finset.separatedVarianceFloor
        (thresholdRadialSupport S w y).card q K <=
      Finset.sum S (fun i => w i * (y i - H / K) ^ 2) := by
  classical
  dsimp only
  let R := thresholdRadialSupport S w y
  have hGroup := finiteWeighted_radial_fiber_sum S w y hw
  have hR : 0 < R.card := by
    by_contra hn
    have hEmpty : R = Finset.empty := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hn)
    have h := hGroup (fun _ => 1)
    change Finset.sum R (fun z => thresholdRadialFiberMass S w y z * 1) =
      Finset.sum S (fun i => w i * 1) at h
    have hZero : Finset.sum R (fun z => thresholdRadialFiberMass S w y z * 1) = 0 := by
      rw [hEmpty]
      rfl
    rw [hZero] at h
    simp only [mul_one] at h
    linarith only [hK, h]
  let e := R.orderIsoOfFin rfl
  let a := fun i => thresholdRadialFiberMass S w y (e i).val
  let x := fun i => (e i).val
  have hSum : forall phi : Real -> Real,
      Finset.sum Finset.univ (fun i => a i * phi (x i)) =
        Finset.sum S (fun i => w i * phi (y i)) := by
    intro phi
    have hEnum := Equiv.sum_comp e.toEquiv
      (fun z : R => thresholdRadialFiberMass S w y z.val * phi z.val)
    exact hEnum.trans ((Finset.sum_coe_sort R
      (fun z => thresholdRadialFiberMass S w y z * phi z)).trans (hGroup phi))
  have ha : forall i, q <= a i := by
    intro i
    exact finiteWeighted_radial_fiber_quantum S w y q hw hQuantum (x i) (e i).property
  have hStep : forall i j : Fin R.card, j.val = i.val + 1 -> g <= x j - x i := by
    intro i j hij
    have hlt : i < j := by change i.val < j.val; omega
    exact hSep (x i) (e i).property (x j) (e j).property (e.strictMono hlt)
  have hMass : Finset.sum Finset.univ a = Finset.sum S w := by
    simpa only [mul_one] using hSum (fun _ => 1)
  have hFirst : Finset.sum Finset.univ (fun i => a i * x i) =
      Finset.sum S (fun i => w i * y i) := hSum (fun z => z)
  have hBound := Finset.separated_weighted_variance_lower R.card hR a x q g hq hg ha hStep
  dsimp only at hBound
  rw [hMass, hFirst] at hBound
  exact hBound.2.trans_eq (hSum
    (fun z => (z - Finset.sum S (fun i => w i * y i) / Finset.sum S w) ^ 2))

theorem finiteEven_selected_radial_variance_lower {Iota : Type*} (S : Finset Iota)
    (a : Iota -> Nat) (y : Iota -> Real) (d g : Real) (hg : 0 <= g)
    (hSeparated : thresholdSelectedSeparated d S a y g)
    (hK : 0 < thresholdSelectedMass d S (fun i => 2 * (a i : Real)) y) :
    let w := fun i => 2 * (a i : Real)
    let b := fun i => w i * momentRoundIndicator d (y i)
    let K := thresholdSelectedMass d S w y
    let r := (thresholdRadialSupport S b y).card
    And (2 * (r : Real) <= K)
      (g ^ 2 * Finset.separatedVarianceFloor r 2 K <=
        thresholdSelectedVariance d S w y) := by
  classical
  dsimp only
  let w := fun i => 2 * (a i : Real)
  let b := fun i => w i * momentRoundIndicator d (y i)
  let R := thresholdRadialSupport S b y
  have hw : forall i, Membership.mem S i -> 0 <= w i := by
    intro i _
    exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hb : forall i, Membership.mem S i -> 0 <= b i := by
    intro i hi
    dsimp only [b]
    apply mul_nonneg (hw i hi)
    unfold momentRoundIndicator
    split_ifs <;> norm_num
  have hPos : forall i, 0 < b i -> And (0 < a i) (d <= y i) := by
    intro i hi
    have ha : 0 < a i := by
      by_contra hn
      have hz : a i = 0 := Nat.eq_zero_of_not_pos hn
      simp only [b, w, hz, Nat.cast_zero, mul_zero, zero_mul] at hi
      exact (lt_irrefl 0) hi
    have hc : d <= y i := by
      by_contra hn
      simp only [b, momentRoundIndicator, ite_eq_right hn, mul_zero] at hi
      exact (lt_irrefl 0) hi
    exact And.intro ha hc
  have hQuantum : forall i, Membership.mem S i -> 0 < b i -> 2 <= b i := by
    intro i _ hi
    have h := hPos i hi
    have haR : (1 : Real) <= (a i : Real) := by exact_mod_cast h.1
    simp only [b, w, momentRoundIndicator, ite_eq_left h.2, mul_one]
    linarith only [haR]
  have hSep : forall x, Membership.mem R x ->
      forall z, Membership.mem R z -> x < z -> g <= z - x := by
    intro x hx z hz hxz
    choose i hi using (thresholdRadialSupport_mem S b y x).mp hx
    choose j hj using (thresholdRadialSupport_mem S b y z).mp hz
    have hiP := hPos i hi.2.1
    have hjP := hPos j hj.2.1
    have hNe : Not (y i = y j) := by
      rw [hi.2.2, hj.2.2]
      exact ne_of_lt hxz
    have h := hSeparated i j hi.1 hj.1 hiP.1 hjP.1 hiP.2 hjP.2 hNe
    rw [hi.2.2, hj.2.2, abs_of_neg (sub_neg.mpr hxz), neg_sub] at h
    exact h
  have hMass := finiteWeighted_radial_fiber_sum S b y hb (fun _ => 1)
  simp only [mul_one] at hMass
  have hCount : 2 * (R.card : Real) <= Finset.sum S b := by
    calc
      _ = Finset.sum R (fun _ => (2 : Real)) := by simp; ring
      _ <= Finset.sum R (thresholdRadialFiberMass S b y) := by
        apply Finset.sum_le_sum
        intro z hz
        exact finiteWeighted_radial_fiber_quantum S b y 2 hb hQuantum z hz
      _ = _ := hMass
  have hLower := finiteWeighted_radial_packing_lower S b y 2 g
    (by norm_num) hg hb hQuantum hK hSep
  exact And.intro hCount hLower

theorem finiteEven_selected_radial_packing {Iota : Type*} (S : Finset Iota)
    (a : Iota -> Nat) (y : Iota -> Real) (d g : Real)
    (hd : And (0 < d) (d < 1)) (hg : 0 <= g)
    (hSeparated : thresholdSelectedSeparated d S a y g)
    (hMoment : Finset.sum S (fun i => 2 * (a i : Real) * (y i) ^ 2) =
      Finset.sum S (fun i => 2 * (a i : Real) * y i))
    (hK : 0 < thresholdSelectedMass d S (fun i => 2 * (a i : Real)) y) :
    let w := fun i => 2 * (a i : Real)
    let b := fun i => w i * momentRoundIndicator d (y i)
    let K := thresholdSelectedMass d S w y
    let N := Finset.sum S w
    let M := Finset.sum S (fun i => w i * y i)
    let r := (thresholdRadialSupport S b y).card
    let v := thresholdModelHigh (N - K) K d
    And (2 * (r : Real) <= K)
      (g ^ 2 * Finset.separatedVarianceFloor r 2 K <=
        thresholdVarianceBudget d v K (thresholdTotalUpper d N K - M)) := by
  dsimp only
  have hLower := finiteEven_selected_radial_variance_lower S a y d g hg hSeparated hK
  have hw : forall i, Membership.mem S i -> 0 <= 2 * (a i : Real) := by
    intro i _
    exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hUpper := finiteWeighted_selected_variance_budget S (fun i => 2 * (a i : Real))
    y d hd hw hMoment hK
  exact And.intro hLower.1 (hLower.2.trans hUpper)

theorem finiteWeighted_radialSupport_mem_iff_stat_pos {Iota : Type*}
    (S : Finset Iota) (w y : Iota -> Real)
    (hw : forall i, Membership.mem S i -> 0 <= w i) (z : Real) :
    Membership.mem (thresholdRadialSupport S w y) z <->
      0 < Finset.sum S (fun i => w i * (if y i = z then 1 else 0)) := by
  classical
  have hNonneg : forall i, Membership.mem S i ->
      0 <= w i * (if y i = z then 1 else 0) := by
    intro i hi
    split_ifs
    case pos => simpa only [mul_one] using hw i hi
    case neg => simp only [mul_zero, le_refl]
  constructor
  case mp =>
    intro hz
    choose i hi using (thresholdRadialSupport_mem S w y z).mp hz
    have hp : 0 < w i * (if y i = z then 1 else 0) := by
      simpa only [ite_eq_left hi.2.2, mul_one] using hi.2.1
    exact lt_of_lt_of_le hp (Finset.single_le_sum hNonneg hi.1)
  case mpr =>
    intro hp
    choose i hi hPos using (Finset.sum_pos_iff_of_nonneg hNonneg).mp hp
    by_cases hy : y i = z
    case pos =>
      have hwPos : 0 < w i := by
        simpa only [ite_eq_left hy, mul_one] using hPos
      exact (thresholdRadialSupport_mem S w y z).mpr
        (Exists.intro i (And.intro hi (And.intro hwPos hy)))
    case neg =>
      simp only [ite_eq_right hy, mul_zero] at hPos
      exact False.elim ((lt_irrefl 0) hPos)

theorem finiteWeighted_radialSupport_eq_of_statistics {Iota Kappa : Type*}
    (S : Finset Iota) (T : Finset Kappa) (w y : Iota -> Real) (v z : Kappa -> Real)
    (hw : forall i, Membership.mem S i -> 0 <= w i)
    (hv : forall j, Membership.mem T j -> 0 <= v j)
    (hStat : forall phi : Real -> Real,
      Finset.sum S (fun i => w i * phi (y i)) =
        Finset.sum T (fun j => v j * phi (z j))) :
    thresholdRadialSupport S w y = thresholdRadialSupport T v z := by
  classical
  ext x
  rw [finiteWeighted_radialSupport_mem_iff_stat_pos S w y hw x,
    finiteWeighted_radialSupport_mem_iff_stat_pos T v z hv x,
    hStat (fun u => if u = x then 1 else 0)]

end PrimeFactorOscillations
