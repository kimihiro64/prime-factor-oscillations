/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdRadialPacking
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.EvenSeparatedGrid
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.MomentNormalization
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.SeparatedExtremizers

/-! # Sharp radial packing in the equal-moment law and its complete support-size range -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

structure ThresholdPackingAttainer (r : Nat) (d eta K : Real)
    (a : Fin r -> Nat) (y : Fin r -> Real) (g M : Real) : Prop where
  order_pos : forall i, 0 < a i
  coords_above : forall i, d < y i
  total_mass : Finset.sum Finset.univ (fun i => 2 * (a i : Real)) = K
  admissible : thresholdEvenAdmissible d M K a y
  gap_pos : 0 < g
  gap_small : g < eta
  gap_formula : forall i j, y j - y i = g * ((j.val : Real) - (i.val : Real))
  separated : thresholdSelectedSeparated d Finset.univ a y g
  radial_card : (thresholdRadialSupport Finset.univ
    (fun i => 2 * (a i : Real) * momentRoundIndicator d (y i)) y).card = r
  deficit_pos : 0 < K - M
  deficit_small : K - M < eta
  variance_floor : thresholdSelectedVariance d Finset.univ (fun i => 2 * (a i : Real)) y =
    g ^ 2 * Finset.separatedVarianceFloor r 2 K
  variance_budget : thresholdSelectedVariance d Finset.univ (fun i => 2 * (a i : Real)) y =
    thresholdVarianceBudget d 1 K (K - M)

theorem thresholdRadialPacking_attainers (r k : Nat) (d eta : Real)
    (hr : 2 <= r) (hkr : r <= k) (hd : And (0 < d) (d < 1)) (heta : 0 < eta) :
    exists a : Fin r -> Nat, exists y : Fin r -> Real, exists g M : Real,
      ThresholdPackingAttainer r d eta (2 * (k : Real)) a y g M := by
  classical
  let K : Real := 2 * (k : Real)
  let F := Finset.separatedVarianceFloor r 2 K
  choose a z hData using Finset.even_separatedGrid_centered r k hr hkr
  have hOrder : forall i, 0 < a i := hData.1
  let w := fun i => 2 * (a i : Real)
  have hMass : Finset.sum Finset.univ w = K := hData.2.1
  have hCenter : Finset.sum Finset.univ (fun i => w i * z i) = 0 := hData.2.2.1
  have hSecond : Finset.sum Finset.univ (fun i => w i * (z i) ^ 2) = F := hData.2.2.2.1
  have hF : 0 < F := hData.2.2.2.2.1
  have hZGap : forall i j, z j - z i = (j.val : Real) - (i.val : Real) :=
    hData.2.2.2.2.2
  have hk : 0 < k := by omega
  have hK : 0 < K := by dsimp only [K]; positivity
  have hw : forall i, 0 <= w i := by
    intro i
    exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hwp : forall i, 0 < w i := by
    intro i
    exact mul_pos (by norm_num) (by exact_mod_cast hOrder i)
  let A := 1 + Finset.sum Finset.univ (fun i => abs (z i))
  have hA : 0 <= A := by
    have hs := Finset.sum_nonneg (fun i (_ : Membership.mem Finset.univ i) => abs_nonneg (z i))
    dsimp only [A]
    linarith only [hs]
  have hAbs : forall i, abs (z i) <= A := by
    intro i
    have h := Finset.single_le_sum
      (fun j (_ : Membership.mem Finset.univ j) => abs_nonneg (z j)) (Finset.mem_univ i)
    dsimp only [A]
    linarith only [h]
  let rho := F / K
  have hrho : 0 < rho := div_pos hF hK
  choose p hp using Finset.momentNormalization_small_parameter A rho K d eta hA hrho hK hd heta
  let D := 1 + rho * p ^ 2
  let y := fun i => (1 + p * z i) / D
  let g := p / D
  let M := K / D
  let delta := K - M
  have hNorm := Finset.centered_moment_normalization Finset.univ w z K F p
    hK hF hMass hCenter hSecond
  have hD : 0 < D := hNorm.1
  have hFirst : Finset.sum Finset.univ (fun i => w i * y i) = M := hNorm.2.1
  have hSquare : Finset.sum Finset.univ (fun i => w i * (y i) ^ 2) = M := hNorm.2.2.1
  have hVar : Finset.sum Finset.univ (fun i => w i * (y i - 1 / D) ^ 2) = g ^ 2 * F :=
    hNorm.2.2.2
  have hCoords : forall i, d < y i := fun i => hp.2.2.2.2.1 (z i) (hAbs i)
  have hI : forall i, momentRoundIndicator d (y i) = 1 := by
    intro i
    simp only [momentRoundIndicator, ite_eq_left (hCoords i).le]
  have hSel : thresholdSelectedMass d Finset.univ w y = K := by
    change Finset.sum Finset.univ (fun i => w i * momentRoundIndicator d (y i)) = K
    calc
      _ = Finset.sum Finset.univ w := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hI i, mul_one]
      _ = K := hMass
  have hMu : thresholdSelectedMean d Finset.univ w y = 1 / D := by
    unfold thresholdSelectedMean
    rw [hSel]
    have hNumerator : Finset.sum Finset.univ
        (fun i => w i * momentRoundIndicator d (y i) * y i) = M := by
      calc
        _ = Finset.sum Finset.univ (fun i => w i * y i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hI i, mul_one]
        _ = M := hFirst
    rw [hNumerator]
    dsimp only [M]
    field_simp [ne_of_gt hK, ne_of_gt hD]
  have hVariance : thresholdSelectedVariance d Finset.univ w y = g ^ 2 * F := by
    unfold thresholdSelectedVariance
    rw [hMu]
    calc
      _ = Finset.sum Finset.univ (fun i => w i * (y i - 1 / D) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hI i, mul_one]
      _ = _ := hVar
  have hGap : forall i j, y j - y i = g * ((j.val : Real) - (i.val : Real)) := by
    intro i j
    calc
      _ = p * (z j - z i) / D := by dsimp only [y]; ring
      _ = _ := by rw [hZGap i j]; dsimp only [g]; ring
  have hg : 0 < g := div_pos hp.1 hD
  have hDge : 1 <= D := by
    dsimp only [D]
    nlinarith only [mul_nonneg hrho.le (sq_nonneg p)]
  have hGmul : g * D = p := by dsimp only [g]; field_simp [ne_of_gt hD]
  have hGReserve := mul_nonneg hg.le (sub_nonneg.mpr hDge)
  have hGle : g <= p := by nlinarith only [hGReserve, hGmul]
  have hGSmall : g < eta := lt_of_le_of_lt hGle hp.2.2.2.2.2
  have hInj : Function.Injective y := by
    intro i j hij
    have h := hGap i j
    rw [hij, sub_self] at h
    have hDiff := (mul_eq_zero.mp h.symm).resolve_left (ne_of_gt hg)
    have hReal : (i.val : Real) = (j.val : Real) := by linarith only [hDiff]
    exact Fin.ext (by exact_mod_cast hReal)
  have hCard : (thresholdRadialSupport Finset.univ
      (fun i => w i * momentRoundIndicator d (y i)) y).card = r := by
    unfold thresholdRadialSupport
    have hFilter : Finset.univ.filter (fun i => 0 < w i * momentRoundIndicator d (y i)) =
        Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro i _
      rw [hI i, mul_one]
      exact hwp i
    rw [hFilter]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_image_of_injective Finset.univ hInj
  have hSeparated : thresholdSelectedSeparated d Finset.univ a y g := by
    intro i j _ _ _ _ _ _ hNe
    have hIndex : Not (i.val = j.val) := by
      intro h
      exact hNe (congrArg y (Fin.ext h))
    by_cases hij : i.val < j.val
    case pos =>
      have hNat : i.val + 1 <= j.val := hij
      have hCast : (i.val : Real) + 1 <= (j.val : Real) := by exact_mod_cast hNat
      have hStep : 1 <= (j.val : Real) - (i.val : Real) := by linarith only [hCast]
      have hMult := _root_.mul_le_mul_of_nonneg_left hStep hg.le
      have hLower : g <= y j - y i := by rw [hGap i j]; linarith only [hMult]
      rw [abs_of_neg (show y i - y j < 0 by linarith only [hLower, hg])]
      linarith only [hLower]
    case neg =>
      have hNat : j.val + 1 <= i.val := by omega
      have hCast : (j.val : Real) + 1 <= (i.val : Real) := by exact_mod_cast hNat
      have hStep : 1 <= (i.val : Real) - (j.val : Real) := by linarith only [hCast]
      have hMult := _root_.mul_le_mul_of_nonneg_left hStep hg.le
      have hLower : g <= y i - y j := by rw [hGap j i]; linarith only [hMult]
      rw [abs_of_pos (show 0 < y i - y j by linarith only [hLower, hg])]
      exact hLower
  have hMge : d * K <= M := by
    calc
      _ = Finset.sum Finset.univ (fun i => w i * d) := by rw [<- Finset.sum_mul, hMass]; ring
      _ <= Finset.sum Finset.univ (fun i => w i * y i) := by
        apply Finset.sum_le_sum
        intro i _
        exact _root_.mul_le_mul_of_nonneg_left (hCoords i).le (hw i)
      _ = M := hFirst
  have hCap : delta - K * (1 - d) <= 0 := by
    dsimp only [delta]
    nlinarith only [hMge]
  have hRho : K * rho = F := by dsimp only [rho]; field_simp [ne_of_gt hK]
  have hBudget : thresholdVarianceBudget d 1 K delta = g ^ 2 * F := by
    unfold thresholdVarianceBudget
    rw [max_eq_right hCap]
    norm_num only
    dsimp only [delta, M, g]
    rw [<- hRho]
    dsimp only [D]
    field_simp [ne_of_gt hK, ne_of_gt hD]
    ring
  refine Exists.intro a (Exists.intro y (Exists.intro g (Exists.intro M ?_)))
  exact {
    order_pos := hOrder
    coords_above := hCoords
    total_mass := hMass
    admissible := And.intro (fun i => le_trans hd.1.le (hCoords i).le)
      (And.intro hFirst (And.intro hSquare hSel))
    gap_pos := hg
    gap_small := hGSmall
    gap_formula := hGap
    separated := hSeparated
    radial_card := hCard
    deficit_pos := hp.2.2.1
    deficit_small := hp.2.2.2.1
    variance_floor := hVariance
    variance_budget := hVariance.trans hBudget.symm }

theorem thresholdPackingAttainer_not_small (r : Nat) (d eta K : Real)
    (a : Fin r -> Nat) (y : Fin r -> Real) (g M : Real)
    (hd : And (0 < d) (d < 1)) (hK : 0 < K) (hr : r <= 1) :
    Not (ThresholdPackingAttainer r d eta K a y g M) := by
  intro h
  let w := fun i => 2 * (a i : Real)
  have hw : forall i, Membership.mem Finset.univ i -> 0 <= w i := by
    intro i _
    exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hMge : d * K <= M := by
    calc
      _ = Finset.sum Finset.univ (fun i => w i * d) := by
        rw [<- Finset.sum_mul, h.total_mass]
        ring
      _ <= Finset.sum Finset.univ (fun i => w i * y i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact _root_.mul_le_mul_of_nonneg_left (h.coords_above i).le (hw i hi)
      _ = M := h.admissible.2.1
  have hM : 0 < Finset.sum Finset.univ (fun i => w i * y i) := by
    rw [h.admissible.2.1]
    exact lt_of_lt_of_le (mul_pos hd.1 hK) hMge
  have hMoment : Finset.sum Finset.univ (fun i => w i * (y i) ^ 2) =
      Finset.sum Finset.univ (fun i => w i * y i) :=
    h.admissible.2.2.1.trans h.admissible.2.1.symm
  have hCard : (thresholdRadialSupport Finset.univ w y).card <= 1 :=
    le_trans (thresholdRadialSupport_card_le_fin w y) hr
  have hRigid := finiteWeighted_one_radius_rigid Finset.univ w y d hd.2 hw
    (fun i _ => h.admissible.1 i) hMoment hM hCard
  have hMK : M = K := h.admissible.2.1.symm.trans (hRigid.1.trans h.total_mass)
  have hDelta := h.deficit_pos
  rw [hMK, sub_self] at hDelta
  exact (lt_irrefl 0) hDelta

theorem thresholdRadialPacking_attainers_iff (r k : Nat) (d eta : Real)
    (hk : 0 < k) (hd : And (0 < d) (d < 1)) (heta : 0 < eta) :
    (exists a : Fin r -> Nat, exists y : Fin r -> Real, exists g M : Real,
      ThresholdPackingAttainer r d eta (2 * (k : Real)) a y g M) <->
        And (2 <= r) (r <= k) := by
  constructor
  case mp =>
    intro h
    choose a y g M ha using h
    have hK : 0 < 2 * (k : Real) :=
      mul_pos (by norm_num) (by exact_mod_cast hk)
    have hr : 2 <= r := by
      by_contra hn
      have hSmall : r <= 1 := by omega
      exact thresholdPackingAttainer_not_small r d eta (2 * (k : Real)) a y g M hd hK hSmall ha
    have hSel : 0 < thresholdSelectedMass d Finset.univ (fun i => 2 * (a i : Real)) y := by
      rw [ha.admissible.2.2.2]
      exact hK
    have hCount := finiteEven_selected_radial_variance_lower Finset.univ a y d g
      ha.gap_pos.le ha.separated hSel
    dsimp only at hCount
    have hBound := hCount.1
    rw [ha.radial_card, ha.admissible.2.2.2] at hBound
    have hReal : (r : Real) <= (k : Real) := by linarith only [hBound]
    have hkr : r <= k := by exact_mod_cast hReal
    exact And.intro hr hkr
  case mpr =>
    intro h
    exact thresholdRadialPacking_attainers r k d eta h.1 h.2 hd heta

theorem thresholdPackingAttainer_order_rigidity (r : Nat) (d eta K : Real)
    (a : Fin r -> Nat) (y : Fin r -> Real) (g M : Real) (hr : 0 < r)
    (h : ThresholdPackingAttainer r d eta K a y g M) :
    exists j : Fin r,
      And ((Finset.separatedGridCoord r j) ^ 2 = Finset.separatedGridParity r)
        (And (forall i, Not (i = j) -> a i = 1)
          (2 * (a j : Real) = K - 2 * ((r : Real) - 1))) := by
  classical
  let w := fun i => 2 * (a i : Real)
  have hw : forall i, 2 <= w i := by
    intro i
    have hNat : 1 <= a i := Nat.succ_le_iff.mpr (h.order_pos i)
    have hReal : (1 : Real) <= (a i : Real) := by exact_mod_cast hNat
    dsimp only [w]
    linarith only [hReal]
  have hI : forall i, momentRoundIndicator d (y i) = 1 := by
    intro i
    simp [momentRoundIndicator, (h.coords_above i).le]
  have hVariance : thresholdSelectedVariance d Finset.univ w y =
      Finset.sum Finset.univ (fun i => w i *
        (y i - Finset.sum Finset.univ (fun j => w j * y j) /
          Finset.sum Finset.univ w) ^ 2) := by
    unfold thresholdSelectedVariance thresholdSelectedMean thresholdSelectedMass
    simp_rw [hI, mul_one]
  have hStep : forall i j : Fin r, j.val = i.val + 1 -> g <= y j - y i := by
    intro i j hij
    have hCast : (j.val : Real) = (i.val : Real) + 1 := by exact_mod_cast hij
    have hGap := h.gap_formula i j
    rw [hCast] at hGap
    nlinarith only [hGap]
  have hMass : Finset.sum Finset.univ w = K := h.total_mass
  have hEq := h.variance_floor
  change thresholdSelectedVariance d Finset.univ w y =
    g ^ 2 * Finset.separatedVarianceFloor r 2 K at hEq
  rw [hVariance, <- hMass] at hEq
  have hData := (Finset.separated_weighted_variance_equality_iff r hr w y 2 g
    (by norm_num) h.gap_pos hw hStep).mp hEq
  choose j hj c hwj hy using hData
  have hWeights : forall i, w i = Finset.separatedGridWeights r 2 K j i := by
    intro i
    simpa only [hMass] using hwj i
  refine Exists.intro j (And.intro hj (And.intro ?_ ?_))
  case refine_1 =>
    intro i hij
    have hwi : 2 * (a i : Real) = 2 := by
      simpa [w, Finset.separatedGridWeights, hij] using hWeights i
    have hCast : (a i : Real) = 1 := by linarith only [hwi]
    exact_mod_cast hCast
  case refine_2 =>
    have hwjReal : 2 * (a j : Real) = 2 + (K - 2 * (r : Real)) := by
      simpa [w, Finset.separatedGridWeights] using hWeights j
    nlinarith only [hwjReal]

end PrimeFactorOscillations
