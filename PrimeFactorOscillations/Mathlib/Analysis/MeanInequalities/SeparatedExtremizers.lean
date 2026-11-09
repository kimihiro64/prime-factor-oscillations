/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.VarianceDefect

/-! # Classification of every sharp separated weighted-variance extremizer -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace Finset

theorem weightedVarianceNumerator_affine {Iota : Type*} (S : Finset Iota)
    (w x : Iota -> Real) (c g : Real) :
    weightedVarianceNumerator S w (fun i => c + g * x i) =
      g ^ 2 * weightedVarianceNumerator S w x := by
  have hDouble :
      2 * weightedVarianceNumerator S w (fun i => c + g * x i) =
        g ^ 2 * (2 * weightedVarianceNumerator S w x) := by
    calc
      _ = Finset.sum S (fun i => Finset.sum S
          (fun j => w i * w j * ((c + g * x i) - (c + g * x j)) ^ 2)) :=
        weightedVarianceNumerator_pairwise S w (fun i => c + g * x i)
      _ = Finset.sum S (fun i => Finset.sum S
          (fun j => g ^ 2 * (w i * w j * (x i - x j) ^ 2))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = g ^ 2 * Finset.sum S (fun i => Finset.sum S
          (fun j => w i * w j * (x i - x j) ^ 2)) := by
        simp only [<- Finset.mul_sum]
      _ = _ := by rw [<- weightedVarianceNumerator_pairwise S w x]
  nlinarith only [hDouble]

theorem weightedVarianceNumerator_pairwise_eq_of_le {Iota : Type*} (S : Finset Iota)
    (w x z : Iota -> Real) (hw : forall i, Membership.mem S i -> 0 < w i)
    (hPair : forall i j, Membership.mem S i -> Membership.mem S j ->
      (x i - x j) ^ 2 <= (z i - z j) ^ 2)
    (hEq : weightedVarianceNumerator S w x = weightedVarianceNumerator S w z)
    (i j : Iota) (hi : Membership.mem S i) (hj : Membership.mem S j) :
    (x i - x j) ^ 2 = (z i - z j) ^ 2 := by
  classical
  have hTerm : forall a, Membership.mem S a -> forall b, Membership.mem S b ->
      0 <= w a * w b * ((z a - z b) ^ 2 - (x a - x b) ^ 2) :=
    fun a ha b hb => mul_nonneg (mul_nonneg (hw a ha).le (hw b hb).le)
      (sub_nonneg.mpr (hPair a b ha hb))
  have hInner : forall a, Membership.mem S a -> 0 <= Finset.sum S
      (fun b => w a * w b * ((z a - z b) ^ 2 - (x a - x b) ^ 2)) :=
    fun a ha => Finset.sum_nonneg (hTerm a ha)
  have hSum : Finset.sum S (fun a => Finset.sum S
      (fun b => w a * w b * ((z a - z b) ^ 2 - (x a - x b) ^ 2))) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [<- weightedVarianceNumerator_pairwise S w z,
      <- weightedVarianceNumerator_pairwise S w x, hEq, sub_self]
  have h1 := Finset.single_le_sum (hTerm i hi) hj
  have h2 := Finset.single_le_sum hInner hi
  rw [hSum] at h2
  have hZero : w i * w j * ((z i - z j) ^ 2 - (x i - x j) ^ 2) = 0 :=
    le_antisymm (le_trans h1 h2) (hTerm i hi j hj)
  have hDiff := (mul_eq_zero.mp hZero).resolve_left
    (ne_of_gt (mul_pos (hw i hi) (hw j hj)))
  linarith only [hDiff]

theorem separated_pairwise_sq_of_step (r : Nat) (y : Fin r -> Real) (g : Real)
    (hg : 0 <= g)
    (hStep : forall i j : Fin r, j.val = i.val + 1 -> g <= y j - y i) :
    forall i j : Fin r,
      (g * separatedGridCoord r i - g * separatedGridCoord r j) ^ 2 <=
        (y i - y j) ^ 2 := by
  have hRank := separated_rank_distance_of_step r y g hStep
  intro i j
  by_cases hij : i.val <= j.val
  case pos =>
    have h := hRank i j hij
    have hDiff : 0 <= (j.val : Real) - (i.val : Real) := by
      have hCast : (i.val : Real) <= (j.val : Real) := by exact_mod_cast hij
      exact sub_nonneg.mpr hCast
    have hBase := mul_nonneg hg hDiff
    have hY : 0 <= y j - y i := le_trans hBase h
    have hProd := mul_nonneg (sub_nonneg.mpr h) (add_nonneg hY hBase)
    have hGrid : (g * separatedGridCoord r i - g * separatedGridCoord r j) ^ 2 =
        (g * ((j.val : Real) - (i.val : Real))) ^ 2 := by
      dsimp only [separatedGridCoord]
      ring
    rw [hGrid]
    nlinarith only [hProd]
  case neg =>
    have hji : j.val <= i.val := le_of_not_ge hij
    have h := hRank j i hji
    have hDiff : 0 <= (i.val : Real) - (j.val : Real) := by
      have hCast : (j.val : Real) <= (i.val : Real) := by exact_mod_cast hji
      exact sub_nonneg.mpr hCast
    have hBase := mul_nonneg hg hDiff
    have hY : 0 <= y i - y j := le_trans hBase h
    have hProd := mul_nonneg (sub_nonneg.mpr h) (add_nonneg hY hBase)
    have hGrid : (g * separatedGridCoord r i - g * separatedGridCoord r j) ^ 2 =
        (g * ((i.val : Real) - (j.val : Real))) ^ 2 := by
      dsimp only [separatedGridCoord]
      ring
    rw [hGrid]
    nlinarith only [hProd]

theorem separated_weighted_variance_equality_iff (r : Nat) (hr : 0 < r)
    (w y : Fin r -> Real) (q g : Real) (hq : 0 < q) (hg : 0 < g)
    (hw : forall i, q <= w i)
    (hStep : forall i j : Fin r, j.val = i.val + 1 -> g <= y j - y i) :
    let K := Finset.sum Finset.univ w
    let mu := Finset.sum Finset.univ (fun i => w i * y i) / K
    Finset.sum Finset.univ (fun i => w i * (y i - mu) ^ 2) =
      g ^ 2 * separatedVarianceFloor r q K <->
      exists j : Fin r,
        And ((separatedGridCoord r j) ^ 2 = separatedGridParity r)
          (exists c : Real, And (forall i, w i = separatedGridWeights r q K j i)
            (forall i, y i = c + g * separatedGridCoord r i)) := by
  classical
  dsimp only
  let K := Finset.sum Finset.univ w
  let mu := Finset.sum Finset.univ (fun i => w i * y i) / K
  let B := q * K * ((r : Real) * ((r : Real) ^ 2 - 1) / 12) +
    q * (r : Real) * (K - q * (r : Real)) * separatedGridParity r
  change Finset.sum Finset.univ (fun i => w i * (y i - mu) ^ 2) =
      g ^ 2 * separatedVarianceFloor r q K <->
      exists j : Fin r,
        And ((separatedGridCoord r j) ^ 2 = separatedGridParity r)
          (exists c : Real, And (forall i, w i = separatedGridWeights r q K j i)
            (forall i, y i = c + g * separatedGridCoord r i))
  have hLower := separated_weighted_variance_lower r hr w y q g hq hg.le hw hStep
  have hK : 0 < K := hLower.1
  have hCenter := weightedVarianceNumerator_centered Finset.univ w y (ne_of_gt hK)
  change K * Finset.sum Finset.univ (fun i => w i * (y i - mu) ^ 2) =
    weightedVarianceNumerator Finset.univ w y at hCenter
  have hFloor : K * (g ^ 2 * separatedVarianceFloor r q K) = g ^ 2 * B := by
    dsimp only [separatedVarianceFloor, B]
    field_simp [ne_of_gt hK]
  have hGridLow : B <= weightedVarianceNumerator Finset.univ w (separatedGridCoord r) :=
    weighted_separatedGrid_lower r w q hq.le hw
  have hScale : weightedVarianceNumerator Finset.univ w
      (fun i => g * separatedGridCoord r i) =
        g ^ 2 * weightedVarianceNumerator Finset.univ w (separatedGridCoord r) := by
    simpa only [zero_add] using weightedVarianceNumerator_affine Finset.univ w
      (separatedGridCoord r) 0 g
  have hPair := separated_pairwise_sq_of_step r y g hg.le hStep
  have hComp := weightedVarianceNumerator_le_of_pairwise Finset.univ w
    (fun i => g * separatedGridCoord r i) y (fun i _ => le_trans hq.le (hw i))
      (fun i j _ _ => hPair i j)
  constructor
  case mp =>
    intro hEq
    have hNumY : weightedVarianceNumerator Finset.univ w y = g ^ 2 * B := by
      calc
        _ = K * Finset.sum Finset.univ (fun i => w i * (y i - mu) ^ 2) := hCenter.symm
        _ = K * (g ^ 2 * separatedVarianceFloor r q K) := by rw [hEq]
        _ = _ := hFloor
    have hUpper : g ^ 2 * weightedVarianceNumerator Finset.univ w
        (separatedGridCoord r) <= g ^ 2 * B := by
      calc
        _ = weightedVarianceNumerator Finset.univ w
            (fun i => g * separatedGridCoord r i) := hScale.symm
        _ <= weightedVarianceNumerator Finset.univ w y := hComp
        _ = _ := hNumY
    have hgSq : 0 < g ^ 2 := sq_pos_of_pos hg
    have hGridUpper : weightedVarianceNumerator Finset.univ w (separatedGridCoord r) <= B := by
      by_contra hn
      have hPos := mul_pos hgSq (sub_pos.mpr (lt_of_not_ge hn))
      nlinarith only [hPos, hUpper]
    have hGridEq : weightedVarianceNumerator Finset.univ w (separatedGridCoord r) = B :=
      le_antisymm hGridUpper hGridLow
    have hCompareEq : weightedVarianceNumerator Finset.univ w
        (fun i => g * separatedGridCoord r i) = weightedVarianceNumerator Finset.univ w y := by
      rw [hScale, hGridEq, <- hNumY]
    have hSame := weightedVarianceNumerator_pairwise_eq_of_le Finset.univ w
      (fun i => g * separatedGridCoord r i) y (fun i _ => lt_of_lt_of_le hq (hw i))
        (fun i j _ _ => hPair i j) hCompareEq
    choose j hj hwj using (weighted_separatedGrid_equality_iff r hr w q hq hw).mp hGridEq
    let i0 : Fin r := Fin.mk 0 hr
    refine Exists.intro j (And.intro hj
      (Exists.intro (y i0 - g * separatedGridCoord r i0) (And.intro hwj ?_)))
    intro i
    have hIndex : separatedGridCoord r i - separatedGridCoord r i0 = (i.val : Real) := by
      dsimp only [separatedGridCoord, i0]
      simp only [Nat.cast_zero]
      ring
    have hRank := separated_rank_distance_of_step r y g hStep i0 i (Nat.zero_le _)
    have hi0 : (i0.val : Real) = 0 := by
      dsimp only [i0]
      norm_num
    rw [hi0, sub_zero] at hRank
    have hBase : 0 <= g * (i.val : Real) := mul_nonneg hg.le (Nat.cast_nonneg _)
    have hSq := hSame i i0 (Finset.mem_univ i) (Finset.mem_univ i0)
    have hGridDiff : g * separatedGridCoord r i - g * separatedGridCoord r i0 =
        g * (i.val : Real) := by rw [<- mul_sub, hIndex]
    rw [hGridDiff] at hSq
    have hFactor : ((y i - y i0) - g * (i.val : Real)) *
        ((y i - y i0) + g * (i.val : Real)) = 0 := by nlinarith only [hSq]
    have hGap : y i - y i0 = g * (i.val : Real) := by
      cases mul_eq_zero.mp hFactor with
      | inl h => linarith only [h]
      | inr h => linarith only [h, hRank, hBase]
    have hIndexScaled : g * (separatedGridCoord r i - separatedGridCoord r i0) =
        g * (i.val : Real) := congrArg (fun t : Real => g * t) hIndex
    linarith only [hGap, hIndexScaled]
  case mpr =>
    intro h
    choose j hj c hwj hy using h
    have hGridEq : weightedVarianceNumerator Finset.univ w (separatedGridCoord r) = B :=
      (weighted_separatedGrid_equality_iff r hr w q hq hw).mpr
        (Exists.intro j (And.intro hj hwj))
    have hYFun : y = fun i => c + g * separatedGridCoord r i := funext hy
    have hNumY : weightedVarianceNumerator Finset.univ w y = g ^ 2 * B := by
      rw [hYFun, weightedVarianceNumerator_affine, hGridEq]
    have hFinal : K * (Finset.sum Finset.univ (fun i => w i * (y i - mu) ^ 2) -
        g ^ 2 * separatedVarianceFloor r q K) = 0 := by
      rw [mul_sub, hCenter, hNumY, hFloor, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hFinal).resolve_left (ne_of_gt hK))

end Finset
