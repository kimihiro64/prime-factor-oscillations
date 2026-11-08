/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdSingleLevelCost
import PrimeFactorOscillations.Helpers.ZetaThresholdOrbitProfile

/-! # Minimum selected even order, sharp linear stability, and reflected zeta carriers -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem finiteEven_selected_minimal {Iota : Type*} (S : Finset Iota)
    (a : Iota -> Nat) (y : Iota -> Real) (d : Real)
    (hSelected : thresholdSelectedMass d S (fun i => 2 * (a i : Real)) y = 2) :
    exists j, And (Membership.mem S j) (And (a j = 1) (And (d <= y j)
      (And (forall i, Membership.mem S i -> 0 < a i -> d <= y i -> i = j)
        (forall phi : Real -> Real,
          Finset.sum S (fun i => 2 * (a i : Real) * momentRoundIndicator d (y i) * phi (y i)) =
            2 * phi (y j))))) := by
  classical
  let b := fun i => 2 * (a i : Real) * momentRoundIndicator d (y i)
  have hIndicator : forall z : Real, 0 <= momentRoundIndicator d z := by
    intro z
    unfold momentRoundIndicator
    split_ifs <;> norm_num
  have hTerms : forall i, Membership.mem S i -> 0 <= b i := by
    intro i _
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg (a i))) (hIndicator (y i))
  have hSum : Finset.sum S b = 2 := hSelected
  have hPositive : 0 < Finset.sum S b := by rw [hSum]; norm_num
  choose j hj hp using (Finset.sum_pos_iff_of_nonneg hTerms).mp hPositive
  have hCut : d <= y j := by
    by_contra hn
    simp [b, momentRoundIndicator, hn] at hp
  have hAPos : 0 < a j := by
    by_contra hn
    have hz : a j = 0 := Nat.eq_zero_of_not_pos hn
    simp [b, hz] at hp
  have hOne : a j = 1 := by
    have hSingle := Finset.single_le_sum hTerms hj
    rw [hSum] at hSingle
    simp only [b, momentRoundIndicator, ite_eq_left hCut, mul_one] at hSingle
    have hReal : (a j : Real) <= 1 := by linarith only [hSingle]
    have hNat : a j <= 1 := by exact_mod_cast hReal
    omega
  have hBOne : b j = 2 := by simp [b, momentRoundIndicator, hCut, hOne]
  have hErase : Finset.sum (S.erase j) b = 0 := by
    have hFull := Finset.sum_erase_add S b hj
    rw [hSum, hBOne] at hFull
    linarith only [hFull]
  have hOther : forall i, Membership.mem S i -> Not (i = j) -> b i = 0 := by
    intro i hi hNe
    have hUpper := Finset.single_le_sum
      (fun k hk => hTerms k (Finset.mem_erase.mp hk).2)
      (Finset.mem_erase.mpr (And.intro hNe hi))
    rw [hErase] at hUpper
    exact le_antisymm hUpper (hTerms i hi)
  have hUnique : forall i, Membership.mem S i -> 0 < a i -> d <= y i -> i = j := by
    intro i hi hai hci
    by_contra hNe
    have hPos : 0 < b i := by
      dsimp only [b]
      rw [show momentRoundIndicator d (y i) = 1 by simp [momentRoundIndicator, hci], mul_one]
      exact mul_pos (by norm_num) (by exact_mod_cast hai)
    rw [hOther i hi hNe] at hPos
    exact (lt_irrefl 0) hPos
  refine Exists.intro j (And.intro hj (And.intro hOne (And.intro hCut (And.intro hUnique ?_))))
  intro phi
  change Finset.sum S (fun i => b i * phi (y i)) = 2 * phi (y j)
  calc
    _ = b j * phi (y j) := Finset.sum_eq_single j
      (fun i hi hNe => by rw [hOther i hi hNe, zero_mul])
      (fun hn => False.elim (hn hj))
    _ = _ := by rw [hBOne]

theorem finiteEven_minimal_selected_linear {Iota : Type*} (S : Finset Iota)
    (a : Iota -> Nat) (y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (hMoment : Finset.sum S (fun i => 2 * (a i : Real) * (y i) ^ 2) =
      Finset.sum S (fun i => 2 * (a i : Real) * y i))
    (hSelected : thresholdSelectedMass d S (fun i => 2 * (a i : Real)) y = 2) :
    let N := Finset.sum S (fun i => 2 * (a i : Real))
    let M := Finset.sum S (fun i => 2 * (a i : Real) * y i)
    let v := thresholdModelHigh (N - 2) 2 d
    let Delta := thresholdTotalUpper d N 2 - M
    let L := Finset.sum S (fun i => 2 * (a i : Real) * thresholdTotalLowDistance d (y i))
    And (exists j, And (Membership.mem S j) (And (a j = 1) (d <= y j)))
      (And (0 <= Delta)
        (And (abs (Finset.sum S (fun i => 2 * (a i : Real) * abs (y i - v)) -
          thresholdTotalStatistic d v N 2 (fun z => abs (z - v))) = L + abs (Delta - L))
          (And (forall phi : Real -> Real,
            (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
            abs (Finset.sum S (fun i => 2 * (a i : Real) * phi (y i)) -
              thresholdTotalStatistic d v N 2 phi) <= L + abs (Delta - L))
            (forall phi : Real -> Real,
              (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
              abs (Finset.sum S (fun i => 2 * (a i : Real) * phi (y i)) -
                thresholdTotalStatistic d v N 2 phi) <= thresholdSingleCoefficient d v * Delta)))) := by
  dsimp only
  choose j hj hOne hCut hUnique hCollapse using finiteEven_selected_minimal S a y d hSelected
  have ha : forall i, Membership.mem S i -> 0 <= 2 * (a i : Real) :=
    fun i _ => mul_nonneg (by norm_num) (Nat.cast_nonneg (a i))
  have hK : 0 < thresholdSelectedMass d S (fun i => 2 * (a i : Real)) y := by
    rw [hSelected]
    norm_num
  have hDirac : thresholdSelectedDirac d S (fun i => 2 * (a i : Real)) y (y j) := by
    intro phi
    rw [hSelected]
    exact hCollapse phi
  have hMain := finiteWeighted_single_level_linear S (fun i => 2 * (a i : Real)) y d (y j)
    hd ha hMoment hK hDirac
  rw [hSelected] at hMain
  exact And.intro (Exists.intro j (And.intro hj (And.intro hOne hCut))) hMain

theorem finiteEven_minimal_selected_half {Iota : Type*} (S : Finset Iota)
    (a : Iota -> Nat) (y : Iota -> Real) (d : Real) (hd : And (0 < d) (d <= 1 / 2))
    (hMoment : Finset.sum S (fun i => 2 * (a i : Real) * (y i) ^ 2) =
      Finset.sum S (fun i => 2 * (a i : Real) * y i))
    (hSelected : thresholdSelectedMass d S (fun i => 2 * (a i : Real)) y = 2) :
    let N := Finset.sum S (fun i => 2 * (a i : Real))
    let M := Finset.sum S (fun i => 2 * (a i : Real) * y i)
    let v := thresholdModelHigh (N - 2) 2 d
    let Delta := thresholdTotalUpper d N 2 - M
    And (abs (Finset.sum S (fun i => 2 * (a i : Real) * abs (y i - v)) -
      thresholdTotalStatistic d v N 2 (fun z => abs (z - v))) = Delta)
      (forall phi : Real -> Real,
        (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
        abs (Finset.sum S (fun i => 2 * (a i : Real) * phi (y i)) -
          thresholdTotalStatistic d v N 2 phi) <= Delta) := by
  dsimp only
  choose j hj hOne hCut hUnique hCollapse using finiteEven_selected_minimal S a y d hSelected
  have ha : forall i, Membership.mem S i -> 0 <= 2 * (a i : Real) :=
    fun i _ => mul_nonneg (by norm_num) (Nat.cast_nonneg (a i))
  have hK : 0 < thresholdSelectedMass d S (fun i => 2 * (a i : Real)) y := by
    rw [hSelected]
    norm_num
  have hDirac : thresholdSelectedDirac d S (fun i => 2 * (a i : Real)) y (y j) := by
    intro phi
    rw [hSelected]
    exact hCollapse phi
  have hMain := finiteWeighted_single_level_half S (fun i => 2 * (a i : Real)) y d (y j)
    hd ha hMoment hK hDirac
  rw [hSelected] at hMain
  exact hMain

theorem zeta_selected_two_dirac (W : Finset Complex) (d t : Real) (hd : 0 < d) (ht : 0 < t)
    (hStrip : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hSelected : thresholdSelectedMass d W (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / t) = 2) :
    exists h : Real, And (d <= h)
      (And (thresholdSelectedDirac d W (fun w => (analyticOrderNatAt riemannZeta w : Real))
        (fun w => (w.re - 1 / 2) ^ 2 / t) h)
        (exists w : Complex, And (Membership.mem W w) (And (1 / 2 < w.re)
          (And ((w.re - 1 / 2) ^ 2 / t = h)
            (And (Membership.mem W (zetaHorizontalReflection w))
              (And (Not (w = zetaHorizontalReflection w))
                (And (analyticOrderNatAt riemannZeta w = 1)
                  (analyticOrderNatAt riemannZeta (zetaHorizontalReflection w) = 1)))))))) := by
  choose n a y hy hCarrier hStat using zeta_finite_reflection_profile W t ht hStrip hReflect
  have hI0 : momentRoundIndicator d 0 = 0 := by
    simp [momentRoundIndicator, not_le.mpr hd]
  have hProfileSelected : thresholdSelectedMass d Finset.univ (fun i => 2 * (a i : Real)) y = 2 := by
    have hh := hStat (fun z => momentRoundIndicator d z)
    rw [hI0, mul_zero, add_zero] at hh
    exact hh.symm.trans hSelected
  choose j hj hOne hCut hUnique hCollapse using
    finiteEven_selected_minimal Finset.univ a y d hProfileSelected
  have hDirac : thresholdSelectedDirac d W (fun w => (analyticOrderNatAt riemannZeta w : Real))
      (fun w => (w.re - 1 / 2) ^ 2 / t) (y j) := by
    intro phi
    have hh := hStat (fun z => momentRoundIndicator d z * phi z)
    simp only [hI0, zero_mul, mul_zero, add_zero] at hh
    have hProfile : Finset.sum Finset.univ (fun i =>
        2 * (a i : Real) * (momentRoundIndicator d (y i) * phi (y i))) = 2 * phi (y j) := by
      simpa only [mul_assoc] using hCollapse phi
    rw [hProfile] at hh
    rw [hSelected]
    simpa only [mul_assoc] using hh
  choose w hw hRight hA hY using hCarrier j
  have hOrder : analyticOrderNatAt riemannZeta w = 1 := hA.symm.trans hOne
  have hROrder : analyticOrderNatAt riemannZeta (zetaHorizontalReflection w) = 1 := by
    rw [zetaOrder_reflection w (hStrip w hw), hOrder]
  have hNe : Not (w = zetaHorizontalReflection w) := by
    intro heq
    have hre := congrArg Complex.re heq
    rw [zetaHorizontalReflection_re] at hre
    linarith only [hre, hRight]
  exact Exists.intro (y j) (And.intro hCut (And.intro hDirac
    (Exists.intro w (And.intro hw (And.intro hRight (And.intro hY.symm
      (And.intro (hReflect w hw) (And.intro hNe (And.intro hOrder hROrder)))))))))

end PrimeFactorOscillations
