/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.Energy.DeletedRobustGeometry

/-!
# KappaHalfReflection

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors

The deleted reference window below improves the source's kappa >= 3/4
restriction to every fixed lower floor kappa0 > 1/2. It changes no global
zero-free boundary without the remaining analytic consumers.
-/


noncomputable section

namespace OAI.SevenEighths.KappaHalfReflection

open scoped BigOperators Classical SchwartzMap
open HeckeFamily HeckeDyadic CenteredMomentHeckeHeight CenteredMomentRetainedEnergy
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDeletionBudget
open CenteredMomentEnergyReferenceDeletionCapacity

local notation "O" => HeckeFamily.O

theorem joint_slot_budget (M total ell k k0 xi e : Real)
    (hk0 : 1 / 2 < k0) (hk : k0 <= k) (hell : 0 <= ell)
    (hlarge : 5 * M / 6 - e <= total + ell)
    (hcap : total + 6 * k * ell <= M)
    (hreserve : (6 * k0 - 1) * xi + (6 * k0 + 1) * e <=
      (6 * k0 - 3) * M / 6) :
    2 * ell + xi + e <= M / 6 := by
  have hmono : (6 * k0 - 1) * ell <= (6 * k - 1) * ell :=
    mul_le_mul_of_nonneg_right (by linarith) hell
  have hslot : (6 * k0 - 1) * ell <= M / 6 + e := by
    nlinarith
  have hmul : (6 * k0 - 1) * (2 * ell + xi + e) <=
      (6 * k0 - 1) * (M / 6) := by
    nlinarith
  by_contra hn
  have hg : 0 < 2 * ell + xi + e - M / 6 :=
    sub_pos.mpr (lt_of_not_ge hn)
  have hp := mul_pos (by linarith : 0 < 6 * k0 - 1) hg
  nlinarith

theorem joint_deleted_cases (M total short along ell z c xi e reflected : Real)
    (hM : 0 <= M) (hs : short <= M / 4) (hze : z <= ell)
    (hc : 1 <= c) (hxi : 0 <= xi) (he : 0 <= e)
    (hlarge : 5 * M / 6 - e <= total + ell)
    (hcap : total + c * ell <= M)
    (hjoint : 2 * ell + xi + e <= M / 6)
    (halong : max 0 along <= total - M / 4)
    (href : reflected <= max 0 (M - along + xi)) :
    (short + max 0 along + z <= 5 * M / 6 /\
      short + max 0 along + c * z <= M) \/
    (0 < along /\ reflected + short + z <= 5 * M / 6 /\
      reflected + short + c * z <= M) := by
  have hell : ell <= M / 12 := by linarith
  have hbudget : (c - 1) * ell <= M / 6 + e := by nlinarith
  have hzbudget : (c - 1) * z <= M / 6 + e :=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  by_cases hlo : short + max 0 along + z <= 5 * M / 6
  next =>
    have hcz : c * z <= c * ell :=
      mul_le_mul_of_nonneg_left hze (by linarith)
    exact Or.inl (And.intro hlo (by nlinarith))
  next =>
    have hhigh : 5 * M / 6 < short + max 0 along + z := lt_of_not_ge hlo
    have hapos : 0 < along := by
      by_contra hn
      have ha : along <= 0 := le_of_not_gt hn
      rw [max_eq_left ha] at hhigh
      linarith
    rw [max_eq_right hapos.le] at hhigh
    by_cases hr : 0 <= M - along + xi
    next =>
      rw [max_eq_right hr] at href
      exact Or.inr (And.intro hapos (And.intro (by nlinarith) (by nlinarith)))
    next =>
      rw [max_eq_left (le_of_not_ge hr)] at href
      exact Or.inr (And.intro hapos (And.intro (by nlinarith) (by nlinarith)))

theorem exists_uniform_reserve (k0 M0 : Real) (hk0 : 1 / 2 < k0) (hM0 : 0 < M0) :
    exists e xi : Real, 0 < e /\ 0 < xi /\
      forall M : Real, M0 <= M ->
        (6 * k0 - 1) * xi + (6 * k0 + 1) * e <= (6 * k0 - 3) * M / 6 := by
  let tau : Real := (2 * k0 - 1) * M0 / (48 * k0)
  have hkpos : 0 < k0 := by linarith
  have hknz : Not (k0 = 0) := ne_of_gt hkpos
  have ht : 0 < tau := by
    dsimp [tau]
    exact div_pos (mul_pos (by linarith) hM0) (by linarith)
  have heq : (6 * k0 - 1) * tau + (6 * k0 + 1) * tau =
      (6 * k0 - 3) * M0 / 12 := by
    dsimp [tau]
    field_simp
    ring
  refine Exists.intro tau (Exists.intro tau (And.intro ht (And.intro ht ?_)))
  intro M hMM
  rw [heq]
  have hscaled : (6 * k0 - 3) * M0 <= (6 * k0 - 3) * M :=
    mul_le_mul_of_nonneg_left hMM (by linarith)
  have hp : 0 < (6 * k0 - 3) * M0 := mul_pos (by linarith) hM0
  nlinarith

theorem deleted_reference_window (Z M X1 X2 ell z k k0 xi e : Real)
    (hZ : 1 < Z) (hM : 0 <= M) (hX1 : 0 < X1) (hX2 : 0 < X2)
    (hell : 0 <= ell) (_hz : 0 <= z) (hze : z <= ell)
    (hk0 : 1 / 2 < k0) (hk : k0 <= k) (hxi : 0 <= xi) (he : 0 <= e)
    (hreserve : (6 * k0 - 1) * xi + (6 * k0 + 1) * e <=
      (6 * k0 - 3) * M / 6)
    (hlarge : 5 * M / 6 - e <= Real.logb Z (X1 * X2) + ell)
    (hcap : Real.logb Z (X1 * X2) + 6 * k * ell <= M)
    (D1 D2 : Finset (Ideal O))
    (hD1 : forall I, Membership.mem D1 I -> Prime I)
    (hD2 : forall I, Membership.mem D2 I -> Prime I) :
    let short := length Z (comparisonFirst Z M / ((D1.prod (fun I => I)).absNorm : Real))
    let along := Real.logb Z (comparisonSecond Z M X1 X2 / ((D2.prod (fun I => I)).absNorm : Real))
    (short + length Z (comparisonSecond Z M X1 X2 / ((D2.prod (fun I => I)).absNorm : Real)) + z <=
        5 * M / 6 /\
      short + length Z (comparisonSecond Z M X1 X2 / ((D2.prod (fun I => I)).absNorm : Real)) +
        6 * k * z <= M) \/
    (0 < along /\ forall x : Real,
      Membership.mem (Set.Icc 0 (max 0 (M - along + xi) * Real.log Z)) x ->
        length Z (Real.exp x) + short + z <= 5 * M / 6 /\
        length Z (Real.exp x) + short + 6 * k * z <= M) := by
  classical
  dsimp only
  let total := Real.logb Z (X1 * X2)
  let short := length Z (comparisonFirst Z M / ((D1.prod (fun I => I)).absNorm : Real))
  let along := Real.logb Z (comparisonSecond Z M X1 X2 / ((D2.prod (fun I => I)).absNorm : Real))
  let reflected := max 0 (M - along + xi)
  have hj := joint_slot_budget M total ell k k0 xi e hk0 hk hell hlarge hcap hreserve
  have hlongnonneg : 0 <= total - M / 4 := by
    dsimp [total] at *
    linarith
  have hpos := comparison_positive Z M X1 X2 (zero_lt_one.trans hZ) hX1 hX2
  have hlog : Real.logb Z (comparisonSecond Z M X1 X2) = total - M / 4 := by
    rw [comparison_second_power Z M X1 X2 hZ hX1 hX2,
      Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  have hY : 1 <= comparisonSecond Z M X1 X2 := by
    rw [comparison_second_power Z M X1 X2 hZ hX1 hX2]
    exact Real.one_le_rpow hZ.le hlongnonneg
  have hn2 := product_norm_ge_one D2 hD2
  have hlongpos := div_pos hpos.2 (zero_lt_one.trans_le hn2)
  have hs := deleted_short_length Z M hZ hM D1 hD1
  have hlength : length Z (comparisonSecond Z M X1 X2 / ((D2.prod (fun I => I)).absNorm : Real)) =
      max 0 along :=
    CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z _ hZ hlongpos
  have halong : max 0 along <= total - M / 4 := by
    rw [<- hlength, <- hlog]
    exact Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (le_max_left 1 _))
      (max_le hY (div_le_self hpos.2.le hn2))
  have hh := joint_deleted_cases M total short along ell z (6 * k) xi e reflected
    hM hs hze (by linarith) hxi he hlarge hcap hj halong le_rfl
  rw [hlength]
  cases hh with
  | inl h =>
    exact Or.inl h
  | inr h =>
    refine Or.inr (And.intro h.1 ?_)
    intro x hx
    have hw := CenteredMomentEnergyReferenceLowWindow.reflection_window_length
      Z reflected x hZ (le_max_left _ _) hx
    exact And.intro (by linarith [hw.1]) (by linarith [hw.1])


theorem live_profiles_reference_window {iota : Type*} [Fintype iota]
    (a b M0 k0 : Real) (hM0 : 0 < M0) (hk0 : 1 / 2 < k0) :
    exists e xi Z0 : Real, 0 < e /\ 0 < xi /\ 1 < Z0 /\
      forall Z M : Real, Z0 <= Z -> M0 <= M ->
      forall (eta : Character) (m A u : O) (p : Profiles a b)
        (S : iota -> Finset (Ideal O)) (coeff : iota -> Ideal O -> Complex)
        (P : iota -> Real) (t X1 X2 ell z k : Real),
        0 < X1 -> 0 < X2 -> 0 <= ell -> 0 <= z -> z <= ell -> k0 <= k ->
        5 * M / 6 <= length Z X1 + length Z X2 + ell ->
        length Z X1 + length Z X2 + 6 * k * ell <= M ->
      forall (D1 D2 : Finset (Ideal O)),
        (forall I, Membership.mem D1 I -> Prime I) ->
        (forall I, Membership.mem D2 I -> Prime I) ->
      positiveSlotRow eta m A u (p.profile 0) (p.profile 1) S coeff P t X1 X2 = 0 \/
      (let short := length Z (comparisonFirst Z M / ((D1.prod (fun I => I)).absNorm : Real))
       let along := Real.logb Z (comparisonSecond Z M X1 X2 / ((D2.prod (fun I => I)).absNorm : Real))
       (short + length Z (comparisonSecond Z M X1 X2 / ((D2.prod (fun I => I)).absNorm : Real)) + z <=
          5 * M / 6 /\
         short + length Z (comparisonSecond Z M X1 X2 / ((D2.prod (fun I => I)).absNorm : Real)) +
          6 * k * z <= M) \/
       (0 < along /\ forall x : Real,
         Membership.mem (Set.Icc 0 (max 0 (M - along + xi) * Real.log Z)) x ->
           length Z (Real.exp x) + short + z <= 5 * M / 6 /\
           length Z (Real.exp x) + short + 6 * k * z <= M)) := by
  classical
  let hres := exists_uniform_reserve k0 M0 hk0 hM0
  let e := Classical.choose hres
  let hres2 := Classical.choose_spec hres
  let xi := Classical.choose hres2
  have hdata := Classical.choose_spec hres2
  let hdef := @CenteredMomentEnergyLiveClippingDefect.profiles_uniform_defect
    iota inferInstance a b e hdata.1
  let Z0 := Classical.choose hdef
  have hzdata := Classical.choose_spec hdef
  refine Exists.intro e (Exists.intro xi (Exists.intro Z0
    (And.intro hdata.1 (And.intro hdata.2.1 (And.intro hzdata.1 ?_)))))
  intro Z M hZZ hMM eta m A u p S coeff P t X1 X2 ell z k
    hX1 hX2 hell hz hze hk hlarge hcap D1 D2 hD1 hD2
  by_cases hrow :
      positiveSlotRow eta m A u (p.profile 0) (p.profile 1) S coeff P t X1 X2 = 0
  next =>
    exact Or.inl hrow
  next =>
    apply Or.inr
    have hZ := hzdata.1.trans_le hZZ
    have hclip := hzdata.2 Z hZZ eta m A u p S coeff P t X1 X2 hX1 hX2 hrow
    have hraw := CenteredMomentEnergyLiveClippingDefect.raw_gates_of_defect
      Z M X1 X2 ell k e hZ hX1 hX2 hclip hlarge hcap
    have hrawcap : Real.logb Z (X1 * X2) + 6 * k * ell <= M := by
      nlinarith [hraw.2]
    exact deleted_reference_window Z M X1 X2 ell z k k0 xi e
      hZ (hM0.le.trans hMM) hX1 hX2 hell hz hze hk0 hk hdata.2.1.le hdata.1.le
      (hdata.2.2 M hMM) hraw.1 hrawcap D1 D2 hD1 hD2


theorem actual_deleted_gates {Z Bmask bPhi : Real}
    (s : CenteredMomentEnergyState.NaturalState Z Bmask bPhi)
    (hZ : 1 < Z) (hB : 0 <= Bmask) (Mcap L X1 X2 ell z k k0 xi e : Real)
    (hwidth : s.width <= Mcap) (hL : Mcap + Bmask + xi <= L)
    (hX1 : 0 < X1) (hX2 : 0 < X2) (hell : 0 <= ell)
    (hz : 0 <= z) (hze : z <= ell) (hk0 : 1 / 2 < k0) (hk : k0 <= k)
    (hxi : 0 <= xi) (he : 0 <= e)
    (hreserve : (6 * k0 - 1) * xi + (6 * k0 + 1) * e <=
      (6 * k0 - 3) * s.width / 6)
    (hlarge : 5 * s.width / 6 - e <= Real.logb Z (X1 * X2) + ell)
    (hcap : Real.logb Z (X1 * X2) + 6 * k * ell <= s.width)
    (D1 D2 : Finset (Ideal O))
    (hD1 : Membership.mem (CompletedGauss.primeSupport s.puncture).powerset D1)
    (hD2 : Membership.mem (CompletedGauss.primeSupport s.puncture).powerset D2) :
    let short := s.width / 4 - Real.logb Z ((D1.prod (fun I => I)).absNorm : Real)
    let along := Real.logb Z (X1 * X2) - s.width / 4 -
      Real.logb Z ((D2.prod (fun I => I)).absNorm : Real)
    Z ^ short = comparisonFirst Z s.width / ((D1.prod (fun I => I)).absNorm : Real) /\
    Z ^ along = comparisonSecond Z s.width X1 X2 / ((D2.prod (fun I => I)).absNorm : Real) /\
    short <= s.width / 4 /\ short <= L /\ along <= L /\
    s.width <= (Mcap + Bmask) + along /\ max 0 (s.width - along + xi) <= L /\
    ((length Z (Z ^ short) + length Z (Z ^ along) + z <= 5 * s.width / 6 /\
        length Z (Z ^ short) + length Z (Z ^ along) + 6 * k * z <= s.width) \/
      (max 0 (s.width - along + xi) + length Z (Z ^ short) + z <= 5 * s.width / 6 /\
        max 0 (s.width - along + xi) + length Z (Z ^ short) + 6 * k * z <= s.width)) := by
  classical
  have hbase : 0 < Z := zero_lt_one.trans hZ
  have hj := joint_slot_budget s.width (Real.logb Z (X1 * X2)) ell k k0 xi e
    hk0 hk hell hlarge hcap hreserve
  have hlongnonneg : 0 <= Real.logb Z (X1 * X2) - s.width / 4 := by
    linarith [s.width_nonneg]
  have hy1 : 1 <= comparisonFirst Z s.width :=
    Real.one_le_rpow hZ.le (by linarith [s.width_nonneg])
  have hy2 : 1 <= comparisonSecond Z s.width X1 X2 := by
    rw [comparison_second_power Z s.width X1 X2 hZ hX1 hX2]
    exact Real.one_le_rpow hZ.le hlongnonneg
  have hf : Real.logb Z (comparisonFirst Z s.width) = s.width / 4 :=
    Real.logb_rpow hbase hZ.ne'
  have hl : Real.logb Z (comparisonSecond Z s.width X1 X2) =
      Real.logb Z (X1 * X2) - s.width / 4 := by
    rw [comparison_second_power Z s.width X1 X2 hZ hX1 hX2,
      Real.logb_rpow hbase hZ.ne']
  have hd1 := CenteredMomentEnergyReferenceDivisors.divisor_reflection_range
    s hZ Mcap _ hwidth hy1 D1 hD1
  have hd2 := CenteredMomentEnergyReferenceDivisors.divisor_reflection_range
    s hZ Mcap _ hwidth hy2 D2 hD2
  dsimp only at hd1 hd2
  rw [hf] at hd1
  rw [hl] at hd2
  have hn1 := (CenteredMomentEnergyReferenceDivisors.divisor_norm s D1 hD1).1
  have hn2 := (CenteredMomentEnergyReferenceDivisors.divisor_norm s D2 hD2).1
  have hlog1 := Real.logb_nonneg hZ hn1
  have hlog2 := Real.logb_nonneg hZ hn2
  have hMcap : 0 <= Mcap := s.width_nonneg.trans hwidth
  have hLc : 0 <= L := by linarith
  have hslot : 0 <= 6 * k * ell := mul_nonneg (by linarith) hell
  dsimp only
  refine And.intro hd1.2.2 (And.intro hd2.2.2
    (And.intro (by linarith) (And.intro (by linarith [s.width_nonneg])
      (And.intro (by linarith) (And.intro hd2.2.1
        (And.intro (max_le hLc (by linarith [hd2.1])) ?_))))))
  have hp1 : forall I, Membership.mem D1 I -> Prime I := by
    intro I hI
    exact CenteredMomentNaturalRowSource.support_prime s.puncture I
      (Finset.mem_powerset.mp hD1 hI)
  have hp2 : forall I, Membership.mem D2 I -> Prime I := by
    intro I hI
    exact CenteredMomentNaturalRowSource.support_prime s.puncture I
      (Finset.mem_powerset.mp hD2 hI)
  let along := Real.logb Z (X1 * X2) - s.width / 4 -
    Real.logb Z ((D2.prod (fun I => I)).absNorm : Real)
  have halong : Real.logb Z (comparisonSecond Z s.width X1 X2 /
      ((D2.prod (fun I => I)).absNorm : Real)) = along := by
    rw [<- hd2.2.2]
    exact Real.logb_rpow hbase hZ.ne'
  have hw := deleted_reference_window Z s.width X1 X2 ell z k k0 xi e
    hZ s.width_nonneg hX1 hX2 hell hz hze hk0 hk hxi he hreserve hlarge hcap D1 D2 hp1 hp2
  dsimp only at hw
  rw [halong, <- hd1.2.2, <- hd2.2.2] at hw
  cases hw with
  | inl h =>
    exact Or.inl h
  | inr h =>
    apply Or.inr
    let reflected := max 0 (s.width - along + xi)
    have hr : 0 <= reflected := le_max_left _ _
    have hx : Membership.mem (Set.Icc 0 (reflected * Real.log Z))
        (reflected * Real.log Z) :=
      And.intro (mul_nonneg hr (Real.log_nonneg hZ.le)) le_rfl
    have hc := h.2 (reflected * Real.log Z) hx
    have hex : Real.exp (reflected * Real.log Z) = Z ^ reflected := by
      rw [Real.rpow_def_of_pos hbase]
      congr 1
      ring
    have hp : 1 <= Z ^ reflected := Real.one_le_rpow hZ.le hr
    have hlen : length Z (Real.exp (reflected * Real.log Z)) = reflected := by
      rw [hex, length, max_eq_right hp, Real.logb_rpow hbase hZ.ne']
    simpa only [hlen] using hc

end OAI.SevenEighths.KappaHalfReflection
