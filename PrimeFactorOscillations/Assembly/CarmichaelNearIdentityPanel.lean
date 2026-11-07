/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelFiniteRealPacket
import PrimeFactorOscillations.Mathlib.Analysis.Complex.NearIdentityResiduePanel

/-!
# Effective finite panels of near-identity zeta residues

The complete positive reference term is retained in the signed residue.
Every parameter orbit is injective, so the global zero budget controls the
number of contaminated parameters without a multiplicity cap.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CarmichaelWeightedSignal
open Complex DirichletCompensatedProbe

theorem near_identity_point_eq_powerMap (j : Nat) (rho : Complex) :
    nearIdentityPoint j rho = powerMap (rationalPowerDegree (j + 1) 1) rho := by
  have hn : Not ((j : Real) + 1 = 0) := by positivity
  have hD := rationalPowerDegree_mul_den (j + 1) 1 (by omega)
  have hT := nearIdentityFraction_mul_den j
  have hScaled := congrArg (fun x : Real => nearIdentityFraction j * x) hD
  push_cast at hScaled hT
  have hProduct : (nearIdentityFraction j * rationalPowerDegree (j + 1) 1 - 1) *
      ((j : Real) + 1) = 0 := by nlinarith only [hScaled, hT]
  have hCoef : nearIdentityFraction j * rationalPowerDegree (j + 1) 1 = 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hProduct).resolve_right hn)
  have hCoefC : (nearIdentityFraction j : Complex) *
      (rationalPowerDegree (j + 1) 1 : Complex) = 1 := by exact_mod_cast hCoef
  have hd := rationalPowerDegree_gt_one (j + 1) 1 (by omega) (by omega)
  have hdC : Not ((rationalPowerDegree (j + 1) 1 : Complex) = 0) := by
    exact_mod_cast (show Not (rationalPowerDegree (j + 1) 1 = 0) by linarith only [hd])
  unfold powerMap
  apply (eq_div_iff hdC).mpr
  unfold nearIdentityPoint
  linear_combination (rho - 1) * hCoefC

def nearIdentityReferenceOrder (S : Finset Complex) (j : Nat) : Nat :=
  S.sum (fun rho => analyticOrderNatAt riemannZeta (nearIdentityPoint j rho))

def nearIdentityReferenceWeight (S : Finset Complex) (j : Nat) : Real :=
  S.sum (fun rho => (analyticOrderNatAt riemannZeta (nearIdentityPoint j rho) : Real) *
    (Inv.inv (nearIdentityPoint j rho)).re)

private theorem near_reference_strip (j : Nat) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) :
    And (0 < (nearIdentityPoint j rho).re) ((nearIdentityPoint j rho).re < 1) := by
  have h := nearIdentityPoint_bounds j rho rho.re (abs rho.im)
    le_rfl hRe.2 (abs_nonneg _) le_rfl
  exact And.intro (lt_of_lt_of_le hRe.1 h.1) h.2.1

/-- Every injective parameter orbit spends one global inverse-zero budget. -/
theorem near_identity_orbit_mass_le (T : Finset Nat) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) :
    T.sum (fun j => (analyticOrderNatAt riemannZeta (nearIdentityPoint j rho) : Real) *
      (Inv.inv (nearIdentityPoint j rho)).re) <= (1 / 20 : Real) := by
  classical
  have hNotOne : Not (rho = 1) := by
    intro h
    have hr := congrArg Complex.re h
    change rho.re = 1 at hr
    linarith only [hRe.2, hr]
  have hCap := zeta_finite_inverse_mass_le (T.image (fun j => nearIdentityPoint j rho)) (by
    intro w hw
    cases Finset.mem_image.mp hw with
    | intro j h =>
      rw [<- h.2]
      exact near_reference_strip j rho hRe)
  rw [Finset.sum_image (fun a _ b _ h => nearIdentityPoint_parameter_injective rho hNotOne h)] at hCap
  exact hCap

/-- Sum in the parameter direction before spending the budget at each target point. -/
theorem near_identity_panel_weight_budget (S : Finset Complex) (T : Finset Nat)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1)) :
    T.sum (nearIdentityReferenceWeight S) <= (S.card : Real) / 20 := by
  unfold nearIdentityReferenceWeight
  rw [Finset.sum_comm]
  calc
    _ <= S.sum (fun _ => (1 / 20 : Real)) := by
      apply Finset.sum_le_sum
      intro rho hrho
      exact near_identity_orbit_mass_le T rho (hStrip rho hrho)
    _ = _ := by simp; ring

theorem near_identity_weight_lower (S : Finset Complex) (j : Nat)
    (s : Real) (hs : 0 < s) (H : Real) (hH : 0 <= H)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1))
    (hLower : forall rho : Complex, Membership.mem S rho -> s <= rho.re)
    (hHeight : forall rho : Complex, Membership.mem S rho -> abs rho.im <= H) :
    (s / (1 + H ^ 2)) * (nearIdentityReferenceOrder S j : Real) <=
      nearIdentityReferenceWeight S j := by
  unfold nearIdentityReferenceOrder nearIdentityReferenceWeight
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rho hrho
  have h := nearIdentityPoint_inverse_lower j rho s hs (hLower rho hrho)
    (hStrip rho hrho).2 H hH (hHeight rho hrho)
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (analyticOrderNatAt riemannZeta (nearIdentityPoint j rho)))

/-- The count bound holds on every finite parameter set, however late it begins. -/
theorem near_identity_bad_parameter_bound (S : Finset Complex) (T : Finset Nat)
    (s : Real) (hs : 0 < s) (H : Real) (hH : 0 <= H)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1))
    (hLower : forall rho : Complex, Membership.mem S rho -> s <= rho.re)
    (hHeight : forall rho : Complex, Membership.mem S rho -> abs rho.im <= H) :
    (s / (1 + H ^ 2)) * ((T.filter (fun j => 0 < nearIdentityReferenceOrder S j)).card : Real) <=
      (S.card : Real) / 20 := by
  classical
  have hLambda : 0 < s / (1 + H ^ 2) := div_pos hs (by nlinarith only [sq_nonneg H])
  have hFloor (j : Nat) := near_identity_weight_lower S j s hs H hH hStrip hLower hHeight
  have hNonneg (j : Nat) : 0 <= nearIdentityReferenceWeight S j :=
    (mul_nonneg hLambda.le (Nat.cast_nonneg _)).trans (hFloor j)
  let U := T.filter (fun j => 0 < nearIdentityReferenceOrder S j)
  have hCount : (s / (1 + H ^ 2)) * (U.card : Real) <=
      U.sum (nearIdentityReferenceWeight S) := by
    calc
      _ = U.sum (fun _ => s / (1 + H ^ 2)) := by simp; ring
      _ <= _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hjBad := (Finset.mem_filter.mp hj).2
        have hOne : (1 : Real) <= nearIdentityReferenceOrder S j := by exact_mod_cast hjBad
        have hWeighted := mul_le_mul_of_nonneg_left hOne hLambda.le
        nlinarith only [hWeighted, hFloor j]
  have hSubset : U.sum (nearIdentityReferenceWeight S) <= T.sum (nearIdentityReferenceWeight S) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro j _ _
    exact hNonneg j
  exact hCount.trans (hSubset.trans (near_identity_panel_weight_budget S T hStrip))

/-- Every sufficiently large finite parameter set contains a completely clean row. -/
theorem near_identity_exists_clean (S : Finset Complex) (T : Finset Nat)
    (s : Real) (hs : 0 < s) (H : Real) (hH : 0 <= H)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1))
    (hLower : forall rho : Complex, Membership.mem S rho -> s <= rho.re)
    (hHeight : forall rho : Complex, Membership.mem S rho -> abs rho.im <= H)
    (hSize : (S.card : Real) / 20 < (s / (1 + H ^ 2)) * (T.card : Real)) :
    Exists (fun j : Nat => And (Membership.mem T j) (nearIdentityReferenceOrder S j = 0)) := by
  classical
  by_contra h
  have hBad : forall j : Nat, Membership.mem T j -> 0 < nearIdentityReferenceOrder S j := by
    intro j hj
    by_contra hNot
    have hZero : nearIdentityReferenceOrder S j = 0 := by omega
    exact h (Exists.intro j (And.intro hj hZero))
  have hFilter : T.filter (fun j => 0 < nearIdentityReferenceOrder S j) = T :=
    Finset.filter_eq_self.mpr hBad
  have hCount := near_identity_bad_parameter_bound S T s hs H hH hStrip hLower hHeight
  rw [hFilter] at hCount
  linarith only [hCount, hSize]

/-- The signed original real residue is bounded below by minus the target total. -/
theorem near_identity_residue_target_lower (S : Finset Complex) (j : Nat)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1)) :
    -(zetaPacketTargetOrder S : Real) <= zetaPacketResidue S (j + 1) 1 := by
  unfold zetaPacketTargetOrder zetaPacketResidue
  rw [Nat.cast_sum]
  calc
    _ = S.sum (fun rho => -(analyticOrderNatAt riemannZeta rho : Real)) := by
      rw [Finset.sum_neg_distrib]
    _ <= _ := by
      apply Finset.sum_le_sum
      intro rho hrho
      have h := realPowerResidueCode_target_lower (rationalPowerDegree (j + 1) 1)
        (rationalPowerDegree_gt_one (j + 1) 1 (by omega) (by omega)) rho (hStrip rho hrho).1.le
        (analyticOrderNatAt riemannZeta rho : Int)
        (zetaRationalReferenceOrder (j + 1) 1 rho : Int) (by positivity)
      simpa [zetaCanonicalPowerResidue, realPowerResidueCode, zetaRationalReferenceOrder] using h

theorem near_identity_clean_residue (S : Finset Complex) (j : Nat)
    (hClean : nearIdentityReferenceOrder S j = 0) :
    zetaPacketResidue S (j + 1) 1 = -(zetaPacketTargetOrder S : Real) := by
  have hEach := Finset.sum_eq_zero_iff.mp hClean
  unfold zetaPacketResidue zetaPacketTargetOrder
  rw [Nat.cast_sum, <- Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hb : analyticOrderNatAt riemannZeta (nearIdentityPoint j rho) = 0 := hEach rho hrho
  rw [near_identity_point_eq_powerMap] at hb
  simp [zetaCanonicalPowerResidue, hb]


def nearIdentityPanelDecode (T : Finset Nat) (hT : T.Nonempty) (y : Nat -> Real) : Int :=
  T.sup' hT (fun j => Int.floor (-y j + 1 / 2))

/-- Every noisy row gives an integer lower estimate for the target total. -/
theorem near_identity_floor_le_target (S : Finset Complex) (j : Nat)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1))
    (y : Real) (hNoise : abs (zetaPacketResidue S (j + 1) 1 - y) < 1 / 2) :
    Int.floor (-y + 1 / 2) <= (zetaPacketTargetOrder S : Int) := by
  have hLower := near_identity_residue_target_lower S j hStrip
  have he := abs_lt.mp hNoise
  have hX : -y + 1 / 2 < (zetaPacketTargetOrder S : Real) + 1 := by
    linarith only [hLower, he.2]
  have hFloor := lt_of_le_of_lt (Int.floor_le (-y + 1 / 2)) hX
  have hInt : Int.floor (-y + 1 / 2) < (zetaPacketTargetOrder S : Int) + 1 := by
    exact_mod_cast hFloor
  omega

theorem near_identity_clean_floor (S : Finset Complex) (j : Nat)
    (hClean : nearIdentityReferenceOrder S j = 0) (y : Real)
    (hNoise : abs (zetaPacketResidue S (j + 1) 1 - y) < 1 / 2) :
    Int.floor (-y + 1 / 2) = (zetaPacketTargetOrder S : Int) := by
  rw [near_identity_clean_residue S j hClean] at hNoise
  have he := abs_lt.mp hNoise
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor <;> linarith only [he.1, he.2]

/-- A finite maximum recovers the whole target total at unscaled half-unit accuracy. -/
theorem near_identity_panel_decode (S : Finset Complex) (T : Finset Nat) (hT : T.Nonempty)
    (s : Real) (hs : 0 < s) (H : Real) (hH : 0 <= H)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1))
    (hLower : forall rho : Complex, Membership.mem S rho -> s <= rho.re)
    (hHeight : forall rho : Complex, Membership.mem S rho -> abs rho.im <= H)
    (hSize : (S.card : Real) / 20 < (s / (1 + H ^ 2)) * (T.card : Real))
    (y : Nat -> Real)
    (hNoise : forall j : Nat, Membership.mem T j ->
      abs (zetaPacketResidue S (j + 1) 1 - y j) < 1 / 2) :
    nearIdentityPanelDecode T hT y = (zetaPacketTargetOrder S : Int) := by
  unfold nearIdentityPanelDecode
  apply le_antisymm
  . exact Finset.sup'_le hT _ (fun j hj => near_identity_floor_le_target S j hStrip (y j) (hNoise j hj))
  . cases near_identity_exists_clean S T s hs H hH hStrip hLower hHeight hSize with
    | intro j hj =>
      have hEq := near_identity_clean_floor S j hj.2 (y j) (hNoise j hj.1)
      rw [<- hEq]
      exact Finset.le_sup' (fun i : Nat => Int.floor (-y i + 1 / 2)) hj.1

def nearIdentityBlockDecode (base extra : Nat) (y : Nat -> Real) : Int :=
  nearIdentityPanelDecode (Finset.Ico base (base + extra + 1))
    (Exists.intro base (Finset.mem_Ico.mpr (And.intro le_rfl (by omega)))) y

/-- The block has exactly extra+1 observations and may begin arbitrarily late. -/
theorem near_identity_block_decode (S : Finset Complex) (base extra : Nat)
    (s : Real) (hs : 0 < s) (H : Real) (hH : 0 <= H)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1))
    (hLower : forall rho : Complex, Membership.mem S rho -> s <= rho.re)
    (hHeight : forall rho : Complex, Membership.mem S rho -> abs rho.im <= H)
    (hSize : (S.card : Real) / 20 < (s / (1 + H ^ 2)) * ((extra + 1 : Nat) : Real))
    (y : Nat -> Real)
    (hNoise : forall j : Nat, Membership.mem (Finset.Ico base (base + extra + 1)) j ->
      abs (zetaPacketResidue S (j + 1) 1 - y j) < 1 / 2) :
    nearIdentityBlockDecode base extra y = (zetaPacketTargetOrder S : Int) := by
  unfold nearIdentityBlockDecode
  apply near_identity_panel_decode S _ _ s hs H hH hStrip hLower hHeight _ y hNoise
  have hCard : (Finset.Ico base (base + extra + 1)).card = extra + 1 := by
    rw [Nat.card_Ico]
    omega
  simpa only [hCard] using hSize

/-- All powers in a late panel are uniformly close to one. -/
theorem near_identity_degree_upper (base j : Nat) (hBase : base <= j) :
    rationalPowerDegree (j + 1) 1 <= 1 + (1 : Real) / ((base + 1 : Nat) : Real) := by
  have hb : (0 : Real) < (base : Real) + 1 := by positivity
  have hj : (0 : Real) < (j : Real) + 1 := by positivity
  have hOrder : (base : Real) + 1 <= (j : Real) + 1 := by exact_mod_cast Nat.add_le_add_right hBase 1
  have hBaseIdentity : (1 / ((base : Real) + 1)) * ((base : Real) + 1) = (1 : Real) := by
    field_simp [hb.ne']
  have hJIdentity : (1 / ((j : Real) + 1)) * ((j : Real) + 1) = (1 : Real) := by
    field_simp [hj.ne']
  have hMul : (1 / ((j : Real) + 1)) * ((base : Real) + 1) <= (1 : Real) := by
    calc
      _ <= (1 / ((j : Real) + 1)) * ((j : Real) + 1) :=
        mul_le_mul_of_nonneg_left hOrder (div_pos zero_lt_one hj).le
      _ = 1 := hJIdentity
  have hInv : (1 / ((j : Real) + 1)) <= 1 / ((base : Real) + 1) := by
    by_contra h
    have hProduct := mul_pos (sub_pos.mpr (lt_of_not_ge h)) hb
    nlinarith only [hProduct, hMul, hBaseIdentity]
  simp only [rationalPowerDegree, Nat.cast_one, Nat.cast_add]
  linarith only [hInv]

def nearIdentityPanelObservation (G : Complex -> Complex) (S : Finset Complex)
    (j : Nat) (t : Complex) : Real :=
  S.sum (fun rho => (t * affinePowerReadout (zetaMultiplicityReadout G)
    (rationalPowerDegree (j + 1) 1) (rho + t)).re)

/-- Fixed finite panels of actual analytic observations eventually decode exactly. -/
theorem near_identity_panel_eventual_decode (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {z : Complex | And (0 < z.re) (z.re < 1)})
    (S : Finset Complex) (T : Finset Nat) (hT : T.Nonempty)
    (s : Real) (hs : 0 < s) (H : Real) (hH : 0 <= H)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1))
    (hLower : forall rho : Complex, Membership.mem S rho -> s <= rho.re)
    (hHeight : forall rho : Complex, Membership.mem S rho -> abs rho.im <= H)
    (hSize : (S.card : Real) / 20 < (s / (1 + H ^ 2)) * (T.card : Real)) :
    Filter.Eventually (fun t : Complex =>
      nearIdentityPanelDecode T hT (fun j => nearIdentityPanelObservation G S j t) =
        (zetaPacketTargetOrder S : Int)) (nhdsWithin 0 (Set.compl {0})) := by
  have hLimit (j : Nat) : Filter.Tendsto (nearIdentityPanelObservation G S j)
      (nhdsWithin 0 (Set.compl {0})) (nhds (zetaPacketResidue S (j + 1) 1)) := by
    exact zeta_packet_common_increment_limit G hG S (j + 1) 1 (by omega) (by omega) hStrip
  have hEach (j : Nat) (_hj : Membership.mem T j) :
      Filter.Eventually (fun t : Complex =>
        abs (zetaPacketResidue S (j + 1) 1 - nearIdentityPanelObservation G S j t) < 1 / 2)
        (nhdsWithin 0 (Set.compl {0})) := by
    have hError : Filter.Tendsto (fun t : Complex =>
        abs (zetaPacketResidue S (j + 1) 1 - nearIdentityPanelObservation G S j t))
        (nhdsWithin 0 (Set.compl {0})) (nhds (0 : Real)) := by
      have hc : Filter.Tendsto (fun _ : Complex => zetaPacketResidue S (j + 1) 1)
          (nhdsWithin 0 (Set.compl {0})) (nhds (zetaPacketResidue S (j + 1) 1)) := tendsto_const_nhds
      have h := (hc.sub (hLimit j)).abs
      simpa only [sub_self, abs_zero] using h
    exact (tendsto_order.mp hError).2 (1 / 2) (by norm_num)
  have hUniform := (Finset.eventually_all T).mpr hEach
  filter_upwards [hUniform] with t ht
  exact near_identity_panel_decode S T hT s hs H hH hStrip hLower hHeight hSize
    (fun j => nearIdentityPanelObservation G S j t) ht


def nearIdentityPanelExtra (S : Finset Complex) (s H : Real) : Nat :=
  Nat.floor ((S.card : Real) * (1 + H ^ 2) / (20 * s))

theorem near_identity_explicit_width (S : Finset Complex) (s : Real) (hs : 0 < s) (H : Real) :
    (S.card : Real) / 20 <
      (s / (1 + H ^ 2)) * ((nearIdentityPanelExtra S s H + 1 : Nat) : Real) := by
  let r : Real := (S.card : Real) * (1 + H ^ 2) / (20 * s)
  have hDen : 0 < 1 + H ^ 2 := by nlinarith only [sq_nonneg H]
  have hLambda : 0 < s / (1 + H ^ 2) := div_pos hs hDen
  have hCancel : r * (s / (1 + H ^ 2)) = (S.card : Real) / 20 := by
    dsimp only [r]
    field_simp [hs.ne', hDen.ne']
    <;> ring
  have hFloor := Nat.lt_floor_add_one r
  have hScaled := mul_lt_mul_of_pos_right hFloor hLambda
  rw [hCancel] at hScaled
  simpa only [nearIdentityPanelExtra, r, Nat.cast_add, Nat.cast_one, mul_comm] using hScaled

/-- The floor formula gives a complete base-independent finite observation budget. -/
theorem near_identity_explicit_block_decode (S : Finset Complex) (base : Nat)
    (s : Real) (hs : 0 < s) (H : Real) (hH : 0 <= H)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1))
    (hLower : forall rho : Complex, Membership.mem S rho -> s <= rho.re)
    (hHeight : forall rho : Complex, Membership.mem S rho -> abs rho.im <= H)
    (y : Nat -> Real)
    (hNoise : forall j : Nat,
      Membership.mem (Finset.Ico base (base + nearIdentityPanelExtra S s H + 1)) j ->
        abs (zetaPacketResidue S (j + 1) 1 - y j) < 1 / 2) :
    nearIdentityBlockDecode base (nearIdentityPanelExtra S s H) y =
      (zetaPacketTargetOrder S : Int) :=
  near_identity_block_decode S base (nearIdentityPanelExtra S s H) s hs H hH
    hStrip hLower hHeight (near_identity_explicit_width S s hs H) y hNoise

/-- Across all natural parameters only finitely many rows can be contaminated. -/
theorem near_identity_bad_set_finite (S : Finset Complex)
    (s : Real) (hs : 0 < s) (H : Real) (hH : 0 <= H)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1))
    (hLower : forall rho : Complex, Membership.mem S rho -> s <= rho.re)
    (hHeight : forall rho : Complex, Membership.mem S rho -> abs rho.im <= H) :
    Set.Finite {j : Nat | 0 < nearIdentityReferenceOrder S j} := by
  classical
  by_contra h
  have hInfinite : Set.Infinite {j : Nat | 0 < nearIdentityReferenceOrder S j} := h
  cases hInfinite.exists_subset_card_eq (nearIdentityPanelExtra S s H + 1) with
  | intro T hT =>
    have hAll : forall j : Nat, Membership.mem T j -> 0 < nearIdentityReferenceOrder S j := by
      intro j hj
      exact hT.1 hj
    have hFilter : T.filter (fun j => 0 < nearIdentityReferenceOrder S j) = T :=
      Finset.filter_eq_self.mpr hAll
    have hCount := near_identity_bad_parameter_bound S T s hs H hH hStrip hLower hHeight
    rw [hFilter, hT.2] at hCount
    have hWidth := near_identity_explicit_width S s hs H
    linarith only [hCount, hWidth]

end PrimeFactorOscillations.CarmichaelWeightedSignal
