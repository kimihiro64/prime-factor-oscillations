/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPowerEnergy
import PrimeFactorOscillations.Assembly.CarmichaelRationalSingleRealZeta
import PrimeFactorOscillations.Helpers.NicolasFiniteZeroMass

/-!
# One real coordinate detects an arbitrary finite packet

The complete signed level is retained. The injective affine image spends one
global zero budget, including all multiplicities and overlapping zero locations.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CarmichaelWeightedSignal
open Complex DirichletCompensatedProbe

def zetaPacketTargetOrder (S : Finset Complex) : Nat :=
  S.sum (analyticOrderNatAt riemannZeta)

def zetaPacketReferenceOrder (S : Finset Complex) (n k : Nat) : Nat :=
  S.sum (zetaRationalReferenceOrder n k)

def zetaPacketResidue (S : Finset Complex) (n k : Nat) : Real :=
  S.sum (fun rho => (zetaCanonicalPowerResidue (rationalPowerDegree n k) rho).re)

def zetaPacketDefect (S : Finset Complex) (n k : Nat) : Real :=
  S.sum (fun rho => ((n : Real) * realPowerResidueDefect (rationalPowerDegree n k) rho) *
    (zetaRationalReferenceOrder n k rho : Real))

def zetaPacketLevel (S : Finset Complex) (n k : Nat) : Int :=
  ((n + k : Nat) : Int) * (zetaPacketReferenceOrder S n k : Int) -
    (n : Int) * (zetaPacketTargetOrder S : Int)

def zetaPacketRadius (n k : Nat) (H : Real) : Real :=
  min (1 - (k : Real) / 20)
    ((n : Real) * realResidueHeightScale (rationalPowerDegree n k) H) / n

private theorem packet_reference_strip (n k : Nat) (hn : 0 < n) (hk : 0 < k)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1)) :
    And (0 < (powerMap (rationalPowerDegree n k) rho).re)
      ((powerMap (rationalPowerDegree n k) rho).re < 1) := by
  have hd := rationalPowerDegree_gt_one n k hn hk
  have he := powerMap_real_identity (rationalPowerDegree n k) (by linarith) rho
  constructor <;> nlinarith [hRe.1, hRe.2]

/-- The exact signed aggregate; no term is replaced by its magnitude. -/
theorem zeta_packet_signed_identity (S : Finset Complex) (n k : Nat) (hn : 0 < n) :
    (n : Real) * zetaPacketResidue S n k =
      (zetaPacketLevel S n k : Real) - zetaPacketDefect S n k := by
  unfold zetaPacketResidue zetaPacketDefect zetaPacketLevel
    zetaPacketReferenceOrder zetaPacketTargetOrder
  rw [Finset.mul_sum]
  calc
    _ = S.sum (fun rho => (n + k : Nat) * (zetaRationalReferenceOrder n k rho : Real) -
        (n : Real) * (analyticOrderNatAt riemannZeta rho : Real) -
        ((n : Real) * realPowerResidueDefect (rationalPowerDegree n k) rho) *
          (zetaRationalReferenceOrder n k rho : Real)) := by
      apply Finset.sum_congr rfl
      intro rho _
      have h := rationalPowerResidueCode_scaled_real n k hn rho
        (analyticOrderNatAt riemannZeta rho : Int) (zetaRationalReferenceOrder n k rho : Int)
      simpa [zetaCanonicalPowerResidue, realPowerResidueCode, zetaRationalReferenceOrder] using h
    _ = _ := by
      simp only [Finset.sum_sub_distrib, <- Finset.mul_sum]
      push_cast
      ring

/-- The same one twentieth is shared by the entire injective affine image. -/
theorem zeta_packet_defect_budget (S : Finset Complex) (n k : Nat)
    (hn : 0 < n) (hk : 0 < k)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1)) :
    And (0 <= zetaPacketDefect S n k) (zetaPacketDefect S n k <= (k : Real) / 20) := by
  classical
  have hd := rationalPowerDegree_gt_one n k hn hk
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  constructor
  . apply Finset.sum_nonneg
    intro rho hrho
    exact mul_nonneg (mul_pos hnR (realPowerResidueDefect_pos _ hd rho
      (hStrip rho hrho).1.le)).le (Nat.cast_nonneg _)
  . have hCap := zeta_finite_inverse_mass_le (S.image (powerMap (rationalPowerDegree n k))) (by
      intro w hw
      obtain hPre := Finset.mem_image.mp hw
      cases hPre with
      | intro rho h =>
        rw [<- h.2]
        exact packet_reference_strip n k hn hk rho (hStrip rho h.1))
    rw [Finset.sum_image (fun a _ b _ h => powerMap_injective _ (by linarith) h)] at hCap
    calc
      _ = (k : Real) * S.sum (fun rho =>
          (analyticOrderNatAt riemannZeta (powerMap (rationalPowerDegree n k) rho) : Real) *
            (Inv.inv (powerMap (rationalPowerDegree n k) rho)).re) := by
        unfold zetaPacketDefect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro rho hrho
        rw [zeta_rational_scaled_defect_identity n k hn hk rho (hStrip rho hrho).1.le]
        unfold zetaRationalReferenceOrder
        ring
      _ <= (k : Real) * (1 / 20) :=
        mul_le_mul_of_nonneg_left hCap (Nat.cast_nonneg k)
      _ = _ := by ring

/-- Every reference multiplicity pays the same explicit height floor. -/
theorem zeta_packet_defect_height_lower (S : Finset Complex) (n k : Nat)
    (hn : 0 < n) (hk : 0 < k)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1))
    (H : Real) (hH : 0 <= H)
    (hHeight : forall rho : Complex, Membership.mem S rho -> abs rho.im <= H) :
    ((n : Real) * realResidueHeightScale (rationalPowerDegree n k) H) *
      (zetaPacketReferenceOrder S n k : Real) <= zetaPacketDefect S n k := by
  have hnR : (0 : Real) <= n := Nat.cast_nonneg n
  unfold zetaPacketReferenceOrder zetaPacketDefect
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rho hrho
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (realPowerResidueDefect_height_lower _ (rationalPowerDegree_gt_one n k hn hk)
        rho (hStrip rho hrho).1.le (hStrip rho hrho).2.le H hH (hHeight rho hrho)) hnR)
    (Nat.cast_nonneg _)


private theorem packet_level_cast (S : Finset Complex) (n k : Nat) :
    (zetaPacketLevel S n k : Real) =
      (n + k : Nat) * (zetaPacketReferenceOrder S n k : Real) -
        (n : Real) * (zetaPacketTargetOrder S : Real) := by
  unfold zetaPacketLevel
  push_cast
  ring

/-- An arbitrary finite packet cannot erase its own original real residue. -/
theorem zeta_packet_zero_iff (S : Finset Complex) (n k : Nat)
    (hn : 0 < n) (hk : 0 < k) (hkSmall : k <= 19)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1)) :
    zetaPacketResidue S n k = 0 <->
      And (zetaPacketTargetOrder S = 0) (zetaPacketReferenceOrder S n k = 0) := by
  classical
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  constructor
  . intro hZero
    have hBudget := zeta_packet_defect_budget S n k hn hk hStrip
    have hc : (k : Real) / 20 < 1 := by
      have h : (k : Real) <= 19 := by exact_mod_cast hkSmall
      linarith
    have hSigned := zeta_packet_signed_identity S n k hn
    rw [hZero, mul_zero] at hSigned
    have hInteger := Real.integer_sub_budget_zero (zetaPacketLevel S n k)
      (zetaPacketDefect S n k) ((k : Real) / 20) hBudget.1 hBudget.2 hc hSigned.symm
    have hB : zetaPacketReferenceOrder S n k = 0 := by
      unfold zetaPacketReferenceOrder
      apply Finset.sum_eq_zero_iff.mpr
      intro rho hrho
      have hTerm : ((n : Real) * realPowerResidueDefect (rationalPowerDegree n k) rho) *
          (zetaRationalReferenceOrder n k rho : Real) <= zetaPacketDefect S n k := by
        unfold zetaPacketDefect
        apply Finset.single_le_sum (s := S)
          (f := fun w : Complex => ((n : Real) *
            realPowerResidueDefect (rationalPowerDegree n k) w) *
              (zetaRationalReferenceOrder n k w : Real))
        . intro w hw
          exact mul_nonneg (mul_pos hnR (realPowerResidueDefect_pos _
            (rationalPowerDegree_gt_one n k hn hk) w (hStrip w hw).1.le)).le
            (Nat.cast_nonneg _)
        . exact hrho
      have hPositive := mul_pos hnR (realPowerResidueDefect_pos _
        (rationalPowerDegree_gt_one n k hn hk) rho (hStrip rho hrho).1.le)
      rw [hInteger.2] at hTerm
      have hOrderNonneg : (0 : Real) <= zetaRationalReferenceOrder n k rho := Nat.cast_nonneg _
      have hOrderReal : (zetaRationalReferenceOrder n k rho : Real) = 0 := by
        nlinarith only [hTerm, hPositive, hOrderNonneg]
      exact_mod_cast hOrderReal
    have hLevel := packet_level_cast S n k
    rw [hInteger.1, Int.cast_zero, hB, Nat.cast_zero, mul_zero, zero_sub] at hLevel
    have hAReal : (zetaPacketTargetOrder S : Real) = 0 := by nlinarith only [hLevel, hnR]
    have hA : zetaPacketTargetOrder S = 0 := by exact_mod_cast hAReal
    exact And.intro hA hB
  . intro hOrders
    have hA := Finset.sum_eq_zero_iff.mp hOrders.1
    have hB := Finset.sum_eq_zero_iff.mp hOrders.2
    unfold zetaPacketResidue
    apply Finset.sum_eq_zero
    intro rho hrho
    have ha : analyticOrderNatAt riemannZeta rho = 0 := hA rho hrho
    have hb : analyticOrderNatAt riemannZeta (powerMap (rationalPowerDegree n k) rho) = 0 :=
      hB rho hrho
    simp [zetaCanonicalPowerResidue, ha, hb]

/-- The finite-packet separation radius is strictly positive. -/
theorem zeta_packet_radius_pos (n k : Nat) (hn : 0 < n) (hk : 0 < k)
    (hkSmall : k <= 19) (H : Real) :
    0 < zetaPacketRadius n k H := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hkR : (k : Real) <= 19 := by exact_mod_cast hkSmall
  exact div_pos (lt_min (by linarith) (mul_pos hnR
    (realResidueHeightScale_pos _ (rationalPowerDegree_gt_one n k hn hk) H))) hnR

/-- The signal margin depends on height and the rational power, not the set size. -/
theorem zeta_packet_abs_lower (S : Finset Complex) (n k : Nat)
    (hn : 0 < n) (hk : 0 < k) (hkSmall : k <= 19)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1))
    (H : Real) (hH : 0 <= H)
    (hHeight : forall rho : Complex, Membership.mem S rho -> abs rho.im <= H)
    (hMass : 0 < zetaPacketTargetOrder S + zetaPacketReferenceOrder S n k) :
    zetaPacketRadius n k H <= abs (zetaPacketResidue S n k) := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hkR : (k : Real) <= 19 := by exact_mod_cast hkSmall
  have hBudget := zeta_packet_defect_budget S n k hn hk hStrip
  have hFloor := zeta_packet_defect_height_lower S n k hn hk hStrip H hH hHeight
  have hScalePos := mul_pos hnR
    (realResidueHeightScale_pos _ (rationalPowerDegree_gt_one n k hn hk) H)
  have hAtZero : zetaPacketLevel S n k = 0 ->
      (n : Real) * realResidueHeightScale (rationalPowerDegree n k) H <=
        zetaPacketDefect S n k := by
    intro hLevelZero
    have hBPos : 0 < zetaPacketReferenceOrder S n k := by
      by_contra h
      have hB : zetaPacketReferenceOrder S n k = 0 := by omega
      have hLevel := packet_level_cast S n k
      rw [hLevelZero, Int.cast_zero, hB, Nat.cast_zero, mul_zero, zero_sub] at hLevel
      have hAReal : (zetaPacketTargetOrder S : Real) = 0 := by nlinarith only [hLevel, hnR]
      have hA : zetaPacketTargetOrder S = 0 := by exact_mod_cast hAReal
      omega
    have hBReal : (1 : Real) <= zetaPacketReferenceOrder S n k := by exact_mod_cast hBPos
    nlinarith only [hFloor, hScalePos, hBReal]
  have hAbs := Real.integer_sub_budget_abs_lower (zetaPacketLevel S n k)
    (zetaPacketDefect S n k) ((k : Real) / 20)
    ((n : Real) * realResidueHeightScale (rationalPowerDegree n k) H)
    hBudget.1 hBudget.2 (by linarith) hAtZero
  rw [<- zeta_packet_signed_identity S n k hn, abs_mul, abs_of_pos hnR] at hAbs
  have hDiv := mul_le_mul_of_nonneg_left hAbs (inv_pos.mpr hnR).le
  simpa [zetaPacketRadius, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hnR.ne'] using hDiv

/-- A scalar observation with half-radius error decides whether any order is positive. -/
theorem zeta_packet_threshold (S : Finset Complex) (n k : Nat)
    (hn : 0 < n) (hk : 0 < k) (hkSmall : k <= 19)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1))
    (H : Real) (hH : 0 <= H)
    (hHeight : forall rho : Complex, Membership.mem S rho -> abs rho.im <= H)
    (y : Real) (hNoise : abs (zetaPacketResidue S n k - y) < zetaPacketRadius n k H / 2) :
    0 < zetaPacketTargetOrder S + zetaPacketReferenceOrder S n k <->
      zetaPacketRadius n k H / 2 <= abs y := by
  constructor
  . intro hMass
    have hSignal := zeta_packet_abs_lower S n k hn hk hkSmall hStrip H hH hHeight hMass
    have hTriangle := abs_add_le (zetaPacketResidue S n k - y) y
    rw [sub_add_cancel] at hTriangle
    linarith only [hSignal, hTriangle, hNoise]
  . intro hY
    by_contra hMass
    have hOrders : And (zetaPacketTargetOrder S = 0) (zetaPacketReferenceOrder S n k = 0) := by omega
    have hZero := (zeta_packet_zero_iff S n k hn hk hkSmall hStrip).mpr hOrders
    rw [hZero, zero_sub, abs_neg] at hNoise
    linarith only [hNoise, hY]

/-- The signed integer level is recovered at a cardinality-independent noise scale. -/
theorem zeta_packet_index (S : Finset Complex) (n k : Nat)
    (hn : 0 < n) (hk : 0 < k)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1))
    (y : Real)
    (hNoise : abs ((n : Real) * (zetaPacketResidue S n k - y)) <
      (1 - (k : Real) / 20) / 2) :
    Int.floor ((n : Real) * y + (1 + (k : Real) / 20) / 2) = zetaPacketLevel S n k := by
  have hBudget := zeta_packet_defect_budget S n k hn hk hStrip
  have hNoise' : abs ((zetaPacketLevel S n k : Real) -
      zetaPacketDefect S n k - (n : Real) * y) < (1 - (k : Real) / 20) / 2 := by
    rw [<- zeta_packet_signed_identity S n k hn]
    simpa only [mul_sub] using hNoise
  exact Real.integer_sub_budget_index _ _ _ _ hBudget.1 hBudget.2 hNoise'

/-- At degree two, one constant-accuracy real observation recovers target parity. -/
theorem zeta_packet_quadratic_parity (S : Finset Complex)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1))
    (y : Real) (hNoise : abs (zetaPacketResidue S 1 1 - y) < 19 / 40) :
    (zetaPacketTargetOrder S : Int) % 2 = (-Int.floor (y + 21 / 40)) % 2 := by
  have h := zeta_packet_index S 1 1 (by norm_num) (by norm_num) hStrip y (by norm_num at *; exact hNoise)
  norm_num [zetaPacketLevel] at h
  omega

/-- The packet is the actual common-increment finite readout limit. -/
theorem zeta_packet_common_increment_limit (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | And (0 < s.re) (s.re < 1)})
    (S : Finset Complex) (n k : Nat) (hn : 0 < n) (hk : 0 < k)
    (hStrip : forall rho : Complex, Membership.mem S rho -> And (0 < rho.re) (rho.re < 1)) :
    Filter.Tendsto (fun t : Complex => S.sum (fun rho =>
      (t * affinePowerReadout (zetaMultiplicityReadout G)
        (rationalPowerDegree n k) (rho + t)).re))
      (nhdsWithin 0 (Set.compl {0})) (nhds (zetaPacketResidue S n k)) := by
  apply tendsto_finsetSum S
  intro rho hrho
  have hShift : Filter.Tendsto (fun t : Complex => rho + t)
      (nhdsWithin 0 (Set.compl {0})) (nhdsWithin rho (Set.compl {rho})) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    . have hc : Continuous (fun t : Complex => rho + t) := continuous_const.add continuous_id
      have hc0 := hc.tendsto (0 : Complex)
      have hRestrict : nhdsWithin (0 : Complex) (Set.compl {0}) <= nhds 0 := nhdsWithin_le_nhds
      simpa only [add_zero] using hc0.mono_left hRestrict
    . have hSource : Filter.Eventually (fun t : Complex => Not (t = 0))
          (nhdsWithin (0 : Complex) (Set.compl {0})) := self_mem_nhdsWithin
      filter_upwards [hSource] with t ht
      change Not (rho + t = rho)
      intro h
      have he : rho + t = rho + 0 := by simpa only [add_zero] using h
      exact ht (add_left_cancel he)
  have h := (zeta_rational_single_real_limit G hG n k hn hk rho (hStrip rho hrho)).comp hShift
  simpa only [Function.comp_def, add_sub_cancel_left] using h

end PrimeFactorOscillations.CarmichaelWeightedSignal
