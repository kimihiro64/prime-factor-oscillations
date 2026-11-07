/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.ThreeLineParityGeometry
import PrimeFactorOscillations.Helpers.XiClusterMultiplicity
import PrimeFactorOscillations.Helpers.ZetaReflectionMultiplicity

/-! # Odd actual zeta multiplicity forces a central canonical copy -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

def zetaFiniteTotalOrder (W : Finset Complex) : Nat :=
  Finset.sum W (fun w => analyticOrderNatAt riemannZeta w)

def zetaSignedHorizontalProduct (W : Finset Complex) : Real :=
  Finset.prod W (fun w => (w.re - 1 / 2) ^ analyticOrderNatAt riemannZeta w)

theorem zetaFiniteTotalOrder_cast (W : Finset Complex) :
    (zetaFiniteTotalOrder W : Real) =
      Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real)) := by
  simp [zetaFiniteTotalOrder]

theorem zetaHorizontalReflection_image_eq [DecidableEq Complex] (W : Finset Complex)
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w)) :
    W.image zetaHorizontalReflection = W := by
  apply Finset.ext
  intro w
  constructor
  case mp =>
    intro hw
    choose z hz hzw using Finset.mem_image.mp hw
    rw [<- hzw]
    exact hReflect z hz
  case mpr =>
    intro hw
    apply Finset.mem_image.mpr
    exact Exists.intro (zetaHorizontalReflection w)
      (And.intro (hReflect w hw) (zetaHorizontalReflection_involutive w))

theorem finset_signed_power_product {Iota : Type*} (S : Finset Iota)
    (u : Iota -> Real) (m : Iota -> Nat) :
    Finset.prod S (fun i => (-u i) ^ m i) =
      (-1 : Real) ^ Finset.sum S m * Finset.prod S (fun i => u i ^ m i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [show -u a = (-1 : Real) * u a by ring, mul_pow, ih, pow_add]
      ring

theorem zetaSignedHorizontalProduct_zero_of_odd (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hOdd : Odd (zetaFiniteTotalOrder W)) :
    zetaSignedHorizontalProduct W = 0 := by
  classical
  let u : Complex -> Real := fun w => w.re - 1 / 2
  let m : Complex -> Nat := fun w => analyticOrderNatAt riemannZeta w
  have hImage := zetaHorizontalReflection_image_eq W hReflect
  have hMap : Finset.prod W (fun w => u w ^ m w) =
      Finset.prod W (fun w => (-u w) ^ m w) := by
    calc
      _ = Finset.prod (W.image zetaHorizontalReflection) (fun w => u w ^ m w) := by rw [hImage]
      _ = Finset.prod W (fun w => u (zetaHorizontalReflection w) ^
          m (zetaHorizontalReflection w)) :=
        Finset.prod_image (fun a _ b _ hab => zetaHorizontalReflection_injective hab)
      _ = _ := by
        apply Finset.prod_congr rfl
        intro w hw
        dsimp only [u, m]
        rw [zetaHorizontalCoord_reflection, zetaOrder_reflection w (hCritical w hw)]
  have hSign := finset_signed_power_product W u m
  have hOddPow : (-1 : Real) ^ Finset.sum W m = -1 := hOdd.neg_one_pow
  rw [hOddPow] at hSign
  change Finset.prod W (fun w => u w ^ m w) = 0
  nlinarith only [hMap, hSign]

theorem zeta_odd_total_order_has_critical_point (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hOdd : Odd (zetaFiniteTotalOrder W)) :
    exists w : Complex, And (Membership.mem W w)
      (And (w.re = 1 / 2) (0 < analyticOrderNatAt riemannZeta w)) := by
  classical
  have hProduct := zetaSignedHorizontalProduct_zero_of_odd W hCritical hReflect hOdd
  unfold zetaSignedHorizontalProduct at hProduct
  choose w hw hPower using Finset.prod_eq_zero_iff.mp hProduct
  have hOrder : 0 < analyticOrderNatAt riemannZeta w := by
    by_contra h
    have hZero := Nat.eq_zero_of_not_pos h
    simp [hZero] at hPower
  have hCoord : w.re - 1 / 2 = 0 := by
    by_contra h
    exact (pow_ne_zero _ h) hPower
  exact Exists.intro w (And.intro hw (And.intro (by linarith) hOrder))

theorem xiFiniteMultiplicityUnion_card_eq_totalOrder (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1)) :
    (xiFiniteMultiplicityUnion W).card = zetaFiniteTotalOrder W := by
  have h := zeta_finite_multiplicity_transport W hCritical (fun _ => (1 : Real))
  have hReal : ((xiFiniteMultiplicityUnion W).card : Real) = (zetaFiniteTotalOrder W : Real) := by
    simpa [zetaFiniteTotalOrder, Finset.sum_const, nsmul_eq_mul] using h.symm
  exact_mod_cast hReal

theorem zeta_odd_total_order_has_central_index (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hOdd : Odd (zetaFiniteTotalOrder W)) :
    exists p : RiemannXiDivisorZeroIndex, And (Membership.mem (xiFiniteMultiplicityUnion W) p)
      (((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2 = 0) := by
  classical
  choose w hw hRe hOrder using zeta_odd_total_order_has_critical_point W hCritical hReflect hOdd
  have hw0 : Not (w = 0) := by
    intro h
    have hh := (hCritical w hw).1
    rw [h] at hh
    norm_num at hh
  have hw1 : Not (w = 1) := by
    intro h
    have hh := (hCritical w hw).2
    rw [h] at hh
    norm_num at hh
  have hXiOrder : 0 < xiZeroMultiplicity w := by
    rw [xiZeroMultiplicity_eq_zetaOrder (hCritical w hw).1 hw1]
    exact hOrder
  let q := (xiZeroFiberEquiv w hw0).symm (Fin.mk 0 hXiOrder)
  let p := q.val
  have hValue : riemannXiDivisorZeroValue p = w := q.property
  have hFiber : Membership.mem (xiFiniteMultiplicityFiber w) p :=
    (xiFiniteMultiplicityFiber_mem w hw0 p).mpr hValue
  apply Exists.intro p
  constructor
  case left =>
    change Membership.mem (W.biUnion xiFiniteMultiplicityFiber) p
    exact Finset.mem_biUnion.mpr (Exists.intro w (And.intro hw hFiber))
  case right =>
    rw [hValue, hRe]
    norm_num

theorem zeta_total_order_one_horizontal_moment_zero (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hOne : zetaFiniteTotalOrder W = 1) :
    Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      (w.re - 1 / 2) ^ 2) = 0 := by
  classical
  have hOdd : Odd (zetaFiniteTotalOrder W) := by rw [hOne, Nat.odd_iff]
  choose a ha hZero using zeta_odd_total_order_has_central_index W hCritical hReflect hOdd
  let S := xiFiniteMultiplicityUnion W
  let x : RiemannXiDivisorZeroIndex -> Real := fun p =>
    ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2
  let R := S.erase a
  have hCardS : S.card = 1 := by
    rw [xiFiniteMultiplicityUnion_card_eq_totalOrder W hCritical, hOne]
  have hCardR : (R.card : Real) = 0 := by
    have h := Finset.card_erase_add_one ha
    change R.card + 1 = S.card at h
    rw [hCardS] at h
    exact_mod_cast (by omega : R.card = 0)
  have hNonneg : forall p, Membership.mem R p -> 0 <= x p := fun p _ => sq_nonneg _
  have hRSum : Finset.sum R x = 0 := by
    apply le_antisymm
    case a =>
      calc
        Finset.sum R x <= Finset.sum R (fun _ => Finset.sum R x) := by
          apply Finset.sum_le_sum
          intro p hp
          exact Finset.single_le_sum hNonneg hp
        _ = (R.card : Real) * Finset.sum R x := by simp only [Finset.sum_const, nsmul_eq_mul]
        _ = 0 := by rw [hCardR, zero_mul]
    case a => exact Finset.sum_nonneg hNonneg
  have hSum := Finset.sum_erase_add S x ha
  change Finset.sum R x + x a = Finset.sum S x at hSum
  have hxa : x a = 0 := hZero
  rw [hRSum, hxa, zero_add] at hSum
  have hTransport := zeta_finite_multiplicity_transport W hCritical
    (fun w => (w.re - 1 / 2) ^ 2)
  exact hTransport.trans hSum.symm

theorem zeta_finite_odd_horizontal_charge_trace (t : Real) (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = t)
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hOdd : Odd (zetaFiniteTotalOrder W))
    (hStrip : forall p : RiemannXiDivisorZeroIndex,
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 3 / 8)
    (z : Real) (hN : 1 < (zetaFiniteTotalOrder W : Real))
    (hCenter : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      (w.re - 1 / 2) ^ 2) = ((zetaFiniteTotalOrder W : Real) - 1) * z) :
    And (And (0 <= z) (z <= 9 / 64))
      (threeLineHorizontalVarianceCoefficient * Finset.sum W
        (fun w => (analyticOrderNatAt riemannZeta w : Real) * (w.re - 1 / 2) ^ 4) +
        threeLineCharge + ((zetaFiniteTotalOrder W : Real) - 1) *
          threeLineHorizontalResidualProfile z <= threeLineXiTrace t) := by
  classical
  let S := xiFiniteMultiplicityUnion W
  let x : RiemannXiDivisorZeroIndex -> Real := fun p =>
    ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2
  choose a ha hZero using zeta_odd_total_order_has_central_index W hCritical hReflect hOdd
  let R := S.erase a
  have hCardS : (S.card : Real) = (zetaFiniteTotalOrder W : Real) := by
    rw [xiFiniteMultiplicityUnion_card_eq_totalOrder W hCritical]
  have hCardR : (R.card : Real) = (zetaFiniteTotalOrder W : Real) - 1 := by
    have h := Finset.card_erase_add_one ha
    change R.card + 1 = S.card at h
    have hr : (R.card : Real) + 1 = (S.card : Real) := by exact_mod_cast h
    linarith
  have hMoment := zeta_finite_multiplicity_transport W hCritical
    (fun w => (w.re - 1 / 2) ^ 2)
  change Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
    (w.re - 1 / 2) ^ 2) = Finset.sum S x at hMoment
  have hFourth := zeta_finite_multiplicity_transport W hCritical
    (fun w => (w.re - 1 / 2) ^ 4)
  have hFourthS : Finset.sum S (fun p => ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 4) =
      Finset.sum S (fun p => (x p) ^ 2) := by
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [x]
    ring
  rw [hFourthS] at hFourth
  have hErase := Finset.sum_erase_add S x ha
  have hxa : x a = 0 := hZero
  rw [hxa, add_zero] at hErase
  have hCenterR : Finset.sum R x = (R.card : Real) * z := by
    rw [hErase, <- hMoment, hCenter, hCardR]
  have hx (p : RiemannXiDivisorZeroIndex) (_hp : Membership.mem S p) :
      And (0 <= x p) (x p <= 9 / 64) := by
    have hu := abs_le.mp (hStrip p)
    have hPlus : 0 <= ((riemannXiDivisorZeroValue p).re - 1 / 2) + 3 / 8 := by linarith [hu.1]
    have hProduct := mul_nonneg (sub_nonneg.mpr hu.2) hPlus
    constructor
    case left => exact sq_nonneg _
    case right => dsimp only [x]; nlinarith
  have hz := threeLineHorizontal_mean_bounds R x z
    (fun p hp => hx p (Finset.mem_of_mem_erase hp)) (by rw [hCardR]; linarith) hCenterR
  have hLocal := threeLineHorizontalResidual_central_removal S x a ha hxa z hx hz hCenterR
  have hSplit : Finset.sum S (fun p => threeLineHorizontalProfile (x p)) =
      Finset.sum S (fun p => threeLineHorizontalResidualProfile (x p)) +
        threeLineHorizontalVarianceCoefficient * Finset.sum S (fun p => (x p) ^ 2) := by
    rw [Finset.mul_sum, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    unfold threeLineHorizontalResidualProfile
    ring
  have hSameS (p : RiemannXiDivisorZeroIndex) (hp : Membership.mem S p) :
      (riemannXiDivisorZeroValue p).im = t := by
    change Membership.mem (W.biUnion xiFiniteMultiplicityFiber) p at hp
    choose w hw hpf using Finset.mem_biUnion.mp hp
    have hw0 : Not (w = 0) := by
      intro he
      have h := (hCritical w hw).1
      rw [he] at h
      norm_num at h
    rw [(xiFiniteMultiplicityFiber_mem w hw0 p).mp hpf]
    exact hSame w hw
  have hUpper : Finset.sum S (fun p => threeLineHorizontalProfile (x p)) <= threeLineXiTrace t := by
    have hKernel : Finset.sum S (fun p => threeLineHorizontalProfile (x p)) =
        Finset.sum S (fun p => threeLineKernel ((riemannXiDivisorZeroValue p).re - 1 / 2)
          (t - (riemannXiDivisorZeroValue p).im)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hSameS p hp, sub_self, threeLineKernel_horizontal_profile _ (hStrip p)]
    rw [hKernel]
    exact xi_threeLine_finite_mass t hStrip S
  rw [hCardR] at hLocal
  rw [<- hFourth] at hSplit
  exact And.intro hz (by linarith)

end PrimeFactorOscillations
