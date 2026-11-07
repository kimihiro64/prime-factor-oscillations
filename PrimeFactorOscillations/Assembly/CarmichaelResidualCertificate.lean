/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PositiveTraceResidual
import PrimeFactorOscillations.Helpers.ResolventBlockKernel
import PrimeFactorOscillations.Helpers.XiHorizontalMultiplicity
import PrimeFactorOscillations.Helpers.XiPairedResolventTrace

/-! # Actual zero-copy completeness and simplicity from a finite residual budget -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984 BombieriVinogradov.SiegelWalfisz

def xiUnitResolventTrace (t : Real) : Real :=
  (18 / 5) * (xiPairedLogTrace 2 t - (2 / 3) * xiPairedLogTrace 3 t)

def xiUnitCopyKernel (t : Real) (p : RiemannXiDivisorZeroIndex) : Real :=
  unitResolventKernel ((riemannXiDivisorZeroValue p).re - 1 / 2)
    (t - (riemannXiDivisorZeroValue p).im)

theorem xi_unit_resolvent_finite_mass (t : Real) (S : Finset RiemannXiDivisorZeroIndex) :
    Finset.sum S (xiUnitCopyKernel t) <= xiUnitResolventTrace t := by
  have hStrip : forall p : RiemannXiDivisorZeroIndex,
      And (abs ((riemannXiDivisorZeroValue p).re - 1 / 2) < 2)
        (2 * ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2 <= 2 ^ 2) := by
    intro p
    have hp := riemannXiDivisorZeroValue_re_mem_Ioo p
    have hx : abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 1 / 2 :=
      abs_le.mpr (And.intro (by linarith only [hp.1]) (by linarith only [hp.2]))
    have hProd := mul_nonneg hp.1.le (sub_nonneg.mpr hp.2.le)
    exact And.intro (by linarith only [hx]) (by nlinarith only [hProd])
  have h := xi_compensated_resolvent_finite_mass 2 3 t (by norm_num) (by norm_num) hStrip S
  have hMul := mul_le_mul_of_nonneg_left h (by norm_num : (0 : Real) <= 18 / 5)
  rw [Finset.mul_sum] at hMul
  change Finset.sum S (fun p => (18 / 5) *
    pairedResolventDifference 2 3 ((riemannXiDivisorZeroValue p).re - 1 / 2)
      (t - (riemannXiDivisorZeroValue p).im)) <=
    (18 / 5) * (xiPairedLogTrace 2 t - (2 / 3) * xiPairedLogTrace 3 t)
  exact hMul

theorem xi_unit_resolvent_block_charge (t H : Real) (p : RiemannXiDivisorZeroIndex)
    (hH : And (0 <= H) (H <= 1))
    (hp : abs (t - (riemannXiDivisorZeroValue p).im) <= H) :
    unitResolventBlockCharge H <= xiUnitCopyKernel t p := by
  have hs := riemannXiDivisorZeroValue_re_mem_Ioo p
  have hx : abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 1 / 2 :=
    abs_le.mpr (And.intro (by linarith only [hs.1]) (by linarith only [hs.2]))
  exact unitResolventKernel_block_lower H _ _ hH hx hp

theorem xi_unit_residual_card (t H U : Real)
    (S P : Finset RiemannXiDivisorZeroIndex) (ell : RiemannXiDivisorZeroIndex -> Real)
    (hH : And (0 <= H) (H <= 1)) (hUpper : xiUnitResolventTrace t <= U)
    (hKnown : forall p, Membership.mem S p -> ell p <= xiUnitCopyKernel t p)
    (hBlock : forall p, Membership.mem P p -> abs (t - (riemannXiDivisorZeroValue p).im) <= H)
    (hApart : forall p, Membership.mem P p -> Not (Membership.mem S p)) :
    unitResolventBlockCharge H * (P.card : Real) <= U - Finset.sum S ell := by
  exact finite_trace_residual_card S P (xiUnitCopyKernel t) ell (unitResolventBlockCharge H) U
    (fun W => (xi_unit_resolvent_finite_mass t W).trans hUpper) hKnown
    (fun p hp => xi_unit_resolvent_block_charge t H p hH (hBlock p hp)) hApart

theorem xi_unit_residual_contains (t H U : Real)
    (S : Finset RiemannXiDivisorZeroIndex) (ell : RiemannXiDivisorZeroIndex -> Real)
    (hH : And (0 <= H) (H <= 1)) (hUpper : xiUnitResolventTrace t <= U)
    (hKnown : forall p, Membership.mem S p -> ell p <= xiUnitCopyKernel t p)
    (hBudget : U - Finset.sum S ell < unitResolventBlockCharge H) :
    forall p : RiemannXiDivisorZeroIndex,
      abs (t - (riemannXiDivisorZeroValue p).im) <= H -> Membership.mem S p := by
  exact finite_trace_residual_contains S (xiUnitCopyKernel t) ell (unitResolventBlockCharge H) U
    (fun p => abs (t - (riemannXiDivisorZeroValue p).im) <= H)
    (fun W => (xi_unit_resolvent_finite_mass t W).trans hUpper) hKnown
    (fun p hp => xi_unit_resolvent_block_charge t H p hH hp) hBudget

theorem zeta_unit_residual_simplicity (t H U : Real)
    (S : Finset RiemannXiDivisorZeroIndex) (ell : RiemannXiDivisorZeroIndex -> Real)
    (hH : And (0 <= H) (H <= 1)) (hUpper : xiUnitResolventTrace t <= U)
    (hKnown : forall p, Membership.mem S p -> ell p <= xiUnitCopyKernel t p)
    (hBudget : U - Finset.sum S ell < unitResolventBlockCharge H)
    (hDistinct : forall p, Membership.mem S p -> forall q, Membership.mem S q ->
      riemannXiDivisorZeroValue p = riemannXiDivisorZeroValue q -> p = q)
    (w : Complex) (hw : And (0 < w.re) (w.re < 1)) (hWindow : abs (t - w.im) <= H) :
    analyticOrderNatAt riemannZeta w <= 1 := by
  classical
  have hClosed := xi_unit_residual_contains t H U S ell hH hUpper hKnown hBudget
  have hw0 : Not (w = 0) := by
    intro he
    have hh := hw.1
    rw [he] at hh
    norm_num at hh
  have hw1 : Not (w = 1) := by
    intro he
    have hh := hw.2
    rw [he] at hh
    norm_num at hh
  have hInS : forall p, Membership.mem (xiFiniteMultiplicityFiber w) p -> Membership.mem S p := by
    intro p hp
    have hv := (xiFiniteMultiplicityFiber_mem w hw0 p).mp hp
    apply hClosed p
    rw [hv]
    exact hWindow
  have hCard : (xiFiniteMultiplicityFiber w).card <= 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have hpv := (xiFiniteMultiplicityFiber_mem w hw0 p).mp hp
    have hqv := (xiFiniteMultiplicityFiber_mem w hw0 q).mp hq
    exact hDistinct p (hInS p hp) q (hInS q hq) (hpv.trans hqv.symm)
  rw [xiFiniteMultiplicityFiber_card w hw0, xiZeroMultiplicity_eq_zetaOrder hw.1 hw1] at hCard
  exact hCard

theorem zeta_unit_residual_positive_order_line (t H U : Real)
    (S : Finset RiemannXiDivisorZeroIndex) (ell : RiemannXiDivisorZeroIndex -> Real)
    (hH : And (0 <= H) (H <= 1)) (hUpper : xiUnitResolventTrace t <= U)
    (hKnown : forall p, Membership.mem S p -> ell p <= xiUnitCopyKernel t p)
    (hBudget : U - Finset.sum S ell < unitResolventBlockCharge H)
    (hLine : forall p, Membership.mem S p -> (riemannXiDivisorZeroValue p).re = 1 / 2)
    (w : Complex) (hw : And (0 < w.re) (w.re < 1)) (hWindow : abs (t - w.im) <= H)
    (hOrder : 0 < analyticOrderNatAt riemannZeta w) : w.re = 1 / 2 := by
  classical
  have hClosed := xi_unit_residual_contains t H U S ell hH hUpper hKnown hBudget
  have hw0 : Not (w = 0) := by
    intro he
    have hh := hw.1
    rw [he] at hh
    norm_num at hh
  have hw1 : Not (w = 1) := by
    intro he
    have hh := hw.2
    rw [he] at hh
    norm_num at hh
  have hCard : 0 < (xiFiniteMultiplicityFiber w).card := by
    rw [xiFiniteMultiplicityFiber_card w hw0, xiZeroMultiplicity_eq_zetaOrder hw.1 hw1]
    exact hOrder
  choose p hp using Finset.card_pos.mp hCard
  have hv := (xiFiniteMultiplicityFiber_mem w hw0 p).mp hp
  have hBand : abs (t - (riemannXiDivisorZeroValue p).im) <= H := by rw [hv]; exact hWindow
  have hValue := hLine p (hClosed p hBand)
  rw [hv] at hValue
  exact hValue

end PrimeFactorOscillations
