/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelEffectiveMultiplicity
import PrimeFactorOscillations.Assembly.CarmichaelResidualCertificate
import PrimeFactorOscillations.Helpers.CompensatedEulerPacket
import PrimeFactorOscillations.Helpers.CompensatedXiConstants

/-! # Finite arithmetic inputs for actual zero-copy simplicity certificates -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984 BombieriVinogradov.SiegelWalfisz

def xiFiniteTraceMain (N : Nat) (t : Real) : Real :=
  compensatedXiScalar t - 27 / 25 - 70 / 1089 + (18 / 5) * compensatedEulerPacket N t

def xiFiniteTraceUpper (N : Nat) (t : Real) : Real :=
  xiFiniteTraceMain N t + 70 / 1089 + (18 / 5) * eulerUniformTail N

theorem compensatedXiScalar_neg (t : Real) :
    compensatedXiScalar (-t) = compensatedXiScalar t := by
  simp only [compensatedXiScalar, abs_neg, neg_sq]

theorem xi_finite_euler_scalar_upper (N : Nat) (t : Real)
    (hN : 6 <= N) (ht : 2 <= abs t) :
    (18 / 5) * ((logDeriv riemannXi (xiResolventPoint 2 t)).re -
      (2 / 3) * (logDeriv riemannXi (xiResolventPoint 3 t)).re) <=
      compensatedXiScalar t - 27 / 25 +
        (18 / 5) * ((compensatedEulerHead N t).re + eulerUniformTail N) := by
  have he := compensatedEulerPacket_upper N t hN
  dsimp only [compensatedEulerPoint] at he
  have hcRe : (2 / 3 : Complex).re = 2 / 3 := by norm_num
  have hcIm : (2 / 3 : Complex).im = 0 := by norm_num
  simp only [Complex.sub_re, Complex.mul_re, hcRe, hcIm, zero_mul, sub_zero] at he
  have ht0 : Not (t = 0) := by intro h; simp only [h, abs_zero] at ht; linarith only [ht]
  have hg := compensated_digamma_real_upper t ht0
  have hx2 := xi_logDeriv_point_euler_gamma 2 t (by norm_num)
  have hx3 := xi_logDeriv_point_euler_gamma 3 t (by norm_num)
  norm_num only at hx2 hx3
  dsimp only [compensatedXiScalar, compensatedPoleSquared]
  simp only [div_eq_mul_inv] at he hg hx2 hx3
  simp only [div_eq_mul_inv]
  norm_num only at he hg hx2 hx3
  norm_num only
  linarith only [he, hg, hx2, hx3]

theorem xi_finite_euler_trace_upper (N : Nat) (t : Real)
    (hN : 6 <= N) (ht : 2 <= abs t) :
    xiUnitResolventTrace t <= xiFiniteTraceUpper N t := by
  have h0 := xi_finite_euler_scalar_upper N t hN ht
  have ht1 : 2 <= abs (-t) := by simpa only [abs_neg] using ht
  have h1 := xi_finite_euler_scalar_upper N (-t) hN ht1
  rw [compensatedXiScalar_neg] at h1
  dsimp only [xiUnitResolventTrace, xiPairedLogTrace, xiFiniteTraceUpper,
    xiFiniteTraceMain, compensatedEulerPacket]
  linarith only [h0, h1]

theorem zeta_multiplicity_finite_euler_bound (N : Nat) (w : Complex)
    (hN : 6 <= N) (hw : And (0 < w.re) (w.re < 1)) (ht : 2 <= abs w.im) :
    (analyticOrderNatAt riemannZeta w : Real) <= xiFiniteTraceUpper N w.im := by
  exact (zeta_multiplicity_le_effective_trace hw).trans
    (xi_finite_euler_trace_upper N w.im hN ht)

theorem zeta_simplicity_finite_euler_bound (N : Nat) (w : Complex)
    (hN : 6 <= N) (hw : And (0 < w.re) (w.re < 1)) (ht : 2 <= abs w.im)
    (hBudget : xiFiniteTraceUpper N w.im < 2) :
    analyticOrderNatAt riemannZeta w <= 1 := by
  have hm := (zeta_multiplicity_finite_euler_bound N w hN hw ht).trans_lt hBudget
  exact Nat.le_of_lt_succ (by exact_mod_cast hm)

theorem xi_unit_copy_enclosure_lower (t a e : Real) (p : RiemannXiDivisorZeroIndex)
    (he : 0 <= e) (hLine : (riemannXiDivisorZeroValue p).re = 1 / 2)
    (hEnclosure : abs ((riemannXiDivisorZeroValue p).im - a) <= e) :
    unitResolventBlockCharge (abs (t - a) + e) <= xiUnitCopyKernel t p := by
  have hDist : abs (t - (riemannXiDivisorZeroValue p).im) <= abs (t - a) + e := by
    calc
      abs (t - (riemannXiDivisorZeroValue p).im) =
          abs ((t - a) - ((riemannXiDivisorZeroValue p).im - a)) := by congr 1; ring
      _ <= abs (t - a) + abs ((riemannXiDivisorZeroValue p).im - a) := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (t - a) 0 ((riemannXiDivisorZeroValue p).im - a))
      _ <= abs (t - a) + e := by linarith only [hEnclosure]
  unfold xiUnitCopyKernel
  rw [hLine, sub_self, unitResolventKernel_center]
  exact unitResolventBlockCharge_le _ _ (add_nonneg (abs_nonneg _) he) hDist

theorem finite_euler_residual_contains (N : Nat) (t H : Real)
    (S : Finset RiemannXiDivisorZeroIndex) (a e : RiemannXiDivisorZeroIndex -> Real)
    (hN : 6 <= N) (ht : 2 <= abs t) (hH : And (0 <= H) (H <= 1))
    (hError : forall p, Membership.mem S p -> 0 <= e p)
    (hLine : forall p, Membership.mem S p -> (riemannXiDivisorZeroValue p).re = 1 / 2)
    (hEnclosure : forall p, Membership.mem S p ->
      abs ((riemannXiDivisorZeroValue p).im - a p) <= e p)
    (hBudget : xiFiniteTraceUpper N t -
      Finset.sum S (fun p => unitResolventBlockCharge (abs (t - a p) + e p)) <
        unitResolventBlockCharge H) :
    forall p : RiemannXiDivisorZeroIndex,
      abs (t - (riemannXiDivisorZeroValue p).im) <= H -> Membership.mem S p := by
  exact xi_unit_residual_contains t H (xiFiniteTraceUpper N t) S
    (fun p => unitResolventBlockCharge (abs (t - a p) + e p)) hH
    (xi_finite_euler_trace_upper N t hN ht)
    (fun p hp => xi_unit_copy_enclosure_lower t (a p) (e p) p
      (hError p hp) (hLine p hp) (hEnclosure p hp)) hBudget

theorem finite_euler_residual_simplicity (N : Nat) (t H : Real)
    (S : Finset RiemannXiDivisorZeroIndex) (a e : RiemannXiDivisorZeroIndex -> Real)
    (hN : 6 <= N) (ht : 2 <= abs t) (hH : And (0 <= H) (H <= 1))
    (hError : forall p, Membership.mem S p -> 0 <= e p)
    (hLine : forall p, Membership.mem S p -> (riemannXiDivisorZeroValue p).re = 1 / 2)
    (hEnclosure : forall p, Membership.mem S p ->
      abs ((riemannXiDivisorZeroValue p).im - a p) <= e p)
    (hBudget : xiFiniteTraceUpper N t -
      Finset.sum S (fun p => unitResolventBlockCharge (abs (t - a p) + e p)) <
        unitResolventBlockCharge H)
    (hDistinct : forall p, Membership.mem S p -> forall q, Membership.mem S q ->
      riemannXiDivisorZeroValue p = riemannXiDivisorZeroValue q -> p = q)
    (w : Complex) (hw : And (0 < w.re) (w.re < 1)) (hWindow : abs (t - w.im) <= H) :
    analyticOrderNatAt riemannZeta w <= 1 := by
  exact zeta_unit_residual_simplicity t H (xiFiniteTraceUpper N t) S
    (fun p => unitResolventBlockCharge (abs (t - a p) + e p)) hH
    (xi_finite_euler_trace_upper N t hN ht)
    (fun p hp => xi_unit_copy_enclosure_lower t (a p) (e p) p
      (hError p hp) (hLine p hp) (hEnclosure p hp)) hBudget hDistinct w hw hWindow

theorem finiteEuler_hundred_tail_charge :
    (18 / 5) * eulerUniformTail 100 < unitResolventBlockCharge 1 / 50 := by
  have hh := mul_lt_mul_of_pos_left eulerUniformTail_hundred
    (by norm_num : (0 : Real) < 18 / 5)
  rw [unitResolventBlockCharge_one]
  linarith only [hh]

theorem finiteEuler_hundred_full_error_charge :
    70 / 1089 + (18 / 5) * eulerUniformTail 100 <
      (3 / 25) * unitResolventBlockCharge 1 := by
  have hh := finiteEuler_hundred_tail_charge
  rw [unitResolventBlockCharge_one] at hh
  rw [unitResolventBlockCharge_one]
  linarith only [hh]

theorem finite_euler_hundred_residual_simplicity (t : Real)
    (S : Finset RiemannXiDivisorZeroIndex) (a e : RiemannXiDivisorZeroIndex -> Real)
    (ht : 2 <= abs t)
    (hError : forall p, Membership.mem S p -> 0 <= e p)
    (hLine : forall p, Membership.mem S p -> (riemannXiDivisorZeroValue p).re = 1 / 2)
    (hEnclosure : forall p, Membership.mem S p ->
      abs ((riemannXiDivisorZeroValue p).im - a p) <= e p)
    (hBudget : xiFiniteTraceMain 100 t -
      Finset.sum S (fun p => unitResolventBlockCharge (abs (t - a p) + e p)) <
        (22 / 25) * unitResolventBlockCharge 1)
    (hDistinct : forall p, Membership.mem S p -> forall q, Membership.mem S q ->
      riemannXiDivisorZeroValue p = riemannXiDivisorZeroValue q -> p = q)
    (w : Complex) (hw : And (0 < w.re) (w.re < 1)) (hWindow : abs (t - w.im) <= 1) :
    analyticOrderNatAt riemannZeta w <= 1 := by
  have hErr := finiteEuler_hundred_full_error_charge
  have hFull : xiFiniteTraceUpper 100 t -
      Finset.sum S (fun p => unitResolventBlockCharge (abs (t - a p) + e p)) <
        unitResolventBlockCharge 1 := by
    dsimp only [xiFiniteTraceUpper]
    linarith only [hBudget, hErr]
  exact finite_euler_residual_simplicity 100 t 1 S a e (by norm_num) ht
    (And.intro (by norm_num) (by norm_num)) hError hLine hEnclosure hFull hDistinct w hw hWindow

end PrimeFactorOscillations
