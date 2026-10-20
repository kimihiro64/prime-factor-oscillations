/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticSmoothBandRows

/-!
# QuadraticSmoothUnit

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.QuadraticSmoothUnit

open MeasureTheory IntegerQuadraticPrefix QuadraticProductDivisor QuadraticProductBandSubpower
open QuadraticDivisorMean QuadraticBandUniformPhase QuadraticSmoothBandRows
open SchwartzDyadicSeparation SchwartzFiniteSeparation SchwartzFinitePacket

def smoothUnitMean (R S T : Finset Nat) (a b : Nat -> Complex)
    (F : SchwartzMap Real Complex) (scale : Real) (eta theta epsilon : Nat -> Real) : Real :=
  R.sum (fun r => norm ((S.product T).sum (fun q =>
    coefficient a b 1 r q.1 q.2 *
      F (scale * Real.exp
        (logArgument eta theta (fun _ => 0) epsilon (Prod.mk 1 r) q)))))

theorem smooth_unit_divisor_mean (F : SchwartzMap Real Complex)
    (T0 : Real) (hT0 : 0 <= T0) (A : Nat) (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M N1 N2 : Nat) (R S T : Finset Nat) (a b : Nat -> Complex),
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      forall (scale : Real) (eta theta epsilon : Nat -> Real), 0 <= scale ->
        (forall r, Membership.mem R r -> forall q, Membership.mem (S.product T) q ->
          abs (logArgument eta theta (fun _ => 0) epsilon (Prod.mk 1 r) q) <= T0) ->
        smoothUnitMean R S T a b F scale eta theta epsilon <=
          C * ((max N1 N2 : Nat) : Real) ^ eps / (1 + scale) ^ A *
            Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
            Real.sqrt (prefixNorm M N2 * maskedMass 1 T b) := by
  choose CLog hCLog hlog using local_log_separation F T0 hT0 A
  choose CS hCS hs using unit_divisor_mean eps heps
  refine Exists.intro (CLog * CS) (And.intro (mul_pos hCLog hCS) ?_)
  intro M N1 N2 R S T a b hR hS hT scale eta theta epsilon hscale hArgs
  choose g hpoint hmass hrepr using hlog scale hscale
  let H : Real := CS * ((max N1 N2 : Nat) : Real) ^ eps *
    Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
    Real.sqrt (prefixNorm M N2 * maskedMass 1 T b)
  have hH : 0 <= H := by dsimp only [H]; positivity
  have hpacket (t : Real) :
      R.sum (fun r => norm ((S.product T).sum (fun q =>
        coefficient a b 1 r q.1 q.2 *
          (phase t (logArgument eta theta (fun _ => 0) epsilon (Prod.mk 1 r) q) : Complex)))) <= H := by
    have hb := hs M N1 N2 R S T
      (fun n => a n * (phase t (eta n) : Complex))
      (fun m => b m * (phase t (theta m) : Complex)) hR hS hT
    rw [maskedMass_unit_phase 1 S a (fun n => phase t (eta n)),
      maskedMass_unit_phase 1 T b (fun m => phase t (theta m))] at hb
    have heq :
        R.sum (fun r => norm ((S.product T).sum (fun q =>
          coefficient a b 1 r q.1 q.2 *
            (phase t (logArgument eta theta (fun _ => 0) epsilon (Prod.mk 1 r) q) : Complex)))) =
        R.sum (fun r => norm (divisorRow 1 S T
          (fun n => a n * (phase t (eta n) : Complex))
          (fun m => b m * (phase t (theta m) : Complex)) r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [phase_row, norm_mul, phase_norm, one_mul]
    exact heq.trans_le hb
  have hmain := finite_integral_l1_bound g R (S.product T)
    (fun r q => coefficient a b 1 r q.1 q.2)
    (fun r q => logArgument eta theta (fun _ => 0) epsilon (Prod.mk 1 r) q) H hpacket
  have heq : smoothUnitMean R S T a b F scale eta theta epsilon =
      R.sum (fun r => norm ((S.product T).sum (fun q =>
        coefficient a b 1 r q.1 q.2 *
          g (logArgument eta theta (fun _ => 0) epsilon (Prod.mk 1 r) q)))) := by
    unfold smoothUnitMean
    apply Finset.sum_congr rfl
    intro r hr
    apply congrArg norm
    apply Finset.sum_congr rfl
    intro q hq
    rw [hpoint _ (hArgs r hr q hq)]
  calc
    _ <= H * integral volume (fun t : Real => norm ((FourierTransform.fourier g) t)) :=
      heq.trans_le hmain
    _ <= H * (CLog / (1 + scale) ^ A) := mul_le_mul_of_nonneg_left hmass hH
    _ = _ := by dsimp only [H]; ring

end PrimeFactorOscillations.QuadraticSmoothUnit

