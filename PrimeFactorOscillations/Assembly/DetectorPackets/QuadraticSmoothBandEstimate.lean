/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticSmoothBandRows

/-!
# QuadraticSmoothBandEstimate

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

namespace PrimeFactorOscillations.QuadraticSmoothBandEstimate

open MeasureTheory IntegerQuadraticPrefix QuadraticBandUniformPhase QuadraticSmoothBandRows
open SchwartzDyadicSeparation SchwartzFiniteSeparation SchwartzFinitePacket

theorem smooth_product_divisor_mean (F : SchwartzMap Real Complex)
    (T0 : Real) (hT0 : 0 <= T0) (A : Nat) (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (D M N1 N2 : Nat) (R S T : Finset Nat) (a b : Nat -> Complex),
      0 < D -> 0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      exists L1 L2 : Nat,
        0 < L1 /\ 0 < L2 /\ D < 4 * (L1 * L2) /\ L1 * L2 <= 2 * D /\
        forall (scale : Real) (eta theta delta epsilon : Nat -> Real), 0 <= scale ->
          (forall p, Membership.mem (bandRows D R) p ->
            forall q, Membership.mem (S.product T) q ->
              abs (logArgument eta theta delta epsilon p q) <= T0) ->
          smoothBandMean D R S T a b F scale eta theta delta epsilon <=
            C * ((max N1 N2 : Nat) : Real) ^ eps / (1 + scale) ^ A *
              pairBound M N1 N2 S T a b (Prod.mk L1 L2) := by
  choose CLog hCLog hlog using local_log_separation F T0 hT0 A
  choose CS hCS hs using product_divisor_mean_uniform_phase eps heps
  refine Exists.intro (CLog * CS) (And.intro (mul_pos hCLog hCS) ?_)
  intro D M N1 N2 R S T a b hD hN1 hN2 hR hS hT
  choose L1 L2 h1 h2 hlo hhi hb using hs D M N1 N2 R S T a b
    hD hN1 hN2 hR hS hT
  refine Exists.intro L1 (Exists.intro L2
    (And.intro h1 (And.intro h2 (And.intro hlo (And.intro hhi ?_)))))
  intro scale eta theta delta epsilon hscale hArgs
  choose g hpoint hmass hrepr using hlog scale hscale
  let H : Real := CS * ((max N1 N2 : Nat) : Real) ^ eps *
    pairBound M N1 N2 S T a b (Prod.mk L1 L2)
  have hH : 0 <= H := by dsimp only [H, pairBound]; positivity
  have hpacket (t : Real) :
      (bandRows D R).sum (fun p => norm ((S.product T).sum (fun q =>
        coefficient a b p.1 p.2 q.1 q.2 *
          (phase t (logArgument eta theta delta epsilon p q) : Complex)))) <= H := by
    exact (phase_band_mean D R S T a b eta theta delta epsilon t).le.trans
      (hb (fun n => phase t (eta n)) (fun m => phase t (theta m)))
  have hmain := finite_integral_l1_bound g (bandRows D R) (S.product T)
    (fun p q => coefficient a b p.1 p.2 q.1 q.2)
    (logArgument eta theta delta epsilon) H hpacket
  have heq : smoothBandMean D R S T a b F scale eta theta delta epsilon =
      (bandRows D R).sum (fun p => norm ((S.product T).sum (fun q =>
        coefficient a b p.1 p.2 q.1 q.2 *
          g (logArgument eta theta delta epsilon p q)))) := by
    unfold smoothBandMean
    apply Finset.sum_congr rfl
    intro p hp
    apply congrArg norm
    apply Finset.sum_congr rfl
    intro q hq
    rw [hpoint _ (hArgs p hp q hq)]
  calc
    _ <= H * integral volume (fun t : Real => norm ((FourierTransform.fourier g) t)) :=
      heq.trans_le hmain
    _ <= H * (CLog / (1 + scale) ^ A) := mul_le_mul_of_nonneg_left hmass hH
    _ = _ := by dsimp only [H]; ring

end PrimeFactorOscillations.QuadraticSmoothBandEstimate

