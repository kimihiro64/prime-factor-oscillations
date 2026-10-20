/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.SelectedPrimePuncture
import PrimeFactorOscillations.Proof.DetectorPackets.SexticToQuadraticLocal

/-!
# PuncturedMarkedSeries

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
-/

/-!
# The actual marked local series after physical puncturing

The projector acts on the full frequency u*p^(6*m), before the
sixth-power part is removed. Its exact action sets the frequency
geometric coordinate V to zero in the actual marked row series.
The existing closed form then reduces to -(eta/rho)*X exactly.
No contour estimate or reciprocal-series truncation is used here.
-/

set_option maxHeartbeats 800000

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.PuncturedMarkedSeries

open ProbeEuler SelectedPrimePuncture

local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : Not (Membership.mem (Ideal.span {p}) ConcretePrimeRowBridge.goodLambda))

theorem term_zero_V (eta a X W V rho : Complex) (j e l k m : Nat) :
    rowMarkedTerm p hp hg eta a X W 0 rho j e l k m =
      if m=0 then rowMarkedTerm p hp hg eta a X W V rho j e l k 0 else 0 := by
  by_cases hm : m=0
  . subst m
    simp [rowMarkedTerm, rowWeightedScalar, weightedScalar]
  . simp [rowMarkedTerm, rowWeightedScalar, weightedScalar, hm]

variable [Fintype (SelectedPrimePuncture.Residues p)]

def series (u : O) (eta a X W V rho : Complex) : Complex :=
  Finset.univ.sum fun e : Fin 2 =>
    tsum fun l : Nat => tsum fun k : Nat => tsum fun m : Nat =>
      CubicEisenstein.finiteTranslationMultiplier (shift p) weight (u*p^(6*m))*
        rowMarkedTerm p hp hg eta a X W V rho 0 e.val l k m

theorem punctured_term (u : O) (eta a X W V rho : Complex) (e l k m : Nat) :
    CubicEisenstein.finiteTranslationMultiplier (shift p) weight (u*p^(6*m))*
      rowMarkedTerm p hp hg eta a X W V rho 0 e l k m =
    CubicEisenstein.finiteTranslationMultiplier (shift p) weight u*
      rowMarkedTerm p hp hg eta a X W 0 rho 0 e l k m := by
  rw [sixth_frequency_multiplier p hp.ne_zero u m, term_zero_V p hp hg eta a X W V rho]
  by_cases hm : m=0
  . subst m
    simp
  . simp [hm]

theorem series_eq_zero_V (u : O) (eta a X W V rho : Complex) :
    series p hp hg u eta a X W V rho =
      CubicEisenstein.finiteTranslationMultiplier (shift p) weight u*
        rowMarkedSeries p hp hg eta a X W 0 rho 0 := by
  unfold series rowMarkedSeries rowInner
  simp_rw [punctured_term p hp hg u eta a X W V rho, tsum_mul_left]
  rw [<-Finset.mul_sum]

theorem zero_V_closed
    (hc : Not (ringChar (SelectedPrimePuncture.Residues p)=2))
    (eta a X W rho : Complex) (hrho : rho^6=1) :
    rowMarkedSeries p hp hg eta a X W 0 rho 0= -(eta/rho)*X := by
  have hV : norm (0:Complex)<1 := by norm_num
  have hR : norm (evenRatio ((Ideal.span {p}:Ideal O).absNorm:Complex) a X 0)<1 := by
    simp [evenRatio]
  rw [rowMarkedSeries_eq_closed p hp hg hc eta a X W 0 rho hrho hV hR 0 (by decide),
    rowClosedMarked_unramified p hp hg hc eta a X W 0 rho hrho hV hR]
  simp [evenRatio, markedFactor]

theorem series_closed
    (hc : Not (ringChar (SelectedPrimePuncture.Residues p)=2))
    (u : O) (eta a X W V rho : Complex) (hrho : rho^6=1) :
    series p hp hg u eta a X W V rho =
      CubicEisenstein.finiteTranslationMultiplier (shift p) weight u*(-(eta/rho)*X) := by
  rw [series_eq_zero_V p hp hg u eta a X W V rho,
    zero_V_closed p hp hg hc eta a X W rho hrho]

end OAI.SevenEighths.PuncturedMarkedSeries
