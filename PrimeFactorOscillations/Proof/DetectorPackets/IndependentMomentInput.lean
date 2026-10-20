/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile

/-!
# IndependentMomentInput

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-!
The existing seven-eighths theorem supplies the upper bound needed by the
terminal moment certificate. This lets the arithmetic allowance Delta be
chosen independently of beta-7/8. The lower beta hypothesis is retained
explicitly; it is compatible with the bad-zero case for the active target.
No stronger zero-free boundary is asserted here.
-/


noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
open OAI.SevenEighths

namespace PrimeFactorOscillations.FlexibleMomentInput

open HeckeFamily Parameters ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands
open CenteredMomentEnergyCertifiedExistence CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorPlainSlotProfile

theorem reference_beta_upper : HeckeZeroSupremum.beta <= (7 / 8 : Real) := by
  apply csSup_le HeckeZeroSupremum.zeroSet_nonempty
  intro x hx
  have hc := Set.mem_insert_iff.mp hx
  cases hc with
  | inl hs =>
    subst x
    norm_num
  | inr hz =>
    let eta := Classical.choose hz
    have hEta := Classical.choose_spec hz
    let s := Classical.choose hEta
    have hs0 := Classical.choose_spec hEta
    by_contra h
    have hs : (7 / 8 : Real) < s.re := by
      rw [hs0.2.2.2]
      exact lt_of_not_ge h
    exact hecke_of_chosen_moments
      (chosen_moments_of_certified ProbeFinalAssemblyUnconditional.detector_certified_bands)
      eta s hs hs0.2.1 hs0.2.2.1

theorem source_moments_flexible {Delta : Real} (D : HighData Delta)
    (F : SourceData D) (counts : CountParameters F.modulus Top.top D.t)
    (hbad : (3 / 4 : Real) < HeckeZeroSupremum.beta)
    (hfine : forall j, D.ell j <= detectorMesh Delta D.t / 200) :
    exists J : Real, 0 <= J /\
      forall eta : Character, exists C : Real, 0 < C /\
        forall tau : Real, 0 < tau -> tau <= 1 ->
          Filter.Eventually
            (fun Z : Real =>
              SourceMomentBound F counts eta Z tau
                (C * (1 + Z ^ (2 * tau)) ^ J) (Z ^ (2 * tau)))
            Filter.atTop := by
  have hDelta : 0 < Delta := by
    linarith only [D.t_pos, D.t_delta]
  have hpz := plain_inputs F (by
    intro bPhi hbPhi
    have hp := fixed_parameters D
    exact terminal_certificate F.modulus Top.top le_top
      (fun x => conj (F.W x)) 1 2 (1 / 4) (9 / 4) bPhi 0 1
      (33 / 50) (33 / 50) 2 (kappaPlain D) (stageError D)
      (by norm_num) (conjugate_source_support F)
      (Complex.conjCLE.contDiff.comp (F.W.smooth Top.top))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hbPhi (by norm_num) (by norm_num) hp.2.2.2.2.1.le hp.2.2.1
      (by linarith only [hbad])
      (by unfold kappaPlain
          linarith only [reference_beta_upper, hDelta.le]))
  exact source_moments F counts (detectorMesh Delta D.t)
    (detectorMesh_pos hDelta D.t_pos) hfine hpz.1 hpz.2

theorem exists_source_moments_flexible (Delta : Real) (hDelta : 0 < Delta)
    (hbad : (3 / 4 : Real) < HeckeZeroSupremum.beta) :
    exists D : HighData Delta, exists F : SourceData D,
      exists counts : CountParameters F.modulus Top.top D.t,
        exists J : Real, 0 <= J /\
          forall eta : Character, exists C : Real, 0 < C /\
            forall tau : Real, 0 < tau -> tau <= 1 ->
              Filter.Eventually
                (fun Z : Real =>
                  SourceMomentBound F counts eta Z tau
                    (C * (1 + Z ^ (2 * tau)) ^ J) (Z ^ (2 * tau)))
                Filter.atTop := by
  have hdata := exists_high_data_fine Delta hDelta (detectorMesh Delta)
    (fun t ht => detectorMesh_pos hDelta ht)
  let D := Classical.choose hdata
  have hD := Classical.choose_spec hdata
  let F := Classical.choice (exists_source_data D)
  let counts := Classical.choice (source_count_parameters F)
  exact Exists.intro D (Exists.intro F (Exists.intro counts
    (source_moments_flexible D F counts hbad hD)))

end PrimeFactorOscillations.FlexibleMomentInput
