/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.PrimeRows.Continuation
import PrimeFactorOscillations.Proof.ProbeEuler.Canonical
import PrimeFactorOscillations.Proof.ProbeEuler.Holomorphic
import PrimeFactorOscillations.Proof.ProbeEuler.Ramified
import PrimeFactorOscillations.Proof.ProbeEuler.Unramified

/-!
# CanonicalEulerProduct

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
# The actual masked Euler correction in the extended region

Identifies the source product over prime ideals outside S with the normal
product of the exact masked factors. The ramified factors then give the
actual continued correction, without dividing by any local correction.
This is a continuation input, not a zero-free-region conclusion.
-/


noncomputable section
namespace PrimeFactorOscillations.CanonicalEulerContinuation
open OAI OAI.SevenEighths
open OAI.SevenEighths.HeckeFamily OAI.SevenEighths.HeckeInverseAmplification
open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.ProbeEuler
open OAI.SevenEighths.ProbeHighRowFamily
open OAI.CanonicalRowCompletion OAI.CompletedGauss
local notation "O" => OAI.ActualEisensteinCubic.O

private theorem norm_tprod_defect_bound {I : Type*}
    (f : I -> Complex) (b : I -> Real) (hb0 : forall i, 0 <= b i)
    (hb : Summable b) (hf : forall i, norm (f i - 1) <= b i) :
    norm (tprod f - 1) <= Real.exp (tsum b) - 1 := by
  have hdev : Summable (fun i => norm (f i - 1)) :=
    hb.of_nonneg_of_le (fun i => norm_nonneg _) hf
  have hm : Multipliable f := by
    have h := multipliable_one_add_of_summable hdev
    simpa only [add_sub_cancel] using h
  have hfinite (F : Finset I) :
      norm (F.prod f - 1) <= Real.exp (tsum b) - 1 := by
    have hh := Finset.norm_prod_one_add_sub_one_le F (fun i => f i - 1)
    simp only [add_sub_cancel] at hh
    have hs : F.sum (fun i => norm (f i - 1)) <= tsum b :=
      (Finset.sum_le_sum (fun i _ => hf i)).trans
        (Summable.sum_le_tsum F (fun i _ => hb0 i) hb)
    exact hh.trans (sub_le_sub_right (Real.exp_le_exp.mpr hs) 1)
  have hp : Filter.Tendsto (fun F : Finset I => F.prod f) Filter.atTop
      (nhds (tprod f)) := hm.hasProd
  have hl : Filter.Tendsto (fun F : Finset I => norm (F.prod f - 1)) Filter.atTop
      (nhds (norm (tprod f - 1))) :=
    (continuous_norm.tendsto _).comp (hp.sub tendsto_const_nhds)
  exact le_of_tendsto hl (Filter.Eventually.of_forall hfinite)

def unramifiedUniformConstant : Real :=
  Real.exp (tsum (fun P : SourcePrime =>
    200 * FullEulerContinuation.sourceNorm P ^ (-(149 / 100) : Real)))

private theorem source_factor_uniform_defect (eta : SourceCharacter) (u : FreeRow)
    (P : SourcePrime) (x w z : Complex)
    (hQ : (4 : Real) <= FullEulerContinuation.sourceNorm P)
    (hx : (3 / 4 : Real) <= x.re) (hw : (19 / 20 : Real) <= w.re)
    (hz : (33 / 200 : Real) <= z.re) :
    norm (unramifiedFactor eta u P x w z - 1) <=
      200 * FullEulerContinuation.sourceNorm P ^ (-(149 / 100) : Real) := by
  rw [masked_unramifiedFactor]
  exact FullEulerContinuation.unramified_uniform_defect
    (FullEulerContinuation.sourceNorm P)
    (maskedCoeff u P (actualAPhase eta (primaryGenerator P.val)))
    (maskedCoeff u P (idealCoeff eta P.val))
    (maskedCoeff u P (idealRowHom u.val P.val)) x w z hQ
    (maskedCoeff_norm_le u P _ (actualAPhase_norm_le_one eta (primaryGenerator P.val)))
    (maskedCoeff_norm_le u P _ (idealCoeff_norm_le_one eta P.val))
    (maskedCoeff_norm_le u P _ (idealRowHom_norm u.val P.val)) hx hw hz

theorem unramifiedProduct_extended_bound
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (eta : SourceCharacter) (u : FreeRow) (x w z : Complex)
    (hx : (3 / 4 : Real) <= x.re) (hw : (19 / 20 : Real) <= w.re)
    (hz : (33 / 200 : Real) <= z.re) :
    norm (unramifiedProduct S eta u x w z) <= unramifiedUniformConstant := by
  classical
  let b : SourcePrime -> Real := fun P =>
    200 * FullEulerContinuation.sourceNorm P ^ (-(149 / 100) : Real)
  have hb0 (P : SourcePrime) : 0 <= b P := by
    dsimp [b, FullEulerContinuation.sourceNorm]
    positivity
  have hb : Summable b :=
    FullEulerContinuation.source_norm_majorant_summable.mul_left 200
  let I := {P : SourcePrime // Not (Membership.mem S P.val)}
  let f : I -> Complex := fun P => unramifiedFactor eta u P.val x w z
  have hbi : Summable (fun P : I => b P.val) :=
    hb.comp_injective Subtype.val_injective
  have hf (P : I) : norm (f P - 1) <= b P.val := by
    exact source_factor_uniform_defect eta u P.val x w z
      (by
        change (4 : Real) <= (Ideal.absNorm P.val.val : Real)
        exact_mod_cast (hS.tail.norm_four P.val P.property)) hx hw hz
  have hsub : tsum (fun P : I => b P.val) <= tsum b := by
    apply le_of_tendsto hbi.hasSum
    apply Filter.Eventually.of_forall
    intro F
    have heq : F.sum (fun P : I => b P.val) =
        (F.image (fun P : I => P.val)).sum b := by
      rw [Finset.sum_image]
      intro a ha c hc hac
      exact Subtype.ext hac
    rw [heq]
    exact Summable.sum_le_tsum _ (fun P _ => hb0 P) hb
  have hd := norm_tprod_defect_bound f (fun P : I => b P.val)
    (fun P => hb0 P.val) hbi hf
  have ht := norm_add_le (tprod f - 1) (1 : Complex)
  simp only [sub_add_cancel, norm_one] at ht
  change norm (tprod f) <= Real.exp (tsum b)
  calc
    _ <= norm (tprod f - 1) + 1 := ht
    _ <= Real.exp (tsum (fun P : I => b P.val)) := by linarith [hd]
    _ <= Real.exp (tsum b) := Real.exp_le_exp.mpr hsub

theorem continuedCorrection_extended_subpower (eps : Real) (heps : 0 < eps) :
    Exists (fun C : Real => 0 < C /\
      forall (S : Finset (Ideal O)) (hS : SourceExclusions S)
        (eta : SourceCharacter) (u : FreeRow) (x w z : Complex),
        (3 / 4 : Real) <= x.re -> (19 / 20 : Real) <= w.re ->
          (33 / 200 : Real) <= z.re ->
            norm (continuedCorrection S hS eta u x w z) <=
              C * ((Ideal.span {u.val} : Ideal O).absNorm : Real) ^ eps) := by
  have hr := RamifiedEulerContinuation.ramified_product_extended_subpower eps heps
  let C : Real := Classical.choose hr
  have hC : 0 < C := (Classical.choose_spec hr).1
  have hbound := (Classical.choose_spec hr).2
  refine Exists.intro (C * unramifiedUniformConstant) (And.intro ?_ ?_)
  . exact mul_pos hC (Real.exp_pos _)
  . intro S hS eta u x w z hx hw hz
    have hR := hbound S hS eta u x w z hx hw hz
    have hU := unramifiedProduct_extended_bound S hS eta u x w z hx hw hz
    have hpos : 0 <= C * ((Ideal.span {u.val} : Ideal O).absNorm : Real) ^ eps :=
      mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    rw [continuedCorrection, norm_mul]
    calc
      _ <= (C * ((Ideal.span {u.val} : Ideal O).absNorm : Real) ^ eps) *
          unramifiedUniformConstant := mul_le_mul hR hU (norm_nonneg _) hpos
      _ = _ := by ring

end PrimeFactorOscillations.CanonicalEulerContinuation
