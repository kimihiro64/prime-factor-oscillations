/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import OAI.NumberTheory.DirichletL.PrimeRows.Continuation
import PrimeFactorOscillations.Proof.ProbeEuler.Holomorphic
import PrimeFactorOscillations.Proof.ProbeEuler.Unramified

/-!
# The actual masked Euler correction in the extended region

Identifies the source product over prime ideals outside S with the normal
product of the exact masked factors. The ramified factors then give the
actual continued correction, without dividing by any local correction.
This is a continuation input, not a zero-free-region conclusion.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CanonicalEulerContinuation
open OAI OAI.SevenEighths
open OAI.SevenEighths.HeckeFamily OAI.SevenEighths.HeckeInverseAmplification
open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.ProbeEuler
open OAI.SevenEighths.ProbeHighRowFamily
open OAI.CanonicalRowCompletion OAI.CompletedGauss
local notation "O" => OAI.ActualEisensteinCubic.O

abbrev SourcePrime := OAI.SmoothMobiusCorrection.PrimeIdeal
abbrev SourceCharacter := OAI.SevenEighths.HeckeFamily.Character

theorem unramifiedClosed_zero_phases (Q : Real) (x w z : Complex) :
    unramifiedClosed Q 0 0 0 x w z = 1 := by
  simp [unramifiedClosed, coordR, coordW, coordD, coordK, markedFactor,
    OAI.SevenEighths.ProbeLocal.continuedCorrection]

def maskedCoeff (u : FreeRow) (P : SourcePrime) (a : Complex) : Complex := by
  classical
  exact if Dvd.dvd P.val (Ideal.span {u.val} : Ideal O) then 0 else a

theorem maskedCoeff_norm_le (u : FreeRow) (P : SourcePrime) (a : Complex)
    (ha : norm a <= 1) : norm (maskedCoeff u P a) <= 1 := by
  classical
  unfold maskedCoeff
  split_ifs
  . norm_num
  . exact ha

theorem masked_unramifiedFactor (eta : SourceCharacter) (u : FreeRow)
    (P : SourcePrime) (x w z : Complex) :
    unramifiedFactor eta u P x w z =
      unramifiedClosed (Ideal.absNorm P.val)
        (maskedCoeff u P (actualAPhase eta (primaryGenerator P.val)))
        (maskedCoeff u P (idealCoeff eta P.val))
        (maskedCoeff u P (idealRowHom u.val P.val)) x w z := by
  classical
  by_cases h : Dvd.dvd P.val (Ideal.span {u.val} : Ideal O)
  . simp [unramifiedFactor, maskedCoeff, h, unramifiedClosed_zero_phases]
  . simp [unramifiedFactor, maskedCoeff, h, idealUnramifiedCorrection]

theorem unramifiedProduct_extended_analyticOnNhd
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (eta : SourceCharacter) (u : FreeRow)
    (X W Z : Complex -> Complex) (U : Set Complex) (hU : IsOpen U)
    (hX : AnalyticOnNhd Complex X U) (hW : AnalyticOnNhd Complex W U)
    (hZ : AnalyticOnNhd Complex Z U)
    (hRe : forall t, Membership.mem U t ->
      (3 / 4 : Real) <= (X t).re /\ (19 / 20 : Real) <= (W t).re /\
        (33 / 200 : Real) <= (Z t).re) :
    AnalyticOnNhd Complex
      (fun t => unramifiedProduct S eta u (X t) (W t) (Z t)) U := by
  classical
  let I := {P : SourcePrime // Not (Membership.mem S P.val)}
  let Q : I -> Real := fun P => FullEulerContinuation.sourceNorm P.val
  let A : I -> Complex := fun P =>
    maskedCoeff u P.val (actualAPhase eta (primaryGenerator P.val.val))
  let E : I -> Complex := fun P => maskedCoeff u P.val (idealCoeff eta P.val.val)
  let V : I -> Complex := fun P => maskedCoeff u P.val (idealRowHom u.val P.val.val)
  have heq : (fun t => unramifiedProduct S eta u (X t) (W t) (Z t)) =
      (fun t => tprod (fun P : I =>
        unramifiedClosed (Q P) (A P) (E P) (V P) (X t) (W t) (Z t))) := by
    funext t
    apply tprod_congr
    intro P
    exact masked_unramifiedFactor eta u P.val (X t) (W t) (Z t)
  rw [heq]
  apply FullEulerContinuation.analyticOnNhd_unramifiedProduct Q A E V X W Z U
  . intro P
    change (4 : Real) <= (Ideal.absNorm P.val.val : Real)
    exact_mod_cast (hS.tail.norm_four P.val P.property)
  . intro P
    exact maskedCoeff_norm_le u P.val _
      (actualAPhase_norm_le_one eta (primaryGenerator P.val.val))
  . intro P
    exact maskedCoeff_norm_le u P.val _ (idealCoeff_norm_le_one eta P.val.val)
  . intro P
    exact maskedCoeff_norm_le u P.val _ (idealRowHom_norm u.val P.val.val)
  . exact FullEulerContinuation.source_norm_majorant_summable.comp_injective
      Subtype.val_injective
  . exact hU
  . exact hX
  . exact hW
  . exact hZ
  . exact hRe

theorem continuedCorrection_extended_analyticOnNhd
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (eta : SourceCharacter) (u : FreeRow)
    (X W Z : Complex -> Complex) (U : Set Complex) (hU : IsOpen U)
    (hX : AnalyticOnNhd Complex X U) (hW : AnalyticOnNhd Complex W U)
    (hZ : AnalyticOnNhd Complex Z U)
    (hRe : forall t, Membership.mem U t ->
      (3 / 4 : Real) <= (X t).re /\ (19 / 20 : Real) <= (W t).re /\
        (33 / 200 : Real) <= (Z t).re) :
    AnalyticOnNhd Complex
      (fun t => continuedCorrection S hS eta u (X t) (W t) (Z t)) U := by
  change AnalyticOnNhd Complex
    (fun t => ramifiedProduct S hS eta u (X t) (W t) (Z t) *
      unramifiedProduct S eta u (X t) (W t) (Z t)) U
  apply AnalyticOnNhd.mul
  . exact RamifiedHolomorphicContinuation.ramifiedProduct_extended_analyticOnNhd
      S hS eta u X W Z U hU hX hW hZ
      (fun t ht => And.intro (hRe t ht).1 (hRe t ht).2.2)
  . exact unramifiedProduct_extended_analyticOnNhd
      S hS eta u X W Z U hU hX hW hZ hRe

end PrimeFactorOscillations.CanonicalEulerContinuation
