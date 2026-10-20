/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CubeRowQuotientMean

/-!
# RawCubeRowCoefficients

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Classical

namespace OAI.SevenEighths.CubeRowQuotientMean

open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily HeckeRowClosure

abbrev sourcePrincipal : Character :=
  ProbePhysical.fixedSourcePrincipal (EmptyCollection.emptyCollection : Finset (Ideal O))
    (by simp)

theorem rawRow_element (u : HeckeInverseAmplification.FreeRow) (n : O) :
    elementCoeff (ProbeHighRowFamily.rawRow u) n =
      rowTwist (elementHom sourcePrincipal) ProbeHighRowFamily.rowMaskElement 1 u.val n := by
  exact (Classical.choose_spec
    (exists_row_character_with_conductor sourcePrincipal
      ProbeHighRowFamily.rowMaskElement 1 u.val ProbeHighRowFamily.rowMaskElement_ne_zero
      one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2 n

theorem rawRow_cube_ideal (u : HeckeInverseAmplification.FreeRow) (t : O)
    (hu : u.val = t ^ 3) (I : Ideal O) (hI : Admissible I) :
    idealCoeff (ProbeHighRowFamily.rawRow u) I =
      elementCoeff sourcePrincipal (CompletedGauss.primaryGenerator I) *
        (if IsCoprime I (Ideal.span {ProbeHighRowFamily.rowMaskElement}) then 1 else 0) *
        quadraticRow I t := by
  let n := CompletedGauss.primaryGenerator I
  have hn : Not (n = 0) := supported_primaryGenerator_ne_zero I (admissible_supported hI)
  have hs : Ideal.span {n} = I := (CompletedGauss.primaryGenerator_spec I hn).1
  calc
    idealCoeff (ProbeHighRowFamily.rawRow u) I =
        elementCoeff (ProbeHighRowFamily.rawRow u) n :=
      (congrArg (idealCoeff (ProbeHighRowFamily.rawRow u)) hs).symm.trans
        (idealCoeff_span _ hn)
    _ = rowTwist (elementHom sourcePrincipal) ProbeHighRowFamily.rowMaskElement 1 u.val n :=
      rawRow_element u n
    _ = _ := by
      change elementCoeff sourcePrincipal n *
        idealRowHom (ProbeHighRowFamily.rowMaskElement ^ 6 * 1 ^ 4 * u.val)
          (Ideal.span {n}) = _
      rw [one_pow, mul_one, hu, hs,
        masked_cube_row I hI ProbeHighRowFamily.rowMaskElement t]
      ring


theorem rawRow_cube_supported (u : HeckeInverseAmplification.FreeRow) (t : O)
    (hu : u.val = t ^ 3) (I : Ideal O) (hI : Supported I) :
    idealCoeff (ProbeHighRowFamily.rawRow u) I =
      (elementCoeff sourcePrincipal (CompletedGauss.primaryGenerator I) *
        (if IsCoprime I (Ideal.span {ProbeHighRowFamily.rowMaskElement}) then 1 else 0)) *
        idealRowHom (t ^ 3) I := by
  let n := CompletedGauss.primaryGenerator I
  have hn : Not (n = 0) := supported_primaryGenerator_ne_zero I hI
  have hs : Ideal.span {n} = I := (CompletedGauss.primaryGenerator_spec I hn).1
  calc
    idealCoeff (ProbeHighRowFamily.rawRow u) I =
        elementCoeff (ProbeHighRowFamily.rawRow u) n :=
      (congrArg (idealCoeff (ProbeHighRowFamily.rawRow u)) hs).symm.trans
        (idealCoeff_span _ hn)
    _ = rowTwist (elementHom sourcePrincipal) ProbeHighRowFamily.rowMaskElement 1 u.val n :=
      rawRow_element u n
    _ = _ := by
      change elementCoeff sourcePrincipal n *
        idealRowHom (ProbeHighRowFamily.rowMaskElement ^ 6 * 1 ^ 4 * u.val)
          (Ideal.span {n}) = _
      rw [one_pow, mul_one, hu, hs, idealRowHom_argument_mul,
        idealRowHom_sixth_mask ProbeHighRowFamily.rowMaskElement I hI]
      ring

def rowAmplitude (S : Finset (Ideal O)) (I : Ideal O) : Complex :=
  if forall P, Membership.mem S P -> IsCoprime I P then
    elementCoeff sourcePrincipal (CompletedGauss.primaryGenerator I) *
      (if IsCoprime I (Ideal.span {ProbeHighRowFamily.rowMaskElement}) then 1 else 0)
  else 0

theorem rowCharacter_cube_supported
    (S : Finset (Ideal O)) (hS : forall P, Membership.mem S P -> Prime P)
    (u : HeckeInverseAmplification.FreeRow) (t : O) (hu : u.val = t ^ 3)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
      rowAmplitude S I * idealRowHom (t ^ 3) I := by
  change idealCoeff ((ProbeHighRowFamily.rawRow u).excludePrimes S hS) I = _
  rw [idealCoeff_excludePrimes, rawRow_cube_supported u t hu I hI]
  simp only [rowAmplitude, ite_mul, zero_mul]

def characterPairedPacket
    (S : Finset (Ideal O)) (hS : forall P, Membership.mem S P -> Prime P)
    (u : HeckeInverseAmplification.FreeRow) (A B : Finset (Ideal O))
    (a b : Ideal O -> Complex) : Complex :=
  Finset.sum A (fun I => idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I * a I) *
    Finset.sum B (fun J =>
      (idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) J) ^ (-1 : Int) * b J)

theorem character_paired_identity
    (S : Finset (Ideal O)) (hS : forall P, Membership.mem S P -> Prime P)
    (u : HeckeInverseAmplification.FreeRow) (t : O) (hu : u.val = t ^ 3)
    (A B : Finset (Ideal O)) (a b : Ideal O -> Complex)
    (hA : forall I, Membership.mem A I -> Supported I)
    (hB : forall J, Membership.mem B J -> Admissible J) :
    characterPairedPacket S hS u A B a b =
      pairedPacket A B (fun I => rowAmplitude S I * a I)
        (fun J => (rowAmplitude S J) ^ (-1 : Int) * b J) t := by
  have hp : Finset.sum A (fun I =>
      idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I * a I) =
      Finset.sum A (fun I => idealRowHom (t ^ 3) I * (rowAmplitude S I * a I)) := by
    apply Finset.sum_congr rfl
    intro I hI
    rw [rowCharacter_cube_supported S hS u t hu I (hA I hI)]
    ring
  have hi : Finset.sum B (fun J =>
      (idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) J) ^ (-1 : Int) * b J) =
      Finset.sum B (fun J =>
        (idealRowHom (t ^ 3) J) ^ (-1 : Int) *
          ((rowAmplitude S J) ^ (-1 : Int) * b J)) := by
    apply Finset.sum_congr rfl
    intro J hJ
    rw [rowCharacter_cube_supported S hS u t hu J (admissible_supported (hB J hJ))]
    simp only [zpow_neg_one, mul_inv_rev]
    ring
  unfold characterPairedPacket pairedPacket
  rw [hp, hi]


universe u

theorem actual_character_paired_sieve (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M U V : Real), 1 <= M -> 1 <= U -> 1 <= V ->
      forall (S : Finset (Ideal O)) (hS : forall P, Membership.mem S P -> Prime P)
        {r : Type u} [Fintype r] (rows : r -> Ideal O)
        (ur : r -> HeckeInverseAmplification.FreeRow),
      (forall x, (ur x).val = (CompletedGauss.primaryGenerator (rows x)) ^ 3) ->
      forall (A B : Finset (Ideal O)) (a b : Ideal O -> Complex),
      Function.Injective rows ->
      (forall x, Admissible (rows x) /\ (Ideal.absNorm (rows x) : Real) <= M) ->
      (forall I, Membership.mem A I ->
        Supported I /\ (Ideal.absNorm I : Real) <= U) ->
      (forall J, Membership.mem B J ->
        Admissible J /\ (Ideal.absNorm J : Real) <= V) ->
      Finset.sum Finset.univ (fun x =>
        norm (characterPairedPacket S hS (ur x) A B a b) ^ 2) <=
        2 * (C * (M * (U * V)) ^ eps * (M + U * V) *
          goodMass (A.product B) pairCol
            (pairCoeff (fun I => rowAmplitude S I * a I)
              (fun J => (rowAmplitude S J) ^ (-1 : Int) * b J))) +
        2 * Finset.sum Finset.univ (fun x =>
          norm (remainderPacket (A.product B) pairCol
            (pairCoeff (fun I => rowAmplitude S I * a I)
              (fun J => (rowAmplitude S J) ^ (-1 : Int) * b J))
            (CompletedGauss.primaryGenerator (rows x))) ^ 2) := by
  have hc := paired_cube_sieve.{u} eps heps
  let C := hc.choose
  have hC := hc.choose_spec.1
  have hCs := hc.choose_spec.2
  refine Exists.intro C (And.intro hC ?_)
  intro M U V hM hU hV S hS r hr rows ur hur A B a b hrows hrow hA hB
  have hb := hCs M U V hM hU hV rows A B
    (fun I => rowAmplitude S I * a I)
    (fun J => (rowAmplitude S J) ^ (-1 : Int) * b J)
    hrows hrow (fun I hI => (hA I hI).2) hB
  have heq (x : r) :
      characterPairedPacket S hS (ur x) A B a b =
      pairedPacket A B (fun I => rowAmplitude S I * a I)
        (fun J => (rowAmplitude S J) ^ (-1 : Int) * b J)
        (CompletedGauss.primaryGenerator (rows x)) :=
    character_paired_identity S hS (ur x) _ (hur x) A B a b
      (fun I hI => (hA I hI).1) (fun J hJ => (hB J hJ).1)
  simpa only [heq] using hb

end OAI.SevenEighths.CubeRowQuotientMean
