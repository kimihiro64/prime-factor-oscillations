/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.RowRadicalConductor
import OAI.NumberTheory.DirichletL.QuadraticSieve.SquareParts

/-!
# QuadraticLowKernelConductor

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
# Actual conductor bound on low quadratic-kernel rows

The existing primitive-row theorem retains the original coprimality mask.
This consumer bounds its radical conductor by the squarefree-kernel size.
No L-function numerator, reciprocal, mask or row is discarded.
-/

set_option maxHeartbeats 800000

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.QuadraticLowKernelConductor

open HeckeFamily QuadraticSquarefreeKernel ProbeRowRadicalConductor

local notation "O" => HeckeFamily.O

theorem radical_norm_square (I : Ideal O) (hI : Not (I=0)) :
    I.radical.absNorm^2 <= I.absNorm*(squarefreePart I).absNorm := by
  let A := squarePart I
  let B := squarefreePart I
  have he : A^2*B=I := squarePart_sq_mul_squarefreePart I
  have hA : Not (A=0) := by
    intro h
    apply hI
    rw [<-he, h, zero_pow (by decide), zero_mul]
  have hB : Not (B=0) := by
    intro h
    apply hI
    rw [<-he, h, mul_zero]
  have hAB : Not (A*B=0) := mul_ne_zero hA hB
  have hsmall : A*B <= I.radical := by
    rw [<-he, Ideal.radical_mul, Ideal.radical_pow A (by decide : Not ((2:Nat)=0))]
    exact Ideal.mul_le_inf.trans (inf_le_inf A.le_radical B.le_radical)
  let := Ring.HasFiniteQuotients.finiteQuotient hAB
  have hn := FiniteConductor.absNorm_le_of_le hsmall
  have hn2 : I.radical.absNorm^2 <= (A.absNorm*B.absNorm)^2 := by
    have hs := Nat.mul_self_le_mul_self hn
    simpa only [map_mul, pow_two] using hs
  have heN : A.absNorm^2*B.absNorm=I.absNorm := by
    simpa only [map_mul, map_pow] using congrArg Ideal.absNorm he
  calc
    I.radical.absNorm^2 <= (A.absNorm*B.absNorm)^2 := hn2
    _ = (A.absNorm^2*B.absNorm)*B.absNorm := by ring
    _ = I.absNorm*B.absNorm := by rw [heN]

theorem primitive_squared (S : Finset (Ideal O))
    (hS : forall P, Membership.mem S P -> Prime P)
    (u : HeckeInverseAmplification.FreeRow) :
    exists psi : Character,
      (ProbeHighRowFamily.rowCharacter S hS u).modulus <= psi.modulus /\
      FiniteFourier.IsPrimitiveOnIdeals psi.residue /\
      psi.modulus.absNorm^2 <= (fixedConductorConstant S)^2 *
        (Ideal.span {u.val}:Ideal O).absNorm *
        (squarefreePart (Ideal.span {u.val}:Ideal O)).absNorm /\
      forall I : Ideal O,
        idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
          if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
          then idealCoeff psi I else 0 := by
  classical
  let psi := Classical.choose (rowCharacter_primitive_radical S hS u)
  have hp := Classical.choose_spec (rowCharacter_primitive_radical S hS u)
  have hI : Not ((Ideal.span {u.val}:Ideal O)=0) :=
    Ideal.span_singleton_eq_bot.not.mpr u.property.1
  have hb := radical_norm_square (Ideal.span {u.val}) hI
  refine Exists.intro psi (And.intro hp.1 (And.intro hp.2.1 (And.intro ?_ hp.2.2.2)))
  calc
    psi.modulus.absNorm^2 <=
        (fixedConductorConstant S * (Ideal.span {u.val}:Ideal O).radical.absNorm)^2 := by
      have hn : psi.modulus.absNorm <= fixedConductorConstant S *
          (Ideal.span {u.val}:Ideal O).radical.absNorm := hp.2.2.1
      simpa only [pow_two] using Nat.mul_self_le_mul_self hn
    _ = (fixedConductorConstant S)^2 * (Ideal.span {u.val}:Ideal O).radical.absNorm^2 := by ring
    _ <= (fixedConductorConstant S)^2 *
        ((Ideal.span {u.val}:Ideal O).absNorm *
          (squarefreePart (Ideal.span {u.val}:Ideal O)).absNorm) :=
      Nat.mul_le_mul_left _ hb
    _ = _ := by ring

theorem low_kernel_conductor (S : Finset (Ideal O))
    (hS : forall P, Membership.mem S P -> Prime P)
    (u : HeckeInverseAmplification.FreeRow) (U K : Real)
    (hU : ((Ideal.span {u.val}:Ideal O).absNorm:Real) <= U)
    (hK : ((squarefreePart (Ideal.span {u.val}:Ideal O)).absNorm:Real) <= K) :
    exists psi : Character,
      (ProbeHighRowFamily.rowCharacter S hS u).modulus <= psi.modulus /\
      FiniteFourier.IsPrimitiveOnIdeals psi.residue /\
      (psi.modulus.absNorm:Real) <= (fixedConductorConstant S:Real)*Real.sqrt (U*K) /\
      forall I : Ideal O,
        idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
          if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
          then idealCoeff psi I else 0 := by
  classical
  let psi := Classical.choose (primitive_squared S hS u)
  have hp := Classical.choose_spec (primitive_squared S hS u)
  have hUn : 0 <= U := (Nat.cast_nonneg _).trans hU
  have hKn : 0 <= K := (Nat.cast_nonneg _).trans hK
  have hs : (psi.modulus.absNorm:Real)^2 <= (fixedConductorConstant S:Real)^2 *
      ((Ideal.span {u.val}:Ideal O).absNorm:Real) *
      ((squarefreePart (Ideal.span {u.val}:Ideal O)).absNorm:Real) := by
    exact_mod_cast hp.2.2.1
  have hprod : ((Ideal.span {u.val}:Ideal O).absNorm:Real) *
      ((squarefreePart (Ideal.span {u.val}:Ideal O)).absNorm:Real) <= U*K :=
    mul_le_mul hU hK (Nat.cast_nonneg _) hUn
  have hs' : (psi.modulus.absNorm:Real)^2 <=
      (fixedConductorConstant S:Real)^2*(U*K) := by
    calc
      _ <= (fixedConductorConstant S:Real)^2 *
          (((Ideal.span {u.val}:Ideal O).absNorm:Real) *
          ((squarefreePart (Ideal.span {u.val}:Ideal O)).absNorm:Real)) := by
        nlinarith only [hs]
      _ <= _ := mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
  have hr := Real.sq_sqrt (mul_nonneg hUn hKn)
  have hroot := Real.sqrt_nonneg (U*K)
  have hC : 0 <= (fixedConductorConstant S:Real) := Nat.cast_nonneg _
  have hpsi : 0 <= (psi.modulus.absNorm:Real) := Nat.cast_nonneg _
  refine Exists.intro psi (And.intro hp.1 (And.intro hp.2.1 (And.intro ?_ hp.2.2.2)))
  nlinarith [mul_nonneg hC hroot]

end OAI.SevenEighths.QuadraticLowKernelConductor
