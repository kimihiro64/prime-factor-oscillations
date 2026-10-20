/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Hecke.Origin
import OAI.NumberTheory.DirichletL.PrimeRows.Euler
import PrimeFactorOscillations.Proof.DetectorPackets.QuadraticLowKernelConductor

/-!
# LowKernelQuotientTransport

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
# Reduced conductors for the complete numerator-reciprocal pair

Both characters have exactly the original element coefficients, including
all excluded-prime masks. Equality assumes positive real part and avoids
one. It is unconditional and does not bound inverse L near its zeros.
-/

set_option maxHeartbeats 800000

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.LowKernelQuotientTransport

open HeckeFamily ProbeRowRadicalConductor QuadraticLowKernelConductor
open QuadraticSquarefreeKernel

local notation "O" => HeckeFamily.O

theorem quotient_eq_of_elements (chi rho target tau : Character)
    (heN : forall n, elementCoeff chi n=elementCoeff rho n)
    (heD : forall n, elementCoeff target n=elementCoeff tau n)
    (x w : Complex) (hx : 0 < x.re) (hw : 0 < w.re)
    (hx1 : Not (x=1)) (hw1 : Not (w=1)) :
    HeckeOrigin.continued chi w * HeckeReciprocal.reciprocal target x =
      HeckeOrigin.continued rho w * HeckeReciprocal.reciprocal tau x := by
  have hx0 : Not (x=0) := by intro h; simp [h] at hx
  have hw0 : Not (w=0) := by intro h; simp [h] at hw
  rw [HeckeOrigin.continued_eq chi hw0 hw1,
    HeckeOrigin.continued_eq rho hw0 hw1,
    HeckeReciprocal.reciprocal_eq_inv target hx0 hx1,
    HeckeReciprocal.reciprocal_eq_inv tau hx0 hx1]
  unfold LFunction
  rw [continuedLattice_eq_of_elementCoeff_eq chi rho heN hw hw1,
    continuedLattice_eq_of_elementCoeff_eq target tau heD hx hx1]

theorem paired_reduced_conductors (S : Finset (Ideal O))
    (hS : forall P, Membership.mem S P -> Prime P)
    (eta : Character) (u : HeckeInverseAmplification.FreeRow) :
    exists rho tau : Character,
      rho.modulus.absNorm^2 <= (fixedConductorConstant S)^2 *
        (Ideal.span {u.val}:Ideal O).absNorm *
        (squarefreePart (Ideal.span {u.val}:Ideal O)).absNorm /\
      tau.modulus.absNorm^2 <= (eta.modulus.absNorm*fixedConductorConstant S)^2 *
        (Ideal.span {u.val}:Ideal O).absNorm *
        (squarefreePart (Ideal.span {u.val}:Ideal O)).absNorm /\
      (forall n : O, elementCoeff (ProbeHighRowFamily.rowCharacter S hS u) n =
        elementCoeff rho n) /\
      (forall n : O,
        elementCoeff ((ProbeHighRowFamily.targetRow eta u).excludePrimes S hS) n =
        elementCoeff tau n) /\
      forall x w : Complex, 0 < x.re -> 0 < w.re ->
        Not (x=1) -> Not (w=1) ->
        HeckeOrigin.continued (ProbeHighRowFamily.rowCharacter S hS u) w *
          HeckeReciprocal.reciprocal
            ((ProbeHighRowFamily.targetRow eta u).excludePrimes S hS) x =
        HeckeOrigin.continued rho w * HeckeReciprocal.reciprocal tau x := by
  let theta := Classical.choose (rawRow_small_presentation u)
  have ht := Classical.choose_spec (rawRow_small_presentation u)
  let rho := theta.excludePrimes S hS
  let tau := (eta.product theta.inverse).excludePrimes S hS
  let R := (Ideal.span {u.val}:Ideal O).radical.absNorm
  let C := fixedConductorConstant S
  let B := (Finset.prod S fun P => P).absNorm
  have hn : theta.modulus.absNorm <= ProbeHighRowFamily.conductorConstant*R := ht.1
  have hN : rho.modulus.absNorm <= C*R := by
    change (theta.modulus * Finset.prod S (fun P => P)).absNorm <= C*R
    rw [map_mul]
    have hb := Nat.mul_le_mul_right B hn
    simpa only [B, C, fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm] using hb
  have hp : (eta.product theta.inverse).modulus.absNorm <=
      eta.modulus.absNorm*theta.modulus.absNorm := by
    have hmul : Not (eta.modulus*theta.modulus=0) :=
      mul_ne_zero eta.modulus_ne_bot theta.modulus_ne_bot
    let := Ring.HasFiniteQuotients.finiteQuotient hmul
    have hmain := FiniteConductor.absNorm_le_of_le
      (show eta.modulus*theta.modulus <= (eta.product theta.inverse).modulus
        from Ideal.mul_le_inf)
    simpa only [map_mul] using hmain
  have hD : tau.modulus.absNorm <= (eta.modulus.absNorm*C)*R := by
    change ((eta.product theta.inverse).modulus * Finset.prod S (fun P => P)).absNorm <= _
    rw [map_mul]
    have h1 := Nat.mul_le_mul_right B hp
    have h2 := Nat.mul_le_mul_right B (Nat.mul_le_mul_left eta.modulus.absNorm hn)
    exact h1.trans (by
      simpa only [B, C, fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm] using h2)
  have hI : Not ((Ideal.span {u.val}:Ideal O)=0) :=
    Ideal.span_singleton_eq_bot.not.mpr u.property.1
  have hr : R^2 <= (Ideal.span {u.val}:Ideal O).absNorm *
      (squarefreePart (Ideal.span {u.val}:Ideal O)).absNorm := radical_norm_square _ hI
  have sqbound (q d : Nat) (h : q <= d*R) :
      q^2 <= d^2*(Ideal.span {u.val}:Ideal O).absNorm *
        (squarefreePart (Ideal.span {u.val}:Ideal O)).absNorm := by
    calc
      q^2 <= (d*R)^2 := by simpa only [pow_two] using Nat.mul_self_le_mul_self h
      _ = d^2*R^2 := by ring
      _ <= d^2*((Ideal.span {u.val}:Ideal O).absNorm *
          (squarefreePart (Ideal.span {u.val}:Ideal O)).absNorm) := Nat.mul_le_mul_left _ hr
      _ = _ := by ring
  have heN : forall n : O,
      elementCoeff (ProbeHighRowFamily.rowCharacter S hS u) n = elementCoeff rho n :=
    equal_elements_excludePrimes _ theta ht.2 S hS
  have heT : forall n : O,
      elementCoeff (ProbeHighRowFamily.targetRow eta u) n =
        elementCoeff (eta.product theta.inverse) n := by
    intro n
    simp only [ProbeHighRowFamily.targetRow, elementCoeff_product, elementCoeff_inverse]
    rw [show elementCoeff (ProbeHighRowFamily.rawRow u) n = elementCoeff theta n from ht.2 n]
  have heD : forall n : O,
      elementCoeff ((ProbeHighRowFamily.targetRow eta u).excludePrimes S hS) n =
        elementCoeff tau n :=
    equal_elements_excludePrimes _ _ heT S hS
  refine Exists.intro rho (Exists.intro tau
    (And.intro (sqbound _ _ hN) (And.intro (sqbound _ _ hD)
      (And.intro heN (And.intro heD ?_)))))
  intro x w hx hw hx1 hw1
  exact quotient_eq_of_elements _ _ _ _ heN heD x w hx hw hx1 hw1

end OAI.SevenEighths.LowKernelQuotientTransport
