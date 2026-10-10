/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Quintic torus cross phases and a two-prime packet

The prefix-coordinate substitution in the torus cocycle of
Banks--Bump--Lieman, Whittaker--Fourier Coefficients of Metaplectic
Eisenstein Series, equations (2.2)--(2.3), yields a symmetric pairing.
This file proves that polynomial identity and evaluates the complete
two-prime assignment packet under its explicit cross-phase model.

Canceling the diagonal interactions does not cancel the mixed ones:
the weights (-1,1,-1) give a value different from one at every nontrivial
fifth root. These are algebraic statements, not a formal construction
of global Whittaker coefficients or an arithmetic prime-pair realization.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Metaplectic.QuinticCocycle

abbrev Triple := Prod Int (Prod Int Int)

def determinantExponent (k : Triple) : Int := k.1 + 2 * k.2.1 + 3 * k.2.2

def torusCocycleExponent (k l : Triple) : Int :=
  (k.1 + k.2.1 + k.2.2) * (l.2.1 + 2 * l.2.2) +
    (k.2.1 + k.2.2) * l.2.2 - determinantExponent k * determinantExponent l

def pairing (k l : Triple) : Int :=
  2 * k.1 * l.1 + 3 * (k.1 * l.2.1 + k.2.1 * l.1) +
  4 * (k.1 * l.2.2 + k.2.2 * l.1) + 6 * k.2.1 * l.2.1 +
  8 * (k.2.1 * l.2.2 + k.2.2 * l.2.1) + 12 * k.2.2 * l.2.2

/-- The two source cocycle orders give the complete symmetric cross exponent. -/
theorem negative_symmetrization (k l : Triple) :
    -(torusCocycleExponent k l + torusCocycleExponent l k) = pairing k l := by
  dsimp [torusCocycleExponent, determinantExponent, pairing]
  ring

def axis (i : Fin 3) : Triple :=
  if i = 0 then (1, 0, 0) else if i = 1 then (0, 1, 0) else (0, 0, 1)

def weight (i : Fin 3) : Int := if i = 1 then 1 else -1

/-- Diagonal interactions are assumed already canceled by the coordinate Gauss
packets; all off-diagonal interactions are explicitly retained. -/
noncomputable def twoPrimePacket (r : Complex) : Complex :=
  Finset.univ.sum (fun i : Fin 3 => Finset.univ.sum (fun j : Fin 3 =>
    (weight i : Complex) * (weight j : Complex) *
      (if i = j then 1 else r ^ (pairing (axis i) (axis j)).toNat)))

theorem twoPrimePacket_polynomial (r : Complex) :
    twoPrimePacket r = 3 - 2 * r ^ 3 + 2 * r ^ 4 - 2 * r ^ 8 := by
  simp [twoPrimePacket, Fin.sum_univ_succ, weight, axis, pairing]
  ring

theorem twoPrimePacket_quintic (r : Complex) (hfive : r ^ 5 = 1) :
    twoPrimePacket r = 3 - 4 * r ^ 3 + 2 * r ^ 4 := by
  have h8 : r ^ 8 = r ^ 3 := by
    calc
      r ^ 8 = r ^ 5 * r ^ 3 := by ring
      _ = r ^ 3 := by rw [hfive, one_mul]
  rw [twoPrimePacket_polynomial, h8]
  ring

/-- No nonprincipal fifth-root cross phase gives the claimed Mobius value one. -/
theorem twoPrimePacket_ne_one (r : Complex) (hfive : r ^ 5 = 1)
    (hr : Not (r = 1)) : Not (twoPrimePacket r = 1) := by
  rw [twoPrimePacket_quintic r hfive]
  intro h
  apply hr
  linear_combination (4 * r ^ 2 - 12 * r + 9) / 11 * hfive -
    (4 * r ^ 3 - 4 * r ^ 2 + r + 2) / 22 * h

end Metaplectic.QuinticCocycle
