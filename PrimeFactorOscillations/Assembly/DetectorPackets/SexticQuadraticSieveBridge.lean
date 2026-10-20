/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Reflection.IdealBridge
import PrimeFactorOscillations.Assembly.DetectorPackets.SexticQuadraticSymbol

/-!
# SexticQuadraticSieveBridge

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
# Connection of the extracted phase to the proved quadratic sieve

The ideal character cube is the existing sieve coordinate, with its
admissibility and unit-phase hypotheses retained. The coordinate theorem
is algebraic for admissible columns; its physical local Euler use is at
prime columns. Ramified rows, principal transport and the full L quotient
are not erased by this bridge.
-/

set_option maxHeartbeats 800000

noncomputable section
namespace OAI.SevenEighths.SexticQuadraticSieveBridge

open CanonicalRowCompletion SexticToQuadraticLocal SexticQuadraticSymbol

local notation "O" => ActualEisensteinCubic.O

-- Existing mathematical bridge, retained only as a compatibility name.
theorem ideal_cube_sieve (I : Ideal O) (hI : CanonicalQuadraticSieve.Admissible I) (u : O) :
    (idealRowHom u I)^3 = CanonicalQuadraticSieve.quadraticRow I u := by
  exact InverseReflectedPhase.idealRowHom_cube_eq_quadratic I hI u

theorem conjugate_cube_sieve (I : Ideal O) (hI : CanonicalQuadraticSieve.Admissible I) (u : O) :
    (star (idealRowHom u I))^3 = star (CanonicalQuadraticSieve.quadraticRow I u) := by
  change ((starRingEnd Complex) (idealRowHom u I))^3 =
    (starRingEnd Complex) (CanonicalQuadraticSieve.quadraticRow I u)
  rw [<-map_pow, ideal_cube_sieve I hI u]

def contour (a kappa : Real) : Real :=
  max (17/50) (max (a/2) (2/3-a/2)+kappa/6)

theorem contour_gates (a b kappa : Real) (ha : 0 <= a) (hab : 1 <= a+b) :
    4-3*a-6*contour a kappa <= -kappa /\
    1+2*a-b-6*contour a kappa <= -kappa /\
    2*a-6*contour a kappa <= -kappa := by
  have houter := le_max_right (17/50:Real) (max (a/2) (2/3-a/2)+kappa/6)
  have hleft := add_le_add (le_max_left (a/2) (2/3-a/2)) (le_refl (kappa/6))
  have hright := add_le_add (le_max_right (a/2) (2/3-a/2)) (le_refl (kappa/6))
  change _ <= contour a kappa at houter
  have hl := hleft.trans houter
  have hr := hright.trans houter
  constructor
  . linarith
  constructor <;> linarith

theorem uniform_sieve_symbol (I : Ideal O) (hI : CanonicalQuadraticSieve.Admissible I)
    (u : O) (kappa : Real) (A eta x w z : Complex)
    (hk : 0 < kappa) (hsmall : (I.absNorm:Real)^(-kappa) <= 1/2)
    (hA : norm A <= 1) (heta : norm eta=1) (heta2 : eta^2=1)
    (hu : norm (idealRowHom u I)=1)
    (hx : kappa <= x.re) (hw : kappa <= w.re)
    (hxw : 1 <= x.re+w.re) (hz : z.re=contour x.re kappa) :
    norm (((I.absNorm:Real):Complex)^(2*x)*
      enhancedSelected (I.absNorm:Real) A eta (idealRowHom u I) x w z+
      star (CanonicalQuadraticSieve.quadraticRow I u)) <= 526*(I.absNorm:Real)^(-kappa) := by
  have hN : 1 <= I.absNorm := Nat.one_le_iff_ne_zero.mpr
    (fun h => hI.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hQ : (1:Real) <= I.absNorm := by exact_mod_cast hN
  have hg := contour_gates x.re w.re kappa (by linarith) hxw
  rw [<-hz] at hg
  have hb := uniform_symbol (I.absNorm:Real) kappa A eta (idealRowHom u I) x w z
    hQ hk hsmall hA heta hu hx hw hg.1 hg.2.1 hg.2.2
  rw [heta2, one_mul, conjugate_cube_sieve I hI u] at hb
  exact hb

end OAI.SevenEighths.SexticQuadraticSieveBridge

