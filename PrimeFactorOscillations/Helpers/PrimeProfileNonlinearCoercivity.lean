/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileCutoffRigidity
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CompensatedReciprocalCoercivity

/-!
# Nonlinear coercivity of the complete prime-prefix profile

The complete signed boundary transport satisfies a probe-uniform saturating
lower bound. Every budget below half the boundary prime gives an explicit
bound on the whole prime displacement, including finite permutations.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- The whole signed prime displacement is controlled by a nonlinear gauge. -/
theorem primePrefixDefect_nonlinear_coercivity (e : Equiv.Perm Nat)
    (t : Nat -> Real) (n : Nat) (ht : 0 < t n) :
    0 <= Finset.prefixDefect
      (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1) /\
    Real.reciprocalBoundaryGauge (PrimeFactorUnimodality.primeAt n : Real)
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1)) <= normalizedPrimePrefixDefect e t n := by
  let p := fun j : Nat => (PrimeFactorUnimodality.primeAt j : Real)
  let s := (Finset.range (n + 1)).image e
  let u := Finset.range (n + 1)
  have hpmono : Monotone p := by
    intro i j hij
    change (PrimeFactorUnimodality.primeAt i : Real) <= PrimeFactorUnimodality.primeAt j
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone hij
  have hr : 0 < p n := by
    change (0 : Real) < PrimeFactorUnimodality.primeAt n
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hc : s.card = u.card := Finset.card_image_iff.mpr
    (fun _ _ _ _ h => e.injective h)
  have hgap : 0 <= p (n + 1) - p n := sub_nonneg.mpr (hpmono (Nat.le_succ n))
  have hS := (mul_nonneg
    (Nat.cast_nonneg (Finset.prefixDisplacement e (n + 1))) hgap).trans
    (Finset.prefixDisplacement_mul_gap_le_prefixDefect p hpmono e n)
  refine And.intro hS ?_
  have h := Real.normalized_reference_transport_nonlinear_lower
    s u p (t n) (p n) hc ht hr
    (by
      intro j hj
      have hn := (Finset.mem_sdiff.mp hj).2
      change Not (Membership.mem (Finset.range (n + 1)) j) at hn
      rw [Finset.mem_range] at hn
      exact hpmono (by omega))
    (by
      intro j hj
      have hn := (Finset.mem_sdiff.mp hj).1
      change Membership.mem (Finset.range (n + 1)) j at hn
      rw [Finset.mem_range] at hn
      refine And.intro ?_ (hpmono (by omega))
      change (0 : Real) < PrimeFactorUnimodality.primeAt j
      exact_mod_cast (PrimeFactorUnimodality.prime_primeAt j).pos)
  dsimp [s, u] at h
  rw [Finset.sum_image (fun _ _ _ _ he => e.injective he),
    Finset.sum_image (fun _ _ _ _ he => e.injective he)] at h
  exact h

/-- Half-reference budgets localize the total displacement, uniformly in the probe. -/
theorem primePrefixDefect_half_window_localization (e : Equiv.Perm Nat)
    (t : Nat -> Real) (n : Nat) (C : Real) (ht : 0 < t n)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 2)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1) <=
      (PrimeFactorUnimodality.primeAt n : Real) *
        (1 / Real.sqrt (1 - 2 * C / (PrimeFactorUnimodality.primeAt n : Real)) - 1) := by
  have h := primePrefixDefect_nonlinear_coercivity e t n ht
  have hr : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  exact Real.reciprocalBoundaryGauge_inverse_bound _ _ C hr h.1 hC
    (h.2.trans hcost)

end PrimeFactorOscillations.PrimeProfileRigidity
