/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileSquareFilter

/-!
# Square-filter control using exactly the retained finite supports

The filter norm is needed only after common-coordinate cancellation. This
support formulation permits stronger cost windows without changing the observable.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- Keep the same signed transport and test the norm only on retained coordinates. -/
theorem primePrefixSquareFilterTransport_supported_bounds
    (H : Polynomial Real) (eta : Real) (e : Equiv.Perm Nat) (n : Nat)
    (hfilter : forall j, Or
      (Membership.mem ((Finset.range (n + 1)).image e \ Finset.range (n + 1)) j)
      (Membership.mem (Finset.range (n + 1) \ (Finset.range (n + 1)).image e) j) ->
      abs (Polynomial.eval ((PrimeFactorUnimodality.primeAt n : Real) /
        PrimeFactorUnimodality.primeAt j) H) <= eta) :
    (1 - eta ^ 2) * Finset.prefixDefect
      (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1) <=
        primePrefixSquareFilterTransport H e n /\
    primePrefixSquareFilterTransport H e n <= Finset.prefixDefect
      (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1) := by
  let p : Nat -> Real := fun j => PrimeFactorUnimodality.primeAt j
  let r : Real := p n
  let g : Nat -> Real := fun j =>
    (p j - r) * (1 - (Polynomial.eval (r / p j) H) ^ 2)
  let s := (Finset.range (n + 1)).image e
  let u := Finset.range (n + 1)
  have hc : s.card = u.card := Finset.card_image_iff.mpr
    (fun _ _ _ _ h => e.injective h)
  have hmono : Monotone p := by
    intro i j hij
    dsimp only [p]
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone hij
  have hin : forall j, Membership.mem (s \ u) j ->
      (1 - eta ^ 2) * (p j - r) <= g j - 0 /\
      g j - 0 <= 1 * (p j - r) := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).2
    change Not (Membership.mem (Finset.range (n + 1)) j) at hn
    rw [Finset.mem_range] at hn
    have hpr : r <= p j := hmono (by omega)
    have hnorm := hfilter j (Or.inl hj)
    have hb := Real.reciprocal_square_filter_mul_bounds (p j - r)
      (Polynomial.eval (r / p j) H) eta (sub_nonneg.mpr hpr) hnorm
    simpa only [g, sub_zero, one_mul] using hb
  have hout : forall j, Membership.mem (u \ s) j ->
      (1 - eta ^ 2) * (r - p j) <= 0 - g j /\
      0 - g j <= 1 * (r - p j) := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).1
    change Membership.mem (Finset.range (n + 1)) j at hn
    rw [Finset.mem_range] at hn
    have hpr : p j <= r := hmono (by omega)
    have hnorm := hfilter j (Or.inr hj)
    have hb := Real.reciprocal_square_filter_mul_bounds (r - p j)
      (Polynomial.eval (r / p j) H) eta (sub_nonneg.mpr hpr) hnorm
    have hg : 0 - g j = (r - p j) * (1 - (Polynomial.eval (r / p j) H) ^ 2) := by
      dsimp only [g]
      ring
    rw [hg, one_mul]
    exact hb
  have hb := Finset.reference_transport_comparison s u p g r 0
    (1 - eta ^ 2) 1 hc hin hout
  have hf : s.sum p - u.sum p = Finset.prefixDefect p e (n + 1) := by
    dsimp only [s, u]
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    rfl
  have hg : s.sum g - u.sum g = primePrefixSquareFilterTransport H e n := by
    dsimp only [s, u]
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    rfl
  rw [hf, hg, one_mul] at hb
  exact hb

/-- The full signed error keeps coefficient one on the original displacement. -/
theorem primePrefixSquareFilterTransport_supported_error
    (H : Polynomial Real) (eta : Real) (e : Equiv.Perm Nat) (n : Nat)
    (hfilter : forall j, Or
      (Membership.mem ((Finset.range (n + 1)).image e \ Finset.range (n + 1)) j)
      (Membership.mem (Finset.range (n + 1) \ (Finset.range (n + 1)).image e) j) ->
      abs (Polynomial.eval ((PrimeFactorUnimodality.primeAt n : Real) /
        PrimeFactorUnimodality.primeAt j) H) <= eta) :
    0 <= Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
      e (n + 1) - primePrefixSquareFilterTransport H e n /\
    Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
      e (n + 1) - primePrefixSquareFilterTransport H e n <=
      eta ^ 2 * Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) := by
  have h := primePrefixSquareFilterTransport_supported_bounds H eta e n hfilter
  refine And.intro (sub_nonneg.mpr h.2) ?_
  nlinarith only [h.1]

end PrimeFactorOscillations.PrimeProfileRigidity
