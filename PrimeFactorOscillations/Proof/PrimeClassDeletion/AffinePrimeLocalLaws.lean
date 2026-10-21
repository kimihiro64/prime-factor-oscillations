/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeProbability

/-! # Affine prime probabilities, ordinary divisibility, and the forced endpoint -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def affinePrimeOdds (rho beta : Real) (p : Nat) : Real :=
  rho / ((p : Real) + beta)

noncomputable def affinePrimeProbability (rho beta : Real) (p : Nat) : Real :=
  rho / ((p : Real) + beta + rho)

theorem affinePrimeBase_nonneg (beta : Real) (hbeta : -2 <= beta)
    (p : Nat) (hp : Nat.Prime p) : 0 <= (p : Real) + beta := by
  have hp2 : (2 : Real) <= p := by exact_mod_cast hp.two_le
  linarith only [hbeta, hp2]

theorem affinePrimeBase_pos (beta : Real) (hbeta : -2 < beta)
    (p : Nat) (hp : Nat.Prime p) : 0 < (p : Real) + beta := by
  have hp2 : (2 : Real) <= p := by exact_mod_cast hp.two_le
  linarith only [hbeta, hp2]

theorem affinePrimeProbability_unit (rho beta : Real) (hrho : 0 < rho)
    (hbeta : -2 <= beta) (p : Nat) (hp : Nat.Prime p) :
    And (0 <= affinePrimeProbability rho beta p)
      (affinePrimeProbability rho beta p <= 1) := by
  have hb := affinePrimeBase_nonneg beta hbeta p hp
  have hd : 0 < (p : Real) + beta + rho := add_pos_of_nonneg_of_pos hb hrho
  exact And.intro (div_nonneg hrho.le hd.le)
    ((div_le_one hd).mpr (le_add_of_nonneg_left hb))

theorem affinePrimeProbability_antitone (rho beta : Real) (hrho : 0 < rho)
    (hbeta : -2 <= beta) (p q : Nat) (hp : Nat.Prime p) (_hq : Nat.Prime q)
    (hpq : p <= q) :
    affinePrimeProbability rho beta q <= affinePrimeProbability rho beta p := by
  have hb := affinePrimeBase_nonneg beta hbeta p hp
  have hd : 0 < (p : Real) + beta + rho := add_pos_of_nonneg_of_pos hb hrho
  exact div_le_div_of_nonneg_left hrho.le hd
    (add_le_add (add_le_add (Nat.cast_le.mpr hpq) (le_refl beta)) (le_refl rho))

theorem affinePrimeProbability_interior (rho beta : Real) (hrho : 0 < rho)
    (hbeta : -2 < beta) (p : Nat) (hp : Nat.Prime p) :
    And (0 < affinePrimeProbability rho beta p)
      (affinePrimeProbability rho beta p < 1) := by
  have hb := affinePrimeBase_pos beta hbeta p hp
  have hd : 0 < (p : Real) + beta + rho := add_pos hb hrho
  exact And.intro (div_pos hrho hd)
    ((div_lt_one hd).mpr (by linarith only [hb]))

theorem affinePrimeOdds_nonneg (rho beta : Real) (hrho : 0 < rho)
    (hbeta : -2 < beta) (p : Nat) (hp : Nat.Prime p) :
    0 <= affinePrimeOdds rho beta p := by
  exact div_nonneg hrho.le (affinePrimeBase_pos beta hbeta p hp).le

theorem affinePrimeOdds_antitone (rho beta : Real) (hrho : 0 < rho)
    (hbeta : -2 < beta) (p q : Nat) (hp : Nat.Prime p) (_hq : Nat.Prime q)
    (hpq : p <= q) :
    affinePrimeOdds rho beta q <= affinePrimeOdds rho beta p := by
  exact div_le_div_of_nonneg_left hrho.le (affinePrimeBase_pos beta hbeta p hp)
    (add_le_add (Nat.cast_le.mpr hpq) (le_refl beta))

theorem affinePrimeProbability_odds (rho beta : Real) (hrho : 0 < rho)
    (p : Nat) (hb : 0 < (p : Real) + beta) :
    affinePrimeProbability rho beta p / (1 - affinePrimeProbability rho beta p) =
      affinePrimeOdds rho beta p := by
  have hd : 0 < (p : Real) + beta + rho := add_pos hb hrho
  have hs : 1 - rho / ((p : Real) + beta + rho) =
      ((p : Real) + beta) / ((p : Real) + beta + rho) := by
    field_simp [ne_of_gt hd]
    ring
  unfold affinePrimeProbability affinePrimeOdds
  rw [hs]
  field_simp [ne_of_gt hb, ne_of_gt hd]

theorem affinePrimeProbability_endpoint_two (rho : Real) (hrho : 0 < rho) :
    affinePrimeProbability rho (-2) 2 = 1 := by
  simp [affinePrimeProbability, ne_of_gt hrho]

theorem affinePrimeProbability_endpoint_one_iff (rho : Real) (hrho : 0 < rho)
    (p : Nat) (hp : Nat.Prime p) :
    affinePrimeProbability rho (-2) p = 1 <-> p = 2 := by
  constructor
  next =>
    intro h
    have hb := affinePrimeBase_nonneg (-2) (le_refl _) p hp
    have hd : 0 < (p : Real) + -2 + rho := add_pos_of_nonneg_of_pos hb hrho
    have heq := (div_eq_iff (ne_of_gt hd)).mp h
    have hp2 : (p : Real) = 2 := by linarith only [heq]
    exact_mod_cast hp2
  next =>
    intro h
    subst p
    exact affinePrimeProbability_endpoint_two rho hrho

theorem affinePrimeProbability_ordinary (p : Nat) :
    affinePrimeProbability 1 (-1) p = 1 / (p : Real) := by
  simp [affinePrimeProbability, add_assoc]

theorem affinePrimeOdds_ordinary (p : Nat) :
    affinePrimeOdds 1 (-1) p = 1 / ((p : Real) - 1) := by
  rfl

end PrimeFactorOscillations.PrimeClassDeletion
