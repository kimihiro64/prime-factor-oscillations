/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PowerPolynomialLaw

/-!
# AffineRootTransition

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
# Two uniform unit increments and translated root clocks

The off-diagonal transition on a finite alphabet is the distribution obtained
by adding an independent uniform nonzero element of a finite additive group.
Two such transitions bound the scaled mass of every root set, uniformly in
the preceding distribution. The final theorem retains the complete signed
clock and transfers a lower bound without a new error term.

This private prototype does not assert the missing infinite-range lower bound.
-/


noncomputable section
namespace PrimeFactorOscillations.AffineRootClock

def offDiagonalStep {I : Type*} [DecidableEq I] (S : Finset I)
    (q : Real) (mass : I -> Real) (r : I) : Real :=
  (S.erase r).sum mass / q

theorem root_step_identity {I : Type*} [DecidableEq I]
    (S R : Finset I)
    (hRS : forall r, Membership.mem R r -> Membership.mem S r) (q : Real)
    (mass : I -> Real) (htotal : S.sum mass = 1) :
    R.sum (offDiagonalStep S q mass) =
      ((R.card : Real) - R.sum mass) / q := by
  have hpoint (r : I) (hr : Membership.mem R r) :
      offDiagonalStep S q mass r = (1 - mass r) / q := by
    have he := Finset.sum_erase_add S mass (hRS r hr)
    unfold offDiagonalStep
    congr 1
    linarith
  calc
    _ = R.sum (fun r => (1 - mass r) / q) := by
      apply Finset.sum_congr rfl
      exact hpoint
    _ = ((R.card : Real) - R.sum mass) / q := by
      rw [<- Finset.sum_div, Finset.sum_sub_distrib]
      simp

theorem step_nonnegative {I : Type*} [DecidableEq I]
    (S : Finset I) (q : Real) (hq : 0 <= q)
    (mass : I -> Real)
    (hmass : forall r, Membership.mem S r -> 0 <= mass r) (r : I) :
    0 <= offDiagonalStep S q mass r := by
  apply div_nonneg _ hq
  apply Finset.sum_nonneg
  intro i hi
  exact hmass i (Finset.mem_of_mem_erase hi)

theorem step_total {I : Type*} [DecidableEq I]
    (S : Finset I) (q : Real) (hq : Not (q = 0))
    (hcard : (S.card : Real) = q + 1)
    (mass : I -> Real) (htotal : S.sum mass = 1) :
    S.sum (offDiagonalStep S q mass) = 1 := by
  rw [root_step_identity S S (fun _ h => h) q mass htotal, hcard, htotal]
  have he : q + 1 - (1 : Real) = q := by ring
  rw [he, div_self hq]

theorem two_step_root_mass_bounds {I : Type*} [DecidableEq I]
    (S R : Finset I)
    (hRS : forall r, Membership.mem R r -> Membership.mem S r)
    (q : Real) (hq : 1 <= q)
    (hcard : (S.card : Real) = q + 1)
    (mass : I -> Real) (htotal : S.sum mass = 1)
    (hmass : forall r, Membership.mem S r -> 0 <= mass r) :
    And
      ((R.card : Real) * (1 - 1 / q) <=
        q * R.sum (offDiagonalStep S q (offDiagonalStep S q mass)))
      (q * R.sum (offDiagonalStep S q (offDiagonalStep S q mass)) <=
        (R.card : Real)) := by
  have hq0 : 0 < q := by linarith
  have hqne : Not (q = 0) := ne_of_gt hq0
  have hfirst : S.sum (offDiagonalStep S q mass) = 1 :=
    step_total S q hqne hcard mass htotal
  have hmassR : 0 <= R.sum mass := by
    apply Finset.sum_nonneg
    intro r hr
    exact hmass r (hRS r hr)
  have hstepR : 0 <= R.sum (offDiagonalStep S q mass) := by
    apply Finset.sum_nonneg
    intro r hr
    exact step_nonnegative S q (le_of_lt hq0) mass hmass r
  have hupper : R.sum (offDiagonalStep S q mass) <= (R.card : Real) / q := by
    rw [root_step_identity S R hRS q mass htotal]
    apply div_le_div_of_nonneg_right _ (le_of_lt hq0)
    linarith
  have hsecond :
      q * R.sum (offDiagonalStep S q (offDiagonalStep S q mass)) =
        (R.card : Real) - R.sum (offDiagonalStep S q mass) := by
    rw [root_step_identity S R hRS q (offDiagonalStep S q mass) hfirst]
    field_simp [hqne]
  rw [hsecond]
  constructor
  . have hshape :
        (R.card : Real) * (1 - 1 / q) =
          (R.card : Real) - (R.card : Real) / q := by ring
    rw [hshape]
    linarith
  . linarith

theorem signed_clock_from_mass_bounds {P : Type*}
    (T : Finset P) (rho scaled logWeight q : P -> Real)
    (hl : forall p, Membership.mem T p ->
      rho p * (1 - 1 / q p) <= scaled p)
    (hu : forall p, Membership.mem T p -> scaled p <= rho p)
    (hw : forall p, Membership.mem T p -> 0 <= logWeight p)
    (nu feedback : Real) :
    And
      (0 <=
        (nu * feedback - T.sum (fun p => scaled p * logWeight p)) -
        (nu * feedback - T.sum (fun p => rho p * logWeight p)))
      ((nu * feedback - T.sum (fun p => scaled p * logWeight p)) -
        (nu * feedback - T.sum (fun p => rho p * logWeight p)) <=
        T.sum (fun p => rho p * logWeight p / q p)) := by
  have he :
      (nu * feedback - T.sum (fun p => scaled p * logWeight p)) -
          (nu * feedback - T.sum (fun p => rho p * logWeight p)) =
        T.sum (fun p => (rho p - scaled p) * logWeight p) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he]
  constructor
  . apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (by linarith [hu p hp]) (hw p hp)
  . apply Finset.sum_le_sum
    intro p hp
    have hbound : rho p - scaled p <= rho p / q p := by
      have hshape : rho p * (1 - 1 / q p) = rho p - rho p / q p := by ring
      have hlow := hl p hp
      rw [hshape] at hlow
      linarith
    calc
      _ <= (rho p / q p) * logWeight p :=
        mul_le_mul_of_nonneg_right hbound (hw p hp)
      _ = rho p * logWeight p / q p := by ring

theorem nonzero_increment_step {G : Type*} [Field G] [Fintype G]
    [DecidableEq G] (q : Real) (mass : G -> Real) (r : G) :
    (Finset.univ.erase (0 : G)).sum (fun z => mass (r - z)) / q =
      offDiagonalStep Finset.univ q mass r := by
  unfold offDiagonalStep
  congr 1
  have hinv (z : G) : r - (r - z) = z := by ring
  refine Finset.sum_bij (fun z _ => r - z) ?_ ?_ ?_ ?_
  . intro z hz
    apply Finset.mem_erase.mpr
    constructor
    . intro he
      have hz0 : z = 0 := by
        calc
          z = r - (r - z) := (hinv z).symm
          _ = r - r := congrArg (fun t : G => r - t) he
          _ = 0 := sub_self r
      exact (Finset.mem_erase.mp hz).1 hz0
    . exact Finset.mem_univ _
  . intro a ha b hb hab
    calc
      a = r - (r - a) := (hinv a).symm
      _ = r - (r - b) := congrArg (fun t : G => r - t) hab
      _ = b := hinv b
  . intro y hy
    have hm : Membership.mem (Finset.univ.erase (0 : G)) (r - y) := by
      apply Finset.mem_erase.mpr
      constructor
      . intro he
        have hyr : y = r := by
          calc
            y = r - (r - y) := (hinv y).symm
            _ = r - 0 := congrArg (fun t : G => r - t) he
            _ = r := sub_zero r
        exact (Finset.mem_erase.mp hy).1 hyr
      . exact Finset.mem_univ _
    exact Exists.intro (r - y) (Exists.intro hm (hinv y))
  . intro z hz
    rfl

def twoStepRootMass {I : Type*} [DecidableEq I]
    (S R : Finset I) (q : Real) (mass : I -> Real) : Real :=
  q * R.sum (offDiagonalStep S q (offDiagonalStep S q mass))

theorem two_increment_signed_clock {P : Type*}
    (I : P -> Type*) [forall p, DecidableEq (I p)]
    (T : Finset P) (S R : forall p, Finset (I p))
    (q logWeight : P -> Real) (mass : forall p, I p -> Real)
    (hRS : forall p, Membership.mem T p ->
      forall r, Membership.mem (R p) r -> Membership.mem (S p) r)
    (hq : forall p, Membership.mem T p -> 1 <= q p)
    (hcard : forall p, Membership.mem T p -> ((S p).card : Real) = q p + 1)
    (htotal : forall p, Membership.mem T p -> (S p).sum (mass p) = 1)
    (hmass : forall p, Membership.mem T p ->
      forall r, Membership.mem (S p) r -> 0 <= mass p r)
    (hw : forall p, Membership.mem T p -> 0 <= logWeight p)
    (nu feedback : Real) :
    And
      (0 <=
        (nu * feedback -
          T.sum (fun p => twoStepRootMass (S p) (R p) (q p) (mass p) *
            logWeight p)) -
        (nu * feedback - T.sum (fun p => ((R p).card : Real) * logWeight p)))
      ((nu * feedback -
          T.sum (fun p => twoStepRootMass (S p) (R p) (q p) (mass p) *
            logWeight p)) -
        (nu * feedback - T.sum (fun p => ((R p).card : Real) * logWeight p)) <=
        T.sum (fun p => ((R p).card : Real) * logWeight p / q p)) := by
  apply signed_clock_from_mass_bounds T
      (fun p => ((R p).card : Real))
      (fun p => twoStepRootMass (S p) (R p) (q p) (mass p))
      logWeight q
  . intro p hp
    exact (two_step_root_mass_bounds (S p) (R p) (hRS p hp)
      (q p) (hq p hp) (hcard p hp) (mass p) (htotal p hp) (hmass p hp)).1
  . intro p hp
    exact (two_step_root_mass_bounds (S p) (R p) (hRS p hp)
      (q p) (hq p hp) (hcard p hp) (mass p) (htotal p hp) (hmass p hp)).2
  . exact hw

end PrimeFactorOscillations.AffineRootClock
