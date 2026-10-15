/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QRHPrimeRows
import PrimeFactorOscillations.Mathlib.NumberTheory.DirichletCharacter.ResidueCount
import PrimeFactorOscillations.Mathlib.NumberTheory.SmoothNumbers.ResidueSupport

/-!
# Positive weights on prime rows

The audited zero exclusion is applied to every unit input class. The output
weight is arbitrary, so multiplication by three need not be invertible.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem prime_row_isUnit {N X y m r : Nat} [NeZero N]
    (hm : 0 < m) (hN : Nat.largestPrimeFactor N <= y)
    (hr : Membership.mem (Nat.largestPrimeFactorRow X y m) r) :
    IsUnit (r : ZMod N) := by
  have hp := (Nat.mem_largestPrimeFactorRow hm).mp hr
  have hu := Nat.isUnit_largestPrimeFactor_of_le_cutoff hp.1.pos hN
    (show y < Nat.largestPrimeFactor r by rw [Nat.largestPrimeFactor_of_prime hp.1]; omega)
  simpa only [Nat.largestPrimeFactor_of_prime hp.1] using hu

theorem sum_unit_fibers {N : Nat} [NeZero N] (s : Finset Nat)
    (hUnit : forall r, Membership.mem s r -> IsUnit (r : ZMod N))
    (w : ZMod N -> Real) :
    Finset.sum (Finset.univ : Finset (Units (ZMod N))) (fun a =>
      w (a : ZMod N) * ((s.filter (fun (r : Nat) => (r : ZMod N) = (a : ZMod N))).card : Real)) =
      Finset.sum s (fun r => w (r : ZMod N)) := by
  classical
  calc
    _ = Finset.sum (Finset.univ : Finset (Units (ZMod N))) (fun a =>
        Finset.sum s (fun r => if (r : ZMod N) = (a : ZMod N) then w (a : ZMod N) else 0)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [<- Finset.sum_filter]
      simp [mul_comm]
    _ = Finset.sum s (fun r =>
        Finset.sum (Finset.univ : Finset (Units (ZMod N)))
          (fun a => if (r : ZMod N) = (a : ZMod N) then w (a : ZMod N) else 0)) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      let u : Units (ZMod N) := (hUnit r hr).unit
      have hu : (u : ZMod N) = (r : ZMod N) := (hUnit r hr).unit_spec
      rw [Finset.sum_eq_single u]
      next => simp [hu]
      next =>
        intro b hb hbu
        have hne : Not ((r : ZMod N) = (b : ZMod N)) := by
          intro he
          exact hbu (Units.ext (he.symm.trans hu.symm))
        simp [hne]
      next => simp

theorem weighted_sum_lower_of_unit_discrepancy {N : Nat} [NeZero N]
    (s : Finset Nat) (hUnit : forall r, Membership.mem s r -> IsUnit (r : ZMod N))
    (w : ZMod N -> Real) (hw : forall a, 0 <= w a) (E : Real)
    (hError : forall a : Units (ZMod N),
      abs (((s.filter (fun (r : Nat) => (r : ZMod N) = (a : ZMod N))).card : Real) -
        (s.card : Real) / (N.totient : Real)) <= E) :
    ((s.card : Real) / (N.totient : Real) - E) *
      Finset.sum (Finset.univ : Finset (Units (ZMod N))) (fun a => w (a : ZMod N)) <=
      Finset.sum s (fun r => w (r : ZMod N)) := by
  rw [<- sum_unit_fibers s hUnit w, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hLower := (abs_le.mp (hError a)).1
  have h := mul_le_mul_of_nonneg_right
    (show (s.card : Real) / (N.totient : Real) - E <=
      ((s.filter (fun (r : Nat) => (r : ZMod N) = (a : ZMod N))).card : Real) by linarith)
    (hw (a : ZMod N))
  simpa only [mul_comm] using h

theorem exists_uniform_weighted_prime_row_lower_bound :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N] (X y m : Nat), 0 < m ->
        Nat.largestPrimeFactor N <= y ->
        forall w : ZMod N -> Real, (forall a, 0 <= w a) ->
          (((Nat.largestPrimeFactorRow X y m).card : Real) / (N.totient : Real) -
            C * (X : Real) ^ (7 / 8 : Real) *
              (1 + Real.log N + Real.log ((X : Real) + 2)) ^ 2) *
            Finset.sum (Finset.univ : Finset (Units (ZMod N))) (fun a => w (a : ZMod N)) <=
          Finset.sum (Nat.largestPrimeFactorRow X y m) (fun r => w (r : ZMod N))) := by
  let C : Real := Classical.choose QRH.exists_uniform_prime_row_bounds
  have hC := Classical.choose_spec QRH.exists_uniform_prime_row_bounds
  refine Exists.intro C (And.intro hC.1 ?_)
  intro N inst X y m hm hN w hw
  have hUnit : forall r, Membership.mem (Nat.largestPrimeFactorRow X y m) r ->
      IsUnit (r : ZMod N) := fun r hr => prime_row_isUnit hm hN hr
  apply weighted_sum_lower_of_unit_discrepancy (Nat.largestPrimeFactorRow X y m) hUnit w hw
  intro a
  have hFilter : (Nat.largestPrimeFactorRow X y m).filter
      (fun (r : Nat) => IsUnit (r : ZMod N)) = Nat.largestPrimeFactorRow X y m := by
    apply Finset.filter_eq_self.mpr
    exact hUnit
  have h := DirichletCharacter.abs_residue_count_sub_unit_mean_le
    (Nat.largestPrimeFactorRow X y m) (fun (r : Nat) => (r : ZMod N)) a
    (C * (X : Real) ^ (7 / 8 : Real) * (1 + Real.log N + Real.log ((X : Real) + 2)) ^ 2)
    (by have := hC.1; positivity) (fun chi hchi => hC.2 chi hchi X y m)
  rw [hFilter] at h
  exact h

end PrimeFactorOscillations.LPF
