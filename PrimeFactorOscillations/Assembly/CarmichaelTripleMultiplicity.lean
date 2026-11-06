/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelMultiplicitySupportBound

/-!
# Carrier deficits force triple multiplicity

Only common-weak orders are charged. Carrier orders are unrestricted.
The full joint support bound, rather than a separate norm estimate, supplies
the coefficient 20/21.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

variable {I : Type*} [Fintype I] {sigma : Real}

def tripleExcessAt (S : ReflectedSpectrum I sigma) (i : I) : Real :=
  ((S.mult i - 2 : Nat) : Real) / (S.point i).im ^ 2

def weakTripleExcessMass (S : ReflectedSpectrum I sigma) : Real :=
  S.weakIndices.sum S.tripleExcessAt

theorem tripleExcessAt_nonneg (S : ReflectedSpectrum I sigma) (i : I) :
    0 <= S.tripleExcessAt i :=
  div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem weakTripleExcessMass_nonneg (S : ReflectedSpectrum I sigma) :
    0 <= S.weakTripleExcessMass :=
  Finset.sum_nonneg (fun i _ => S.tripleExcessAt_nonneg i)

theorem excessMassAt_eq_repeated_add_triple (S : ReflectedSpectrum I sigma) (i : I) :
    S.excessMassAt i = S.repeatedUnitAt i + S.tripleExcessAt i := by
  by_cases h : 2 <= S.mult i
  . unfold excessMassAt repeatedUnitAt tripleExcessAt
    rw [ite_eq_left h, Nat.cast_sub h]
    norm_num only [Nat.cast_ofNat]
    unfold unitMass
    ring
  . have hm : S.mult i = 1 := by
      have hp := S.mult_pos i
      omega
    simp [excessMassAt, repeatedUnitAt, tripleExcessAt, hm]

theorem weakExcessMass_eq_repeated_add_triple (S : ReflectedSpectrum I sigma) :
    S.weakExcessMass = S.weakRepeatedUnitMass + S.weakTripleExcessMass := by
  unfold weakExcessMass weakRepeatedUnitMass weakTripleExcessMass
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact S.excessMassAt_eq_repeated_add_triple i

theorem weakTripleExcessMass_eq_zero_of_double (S : ReflectedSpectrum I sigma)
    (hDouble : forall i, Membership.mem S.weakIndices i -> S.mult i <= 2) :
    S.weakTripleExcessMass = 0 := by
  unfold weakTripleExcessMass
  apply Finset.sum_eq_zero
  intro i hi
  simp only [tripleExcessAt, Nat.sub_eq_zero_of_le (hDouble i hi),
    Nat.cast_zero, zero_div]

theorem carrier_triple_excess_bound (S : ReflectedSpectrum I (7 / 8)) :
    (20 / 21 : Real) * S.totalMass <=
      S.carrierMass + (20 / 21 : Real) * S.weakTripleExcessMass := by
  have hc := S.carrier_multiplicity_support_bound
  have hq := S.weakRepeatedUnitMass_le_unit
  have he := S.weakExcessMass_eq_repeated_add_triple
  have hw := S.weakMass_eq_unit_add_excess
  have ht := S.totalMass_eq_weakMass_add_carrierMass
  linarith

theorem carrier_triple_compensated_bound (S : ReflectedSpectrum I (7 / 8)) :
    (20 / 21 : Real) * (S.totalMass - S.weakTripleExcessMass) <= S.carrierMass := by
  have h := S.carrier_triple_excess_bound
  linarith

theorem double_weak_carrier_bound (S : ReflectedSpectrum I (7 / 8))
    (hDouble : forall i, Membership.mem S.weakIndices i -> S.mult i <= 2) :
    (20 / 21 : Real) * S.totalMass <= S.carrierMass := by
  have h := S.carrier_triple_excess_bound
  rw [S.weakTripleExcessMass_eq_zero_of_double hDouble, mul_zero, add_zero] at h
  exact h

theorem triple_weak_atom_of_deficit (S : ReflectedSpectrum I (7 / 8))
    (hDeficit : S.carrierMass < (20 / 21 : Real) * S.totalMass) :
    exists i : I, Membership.mem S.weakIndices i /\ 3 <= S.mult i := by
  classical
  by_contra hNot
  have hDouble : forall i, Membership.mem S.weakIndices i -> S.mult i <= 2 := by
    intro i hi
    by_contra hn
    exact hNot (Exists.intro i (And.intro hi (by omega)))
  exact (not_le_of_gt hDeficit) (S.double_weak_carrier_bound hDouble)

theorem totalMass_sub_triple_nonneg (S : ReflectedSpectrum I (7 / 8)) :
    0 <= S.totalMass - S.weakTripleExcessMass := by
  have hp : 0 <= S.weakUnitMass :=
    Finset.sum_nonneg (fun i _ => S.unitMass_nonneg i)
  have hq := S.weakRepeatedUnitMass_nonneg
  have hc : 0 <= S.carrierMass :=
    Finset.sum_nonneg (fun i _ => S.mass_nonneg i)
  have he := S.weakExcessMass_eq_repeated_add_triple
  have hw := S.weakMass_eq_unit_add_excess
  have ht := S.totalMass_eq_weakMass_add_carrierMass
  linarith

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum
