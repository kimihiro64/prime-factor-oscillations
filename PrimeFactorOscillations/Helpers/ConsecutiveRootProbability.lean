/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ConsecutiveRootResidues
import PrimeFactorOscillations.Helpers.QuadraticProbabilityRH

/-!
# The exact probability law of a consecutive-root polynomial plus a prime

The local probability is defined by actual finite residue pairs. Its exact
formula, all-prime bounds and quadratic error build the existing family
profile with dimension one, retaining every small-prime exception.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations

def consecutiveRootProbability (d p : Nat) : Real := by
  classical
  exact if hp : Nat.Prime p then
    letI : NeZero p := NeZero.mk hp.ne_zero
    ((((Finset.univ : Finset (ZMod p)).product (Finset.univ.erase (0 : ZMod p))).filter
      (fun ab : Prod (ZMod p) (ZMod p) => consecutiveRootValue d ab.1 + ab.2 = 0)).card : Real) /
        ((p : Real) * ((p : Real) - 1))
  else 0

theorem consecutiveRootProbability_formula (d p : Nat) (hp : Nat.Prime p) :
    consecutiveRootProbability d p =
      ((p : Real) - (min d p : Nat)) / ((p : Real) * ((p : Real) - 1)) := by
  classical
  let : NeZero p := NeZero.mk hp.ne_zero
  unfold consecutiveRootProbability
  rw [dif_pos hp, consecutiveRootPrimeAddition_count d p hp,
    Nat.cast_sub (Nat.min_le_right d p)]

theorem consecutiveRootProbability_bounds (d : Nat) (hd : 1 <= d)
    (p : Nat) (hp : Nat.Prime p) :
    0 <= consecutiveRootProbability d p /\ consecutiveRootProbability d p <= 1 / p := by
  have hpR : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hMin : (1 : Real) <= (min d p : Nat) := by
    exact_mod_cast (Nat.le_min.mpr (And.intro hd hp.one_lt.le))
  have hMax : ((min d p : Nat) : Real) <= (p : Real) := by exact_mod_cast Nat.min_le_right d p
  rw [consecutiveRootProbability_formula d p hp]
  refine And.intro (div_nonneg (by linarith) (by positivity)) ?_
  calc
    _ <= ((p : Real) - 1) / ((p : Real) * ((p : Real) - 1)) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by field_simp [(sub_pos.mpr hpR).ne']

theorem consecutiveRootProbability_error (d : Nat) (hd : 1 <= d)
    (p : Nat) (hp : Nat.Prime p) :
    abs (consecutiveRootProbability d p - 1 / p) <= (2 * (d : Real)) / (p : Real) ^ 2 := by
  have hpR : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hpTwo : (2 : Real) <= p := by exact_mod_cast hp.two_le
  have hMin : (1 : Real) <= (min d p : Nat) := by
    exact_mod_cast (Nat.le_min.mpr (And.intro hd hp.one_lt.le))
  have hMax : ((min d p : Nat) : Real) <= (d : Real) := by exact_mod_cast Nat.min_le_left d p
  have hid : consecutiveRootProbability d p - 1 / p =
      -(((min d p : Nat) : Real) - 1) / ((p : Real) * ((p : Real) - 1)) := by
    rw [consecutiveRootProbability_formula d p hp]
    field_simp [(sub_pos.mpr hpR).ne']
    <;> ring
  rw [hid, abs_div, abs_neg, abs_of_nonneg (by linarith : 0 <= ((min d p : Nat) : Real) - 1),
    abs_of_pos (by positivity : 0 < (p : Real) * ((p : Real) - 1))]
  calc
    _ <= (d : Real) / ((p : Real) * ((p : Real) - 1)) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ <= (d : Real) / ((p : Real) ^ 2 / 2) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg d) (by positivity) (by nlinarith)
    _ = _ := by ring

def consecutiveRootLaw (d : Nat) (hd : 1 <= d) : QuadraticPrimeLaw :=
  quadraticPrimeLawOfProbability (consecutiveRootProbability d) 1 (2 * (d : Real))
    (by norm_num) (by positivity)
    (by
      intro p hp
      have h := consecutiveRootProbability_bounds d hd p hp
      refine And.intro h.1 (h.2.trans ?_)
      have hpR : (1 : Real) <= p := by exact_mod_cast hp.one_lt.le
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hpR)
    (by
      intro p hp
      simpa only [one_div] using consecutiveRootProbability_error d hd p hp)

theorem consecutiveRootLaw_weight (d : Nat) (hd : 1 <= d) (p : Nat.Primes) :
    (consecutiveRootLaw d hd).weight p =
      consecutiveRootProbability d (p : Nat) / (1 - consecutiveRootProbability d (p : Nat)) := by
  rfl

theorem consecutiveRootLaw_nu (d : Nat) (hd : 1 <= d) :
    (consecutiveRootLaw d hd).nu = 1 := by
  rfl

end PrimeFactorOscillations
