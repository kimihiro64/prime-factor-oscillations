/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.FinitePrimeResidueFamily
import PrimeFactorOscillations.Helpers.QuadraticProbabilityRH
import PrimeFactorOscillations.Mathlib.Algebra.Group.FiniteFunctionFibers

/-!
# Actual local law after two independent nonzero-residue additions

Exact finite counts give the probability, all-prime bounds, and a uniform
quadratic probability error. The resulting profile retains finite exceptions.
No bound on base-family degree, dimension or state cardinality is required.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations

namespace FinitePrimeResidueFamily

theorem zeroProbability_bounds (F : FinitePrimeResidueFamily) (p : Nat.Primes) :
    0 <= F.zeroProbability p /\ F.zeroProbability p <= 1 := by
  classical
  have hS : (0 : Real) < (F.domain p).card := by
    exact_mod_cast Finset.card_pos.mpr (F.nonempty p)
  unfold zeroProbability
  refine And.intro (div_nonneg (Nat.cast_nonneg _) hS.le) ?_
  apply (div_le_one hS).mpr
  exact_mod_cast Finset.card_filter_le (F.domain p) (fun a => F.value p a = 0)

theorem twoPrimeProbability_formula (F : FinitePrimeResidueFamily) (p : Nat.Primes) :
    F.twoPrimeProbability p =
      (((p : Nat) : Real) - 2 + F.zeroProbability p) / (((p : Nat) : Real) - 1) ^ 2 := by
  classical
  letI : NeZero (p : Nat) := NeZero.mk p.property.ne_zero
  have hS : (0 : Real) < (F.domain p).card := by
    exact_mod_cast Finset.card_pos.mpr (F.nonempty p)
  have hp : (1 : Real) < (p : Nat) := by exact_mod_cast p.property.one_lt
  have hCount := Finset.card_function_add_two_nonzero
    (I := F.State p) (K := ZMod (p : Nat))
    (by simpa only [ZMod.card] using p.property.two_le) (F.domain p) (F.value p)
  dsimp only [twoPrimeProbability]
  rw [hCount, ZMod.card, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub p.property.two_le, Nat.cast_ofNat]
  unfold zeroProbability
  field_simp [hS.ne', (sub_pos.mpr hp).ne']
  <;> ring

theorem twoPrimeProbability_bounds (F : FinitePrimeResidueFamily) (p : Nat.Primes) :
    0 <= F.twoPrimeProbability p /\ F.twoPrimeProbability p <= 1 := by
  have hr := F.zeroProbability_bounds p
  have hp : (2 : Real) <= (p : Nat) := by exact_mod_cast p.property.two_le
  have hden : 0 < (((p : Nat) : Real) - 1) ^ 2 := sq_pos_of_pos (by linarith)
  rw [F.twoPrimeProbability_formula]
  refine And.intro (div_nonneg (by linarith) hden.le) ?_
  apply (div_le_one hden).mpr
  nlinarith

theorem twoPrimeProbability_error (F : FinitePrimeResidueFamily) (p : Nat.Primes) :
    abs (F.twoPrimeProbability p - 1 / ((p : Nat) : Real)) <=
      2 / (((p : Nat) : Real) ^ 2) := by
  let P : Real := (p : Nat)
  let r := F.zeroProbability p
  have hr := F.zeroProbability_bounds p
  have hp : (2 : Real) <= P := by dsimp [P]; exact_mod_cast p.property.two_le
  have hp0 : 0 < P := by linarith
  have ht : 0 < P - 1 := by linarith
  have hid : F.twoPrimeProbability p - 1 / P =
      (P * r - 1) / (P * (P - 1) ^ 2) := by
    rw [F.twoPrimeProbability_formula]
    change (P - 2 + r) / (P - 1) ^ 2 - 1 / P = _
    field_simp [hp0.ne', ht.ne']
    <;> ring
  have hAbs : abs (P * r - 1) <= P - 1 := by
    apply abs_le.mpr
    change 0 <= r /\ r <= 1 at hr
    constructor <;> nlinarith
  rw [hid, abs_div, abs_of_pos (by positivity : 0 < P * (P - 1) ^ 2)]
  calc
    _ <= (P - 1) / (P * (P - 1) ^ 2) :=
      div_le_div_of_nonneg_right hAbs (by positivity)
    _ = 1 / (P * (P - 1)) := by field_simp
    _ <= 1 / (P ^ 2 / 2) := one_div_le_one_div_of_le (by positivity) (by nlinarith)
    _ = 2 / P ^ 2 := by ring

def twoPrimeLaw (F : FinitePrimeResidueFamily) : QuadraticPrimeLaw :=
  quadraticPrimeLawOfProbability
    (fun p => if hp : Nat.Prime p then F.twoPrimeProbability (Subtype.mk p hp) else 0)
    1 2 (by norm_num) (by norm_num)
    (by intro p hp; simpa only [dif_pos hp] using F.twoPrimeProbability_bounds (Subtype.mk p hp))
    (by intro p hp; simpa only [dif_pos hp] using F.twoPrimeProbability_error (Subtype.mk p hp))

theorem twoPrimeLaw_weight (F : FinitePrimeResidueFamily) (p : Nat.Primes) :
    F.twoPrimeLaw.weight p = F.twoPrimeProbability p / (1 - F.twoPrimeProbability p) := by
  cases p with
  | mk n hn =>
    simp only [twoPrimeLaw, quadraticPrimeLawOfProbability, dite_eq_left hn]

theorem twoPrimeLaw_nu (F : FinitePrimeResidueFamily) : F.twoPrimeLaw.nu = 1 := by
  rfl

end FinitePrimeResidueFamily

theorem constantPrimeResidueFamily_zeroProbability_zero (p : Nat.Primes) :
    (constantPrimeResidueFamily 0).zeroProbability p = 1 := by
  simp [FinitePrimeResidueFamily.zeroProbability, constantPrimeResidueFamily]

theorem constantPrimeResidueFamily_zeroProbability_one (p : Nat.Primes) :
    (constantPrimeResidueFamily 1).zeroProbability p = 0 := by
  letI : NeZero (p : Nat) := NeZero.mk p.property.ne_zero
  letI : Fact (Nat.Prime (p : Nat)) := Fact.mk p.property
  have hOne : Not ((1 : ZMod (p : Nat)) = 0) := one_ne_zero
  simp [FinitePrimeResidueFamily.zeroProbability, constantPrimeResidueFamily, hOne]
  rfl

end PrimeFactorOscillations
