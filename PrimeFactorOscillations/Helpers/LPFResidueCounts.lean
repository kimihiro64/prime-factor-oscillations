/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Helpers.LPFCharacterTransfer
import PrimeFactorOscillations.Mathlib.NumberTheory.DirichletCharacter.ResidueCount
import PrimeFactorOscillations.Mathlib.NumberTheory.SmoothNumbers.ResidueSupport

/-!
# Uniform smooth-number and largest-factor residue counts

There is one absolute constant for all positive integer cutoffs and moduli.
Smooth numbers are centered at the coprime smooth count, not the total count.
Largest factors above y have the full nonsmooth count as their principal mass
when the modulus is y-smooth. Repeated output factors retain their multiplicity.
These theorems count ordinary integers and make no generated-state claim.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem exists_uniform_residue_bounds :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N] (a : Units (ZMod N)) (X y : Nat),
        0 < X -> 0 < y -> And
          (abs ((((Nat.smoothNumbersUpTo X (y + 1)).filter
              (fun (n : Nat) => (n : ZMod N) = (a : ZMod N))).card : Real) -
            (((Nat.smoothNumbersUpTo X (y + 1)).filter
              (fun n => Nat.Coprime n N)).card : Real) / (N.totient : Real)) <=
            (N : Real) + characterError C N X y)
          (Nat.largestPrimeFactor N <= y ->
            abs (((((Finset.Icc 1 X).filter (fun n => y < Nat.largestPrimeFactor n)).filter
                (fun n => (Nat.largestPrimeFactor n : ZMod N) = (a : ZMod N))).card : Real) -
              ((X : Real) - ((Nat.smoothNumbersUpTo X (y + 1)).card : Real)) /
                (N.totient : Real)) <= characterError C N X y)) := by
  let C : Real := Classical.choose exists_uniform_character_bounds
  have hC := Classical.choose_spec exists_uniform_character_bounds
  refine Exists.intro C (And.intro hC.1 ?_)
  intro N inst a X y hX hy
  have hE := characterError_nonneg C hC.1.le N X y
  refine And.intro ?_ ?_
  next =>
    have h := DirichletCharacter.abs_residue_count_sub_unit_mean_le
      (Nat.smoothNumbersUpTo X (y + 1)) (fun (n : Nat) => (n : ZMod N)) a
      ((N : Real) + characterError C N X y) (add_nonneg (Nat.cast_nonneg N) hE)
      (fun chi hchi => (hC.2 chi hchi X y hX hy).1)
    simpa only [ZMod.isUnit_iff_coprime] using h
  next =>
    intro hN
    let S := (Finset.Icc 1 X).filter (fun n => y < Nat.largestPrimeFactor n)
    have h := DirichletCharacter.abs_residue_count_sub_unit_mean_le
      S (fun n => (Nat.largestPrimeFactor n : ZMod N)) a
      (characterError C N X y) hE (fun chi hchi => (hC.2 chi hchi X y hX hy).2)
    have hSupport : S.filter (fun n => IsUnit (Nat.largestPrimeFactor n : ZMod N)) = S := by
      apply Finset.filter_eq_self.mpr
      intro n hn
      have hmem := Finset.mem_filter.mp hn
      exact Nat.isUnit_largestPrimeFactor_of_le_cutoff
        (Finset.mem_Icc.mp hmem.1).1 hN hmem.2
    rw [hSupport] at h
    have hPartition := Nat.card_smoothNumbersUpTo_add_largePrimeFactor X y hy
    have hReal : ((Nat.smoothNumbersUpTo X (y + 1)).card : Real) + (S.card : Real) =
        (X : Real) := by exact_mod_cast hPartition
    have hCenter : (S.card : Real) =
        (X : Real) - ((Nat.smoothNumbersUpTo X (y + 1)).card : Real) := by linarith
    rw [hCenter] at h
    exact h

end PrimeFactorOscillations.LPF
