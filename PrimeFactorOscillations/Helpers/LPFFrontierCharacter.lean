/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFStateResidueEnergy
import PrimeFactorOscillations.Helpers.QRHPrimeRows
import PrimeFactorOscillations.Mathlib.NumberTheory.DirichletCharacter.ResidueCount

/-!
# The audited 7/8 input on the exact odd frontier

The two prime rows give a uniform input-character estimate. Unit-residue
counts keep their exact principal mass; in particular the 3r row is not
silently treated as coprime when the modulus is divisible by three.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem odd_frontier_character_eq {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (M : Nat) (hM : 3 <= M) :
    Finset.sum ((oddInterval M).filter (fun n => M < Nat.largestPrimeFactor n))
        (fun n => chi (n : ZMod N)) =
      Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 1) (fun r => chi (r : ZMod N)) +
      chi (3 : ZMod N) *
        Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 3) (fun r => chi (r : ZMod N)) := by
  let f : Nat -> Complex := fun n => if n % 2 = 1 then chi (n : ZMod N) else 0
  have hEven : forall n, f (2 * n) = 0 := by
    intro n
    have hMod : (2 * n) % 2 = 0 := by omega
    simp [f, hMod]
  have hLeft : Finset.sum ((Finset.Icc 1 (4 * M - 1)).filter
      (fun n => M < Nat.largestPrimeFactor n)) f =
      Finset.sum ((oddInterval M).filter (fun n => M < Nat.largestPrimeFactor n))
        (fun n => chi (n : ZMod N)) := by
    unfold oddInterval
    simp only [Finset.sum_filter, f]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hOdd : n % 2 = 1
    next => simp [hOdd]
    next => simp [hOdd]
  have hOne : Nat.largestPrimeFactorRow (4 * M - 1) M 1 =
      (Finset.Icc (M + 1) (4 * M - 1)).filter Nat.Prime := by
    simp [Nat.largestPrimeFactorRow, Nat.largestPrimeFactor,
      max_eq_left (by omega : 1 <= M + 1)]
  have hThree : Nat.largestPrimeFactorRow (4 * M - 1) M 3 =
      (Finset.Icc (M + 1) ((4 * M - 1) / 3)).filter Nat.Prime := by
    unfold Nat.largestPrimeFactorRow
    rw [Nat.largestPrimeFactor_of_prime (by decide : Nat.Prime 3),
      max_eq_left (by omega : 3 <= M + 1)]
  have hFOne : Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 1) f =
      Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 1) (fun r => chi (r : ZMod N)) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hp := (Nat.mem_largestPrimeFactorRow (by decide : 0 < 1)).mp hr
    have hOdd : r % 2 = 1 := hp.1.eq_two_or_odd.resolve_left (by omega)
    simp only [f, if_pos hOdd]
  have hFThree : Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 3) (fun r => f (3 * r)) =
      chi (3 : ZMod N) *
        Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 3) (fun r => chi (r : ZMod N)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hp := (Nat.mem_largestPrimeFactorRow (by decide : 0 < 3)).mp hr
    have hOdd : r % 2 = 1 := hp.1.eq_two_or_odd.resolve_left (by omega)
    have hOddThree : (3 * r) % 2 = 1 := by omega
    simp only [f, if_pos hOddThree, Nat.cast_mul, map_mul, Nat.cast_ofNat]
  have h := Nat.sum_largestPrimeFactor_frontier_eq_two_rows f hEven M hM
  rw [hLeft, <- hOne, <- hThree, hFOne, hFThree] at h
  exact h

theorem exists_uniform_odd_frontier_character_bound :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N), Not (chi = 1) ->
        forall M : Nat, 3 <= M ->
          norm (Finset.sum ((oddInterval M).filter (fun n => M < Nat.largestPrimeFactor n))
            (fun n => chi (n : ZMod N))) <=
            C * ((4 * M - 1 : Nat) : Real) ^ (7 / 8 : Real) *
              (1 + Real.log N + Real.log (((4 * M - 1 : Nat) : Real) + 2)) ^ 2) := by
  let B : Real := Classical.choose QRH.exists_uniform_prime_row_bounds
  have hB := Classical.choose_spec QRH.exists_uniform_prime_row_bounds
  refine Exists.intro (2 * B) (And.intro (by have := hB.1; positivity) ?_)
  intro N inst chi hchi M hM
  let E : Real := B * ((4 * M - 1 : Nat) : Real) ^ (7 / 8 : Real) *
    (1 + Real.log N + Real.log (((4 * M - 1 : Nat) : Real) + 2)) ^ 2
  have hOne : norm (Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 1)
      (fun r => chi (r : ZMod N))) <= E := hB.2 chi hchi (4 * M - 1) M 1
  have hThree : norm (Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 3)
      (fun r => chi (r : ZMod N))) <= E := hB.2 chi hchi (4 * M - 1) M 3
  have hWeighted : norm (chi (3 : ZMod N) *
      Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 3) (fun r => chi (r : ZMod N))) <= E := by
    rw [norm_mul]
    calc
      _ <= 1 * norm (Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 3)
          (fun r => chi (r : ZMod N))) :=
        mul_le_mul_of_nonneg_right (chi.norm_le_one _) (norm_nonneg _)
      _ <= E := by simpa only [one_mul] using hThree
  rw [odd_frontier_character_eq chi M hM]
  calc
    _ <= norm (Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 1)
        (fun r => chi (r : ZMod N))) +
        norm (chi (3 : ZMod N) * Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 3)
          (fun r => chi (r : ZMod N))) := norm_add_le _ _
    _ <= E + E := add_le_add hOne hWeighted
    _ = _ := by dsimp [E]; ring

theorem exists_uniform_odd_frontier_unit_residue_bound :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N] (a : Units (ZMod N)) (M : Nat), 3 <= M ->
        abs (((((oddInterval M).filter (fun n => M < Nat.largestPrimeFactor n)).filter
              (fun (n : Nat) => (n : ZMod N) = (a : ZMod N))).card : Real) -
          ((((oddInterval M).filter (fun n => M < Nat.largestPrimeFactor n)).filter
            (fun (n : Nat) => IsUnit (n : ZMod N))).card : Real) / (N.totient : Real)) <=
            C * ((4 * M - 1 : Nat) : Real) ^ (7 / 8 : Real) *
              (1 + Real.log N + Real.log (((4 * M - 1 : Nat) : Real) + 2)) ^ 2) := by
  let C : Real := Classical.choose exists_uniform_odd_frontier_character_bound
  have hC := Classical.choose_spec exists_uniform_odd_frontier_character_bound
  refine Exists.intro C (And.intro hC.1 ?_)
  intro N inst a M hM
  apply DirichletCharacter.abs_residue_count_sub_unit_mean_le
  next => have := hC.1; positivity
  next => intro chi hchi; exact hC.2 chi hchi M hM

end PrimeFactorOscillations.LPF
