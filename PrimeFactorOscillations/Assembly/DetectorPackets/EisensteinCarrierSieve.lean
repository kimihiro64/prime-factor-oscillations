/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Eisenstein.CompactEnergyFamilies
import PrimeFactorOscillations.Assembly.DetectorPackets.CarrierIndexedAdmission

/-!
# EisensteinCarrierSieve

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
# Actual probability observations under the sharp quadratic large sieve

The coefficient observation constants are independent of the degree,
coefficient array, row and column families, and sieve ranges. The large
sieve is applied to the actual observed array. No arithmetic cancellation
or zero-free estimate is an input to this theorem.
-/


noncomputable section
namespace PrimeFactorOscillations.EisensteinCarrierSieve

open UniformCarrier

theorem exists_uniform_probability_quadratic_sieve :
    exists n0 : Nat, exists C0 : Real, 100 <= n0 /\ 0 < C0 /\
      forall eps : Real, 0 < eps ->
      exists Cs : Real, 0 < Cs /\
      forall (d h : Nat), 2 <= d -> n0 <= h ->
      forall (M N : Real), 1 <= M -> 1 <= N ->
      forall (R I : Type) [Fintype R] [Fintype I]
        (rows : R -> Ideal OAI.CanonicalQuadraticSieve.O)
        (cols : I -> Ideal OAI.CanonicalQuadraticSieve.O),
      Function.Injective rows -> Function.Injective cols ->
      (forall r, OAI.CanonicalQuadraticSieve.Admissible (rows r) /\
        (Ideal.absNorm (rows r) : Real) <= M) ->
      (forall i, OAI.CanonicalQuadraticSieve.Admissible (cols i) /\
        (Ideal.absNorm (cols i) : Real) <= N) ->
      forall (a : I -> Complex) (ha : forall i, norm (a i) <= (h : Real)),
      exists f : I -> Complex,
        (forall i, exists O : CoefficientObservation d h (a i) (ha i),
          f i = O.value) /\
        (forall i, norm (f i - a i) <= C0 / (h : Real) ^ (d - 1)) /\
        (Finset.univ.sum fun r : R =>
          norm (Finset.univ.sum fun i : I =>
            OAI.CanonicalQuadraticSieve.quadraticRow (cols i)
              (OAI.CompletedGauss.primaryGenerator (rows r)) * (f i - a i)) ^ 2) <=
          Cs * (M * N) ^ eps * (M + N) *
            ((Fintype.card I : Real) * (C0 / (h : Real) ^ (d - 1)) ^ 2) /\
        (Finset.univ.sum fun r : R =>
          norm (Finset.univ.sum fun i : I =>
            OAI.CanonicalQuadraticSieve.quadraticRow (cols i)
              (OAI.CompletedGauss.primaryGenerator (rows r)) * f i) ^ 2) <=
          Cs * (M * N) ^ eps * (M + N) *
            (2 * (Finset.univ.sum fun i : I => norm (a i) ^ 2) +
              2 * (Fintype.card I : Real) *
                (C0 / (h : Real) ^ (d - 1)) ^ 2) := by
  classical
  choose n0 C0 hn0 hC0 hPoint using
    UniformCarrier.IndexedAdmission.exists_uniform_point_observations
  refine Exists.intro n0 (Exists.intro C0 (And.intro hn0 (And.intro hC0 ?_)))
  intro eps heps
  choose Cs hCs hSieve using
    OAI.CanonicalQuadraticSieve.finite_family_quadratic_large_sieve eps heps
  refine Exists.intro Cs (And.intro hCs ?_)
  intro d h hd hh M N hM hN R I _ _ rows cols hr hc hrows hcols a ha
  choose O hO using fun i : I => hPoint d hd h hh (a i) (ha i)
  let f : I -> Complex := fun i => (O i).value
  have hErr : forall i, norm (f i - a i) <= C0 / (h : Real) ^ (d - 1) := hO
  have hEach : forall i, norm (f i) ^ 2 <=
      2 * norm (a i) ^ 2 + 2 * (C0 / (h : Real) ^ (d - 1)) ^ 2 := by
    intro i
    have hNorm : norm (f i) <= norm (a i) + C0 / (h : Real) ^ (d - 1) := by
      calc
        norm (f i) = norm (a i + (f i - a i)) := by congr 1; ring
        _ <= norm (a i) + norm (f i - a i) := norm_add_le _ _
        _ <= norm (a i) + C0 / (h : Real) ^ (d - 1) :=
          add_le_add (le_refl (norm (a i))) (hErr i)
    calc
      norm (f i) ^ 2 <= (norm (a i) + C0 / (h : Real) ^ (d - 1)) ^ 2 := by
        gcongr
      _ <= 2 * norm (a i) ^ 2 + 2 * (C0 / (h : Real) ^ (d - 1)) ^ 2 := by
        nlinarith [sq_nonneg (norm (a i) - C0 / (h : Real) ^ (d - 1))]
  have hMass : (Finset.univ.sum fun i : I => norm (f i) ^ 2) <=
      2 * (Finset.univ.sum fun i : I => norm (a i) ^ 2) +
        2 * (Fintype.card I : Real) * (C0 / (h : Real) ^ (d - 1)) ^ 2 := by
    calc
      _ <= Finset.univ.sum (fun i : I =>
          2 * norm (a i) ^ 2 + 2 * (C0 / (h : Real) ^ (d - 1)) ^ 2) :=
        Finset.sum_le_sum (fun i _ => hEach i)
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hCost : 0 <= Cs * (M * N) ^ eps * (M + N) := by
    exact mul_nonneg (mul_nonneg hCs.le (Real.rpow_nonneg (by positivity) _))
      (by linarith)
  have hErrorMass : (Finset.univ.sum fun i : I => norm (f i - a i) ^ 2) <=
      (Fintype.card I : Real) * (C0 / (h : Real) ^ (d - 1)) ^ 2 := by
    calc
      _ <= Finset.univ.sum (fun _ : I =>
          (C0 / (h : Real) ^ (d - 1)) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        gcongr <;> exact hErr i
      _ = _ := by simp
  have hErrorSieve := (hSieve M N hM hN rows cols hr hc hrows hcols
    (fun i => f i - a i)).trans (mul_le_mul_of_nonneg_left hErrorMass hCost)
  refine Exists.intro f (And.intro ?_ (And.intro hErr (And.intro hErrorSieve ?_)))
  . intro i
    exact Exists.intro (O i) rfl
  . exact (hSieve M N hM hN rows cols hr hc hrows hcols f).trans
      (mul_le_mul_of_nonneg_left hMass hCost)

end PrimeFactorOscillations.EisensteinCarrierSieve
