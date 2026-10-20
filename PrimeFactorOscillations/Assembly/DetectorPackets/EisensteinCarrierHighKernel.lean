/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Eisenstein.CompactEnergyFamilies
import PrimeFactorOscillations.Assembly.DetectorPackets.CarrierIndexedAdmission

/-!
# EisensteinCarrierHighKernel

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
# Uniform probability error on the squareful high-kernel rows

Rows are all supported ideals whose squarefree part has norm greater
than K. Their square parts and the source coprimality masks are retained.
The perfect-square rows are not erased from the full research target:
they lie in the complementary low packet and still need an independent
joint arithmetic estimate.
-/


noncomputable section
namespace PrimeFactorOscillations.EisensteinCarrierHighKernel

abbrev Columns (N : Real) : Type :=
  {J : Ideal OAI.CanonicalQuadraticSieve.O //
    Membership.mem (OAI.CanonicalQuadraticSieve.idealRange N) J}

abbrev Rows (M K : Real) : Type :=
  {J : Ideal OAI.CanonicalQuadraticSieve.O //
    Membership.mem (OAI.CanonicalQuadraticSieve.highKernelRange M K) J}

def energy (M N K : Real) (a : Columns N -> Complex) : Real :=
  Finset.univ.sum fun r : Rows M K =>
    norm (Finset.univ.sum fun i : Columns N =>
      OAI.CanonicalQuadraticSieve.highKernelMatrix M N K r i * a i) ^ 2

theorem exists_uniform_high_energy_bound (eps : Real) (heps : 0 < eps) :
    exists Cs : Real, 0 < Cs /\
      forall (M N K : Real), 1 <= M -> 1 <= N -> 1 <= K ->
      forall a : Columns N -> Complex,
        energy M N K a <=
          Cs * (M * N) ^ eps * (M + Real.sqrt (M / K) * N) *
            (Finset.univ.sum fun i : Columns N => norm (a i) ^ 2) := by
  classical
  choose Cs hCs hHigh using
    OAI.CanonicalQuadraticSieve.HasSieveExponent.high_kernel
      OAI.CanonicalQuadraticSieve.hasSieveExponent_one eps heps
  refine Exists.intro Cs (And.intro hCs ?_)
  intro M N K hM hN hK a
  have hHigh' : OAI.CanonicalQuadraticSieve.highKernelNorm M N K <=
      Cs * (M * N) ^ eps * (M + Real.sqrt (M / K) * N) := by
    simpa only [Real.rpow_one] using hHigh M N K hM hN hK
  have hBase : energy M N K a <=
      OAI.CanonicalQuadraticSieve.highKernelNorm M N K *
        (Finset.univ.sum fun i : Columns N => norm (a i) ^ 2) :=
    OAI.FiniteSieveOperator.energy_bound
      (OAI.CanonicalQuadraticSieve.highKernelMatrix M N K) a
  exact hBase.trans (mul_le_mul_of_nonneg_right hHigh'
    (Finset.sum_nonneg (fun i _ => sq_nonneg (norm (a i)))))

theorem exists_uniform_probability_high_kernel :
    exists n0 : Nat, exists C0 : Real, 100 <= n0 /\ 0 < C0 /\
      forall eps : Real, 0 < eps ->
      exists Cs : Real, 0 < Cs /\
      forall (d h : Nat), 2 <= d -> n0 <= h ->
      forall (M N K : Real), 1 <= M -> 1 <= N -> 1 <= K ->
      forall (a : Columns N -> Complex)
        (ha : forall i, norm (a i) <= (h : Real)),
      exists f : Columns N -> Complex,
        (forall i, exists O : UniformCarrier.CoefficientObservation d h (a i) (ha i),
          f i = O.value) /\
        (forall i, norm (f i - a i) <= C0 / (h : Real) ^ (d - 1)) /\
        energy M N K (fun i => f i - a i) <=
          Cs * (M * N) ^ eps * (M + Real.sqrt (M / K) * N) *
            ((Fintype.card (Columns N) : Real) *
              (C0 / (h : Real) ^ (d - 1)) ^ 2) := by
  classical
  choose n0 C0 hn0 hC0 hPoint using
    UniformCarrier.IndexedAdmission.exists_uniform_point_observations
  refine Exists.intro n0 (Exists.intro C0 (And.intro hn0 (And.intro hC0 ?_)))
  intro eps heps
  choose Cs hCs hEnergy using exists_uniform_high_energy_bound eps heps
  refine Exists.intro Cs (And.intro hCs ?_)
  intro d h hd hh M N K hM hN hK a ha
  choose O hO using fun i : Columns N => hPoint d hd h hh (a i) (ha i)
  let f : Columns N -> Complex := fun i => (O i).value
  have hErr : forall i, norm (f i - a i) <= C0 / (h : Real) ^ (d - 1) := hO
  have hMass : (Finset.univ.sum fun i : Columns N => norm (f i - a i) ^ 2) <=
      (Fintype.card (Columns N) : Real) * (C0 / (h : Real) ^ (d - 1)) ^ 2 := by
    calc
      _ <= Finset.univ.sum (fun _ : Columns N =>
          (C0 / (h : Real) ^ (d - 1)) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        gcongr <;> exact hErr i
      _ = _ := by simp
  have hCost : 0 <= Cs * (M * N) ^ eps *
      (M + Real.sqrt (M / K) * N) := by
    positivity
  refine Exists.intro f (And.intro ?_ (And.intro hErr ?_))
  . intro i
    exact Exists.intro (O i) rfl
  . exact (hEnergy M N K hM hN hK (fun i => f i - a i)).trans
      (mul_le_mul_of_nonneg_left hMass hCost)

end PrimeFactorOscillations.EisensteinCarrierHighKernel
