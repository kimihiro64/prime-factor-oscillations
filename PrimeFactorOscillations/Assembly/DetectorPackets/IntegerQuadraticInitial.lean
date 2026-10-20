/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import BombieriVinogradov.Proof.LargeSieve.CharacterReduction
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticSquarefree

/-!
# IntegerQuadraticInitial

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
# Initial integer quadratic-sieve bound

The exact Jacobi transform embeds the supported odd squarefree columns
in the reduced Farey frequencies. Its coefficient mass is at most the
original mass. The cached dual additive large sieve then gives the
initial M + N^2 estimate. This is not the sharp quadratic large sieve.
-/


noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticInitial

open QuadraticCarrierPacket IntegerQuadraticCharacter IntegerQuadraticSquarefree
open BombieriVinogradov.LargeSieve
open scoped BigOperators

noncomputable local instance unitFintype (q : Nat) : Fintype (Units (ZMod q)) :=
  Fintype.ofFinite _

abbrev Good (q : Nat) : Prop := 1 < q /\ Odd q /\ Squarefree q

def fourierCoefficient {N : Nat} (a : Nat -> Complex) (i : FareyIndex N) : Complex := by
  classical
  exact if h : Good i.1.1 then
    letI : NeZero i.1.1 := NeZero.mk (by have := h.1; omega)
    a i.1.1 * character i.1.1 h.1 (i.2 : ZMod i.1.1) /
      gaussSum (character i.1.1 h.1) ZMod.stdAddChar
  else 0

theorem gauss_ne_zero (q : Nat) [NeZero q] (h : Good q) :
    Not (gaussSum (character q h.1) ZMod.stdAddChar = 0) := by
  have hg := squarefree_gauss_norm_sq q h.1 h.2.1 h.2.2
    ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar q)
  intro hz
  rw [hz, norm_zero, zero_pow (by decide : Not (2 = 0))] at hg
  have hq : (0 : Real) < (q : Real) := by
    exact_mod_cast (show 0 < q from Nat.zero_lt_of_lt h.1)
  linarith

theorem unit_fourier_identity {N : Nat} (a : Nat -> Complex)
    (q : {q : Nat // Membership.mem (Finset.Icc 1 N) q}) (u : Nat)
    (hs : Not (a q.1 = 0) -> Good q.1) :
    (Finset.sum Finset.univ (fun k : Units (ZMod q.1) =>
      additivePhase ((u : Real) * (unitFraction k : Real)) *
        fourierCoefficient a (Sigma.mk q k))) =
      a q.1 * kernel u q.1 := by
  classical
  letI : NeZero q.1 := NeZero.mk (by
    have := (Finset.mem_Icc.mp q.2).1
    omega)
  by_cases h : Good q.1
  . have hG := gauss_ne_zero q.1 h
    have hphase (k : Units (ZMod q.1)) :
        additivePhase ((u : Real) * (unitFraction k : Real)) =
          ZMod.stdAddChar ((u : ZMod q.1) * (k : ZMod q.1)) := by
      simpa only [Int.cast_natCast, Int.cast_ofNat] using
        additivePhase_int_unitFraction (u : Int) k
    simp only [fourierCoefficient, Good, h, and_self, dite_true]
    simp_rw [hphase]
    calc
      _ = (a q.1 / gaussSum (character q.1 h.1) ZMod.stdAddChar) *
          Finset.sum Finset.univ (fun k : Units (ZMod q.1) =>
            character q.1 h.1 (k : ZMod q.1) *
              ZMod.stdAddChar ((u : ZMod q.1) * (k : ZMod q.1))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = (a q.1 / gaussSum (character q.1 h.1) ZMod.stdAddChar) *
          gaussSum (character q.1 h.1)
            (ZMod.stdAddChar.mulShift (u : ZMod q.1)) := by
        rw [sum_units_eq_sum_residues (character q.1 h.1)
          (fun x : ZMod q.1 => ZMod.stdAddChar ((u : ZMod q.1) * x))]
        rfl
      _ = (a q.1 / gaussSum (character q.1 h.1) ZMod.stdAddChar) *
          (character q.1 h.1 (u : ZMod q.1) *
            gaussSum (character q.1 h.1) ZMod.stdAddChar) := by
        rw [squarefree_fourier_factor q.1 h.1 h.2.1 h.2.2]
      _ = a q.1 * kernel u q.1 := by
        rw [character_natCast]
        field_simp
  . have ha : a q.1 = 0 := by
      by_contra hz
      exact h (hs hz)
    simp [fourierCoefficient, h, ha]

theorem unit_coefficient_mass {N : Nat} (a : Nat -> Complex)
    (q : {q : Nat // Membership.mem (Finset.Icc 1 N) q}) :
    (Finset.sum Finset.univ (fun k : Units (ZMod q.1) =>
      norm (fourierCoefficient a (Sigma.mk q k)) ^ 2)) <= norm (a q.1) ^ 2 := by
  classical
  letI : NeZero q.1 := NeZero.mk (by
    have := (Finset.mem_Icc.mp q.2).1
    omega)
  by_cases h : Good q.1
  . have hG := squarefree_gauss_norm_sq q.1 h.1 h.2.1 h.2.2
      ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar q.1)
    have hq : (0 : Real) < (q.1 : Real) := by exact_mod_cast (NeZero.pos q.1)
    have hterm (k : Units (ZMod q.1)) :
        norm (fourierCoefficient a (Sigma.mk q k)) ^ 2 <=
          norm (a q.1) ^ 2 / (q.1 : Real) := by
      have hc := (character q.1 h.1).norm_le_one (k : ZMod q.1)
      have hc0 := norm_nonneg (character q.1 h.1 (k : ZMod q.1))
      have hc2 : norm (character q.1 h.1 (k : ZMod q.1)) ^ 2 <= 1 := by
        nlinarith
      simp only [fourierCoefficient, Good, h, and_self, dite_true,
        norm_div, norm_mul, mul_pow, div_pow]
      rw [hG]
      apply div_le_div_of_nonneg_right _ (le_of_lt hq)
      nlinarith [sq_nonneg (norm (a q.1))]
    calc
      _ <= Finset.sum Finset.univ (fun _k : Units (ZMod q.1) =>
          norm (a q.1) ^ 2 / (q.1 : Real)) := by
        exact Finset.sum_le_sum (fun k hk => hterm k)
      _ = (q.1.totient : Real) * (norm (a q.1) ^ 2 / (q.1 : Real)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ZMod.card_units_eq_totient]
      _ <= (q.1 : Real) * (norm (a q.1) ^ 2 / (q.1 : Real)) := by
        apply mul_le_mul_of_nonneg_right
        . exact_mod_cast Nat.totient_le q.1
        . positivity
      _ = norm (a q.1) ^ 2 := by field_simp
  . simp [fourierCoefficient, h, sq_nonneg]

theorem farey_sample_eq {N : Nat} (a : Nat -> Complex) (u : Nat)
    (hs : forall q, Membership.mem (Finset.Icc 1 N) q ->
      Not (a q = 0) -> Good q) :
    fareyDualSample (fourierCoefficient (N := N) a) u =
      Finset.sum (Finset.Icc 1 N) (fun q => a q * kernel u q) := by
  classical
  unfold fareyDualSample fareyIndices
  rw [Finset.sum_sigma]
  calc
    _ = Finset.sum (Finset.Icc 1 N).attach (fun q => a q.1 * kernel u q.1) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact unit_fourier_identity a q u (hs q.1 q.2)
    _ = _ := Finset.sum_attach (Finset.Icc 1 N) (fun q => a q * kernel u q)

theorem farey_coefficient_mass {N : Nat} (a : Nat -> Complex) :
    (Finset.sum (fareyIndices N) (fun i => norm (fourierCoefficient a i) ^ 2)) <=
      Finset.sum (Finset.Icc 1 N) (fun q => norm (a q) ^ 2) := by
  classical
  unfold fareyIndices
  rw [Finset.sum_sigma]
  calc
    _ <= Finset.sum (Finset.Icc 1 N).attach (fun q => norm (a q.1) ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      exact unit_coefficient_mass a q
    _ = _ := Finset.sum_attach (Finset.Icc 1 N) (fun q => norm (a q) ^ 2)

theorem initial_quadratic_sieve {M N : Nat} (hM : 0 < M) (hN : 0 < N)
    (a : Nat -> Complex)
    (hs : forall q, Membership.mem (Finset.Icc 1 N) q ->
      Not (a q = 0) -> Good q) :
    (Finset.sum Finset.univ (fun u : Fin M =>
      norm (Finset.sum (Finset.Icc 1 N) (fun q => a q * kernel u.val q)) ^ 2)) <=
      36 * ((M : Real) + (N : Real) ^ 2) *
        Finset.sum (Finset.Icc 1 N) (fun q => norm (a q) ^ 2) := by
  calc
    _ = Finset.sum Finset.univ (fun u : Fin M =>
        norm (fareyDualSample (fourierCoefficient (N := N) a) u.val) ^ 2) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [farey_sample_eq a u.val hs]
    _ <= 36 * ((M : Real) + (N : Real) ^ 2) *
        Finset.sum (fareyIndices N) (fun i => norm (fourierCoefficient a i) ^ 2) :=
      fareyDualEnergy hN hM _
    _ <= _ := mul_le_mul_of_nonneg_left (farey_coefficient_mass a) (by positivity)

end PrimeFactorOscillations.IntegerQuadraticInitial

