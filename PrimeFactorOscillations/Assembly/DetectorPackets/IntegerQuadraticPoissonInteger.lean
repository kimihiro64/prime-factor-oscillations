/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticPoisson

/-!
# IntegerQuadraticPoissonInteger

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
# Quadratic Poisson summation over all integers

The periodized identity is reindexed by the actual integer quotient and
remainder. Compact support gives convergence of the original lattice sum;
no summability hypothesis is substituted for an analytic proof.
-/


noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticPoissonInteger

open IntegerQuadraticCharacter IntegerQuadraticSquarefree IntegerQuadraticInitial
open IntegerQuadraticPoisson BombieriVinogradov.LargeSieve
open scoped BigOperators

noncomputable local instance unitFintype (q : Nat) : Fintype (Units (ZMod q)) :=
  Fintype.ofFinite _

def residueEquiv (q : Nat) [NeZero q] : Equiv Int (Prod (ZMod q) Int) where
  toFun z := Prod.mk (z : ZMod q) (z / (q : Int))
  invFun p := (p.1.val : Int) + (q : Int) * p.2
  left_inv z := by
    change ((z : ZMod q).val : Int) + (q : Int) * (z / (q : Int)) = z
    rw [ZMod.val_intCast]
    exact Int.emod_add_mul_ediv z (q : Int)
  right_inv p := by
    apply Prod.ext
    . change (((p.1.val : Int) + (q : Int) * p.2 : Int) : ZMod q) = p.1
      simp
    . change ((p.1.val : Int) + (q : Int) * p.2) / (q : Int) = p.2
      rw [Int.add_mul_ediv_left _ _ (by exact_mod_cast NeZero.ne q)]
      have hd : (p.1.val : Int) / (q : Int) = 0 := by
        exact_mod_cast Nat.div_eq_of_lt (ZMod.val_lt p.1)
      rw [hd, zero_add]

theorem residue_real (q : Nat) [NeZero q] (p : Prod (ZMod q) Int) :
    (((residueEquiv q).symm p : Int) : Real) / (q : Real) =
      (p.1.val : Real) / (q : Real) + (p.2 : Real) := by
  have hq : Not ((q : Real) = 0) := by exact_mod_cast NeZero.ne q
  change (((p.1.val : Int) + (q : Int) * p.2 : Int) : Real) / (q : Real) = _
  push_cast
  field_simp

theorem compact_lattice_summable (q : Nat) [NeZero q] (hq : Good q)
    (f : SchwartzMap Real Complex) (B : Nat)
    (hB : forall x : Real, (B : Real) < abs x -> f x = 0) :
    Summable (fun z : Int => character q hq.1 (z : ZMod q) *
      f ((z : Real) / (q : Real))) := by
  classical
  let g : Int -> Complex := fun z => character q hq.1 (z : ZMod q) *
    f ((z : Real) / (q : Real))
  have hqpos : (0 : Real) < (q : Real) := by exact_mod_cast NeZero.pos q
  have hfin : (Function.support g).Finite := by
    apply (Set.finite_Icc (-((B * q : Nat) : Int)) ((B * q : Nat) : Int)).subset
    intro z hz
    change Not (g z = 0) at hz
    by_contra hn
    have hout : (B : Real) < abs ((z : Real) / (q : Real)) := by
      have hn' : z < -((B * q : Nat) : Int) \/ ((B * q : Nat) : Int) < z := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hn
      rw [abs_div, abs_of_pos hqpos]
      have hm : (abs (z : Real) / (q : Real)) * (q : Real) = abs (z : Real) := by
        field_simp
      have hl : (B : Real) * (q : Real) < abs (z : Real) := by
        rcases hn' with h | h
        . apply lt_abs.mpr
          apply Or.inr
          have hr : (z : Real) < -((B : Real) * (q : Real)) := by exact_mod_cast h
          linarith
        . apply lt_abs.mpr
          apply Or.inl
          exact_mod_cast h
      nlinarith
    apply hz
    dsimp [g]
    rw [hB _ hout, mul_zero]
  exact summable_of_hasFiniteSupport hfin

theorem integer_poisson (q : Nat) [NeZero q] (hq : Good q)
    (f : SchwartzMap Real Complex) (B : Nat)
    (hB : forall x : Real, (B : Real) < abs x -> f x = 0) :
    tsum (fun z : Int => character q hq.1 (z : ZMod q) *
      f ((z : Real) / (q : Real))) =
      gaussSum (character q hq.1) ZMod.stdAddChar *
        tsum (fun h : Int => character q hq.1 (h : ZMod q) *
          (FourierTransform.fourier f) (h : Real)) := by
  classical
  let g : Int -> Complex := fun z => character q hq.1 (z : ZMod q) *
    f ((z : Real) / (q : Real))
  let F : Prod (ZMod q) Int -> Complex := fun p =>
    character q hq.1 p.1 * f ((p.1.val : Real) / (q : Real) + (p.2 : Real))
  have heq (p : Prod (ZMod q) Int) : g ((residueEquiv q).symm p) = F p := by
    dsimp [g, F]
    rw [residue_real]
    have hc : (((residueEquiv q).symm p : Int) : ZMod q) = p.1 :=
      congrArg Prod.fst ((residueEquiv q).apply_symm_apply p)
    rw [hc]
  have hg : Summable g := compact_lattice_summable q hq f B hB
  have hF : Summable F := by
    have ht := hg.comp_injective (residueEquiv q).symm.injective
    exact ht.congr heq
  calc
    _ = tsum F := by
      calc
        _ = tsum (fun p : Prod (ZMod q) Int => g ((residueEquiv q).symm p)) :=
          ((residueEquiv q).symm.tsum_eq g).symm
        _ = _ := tsum_congr heq
    _ = tsum (fun x : ZMod q => tsum (fun m : Int =>
        character q hq.1 x * f ((x.val : Real) / (q : Real) + (m : Real)))) :=
      hF.tsum_prod
    _ = Finset.sum Finset.univ (fun x : ZMod q =>
        character q hq.1 x * tsum (fun m : Int =>
          f ((x.val : Real) / (q : Real) + (m : Real)))) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro x hx
      rw [tsum_mul_left]
    _ = Finset.sum Finset.univ (fun k : Units (ZMod q) =>
        character q hq.1 (k : ZMod q) * tsum (fun m : Int =>
          f ((unitFraction k : Real) + (m : Real)))) := by
      rw [<- sum_units_eq_sum_residues (character q hq.1)
        (fun x : ZMod q => tsum (fun m : Int =>
          f ((x.val : Real) / (q : Real) + (m : Real))))]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [unitFraction, Rat.cast_div, Rat.cast_natCast]
    _ = _ := weighted_periodization q hq f

end PrimeFactorOscillations.IntegerQuadraticPoissonInteger

