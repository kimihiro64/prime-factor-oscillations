/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import PrimeFactorOscillations.Proof.DetectorPackets.NormicPowerFamily

/-!
# PowerResidueProjector

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
# Exact power-residue character projectors

These finite identities hold without a zero-free hypothesis. They identify
the exact-order-four part of a native normic family difference. They do not
estimate a character moment or assert a zero-free exponent improvement.
-/


open scoped Classical
noncomputable section
namespace PrimeFactorOscillations.PowerResidueProjector

def rootSet (q d : Nat) [NeZero q] (c : ZMod q) : Finset (ZMod q) :=
  Finset.univ.filter (fun x => x^d = c)

def projector (q d : Nat) [NeZero q] (c : ZMod q) : Complex :=
  (Finset.univ.filter (fun chi : DirichletCharacter Complex q => chi^d = 1)).sum
    (fun chi => chi c)

theorem power_character_sum (q d : Nat) [NeZero q] (hd : Not (d = 0))
    (chi : DirichletCharacter Complex q) :
    (Finset.univ.sum (fun x : ZMod q => chi (x^d))) =
      if chi^d = 1 then (q.totient : Complex) else 0 := by
  classical
  have he (x : ZMod q) : chi (x^d) = (chi^d) x := by
    rw [MulChar.pow_apply' chi hd]
    exact map_pow chi.toMonoidHom x d
  simp_rw [he]
  by_cases h : chi^d = 1
  . rw [h]
    simpa only [ite_eq_left rfl, ite_true, ZMod.card_units_eq_totient] using
      (MulChar.sum_one_eq_card_units (R := ZMod q) (R' := Complex))
  . rw [ite_eq_right h]
    exact MulChar.sum_eq_zero_of_ne_one h

theorem rootCount_eq_projector (q d : Nat) [NeZero q]
    (hd : Not (d = 0)) (c : ZMod q) (hc : IsUnit c) :
    ((rootSet q d c).card : Complex) = projector q d (Inv.inv c) := by
  classical
  have hphi : Not ((q.totient : Complex) = 0) := by
    exact Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))))
  apply (mul_right_inj' hphi).mp
  calc
    (q.totient : Complex) * ((rootSet q d c).card : Complex) =
        Finset.univ.sum (fun x : ZMod q =>
          Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
            chi (Inv.inv c) * chi (x^d))) := by
      simp_rw [DirichletCharacter.sum_char_inv_mul_char_eq Complex hc]
      simp [rootSet, Finset.sum_ite, eq_comm, mul_comm]
    _ = Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        chi (Inv.inv c) * Finset.univ.sum (fun x : ZMod q => chi (x^d))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro chi _
      exact (Finset.mul_sum _ _ _).symm
    _ = (q.totient : Complex) * projector q d (Inv.inv c) := by
      simp_rw [power_character_sum q d hd]
      simp [projector, Finset.sum_filter, Finset.mul_sum, mul_comm]

def pureQuarticProjector (q : Nat) [NeZero q] (c : ZMod q) : Complex :=
  (Finset.univ.filter (fun chi : DirichletCharacter Complex q =>
    chi^4 = 1 /\ Not (chi^2 = 1))).sum (fun chi => chi c)

theorem quartic_difference (q : Nat) [NeZero q] (c : ZMod q) (hc : IsUnit c) :
    ((rootSet q 4 c).card : Complex) - ((rootSet q 2 c).card : Complex) =
      pureQuarticProjector q (Inv.inv c) := by
  classical
  rw [rootCount_eq_projector q 4 (by decide) c hc,
    rootCount_eq_projector q 2 (by decide) c hc]
  simp only [projector, pureQuarticProjector, Finset.sum_filter]
  rw [<- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro chi _
  by_cases h2 : chi^2 = 1
  . have h4 : chi^4 = 1 := by
      calc
        chi^4 = (chi^2)^2 := by rw [<- pow_mul]
        _ = 1 := by rw [h2, one_pow]
    simp [h2, h4]
  . simp [h2]

local instance (p : Nat.Primes) : NeZero (p : Nat) :=
  NeZero.mk p.property.ne_zero

local instance (p : Nat.Primes) : Fact (Nat.Prime (p : Nat)) :=
  Fact.mk p.property

theorem rootSet_eq_powerUnitRoots (p : Nat.Primes) (d : Nat)
    (hd : Not (d = 0)) (c : ZMod (p : Nat)) (hc : Not (c = 0)) :
    rootSet (p : Nat) d c = NormicPowerFamily.powerUnitRoots d c := by
  classical
  ext x
  simp only [rootSet, NormicPowerFamily.powerUnitRoots, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  . intro hx
    refine And.intro ?_ hx
    intro hz
    apply hc
    rw [<- hx, hz, zero_pow hd]
  . exact And.right

theorem unit_quartic_difference (p : Nat.Primes)
    (c : ZMod (p : Nat)) (hc : Not (c = 0)) :
    ((NormicPowerFamily.powerUnitRoots 4 c).card : Complex) -
      ((NormicPowerFamily.powerUnitRoots 2 c).card : Complex) =
        pureQuarticProjector (p : Nat) (Inv.inv c) := by
  have h := quartic_difference (p : Nat) c (isUnit_iff_ne_zero.mpr hc)
  rw [rootSet_eq_powerUnitRoots p 4 (by decide) c hc,
    rootSet_eq_powerUnitRoots p 2 (by decide) c hc] at h
  exact h

theorem normic_quartic_difference (p : Nat.Primes)
    (a b i : ZMod (p : Nat)) (hi : i^2 = -1)
    (h2 : Not ((2 : ZMod (p : Nat)) = 0)) (hb : Not (b = 0))
    (hp : Not (a+b*i = 0)) (hm : Not (a-b*i = 0)) :
    ((NormicPowerFamily.normicUnitRoots 4 a b).card : Complex) -
      ((NormicPowerFamily.normicUnitRoots 2 a b).card : Complex) =
        pureQuarticProjector (p : Nat) (Inv.inv (a+b*i)) +
          pureQuarticProjector (p : Nat) (Inv.inv (a-b*i)) := by
  classical
  rw [NormicPowerFamily.unitRoots_count_split 4 a b i hi h2 hb,
    NormicPowerFamily.unitRoots_count_split 2 a b i hi h2 hb,
    Nat.cast_add, Nat.cast_add]
  calc
    _ = (((NormicPowerFamily.powerUnitRoots 4 (a+b*i)).card : Complex) -
          ((NormicPowerFamily.powerUnitRoots 2 (a+b*i)).card : Complex)) +
        (((NormicPowerFamily.powerUnitRoots 4 (a-b*i)).card : Complex) -
          ((NormicPowerFamily.powerUnitRoots 2 (a-b*i)).card : Complex)) := by ring
    _ = _ := by
      rw [unit_quartic_difference p (a+b*i) hp,
        unit_quartic_difference p (a-b*i) hm]

theorem native_quartic_difference (a b : Int) (p : Nat.Primes)
    (i : ZMod (p : Nat)) (hi : i^2 = -1)
    (h2 : Not ((2 : ZMod (p : Nat)) = 0))
    (hb : Not ((b : ZMod (p : Nat)) = 0))
    (hp : Not ((a : ZMod (p : Nat))+b*i = 0))
    (hm : Not ((a : ZMod (p : Nat))-b*i = 0)) :
    (GeneralPolynomialLaw.unitRootCount (NormicPowerFamily.polynomial 4 a b) p : Complex) -
      (GeneralPolynomialLaw.unitRootCount (NormicPowerFamily.polynomial 2 a b) p : Complex) =
        pureQuarticProjector (p : Nat) (Inv.inv ((a : ZMod (p : Nat))+b*i)) +
          pureQuarticProjector (p : Nat) (Inv.inv ((a : ZMod (p : Nat))-b*i)) := by
  unfold GeneralPolynomialLaw.unitRootCount
  rw [NormicPowerFamily.native_unitRootSet, NormicPowerFamily.native_unitRootSet]
  exact normic_quartic_difference p _ _ i hi h2 hb hp hm

end PrimeFactorOscillations.PowerResidueProjector
