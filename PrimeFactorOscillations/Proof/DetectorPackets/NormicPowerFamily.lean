/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.GeneralPolynomialDetector

/-!
# NormicPowerFamily

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
# Native normic power families

For fixed integer parameters a,b, the polynomial (X^d-a)^2+b^2 has
degree at most 2d and therefore supplies an existing polynomial-root
probability comparison. At split primes its unit roots partition into
the two power fibres over a+bi and a-bi. At inert primes with b nonzero
the unit-root set is empty. These are local adapters, not moment bounds.
Comparison constants are fixed-law; no growing-parameter sampling theorem
or zero-free exponent improvement is asserted.
-/


noncomputable section
namespace PrimeFactorOscillations.NormicPowerFamily

def polynomial (d : Nat) (a b : Int) : Polynomial Int :=
  (Polynomial.X^d - Polynomial.C a)^2 + Polynomial.C (b^2)

def value {R : Type*} [CommRing R] (d : Nat) (a b x : R) : R :=
  (x^d-a)^2+b^2

theorem natDegree_le (d : Nat) (a b : Int) :
    (polynomial d a b).natDegree <= 2*d := by
  have hb : ((Polynomial.X^d - Polynomial.C a) : Polynomial Int).natDegree <= d :=
    (Polynomial.natDegree_sub_le _ _).trans (by simp)
  unfold polynomial
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  . exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hb)
  . simpa only [Polynomial.natDegree_C] using Nat.zero_le (2*d)

theorem value_factor {R : Type*} [CommRing R] (d : Nat) (a b i x : R)
    (hi : i^2 = -1) :
    value d a b x =
      (x^d-(a+b*i)) * (x^d-(a-b*i)) := by
  calc
    _ = (x^d-a)^2-b^2*i^2 := by rw [hi]; unfold value; ring
    _ = _ := by ring

theorem value_zero_iff {R : Type*} [Field R] (d : Nat) (a b i x : R)
    (hi : i^2 = -1) :
    value d a b x = 0 <-> x^d = a+b*i \/ x^d = a-b*i := by
  rw [value_factor d a b i x hi, mul_eq_zero, sub_eq_zero, sub_eq_zero]

def powerUnitRoots {R : Type*} [Field R] [Fintype R] [DecidableEq R]
    (d : Nat) (c : R) : Finset R :=
  Finset.univ.filter (fun x => Not (x = 0) /\ x^d = c)

def normicUnitRoots {R : Type*} [Field R] [Fintype R] [DecidableEq R]
    (d : Nat) (a b : R) : Finset R :=
  Finset.univ.filter (fun x => Not (x = 0) /\ value d a b x = 0)

theorem unitRoots_split {R : Type*} [Field R] [Fintype R] [DecidableEq R]
    (d : Nat) (a b i : R) (hi : i^2 = -1) :
    normicUnitRoots d a b =
      Union.union (powerUnitRoots d (a+b*i)) (powerUnitRoots d (a-b*i)) := by
  classical
  ext x
  simp only [normicUnitRoots, powerUnitRoots, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union, value_zero_iff d a b i x hi, and_or_left]

theorem split_fibres_disjoint {R : Type*} [Field R] [Fintype R] [DecidableEq R]
    (d : Nat) (a b i : R) (hi : i^2 = -1)
    (h2 : Not ((2 : R) = 0)) (hb : Not (b = 0)) :
    Disjoint (powerUnitRoots d (a+b*i)) (powerUnitRoots d (a-b*i)) := by
  classical
  have hi0 : Not (i = 0) := by
    intro hz
    have hh : (0 : R) = -1 := by
      simpa only [hz, zero_pow (by decide : Not ((2:Nat) = 0))] using hi
    exact (zero_ne_one : Not ((0:R) = 1))
      (by simpa only [neg_zero, neg_neg] using congrArg Neg.neg hh)
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hl := (Finset.mem_filter.mp hx).2.2
  have hr := (Finset.mem_filter.mp hy).2.2
  have heq : a+b*i = a-b*i := hl.symm.trans hr
  have he : b*i = -(b*i) := add_left_cancel
    (show a+b*i = a+ -(b*i) by simpa only [sub_eq_add_neg] using heq)
  have hz : (2:R)*(b*i) = 0 := by
    calc
      _ = b*i+b*i := two_mul _
      _ = -(b*i)+b*i := congrArg (fun y => y+b*i) he
      _ = 0 := neg_add_cancel _
  exact (mul_ne_zero h2 (mul_ne_zero hb hi0)) hz

theorem unitRoots_count_split {R : Type*} [Field R] [Fintype R] [DecidableEq R]
    (d : Nat) (a b i : R) (hi : i^2 = -1)
    (h2 : Not ((2 : R) = 0)) (hb : Not (b = 0)) :
    (normicUnitRoots d a b).card =
      (powerUnitRoots d (a+b*i)).card + (powerUnitRoots d (a-b*i)).card := by
  rw [unitRoots_split d a b i hi]
  exact Finset.card_union_of_disjoint (split_fibres_disjoint d a b i hi h2 hb)

theorem value_ne_zero_of_nonsquare {R : Type*} [Field R]
    (d : Nat) (a b x : R) (hb : Not (b = 0))
    (hno : forall z : R, Not (z^2 = -1)) :
    Not (value d a b x = 0) := by
  intro hv
  have ht : (x^d-a)^2 = -(b^2) :=
    eq_neg_of_add_eq_zero_left hv
  have hs : ((x^d-a)/b)^2 = -1 := by
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 hb)).mpr
    rw [ht]
    ring
  exact hno _ hs

theorem unitRoots_inert {R : Type*} [Field R] [Fintype R] [DecidableEq R]
    (d : Nat) (a b : R) (hb : Not (b = 0))
    (hno : forall z : R, Not (z^2 = -1)) :
    normicUnitRoots d a b = (EmptyCollection.emptyCollection : Finset R) := by
  classical
  ext x
  have hv := value_ne_zero_of_nonsquare d a b x hb hno
  simp [normicUnitRoots, hv]

local instance (p : Nat.Primes) : NeZero (p : Nat) :=
  NeZero.mk p.property.ne_zero

local instance (p : Nat.Primes) : Fact (Nat.Prime (p : Nat)) :=
  Fact.mk p.property

theorem eval_reduction (d : Nat) (a b : Int) (p : Nat.Primes)
    (x : ZMod (p : Nat)) :
    (GeneralPolynomialLaw.reduction (polynomial d a b) p).eval x =
      value d (a : ZMod (p : Nat)) (b : ZMod (p : Nat)) x := by
  simp [GeneralPolynomialLaw.reduction, polynomial, value]

theorem native_unitRootSet (d : Nat) (a b : Int) (p : Nat.Primes) :
    GeneralPolynomialLaw.unitRootSet (polynomial d a b) p =
      normicUnitRoots d (a : ZMod (p : Nat)) (b : ZMod (p : Nat)) := by
  classical
  ext x
  simp [GeneralPolynomialLaw.unitRootSet, GeneralPolynomialLaw.rootSet,
    normicUnitRoots, eval_reduction, and_comm]

theorem native_count_split (d : Nat) (a b : Int) (p : Nat.Primes)
    (i : ZMod (p : Nat)) (hi : i^2 = -1)
    (h2 : Not ((2 : ZMod (p : Nat)) = 0))
    (hb : Not ((b : ZMod (p : Nat)) = 0)) :
    GeneralPolynomialLaw.unitRootCount (polynomial d a b) p =
      (powerUnitRoots d ((a : ZMod (p : Nat))+b*i)).card +
        (powerUnitRoots d ((a : ZMod (p : Nat))-b*i)).card := by
  unfold GeneralPolynomialLaw.unitRootCount
  rw [native_unitRootSet]
  exact unitRoots_count_split d _ _ i hi h2 hb

def primeLaw (d : Nat) (a b : Int) (hd : 0 < d) : PrimeClockLaw :=
  GeneralPolynomialLaw.primeLaw (polynomial d a b) (2*d)
    (Nat.mul_pos (by decide) hd) (natDegree_le d a b)

theorem primeLaw_comparison (d : Nat) (a b : Int) (hd : 0 < d)
    (B : Real) (hB : 0 < B) :
    PowerPolynomialLaw.ComparisonClaim (primeLaw d a b hd) B :=
  GeneralPolynomialLaw.primeLaw_comparison (polynomial d a b) (2*d)
    (Nat.mul_pos (by decide) hd) (natDegree_le d a b) B hB

theorem square_and_quartic_comparison (a b : Int) (B : Real) (hB : 0 < B) :
    PowerPolynomialLaw.ComparisonClaim (primeLaw 2 a b (by decide)) B /\
      PowerPolynomialLaw.ComparisonClaim (primeLaw 4 a b (by decide)) B :=
  And.intro (primeLaw_comparison 2 a b (by decide) B hB)
    (primeLaw_comparison 4 a b (by decide) B hB)

end PrimeFactorOscillations.NormicPowerFamily
