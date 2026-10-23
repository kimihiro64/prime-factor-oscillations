/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import PrimeFactorOscillations.Helpers.PrimeOrderReturnLaw

/-!
# Exact image indices of modular shortened-period maps

The native finite-group law is transported through group equivalences and
products. Squarefree modular CRT then identifies every actual unit-group
image index with an explicit product of local cyclic gcd ratios. The
physical divisor prime two is retained, as are arbitrary power exponents.
This is the arithmetic input for the Carmichael attainment theorem.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeOrderReturnIndex

open PrimeOrderReturnLaw

variable {G H : Type*} [CommGroup G] [CommGroup H] [Fintype G] [Fintype H]

local instance primeNeZero (p : Nat.Primes) : NeZero (p : Nat) :=
  NeZero.mk p.property.ne_zero

local instance factorNeZero (c : Nat) (p : c.primeFactors) : NeZero (p.val : Nat) :=
  NeZero.mk (Nat.mem_primeFactors.mp p.property).1.ne_zero

/-- Power images are preserved by the actual group isomorphism. -/
def returnImageEquiv (e : MulEquiv G H) (L l : Nat) :
    Equiv (returnImage (G := G) L l) (returnImage (G := H) L l) := by
  refine
    { toFun := fun x => Subtype.mk (e x.val) ?_
      invFun := fun y => Subtype.mk (e.symm y.val) ?_
      left_inv := ?_
      right_inv := ?_ }
  { choose g hg using x.property
    refine Exists.intro (e g) ?_
    simp only [powMonoidHom_apply] at hg
    simp only [powMonoidHom_apply]
    rw [<- map_pow, hg] }
  { choose h hh using y.property
    refine Exists.intro (e.symm h) ?_
    simp only [powMonoidHom_apply] at hh
    simp only [powMonoidHom_apply]
    rw [<- map_pow, hh] }
  { intro x
    apply Subtype.ext
    exact e.symm_apply_apply x.val }
  { intro y
    apply Subtype.ext
    exact e.apply_symm_apply y.val }

/-- Normalize with the checked enumeration instance before changing group coordinates. -/
theorem returnIndex_eq_natCard (L l : Nat) :
    returnIndex (G := G) L l = Nat.card (returnImage (G := G) L l) := by
  exact (@Nat.card_eq_fintype_card (returnImage (G := G) L l)
    (PrimeOrderReturnLaw.imageFintype (G := G) L l)).symm

theorem returnIndex_congr (e : MulEquiv G H) (L l : Nat) :
    returnIndex (G := G) L l = returnIndex (G := H) L l := by
  classical
  rw [returnIndex_eq_natCard, returnIndex_eq_natCard]
  exact Nat.card_congr (returnImageEquiv e L l)

/-- Every local power-image coordinate has its own independent lift. -/
def returnImagePiEquiv {I : Type*} [Fintype I] (A : I -> Type*)
    [forall i, CommGroup (A i)] [forall i, Fintype (A i)] (L l : Nat) :
    Equiv (returnImage (G := (i : I) -> A i) L l)
      ((i : I) -> returnImage (G := A i) L l) := by
  classical
  refine
    { toFun := fun x i => Subtype.mk (x.val i) ?_
      invFun := fun y => Subtype.mk (fun i => (y i).val) ?_
      left_inv := ?_
      right_inv := ?_ }
  { choose g hg using x.property
    refine Exists.intro (g i) ?_
    have h := congrFun hg i
    simpa only [powMonoidHom_apply, Pi.pow_apply] using h }
  { choose g hg using fun i : I => (y i).property
    refine Exists.intro g ?_
    simp only [powMonoidHom_apply]
    funext i
    simpa only [powMonoidHom_apply, Pi.pow_apply] using hg i }
  { intro x
    apply Subtype.ext
    rfl }
  { intro y
    funext i
    apply Subtype.ext
    rfl }

theorem returnIndex_pi {I : Type*} [Fintype I] [DecidableEq I] (A : I -> Type*)
    [forall i, CommGroup (A i)] [forall i, Fintype (A i)] (L l : Nat) :
    returnIndex (G := (i : I) -> A i) L l =
      Finset.univ.prod (fun i : I => returnIndex (G := A i) L l) := by
  classical
  rw [returnIndex_eq_natCard, Nat.card_congr (returnImagePiEquiv A L l)]
  have hPi : Nat.card ((i : I) -> returnImage (G := A i) L l) =
      Finset.univ.prod (fun i : I => Nat.card (returnImage (G := A i) L l)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_pi]
    simp only [Nat.card_eq_fintype_card]
  rw [hPi]
  apply Finset.prod_congr rfl
  intro i _
  exact (returnIndex_eq_natCard (G := A i) L l).symm

/-- The existing cyclic power-image theorem in the native index normalization. -/
theorem returnIndex_cyclic [IsCyclic G] (L l : Nat) :
    returnIndex (G := G) L l = Fintype.card G / Nat.gcd (Fintype.card G) (L / l) := by
  classical
  rw [returnIndex_eq_natCard]
  have h := IsCyclic.card_powMonoidHom_range (G := G) (L / l)
  simpa only [returnImage, Nat.card_eq_fintype_card] using h

/-- The physical prime two has local unit-group order one and is not omitted. -/
theorem prime_unit_returnIndex (p : Nat.Primes) (L l : Nat) :
    returnIndex (G := Units (ZMod (p : Nat))) L l =
      ((p : Nat) - 1) / Nat.gcd ((p : Nat) - 1) (L / l) := by
  classical
  letI : Fact (Nat.Prime (p : Nat)) := Fact.mk p.property
  have h := returnIndex_cyclic (G := Units (ZMod (p : Nat))) L l
  simpa only [ZMod.card_units_eq_totient, Nat.totient_prime p.property] using h

/-- Squarefree CRT is applied to the entire unit group, with all prime factors. -/
def squarefreeUnitEquiv (c : Nat) [NeZero c] (hSq : Squarefree c) :
    MulEquiv (Units (ZMod c)) ((p : c.primeFactors) -> Units (ZMod (p.val : Nat))) := by
  have hVal : forall p : c.primeFactors, c.factorization (p.val : Nat) = 1 := by
    intro p
    have hp := Nat.mem_primeFactors.mp p.property
    exact Nat.factorization_eq_one_of_squarefree hSq hp.1 hp.2.1
  let e : RingEquiv (ZMod c) ((p : c.primeFactors) -> ZMod (p.val : Nat)) :=
    (ZMod.equivPi c (NeZero.ne c)).trans
      (RingEquiv.piCongrRight (fun p : c.primeFactors =>
        ZMod.ringEquivCongr (by rw [hVal p, pow_one])))
  exact (Units.mapEquiv e.toMulEquiv).trans MulEquiv.piUnits

/-- The full arithmetic formula for every actual shortened-period image size. -/
theorem squarefree_unit_returnIndex (c : Nat) [NeZero c] (hSq : Squarefree c)
    (L l : Nat) :
    returnIndex (G := Units (ZMod c)) L l =
      Finset.univ.prod (fun p : c.primeFactors =>
        ((p.val : Nat) - 1) / Nat.gcd ((p.val : Nat) - 1) (L / l)) := by
  classical
  rw [returnIndex_congr (squarefreeUnitEquiv c hSq) L l, returnIndex_pi]
  apply Finset.prod_congr rfl
  intro p _
  let r : Nat.Primes := Subtype.mk p.val (Nat.mem_primeFactors.mp p.property).1
  exact prime_unit_returnIndex r L l

/-- Removing one prime from a common period either preserves a local period
or loses exactly that prime, with no coprimality assumption suppressed. -/
theorem local_period_ratio (m L : Nat) (l : Nat.Primes) (hm : 0 < m)
    (hmL : Dvd.dvd m L) (hlL : Dvd.dvd (l : Nat) L) :
    m / Nat.gcd m (L / (l : Nat)) =
      if Dvd.dvd m (L / (l : Nat)) then 1 else (l : Nat) := by
  have hg : 0 < Nat.gcd m (L / (l : Nat)) :=
    Nat.gcd_pos_of_pos_left _ hm
  have hd : Dvd.dvd (m / Nat.gcd m (L / (l : Nat))) (l : Nat) := by
    apply (Nat.coprime_div_gcd_div_gcd hg).dvd_of_dvd_mul_right
    apply Nat.dvd_of_mul_dvd_mul_right hg
    rw [Nat.div_mul_cancel (Nat.gcd_dvd_left _ _), mul_assoc,
      Nat.div_mul_cancel (Nat.gcd_dvd_right _ _), Nat.mul_div_cancel' hlL]
    exact hmL
  split_ifs with h
  { rw [Nat.gcd_eq_left h, Nat.div_self hm] }
  { rcases (Nat.dvd_prime l.property).mp hd with hOne | hPrime
    { exfalso
      apply h
      have hmEq : m = Nat.gcd m (L / (l : Nat)) := by
        calc
          m = (m / Nat.gcd m (L / (l : Nat))) * Nat.gcd m (L / (l : Nat)) :=
            (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
          _ = Nat.gcd m (L / (l : Nat)) := by rw [hOne, one_mul]
      rw [hmEq]
      exact Nat.gcd_dvd_right _ _ }
    { exact hPrime } }

/-- The local canonical exponent includes the prime-two unit group of order one. -/
theorem prime_unit_exponent (p : Nat.Primes) :
    Monoid.exponent (Units (ZMod (p : Nat))) = (p : Nat) - 1 := by
  letI : Fact (Nat.Prime (p : Nat)) := Fact.mk p.property
  rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime p.property]

/-- The canonical exponent is exactly the lcm of all local prime periods. -/
theorem squarefree_unit_exponent (c : Nat) [NeZero c] (hSq : Squarefree c) :
    Monoid.exponent (Units (ZMod c)) =
      Finset.univ.lcm (fun p : c.primeFactors => (p.val : Nat) - 1) := by
  classical
  rw [Monoid.exponent_eq_of_mulEquiv (squarefreeUnitEquiv c hSq),
    Monoid.exponent_pi]
  congr 1
  funext p
  let r : Nat.Primes := Subtype.mk p.val (Nat.mem_primeFactors.mp p.property).1
  exact prime_unit_exponent r

/-- Number of local periods lost after shortening the common period by a prime. -/
def returnMultiplicity (c L : Nat) (l : Nat.Primes) : Nat :=
  (Finset.univ.filter (fun p : c.primeFactors =>
    Not (Dvd.dvd ((p.val : Nat) - 1) (L / (l : Nat))))).card

/-- Each lost local period contributes one full prime coordinate to the image. -/
theorem squarefree_unit_returnIndex_eq_prime_pow (c : Nat) [NeZero c]
    (hSq : Squarefree c) (L : Nat) (l : Nat.Primes)
    (hPeriods : forall p : c.primeFactors, Dvd.dvd ((p.val : Nat) - 1) L)
    (hlL : Dvd.dvd (l : Nat) L) :
    returnIndex (G := Units (ZMod c)) L (l : Nat) =
      (l : Nat) ^ returnMultiplicity c L l := by
  classical
  rw [squarefree_unit_returnIndex c hSq]
  have hLocal : forall p : c.primeFactors,
      ((p.val : Nat) - 1) / Nat.gcd ((p.val : Nat) - 1) (L / (l : Nat)) =
        if Not (Dvd.dvd ((p.val : Nat) - 1) (L / (l : Nat))) then (l : Nat) else 1 := by
    intro p
    have hp := (Nat.mem_primeFactors.mp p.property).1
    rw [local_period_ratio _ L l (Nat.sub_pos_of_lt hp.one_lt) (hPeriods p) hlL]
    split_ifs <;> rfl
  simp_rw [hLocal]
  simp [Finset.prod_ite, returnMultiplicity]

/-- Canonical specialization: all common-period hypotheses are discharged. -/
theorem canonical_squarefree_returnIndex (c : Nat) [NeZero c] (hSq : Squarefree c)
    (l : Nat.Primes) (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod c)))) :
    returnIndex (G := Units (ZMod c)) (Monoid.exponent (Units (ZMod c))) (l : Nat) =
      (l : Nat) ^ returnMultiplicity c (Monoid.exponent (Units (ZMod c))) l := by
  apply squarefree_unit_returnIndex_eq_prime_pow c hSq _ l _ hl
  intro p
  rw [squarefree_unit_exponent c hSq]
  exact Finset.dvd_lcm (Finset.mem_univ p)

end PrimeFactorOscillations.PrimeOrderReturnIndex
