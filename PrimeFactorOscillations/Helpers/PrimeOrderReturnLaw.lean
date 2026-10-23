/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.GroupTheory.Exponent
import PrimeFactorOscillations.Helpers.CyclotomicSampling
import PrimeFactorOscillations.Helpers.FiniteHomProbability

/-!
# Exact prime-order return packets under uniform group sampling

The supported maps are g -> g^(L/l), with l in a finite set of distinct
prime divisors of an annihilating exponent L. CRT interpolation proves
simultaneous surjectivity onto all actual image groups. Uniform sampling
therefore retains each image multiplicity, including the even prime and
empty support. The application is the complete unit group modulo a
Carmichael number, not a sampling of scalar cutoffs.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeOrderReturnLaw

open FiniteHomProbability

variable {G : Type*} [CommGroup G] [Fintype G]

local instance (p : Nat.Primes) : NeZero (p : Nat) := NeZero.mk p.property.ne_zero

local instance (S : Finset Nat.Primes) :
    NeZero (CyclotomicProbability.sampleModulus S) :=
  NeZero.mk (by
    unfold CyclotomicProbability.sampleModulus
    apply Finset.prod_ne_zero_iff.mpr
    intro p _
    exact p.val.property.ne_zero)

/-- The actual image of the shortened-period homomorphism. -/
abbrev returnImage (L l : Nat) : Subgroup G :=
  (powMonoidHom (L / l) : MonoidHom G G).range

local instance imageFintype (L l : Nat) : Fintype (returnImage (G := G) L l) :=
  Fintype.ofFinite _

/-- CRT coefficient equal to one at p and zero at all other labels. -/
def crtWeight (S : Finset Nat.Primes) (p : S) : Nat := by
  classical
  exact ((CyclotomicProbability.residueEquiv S).symm
    (fun q : S => if q = p then 1 else 0)).val

theorem crtWeight_residue (S : Finset Nat.Primes) (p q : S) :
    (crtWeight S p : ZMod (q.val : Nat)) = if q = p then 1 else 0 := by
  classical
  let t : ZMod (CyclotomicProbability.sampleModulus S) :=
    (CyclotomicProbability.residueEquiv S).symm
      (fun q : S => if q = p then 1 else 0)
  change (t.val : ZMod (q.val : Nat)) = _
  calc
    (t.val : ZMod (q.val : Nat)) =
        CyclotomicProbability.residueEquiv S
          (t.val : ZMod (CyclotomicProbability.sampleModulus S)) q :=
      (CyclotomicProbability.residueEquiv_natCast S t.val q).symm
    _ = CyclotomicProbability.residueEquiv S t q := by rw [ZMod.natCast_zmod_val]
    _ = if q = p then 1 else 0 :=
      congrFun ((CyclotomicProbability.residueEquiv S).apply_symm_apply _) q

theorem crtWeight_mod (S : Finset Nat.Primes) (p q : S) :
    crtWeight S p % (q.val : Nat) = if q = p then 1 else 0 := by
  classical
  have h := congrArg ZMod.val (crtWeight_residue S p q)
  have hOne : forall r : S, (1 : ZMod (r.val : Nat)).val = 1 := by
    intro r
    have hz : ZMod.val ((1 : Nat) : ZMod (r.val : Nat)) = 1 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt r.val.property.one_lt]
    simpa only [Nat.cast_one] using hz
  by_cases heq : q = p
  { simpa [heq, ZMod.val_natCast, hOne] using h }
  { simpa [heq, ZMod.val_natCast] using h }

omit [Fintype G] in
/-- A known annihilating power permits exact reduction of every exponent. -/
theorem pow_eq_mod_of_pow_eq_one (x : G) (l n : Nat) (hx : x ^ l = 1) :
    x ^ n = x ^ (n % l) := by
  conv_lhs => rw [<- Nat.mod_add_div n l]
  rw [pow_add, pow_mul, hx, one_pow, mul_one]

omit [Fintype G] in
/-- Shortened-period images have prime exponent, with their full size retained. -/
theorem returnImage_pow_prime (L l : Nat) (hl : Dvd.dvd l L)
    (hAnn : forall g : G, g ^ L = 1) (x : returnImage (G := G) L l) :
    x.val ^ l = 1 := by
  choose g hg using x.property
  rw [<- hg]
  change (g ^ (L / l)) ^ l = 1
  rw [<- pow_mul, Nat.div_mul_cancel hl, hAnn]

/-- All shortened-period images are observed at the same sampled group element. -/
def packetProjection (L : Nat) (S : Finset Nat.Primes) :
    MonoidHom G ((p : S) -> returnImage (G := G) L (p.val : Nat)) :=
  { toFun := fun g p => Subtype.mk (g ^ (L / (p.val : Nat))) (Exists.intro g rfl)
    map_one' := by
      funext p
      apply Subtype.ext
      exact one_pow _
    map_mul' := by
      intro a b
      funext p
      apply Subtype.ext
      exact mul_pow a b _ }

omit [Fintype G] in
/-- Exact simultaneous surjectivity, with no loss from overlaps or norms. -/
theorem packetProjection_surjective (L : Nat) (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) L)
    (hAnn : forall g : G, g ^ L = 1) :
    Function.Surjective (packetProjection (G := G) L S) := by
  classical
  intro y
  choose g hg using fun p : S => (y p).property
  let a : G := Finset.univ.prod (fun p : S => (g p) ^ crtWeight S p)
  refine Exists.intro a ?_
  funext q
  apply Subtype.ext
  change a ^ (L / (q.val : Nat)) = (y q).val
  have hFactor : forall p : S,
      ((g p) ^ crtWeight S p) ^ (L / (q.val : Nat)) =
        if p = q then (y q).val else 1 := by
    intro p
    have hSwap : ((g p) ^ crtWeight S p) ^ (L / (q.val : Nat)) =
        ((g p) ^ (L / (q.val : Nat))) ^ crtWeight S p := by
      rw [<- pow_mul, <- pow_mul, Nat.mul_comm]
    have hPrime : ((g p) ^ (L / (q.val : Nat))) ^ (q.val : Nat) = 1 := by
      rw [<- pow_mul, Nat.div_mul_cancel (hDiv q), hAnn]
    rw [hSwap, pow_eq_mod_of_pow_eq_one _ _ _ hPrime, crtWeight_mod]
    by_cases hpq : p = q
    { subst p
      simpa only [ite_true, pow_one, powMonoidHom_apply] using hg q }
    { have hqp : Not (q = p) := Ne.symm hpq
      simp only [hpq, hqp, ite_false, pow_zero] }
  calc
    a ^ (L / (q.val : Nat)) =
        Finset.univ.prod (fun p : S =>
          ((g p) ^ crtWeight S p) ^ (L / (q.val : Nat))) := by
      change (powMonoidHom (L / (q.val : Nat)) : MonoidHom G G)
        (Finset.univ.prod (fun p : S => (g p) ^ crtWeight S p)) = _
      rw [map_prod]
      rfl
    _ = Finset.univ.prod (fun p : S => if p = q then (y q).val else 1) :=
      Finset.prod_congr rfl (fun p _ => hFactor p)
    _ = (y q).val := by simp

/-- Exact size of the actual shortened-period image. -/
def returnIndex (L l : Nat) : Nat := Fintype.card (returnImage (G := G) L l)

/-- A coordinate success or failure, within its actual image group. -/
def coordinateSet (L l : Nat) (bit : Bool) : Finset (returnImage (G := G) L l) := by
  classical
  exact if bit then {1} else Finset.univ.erase 1

theorem coordinateSet_mem (L l : Nat) (bit : Bool) (x : returnImage (G := G) L l) :
    Membership.mem (coordinateSet L l bit) x <->
      if bit then x = 1 else Not (x = 1) := by
  classical
  cases bit <;> simp [coordinateSet]

theorem coordinateSet_card (L l : Nat) (bit : Bool) :
    (coordinateSet (G := G) L l bit).card =
      if bit then 1 else returnIndex (G := G) L l - 1 := by
  classical
  cases bit <;> simp [coordinateSet, returnIndex, Finset.card_univ]

/-- Complete pattern set in the product of the actual image groups. -/
def imagePatternSet (L : Nat) (S : Finset Nat.Primes) (bits : S -> Bool) :
    Finset ((p : S) -> returnImage (G := G) L (p.val : Nat)) := by
  classical
  exact Fintype.piFinset (fun p : S => coordinateSet L (p.val : Nat) (bits p))

theorem imagePatternSet_mem (L : Nat) (S : Finset Nat.Primes) (bits : S -> Bool)
    (y : (p : S) -> returnImage (G := G) L (p.val : Nat)) :
    Membership.mem (imagePatternSet L S bits) y <->
      forall p : S, if bits p then y p = 1 else Not (y p = 1) := by
  classical
  unfold imagePatternSet
  rw [Fintype.mem_piFinset]
  apply forall_congr'
  intro p
  exact coordinateSet_mem L (p.val : Nat) (bits p) (y p)

theorem imagePatternSet_card (L : Nat) (S : Finset Nat.Primes) (bits : S -> Bool) :
    (imagePatternSet (G := G) L S bits).card =
      Finset.univ.prod (fun p : S =>
        if bits p then 1 else returnIndex (G := G) L (p.val : Nat) - 1) := by
  classical
  unfold imagePatternSet
  rw [Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro p _
  exact coordinateSet_card L (p.val : Nat) (bits p)

/-- Uniform sampling of the entire group, with every outcome retained. -/
def returnPatternProbability (L : Nat) (S : Finset Nat.Primes) (bits : S -> Bool) : Real :=
  uniformProbability (fun g : G => forall p : S, if bits p then
    g ^ (L / (p.val : Nat)) = 1 else Not (g ^ (L / (p.val : Nat)) = 1))

/-- Complete independence under full group sampling, using exact image sizes. -/
theorem returnPatternProbability_eq_product (L : Nat) (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) L)
    (hAnn : forall g : G, g ^ L = 1) (bits : S -> Bool) :
    returnPatternProbability (G := G) L S bits =
      Finset.univ.prod (fun p : S =>
        if bits p then 1 / (returnIndex (G := G) L (p.val : Nat) : Real)
        else 1 - 1 / (returnIndex (G := G) L (p.val : Nat) : Real)) := by
  classical
  let H := (p : S) -> returnImage (G := G) L (p.val : Nat)
  let T : Finset H := imagePatternSet L S bits
  have hPred :
      (fun g : G => forall p : S, if bits p then
        g ^ (L / (p.val : Nat)) = 1 else Not (g ^ (L / (p.val : Nat)) = 1)) =
      (fun g : G => Membership.mem T (packetProjection L S g)) := by
    funext g
    apply propext
    rw [imagePatternSet_mem]
    apply forall_congr'
    intro p
    have heq : (packetProjection L S g) p = 1 <->
        g ^ (L / (p.val : Nat)) = 1 := by
      constructor
      { intro h
        exact congrArg Subtype.val h }
      { intro h
        apply Subtype.ext
        exact h }
    cases bits p
    { exact not_congr heq.symm }
    { exact heq.symm }
  unfold returnPatternProbability
  rw [hPred, uniformProbability_preimage _
    (packetProjection_surjective L S hDiv hAnn)]
  unfold uniformProbability
  change (Nat.card T : Real) / (Nat.card H : Real) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  rw [imagePatternSet_card]
  simp only [Nat.cast_prod]
  rw [<- Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  have hPos : 0 < returnIndex (G := G) L (p.val : Nat) :=
    Fintype.card_pos_iff.mpr (Nonempty.intro 1)
  have hNonzero : Not ((returnIndex (G := G) L (p.val : Nat) : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt hPos)
  cases bits p
  { change (((returnIndex (G := G) L (p.val : Nat) - 1 : Nat) : Real) /
      (returnIndex (G := G) L (p.val : Nat) : Real)) =
      1 - 1 / (returnIndex (G := G) L (p.val : Nat) : Real)
    rw [Nat.cast_sub (by omega), Nat.cast_one, sub_div, div_self hNonzero] }
  { simp [returnIndex] }

/-- The unconditional full-unit law at the canonical Carmichael exponent. -/
theorem modular_unit_returnPatternProbability (c : Nat) [NeZero c]
    (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod c))))
    (bits : S -> Bool) :
    returnPatternProbability (G := Units (ZMod c))
        (Monoid.exponent (Units (ZMod c))) S bits =
      Finset.univ.prod (fun p : S =>
        if bits p then
          1 / (returnIndex (G := Units (ZMod c))
            (Monoid.exponent (Units (ZMod c))) (p.val : Nat) : Real)
        else 1 - 1 / (returnIndex (G := Units (ZMod c))
          (Monoid.exponent (Units (ZMod c))) (p.val : Nat) : Real)) := by
  exact returnPatternProbability_eq_product _ S hDiv
    (fun g => Monoid.pow_exponent_eq_one g) bits

/-- Every divisor of the canonical exponent occurs as a genuine return image order. -/
theorem divisor_le_returnIndex (l : Nat) (hl : Dvd.dvd l (Monoid.exponent G)) :
    l <= returnIndex (G := G) (Monoid.exponent G) l := by
  classical
  choose g hg using Monoid.exists_orderOf_eq_exponent (G := G)
    (Monoid.ExponentExists.of_finite (G := G))
  have hExp : Not (Monoid.exponent G = 0) :=
    Monoid.exponent_ne_zero_of_finite (G := G)
  have hOrder : orderOf (g ^ (Monoid.exponent G / l)) = l := by
    have h := orderOf_pow_orderOf_div (x := g) (n := l)
      (by rw [hg]; exact hExp) (by rw [hg]; exact hl)
    simpa only [hg] using h
  have hMember : Membership.mem (returnImage (G := G) (Monoid.exponent G) l)
      (g ^ (Monoid.exponent G / l)) := Exists.intro g rfl
  have hBound := (returnImage (G := G) (Monoid.exponent G) l).orderOf_le_card
    (Set.toFinite _) hMember
  rw [hOrder, Nat.card_eq_fintype_card] at hBound
  exact hBound

/-- The universal vacancy floor needed by the Carmichael extremal consumer. -/
theorem canonical_vacancy_ge_prime_product (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) :
    Finset.univ.prod (fun p : S => 1 - 1 / ((p.val : Nat) : Real)) <=
      returnPatternProbability (G := G) (Monoid.exponent G) S (fun _ => false) := by
  classical
  rw [returnPatternProbability_eq_product (Monoid.exponent G) S hDiv
    (fun g => Monoid.pow_exponent_eq_one g)]
  simp only [Bool.false_eq_true, ite_false]
  let f : S -> Real := fun p => 1 - 1 / ((p.val : Nat) : Real)
  let g : S -> Real := fun p =>
    1 - 1 / (returnIndex (G := G) (Monoid.exponent G) (p.val : Nat) : Real)
  change Finset.univ.prod f <= Finset.univ.prod g
  have hNonneg : forall p : S, 0 <= f p := by
    intro p
    have hp : (0 : Real) < ((p.val : Nat) : Real) := by
      exact_mod_cast p.val.property.pos
    have hpOne : (1 : Real) <= ((p.val : Nat) : Real) := by
      exact_mod_cast p.val.property.one_lt.le
    exact sub_nonneg.mpr ((div_le_one hp).mpr hpOne)
  have hFactor : forall p : S, f p <= g p := by
    intro p
    have hp : (0 : Real) < ((p.val : Nat) : Real) := by
      exact_mod_cast p.val.property.pos
    have hNat := divisor_le_returnIndex (G := G) (p.val : Nat) (hDiv p)
    have hCast : ((p.val : Nat) : Real) <=
        (returnIndex (G := G) (Monoid.exponent G) (p.val : Nat) : Real) :=
      Nat.cast_le.mpr hNat
    exact sub_le_sub_left (one_div_le_one_div_of_le hp hCast) 1
  have hCompare : forall T : Finset S, T.prod f <= T.prod g := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert p T hp ih =>
      rw [Finset.prod_insert hp, Finset.prod_insert hp]
      exact mul_le_mul (hFactor p) ih
        (Finset.prod_nonneg (fun q _ => hNonneg q))
        ((hNonneg p).trans (hFactor p))
  exact hCompare Finset.univ

end PrimeFactorOscillations.PrimeOrderReturnLaw
