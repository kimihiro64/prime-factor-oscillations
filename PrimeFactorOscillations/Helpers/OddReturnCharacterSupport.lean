/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeOrderReturnLaw

/-!
# Exact exclusion of quadratic modes from odd return packets

An odd annihilator of the observed return images gives a translation that
fixes the complete packet and changes any nonprincipal quadratic character.
The resulting weighted character sum is exactly zero, with no norm estimate.
The principal vacancy coefficient remains the positive product supplied by
the full-unit return law. This is finite spectral cancellation, not a new
zero-free exponent or an RH assumption.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.OddReturnCharacterSupport

open PrimeOrderReturnLaw

variable {G : Type*} [CommGroup G] [Fintype G]

omit [Fintype G] in
theorem packet_projection_fixed_by_annihilator (L P : Nat)
    (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) L)
    (hP : forall p : S, Dvd.dvd (p.val : Nat) P)
    (hAnn : forall g : G, g ^ L = 1) (a g : G) :
    packetProjection L S (a ^ P * g) = packetProjection L S g := by
  funext p
  apply Subtype.ext
  change (a ^ P * g) ^ (L / (p.val : Nat)) = g ^ (L / (p.val : Nat))
  have hPeriod : (a ^ (L / (p.val : Nat))) ^ (p.val : Nat) = 1 := by
    rw [<- pow_mul, Nat.div_mul_cancel (hDiv p), hAnn]
  have hZero : (a ^ P) ^ (L / (p.val : Nat)) = 1 := by
    calc
      _ = (a ^ (L / (p.val : Nat))) ^ P := by
        rw [<- pow_mul, <- pow_mul, Nat.mul_comm]
      _ = (a ^ (L / (p.val : Nat))) ^ (P % (p.val : Nat)) :=
        pow_eq_mod_of_pow_eq_one _ _ _ hPeriod
      _ = 1 := by rw [Nat.mod_eq_zero_of_dvd (hP p), pow_zero]
  rw [mul_pow, hZero, one_mul]

/-- A complete signed cancellation, for arbitrary functions of the packet. -/
theorem quadratic_packet_sum_eq_zero (L P : Nat) (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) L)
    (hP : forall p : S, Dvd.dvd (p.val : Nat) P) (hOdd : P % 2 = 1)
    (hAnn : forall g : G, g ^ L = 1)
    (chi : MonoidHom G Complex) (hchi : Not (chi = 1))
    (hSquare : forall g : G, (chi g) ^ 2 = 1)
    (f : ((p : S) -> returnImage (G := G) L (p.val : Nat)) -> Complex) :
    Finset.univ.sum (fun g : G => f (packetProjection L S g) * chi g) = 0 := by
  classical
  have hExists : exists a : G, Not (chi a = 1) := by
    apply Classical.byContradiction
    intro hn
    apply hchi
    ext a
    change chi a = 1
    apply Classical.byContradiction
    intro ha
    exact hn (Exists.intro a ha)
  choose a ha using hExists
  have hPower : chi (a ^ P) = chi a := by
    rw [map_pow]
    calc
      (chi a) ^ P = (chi a) ^ (P % 2) := by
        conv_lhs => rw [<- Nat.mod_add_div P 2]
        rw [pow_add, pow_mul, hSquare a, one_pow, mul_one]
      _ = chi a := by rw [hOdd, pow_one]
  let T : Complex :=
    Finset.univ.sum (fun g : G => f (packetProjection L S g) * chi g)
  have hTranslate := Equiv.sum_comp (Equiv.mulLeft (a ^ P))
    (fun g : G => f (packetProjection L S g) * chi g)
  have hScaled : chi a * T = T := by
    calc
      _ = Finset.univ.sum (fun g : G =>
          f (packetProjection L S (a ^ P * g)) * chi (a ^ P * g)) := by
        simp only [T, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        rw [packet_projection_fixed_by_annihilator L P S hDiv hP hAnn,
          map_mul, hPower]
        ring
      _ = T := hTranslate
  have hProduct : (chi a - 1) * T = 0 := by
    rw [sub_mul, one_mul, hScaled, sub_self]
  exact (mul_eq_zero.mp hProduct).resolve_left (sub_ne_zero.mpr ha)

theorem odd_prime_product_mod_two (S : Finset Nat.Primes)
    (hOdd : forall p : S, Not ((p.val : Nat) = 2)) :
    (S.prod (fun p => (p : Nat))) % 2 = 1 := by
  classical
  have hAll : forall T : Finset Nat.Primes,
      (forall p : T, Not ((p.val : Nat) = 2)) ->
        (T.prod (fun p => (p : Nat))) % 2 = 1 := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert p T hp ih =>
      intro hT
      have hpOdd : (p : Nat) % 2 = 1 :=
        Nat.odd_iff.mp (p.property.odd_of_ne_two (hT (Subtype.mk p (by simp))))
      have hRest : forall q : T, Not ((q.val : Nat) = 2) := by
        intro q
        exact hT (Subtype.mk q.val (by simp [q.property]))
      rw [Finset.prod_insert hp, Nat.mul_mod, hpOdd, ih hRest]
  exact hAll S hOdd

/-- Every nonprincipal quadratic mode is absent from an odd prime-label packet. -/
theorem odd_packet_quadratic_sum_eq_zero (L : Nat) (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) L)
    (hOdd : forall p : S, Not ((p.val : Nat) = 2))
    (hAnn : forall g : G, g ^ L = 1)
    (chi : MonoidHom G Complex) (hchi : Not (chi = 1))
    (hSquare : forall g : G, (chi g) ^ 2 = 1)
    (f : ((p : S) -> returnImage (G := G) L (p.val : Nat)) -> Complex) :
    Finset.univ.sum (fun g : G => f (packetProjection L S g) * chi g) = 0 := by
  apply quadratic_packet_sum_eq_zero L (S.prod (fun p => (p : Nat))) S hDiv
    (fun p => Finset.dvd_prod_of_mem (fun q : Nat.Primes => (q : Nat))
      (a := p.val) (s := S) p.property)
    (odd_prime_product_mod_two S hOdd) hAnn chi hchi hSquare f

/-- The native full-group vacancy event, with all return coordinates coupled. -/
def vacancy (L : Nat) (S : Finset Nat.Primes) (g : G) : Prop :=
  forall p : S, Not (g ^ (L / (p.val : Nat)) = 1)

local instance vacancyDecidable (L : Nat) (S : Finset Nat.Primes) (g : G) :
    Decidable (vacancy L S g) := Classical.propDecidable _

omit [Fintype G] in
theorem vacancy_iff_projection (L : Nat) (S : Finset Nat.Primes) (g : G) :
    vacancy L S g <->
      forall p : S, Not ((packetProjection L S g) p = 1) := by
  apply forall_congr'
  intro p
  apply not_congr
  constructor
  { intro h
    apply Subtype.ext
    exact h }
  { intro h
    exact congrArg Subtype.val h }

/-- The actual vacancy indicator has no nonprincipal quadratic coefficient. -/
theorem odd_vacancy_quadratic_sum_eq_zero (L : Nat) (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) L)
    (hOdd : forall p : S, Not ((p.val : Nat) = 2))
    (hAnn : forall g : G, g ^ L = 1)
    (chi : MonoidHom G Complex) (hchi : Not (chi = 1))
    (hSquare : forall g : G, (chi g) ^ 2 = 1) :
    Finset.univ.sum (fun g : G =>
      (if vacancy L S g then (1 : Complex) else 0) * chi g) = 0 := by
  classical
  let f : ((p : S) -> returnImage (G := G) L (p.val : Nat)) -> Complex :=
    fun y => if forall p : S, Not (y p = 1) then 1 else 0
  have h := odd_packet_quadratic_sum_eq_zero L S hDiv hOdd hAnn chi hchi hSquare f
  have hWeight : forall g : G, f (packetProjection L S g) =
      if vacancy L S g then (1 : Complex) else 0 := by
    intro g
    dsimp [f]
    simp only [<- vacancy_iff_projection]
  simpa only [hWeight] using h

/-- Exact retained principal coefficient, before any analytic error estimate. -/
theorem vacancy_mean_eq_product (L : Nat) (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) L)
    (hAnn : forall g : G, g ^ L = 1) :
    Finset.univ.sum (fun g : G =>
        if vacancy L S g then (1 : Real) else 0) / (Fintype.card G : Real) =
      Finset.univ.prod (fun p : S =>
        1 - 1 / (returnIndex (G := G) L (p.val : Nat) : Real)) := by
  classical
  have h := returnPatternProbability_eq_product L S hDiv hAnn (fun _ => false)
  rw [Finset.sum_boole]
  simp only [returnPatternProbability, FiniteHomProbability.uniformProbability,
    Bool.false_eq_true, ite_false, Nat.card_eq_fintype_card,
    Fintype.card_subtype] at h
  convert h using 1
  apply congrArg (fun T : Finset G => (T.card : Real) / (Fintype.card G : Real))
  ext g
  simp [vacancy]

/-- Removing every quadratic mode does not remove the principal vacancy mass. -/
theorem canonical_vacancy_mean_pos (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) :
    0 < Finset.univ.sum (fun g : G =>
        if vacancy (Monoid.exponent G) S g then (1 : Real) else 0) /
      (Fintype.card G : Real) := by
  classical
  rw [vacancy_mean_eq_product (Monoid.exponent G) S hDiv
    (fun g => Monoid.pow_exponent_eq_one g)]
  apply Finset.prod_pos
  intro p _
  have hIndex : (1 : Real) <
      (returnIndex (G := G) (Monoid.exponent G) (p.val : Nat) : Real) := by
    exact_mod_cast lt_of_lt_of_le p.val.property.one_lt
      (divisor_le_returnIndex (G := G) (p.val : Nat) (hDiv p))
  exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans hIndex)).mpr hIndex)

/-- In particular this applies to every actual modular-unit group. -/
theorem modular_odd_vacancy_quadratic_sum_eq_zero (c : Nat) [NeZero c]
    (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod c))))
    (hOdd : forall p : S, Not ((p.val : Nat) = 2))
    (chi : MonoidHom (Units (ZMod c)) Complex) (hchi : Not (chi = 1))
    (hSquare : forall g : Units (ZMod c), (chi g) ^ 2 = 1) :
    Finset.univ.sum (fun g : Units (ZMod c) =>
      (if vacancy (Monoid.exponent (Units (ZMod c))) S g
        then (1 : Complex) else 0) * chi g) = 0 := by
  exact odd_vacancy_quadratic_sum_eq_zero _ S hDiv hOdd
    (fun g => Monoid.pow_exponent_eq_one g) chi hchi hSquare

end PrimeFactorOscillations.OddReturnCharacterSupport
