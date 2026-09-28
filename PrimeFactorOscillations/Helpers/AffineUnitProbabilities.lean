import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Totient
import PrimeFactorOscillations.Definitions.AffineSumFamily
import PrimeFactorOscillations.Mathlib.Data.ZMod.UnitPairCRT

/-! # All-prime affine divisibility probabilities in unit coordinates -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.AffineSumFamily

open scoped Classical

theorem unit_divisibility_probability_eq_local
    (F : AffineSumFamily) (p : Nat) [NeZero p] (hp : Nat.Prime p) :
    (Nat.card {ab : Prod (Units (ZMod p)) (Units (ZMod p)) //
      F.eval ((ab.1 : ZMod p) + (ab.2 : ZMod p)) = 0} : Real) /
      (p.totient : Real) ^ 2 = F.localProbability p := by
  let P : Prod (ZMod p) (ZMod p) -> Prop := fun ab => F.eval (ab.1 + ab.2) = 0
  have hunit (a : ZMod p) : IsUnit a <-> Not (a = 0) := by
    let : Fact (Nat.Prime p) := Fact.mk hp
    exact isUnit_iff_ne_zero
  have hcount : Nat.card {ab : Prod (Units (ZMod p)) (Units (ZMod p)) //
      F.eval ((ab.1 : ZMod p) + (ab.2 : ZMod p)) = 0} = F.nonzeroResidueCount p := by
    rw [<- ZMod.natCard_unit_pair_event_eq_filter p P]
    unfold nonzeroResidueCount
    apply congrArg Finset.card
    apply Finset.ext
    intro ab
    have hprod : Membership.mem ((Finset.univ.erase (0 : ZMod p)).product
        (Finset.univ.erase (0 : ZMod p))) ab <->
        Membership.mem (Finset.univ.erase (0 : ZMod p)) ab.1 /\
        Membership.mem (Finset.univ.erase (0 : ZMod p)) ab.2 := Finset.mem_product
    simp only [Finset.mem_filter, Finset.mem_univ, hprod, Finset.mem_erase,
      hunit, true_and, and_assoc, and_comm, P]
  rw [hcount]
  simp only [localProbability, dite_eq_left hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_lt.le, Nat.cast_one]

theorem unit_nondivisibility_probability_eq_one_sub_local
    (F : AffineSumFamily) (p : Nat) [NeZero p] (hp : Nat.Prime p) :
    (Nat.card {ab : Prod (Units (ZMod p)) (Units (ZMod p)) //
      Not (F.eval ((ab.1 : ZMod p) + (ab.2 : ZMod p)) = 0)} : Real) /
      (p.totient : Real) ^ 2 = 1 - F.localProbability p := by
  let P : Prod (Units (ZMod p)) (Units (ZMod p)) -> Prop :=
    fun ab => F.eval ((ab.1 : ZMod p) + (ab.2 : ZMod p)) = 0
  have hamb : Fintype.card (Prod (Units (ZMod p)) (Units (ZMod p))) = p.totient ^ 2 := by
    simp only [Fintype.card_prod, ZMod.card_units_eq_totient, pow_two]
  have hle : Nat.card {ab // P ab} <= p.totient ^ 2 := by
    rw [Nat.card_eq_fintype_card, <- hamb]
    exact Fintype.card_subtype_le P
  have hcompl : Nat.card {ab // Not (P ab)} = p.totient ^ 2 - Nat.card {ab // P ab} := by
    simp only [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl P, hamb]
  have hphi : 0 < (p.totient : Real) := by exact_mod_cast Nat.totient_pos.mpr hp.pos
  change (Nat.card {ab // Not (P ab)} : Real) / (p.totient : Real) ^ 2 = _
  rw [hcompl, Nat.cast_sub hle, Nat.cast_pow,
    sub_div, div_self (pow_ne_zero 2 (ne_of_gt hphi))]
  rw [unit_divisibility_probability_eq_local F p hp]

theorem map_evaluation (F : AffineSumFamily) {R S : Type*}
    [CommRing R] [CommRing S] (f : RingHom R S) (x : R) :
    f (F.eval x) = F.eval (f x) := by
  simp only [eval, map_prod, map_add, map_mul, map_intCast]

theorem value_cast (F : AffineSumFamily) (p q n : Nat) :
    (F.value p q : ZMod n) = F.eval ((p : ZMod n) + (q : ZMod n)) := by
  simpa only [value, Int.coe_castRingHom, Int.cast_add, Int.cast_natCast] using
    F.map_evaluation (Int.castRingHom (ZMod n)) ((p : Int) + (q : Int))

theorem crt_evaluation_eq_value_cast (F : AffineSumFamily)
    {I : Type*} [Fintype I] (m : I -> Nat)
    (hc : Pairwise (fun i j : I => (m i).Coprime (m j))) (p q : Nat) (i : I) :
    F.eval ((ZMod.prodEquivPi m hc (p : ZMod (Finset.univ.prod m))) i +
      (ZMod.prodEquivPi m hc (q : ZMod (Finset.univ.prod m))) i) =
      (F.value p q : ZMod (m i)) := by
  have hcast (a : Nat) : (ZMod.prodEquivPi m hc (a : ZMod (Finset.univ.prod m))) i =
      (a : ZMod (m i)) := by
    exact congrFun (map_natCast (ZMod.prodEquivPi m hc) a) i
  rw [hcast p, hcast q]
  exact (F.value_cast p q (m i)).symm

theorem divides_value_iff_crt_zero (F : AffineSumFamily)
    {I : Type*} [Fintype I] (m : I -> Nat)
    (hc : Pairwise (fun i j : I => (m i).Coprime (m j))) (p q : Nat) (i : I) :
    Dvd.dvd (m i : Int) (F.value p q) <->
      F.eval ((ZMod.prodEquivPi m hc (p : ZMod (Finset.univ.prod m))) i +
        (ZMod.prodEquivPi m hc (q : ZMod (Finset.univ.prod m))) i) = 0 := by
  rw [F.crt_evaluation_eq_value_cast m hc p q i]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (F.value p q) (m i)).symm

end PrimeFactorOscillations.AffineSumFamily
