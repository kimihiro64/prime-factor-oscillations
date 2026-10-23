/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CarmichaelProfileKernel

/-!
# Maximal-order units in each actual extension fiber

The complete prime-label vacancy event is identified with maximal
multiplicative order. The full conditional kernel gives its exact
probability, while CRT gives the sharp criterion for existence of a
maximal-order lift above a prescribed old unit.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelMaximalOrderLifts

open FiniteHomProbability PrimeOrderReturnLaw CarmichaelProfileLifts
  CarmichaelProfileCriterion CarmichaelProfileKernel CarmichaelEvenThinning

def exponentPrimePacket (c : Nat) : Finset Nat.Primes := by
  classical
  exact (Monoid.exponent (Units (ZMod c))).primeFactors.subtype Nat.Prime

theorem exponentPrimePacket_mem (c : Nat) [NeZero c] (p : Nat.Primes) :
    Membership.mem (exponentPrimePacket c) p <->
      Dvd.dvd (p : Nat) (Monoid.exponent (Units (ZMod c))) := by
  classical
  change Membership.mem
    ((Monoid.exponent (Units (ZMod c))).primeFactors.subtype Nat.Prime)
    (show {n : Nat // Nat.Prime n} from p) <->
      Dvd.dvd (p : Nat) (Monoid.exponent (Units (ZMod c)))
  rw [Finset.mem_subtype]
  constructor
  { intro h
    exact (Nat.mem_primeFactors.mp h).2.1 }
  { intro h
    exact Nat.mem_primeFactors.mpr (And.intro p.property
      (And.intro h (Monoid.exponent_ne_zero_of_finite (G := Units (ZMod c))))) }

theorem maximal_order_iff_full_nonreturn (c : Nat) [NeZero c] (u : Units (ZMod c)) :
    orderOf u = Monoid.exponent (Units (ZMod c)) <->
      matchesPattern c (exponentPrimePacket c) (fun _ => false) u := by
  classical
  let E := Monoid.exponent (Units (ZMod c))
  have hPos : 0 < E :=
    Nat.pos_of_ne_zero (Monoid.exponent_ne_zero_of_finite (G := Units (ZMod c)))
  change orderOf u = E <->
    (forall p : exponentPrimePacket c, Not (u ^ (E / (p.val : Nat)) = 1))
  constructor
  { intro h p
    have hDiv := (exponentPrimePacket_mem c p.val).mp p.property
    have hQuotPos : 0 < E / (p.val : Nat) :=
      Nat.div_pos (Nat.le_of_dvd hPos hDiv) p.val.property.pos
    exact ((orderOf_eq_iff hPos).mp h).2 _
      (Nat.div_lt_self hPos p.val.property.one_lt) hQuotPos }
  { intro h
    apply orderOf_eq_of_pow_and_pow_div_prime hPos (Monoid.pow_exponent_eq_one u)
    intro p hp hpE
    let l : Nat.Primes := Subtype.mk p hp
    have hl : Membership.mem (exponentPrimePacket c) l :=
      (exponentPrimePacket_mem c l).mpr hpE
    exact h (Subtype.mk l hl) }

def maximalOrderLiftProbability (m B : Nat) (a : Units (ZMod m)) : Real :=
  uniformProbability
    (fun u : {u : Units (ZMod (m * B)) // unitReduction (dvd_mul_right m B) u = a} =>
      orderOf u.val = Monoid.exponent (Units (ZMod (m * B))))

theorem maximalOrderLiftProbability_eq_profile (m B : Nat) [NeZero (m * B)]
    (a : Units (ZMod m)) :
    maximalOrderLiftProbability m B a =
      fiberProfileProbability m B a (exponentPrimePacket (m * B)) (fun _ => false) := by
  unfold maximalOrderLiftProbability fiberProfileProbability
  congr 1
  funext u
  apply propext
  exact maximal_order_iff_full_nonreturn (m * B) u.val

theorem maximalOrderLiftProbability_eq_product (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) :
    maximalOrderLiftProbability m B a =
      Finset.univ.prod (fun l : exponentPrimePacket (m * B) =>
        if returnGate m B a (l.val : Nat) then
          1 - 1 / (returnIndex (G := Units (ZMod B))
            (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) : Real)
        else 1) := by
  rw [maximalOrderLiftProbability_eq_profile]
  have h := fiberProfileProbability_eq_product m B hCoprime a
    (exponentPrimePacket (m * B))
    (fun l => (exponentPrimePacket_mem (m * B) l.val).mp l.property) (fun _ => false)
  simpa only [Bool.false_eq_true, ite_false] using h

theorem orderOf_crt (m B : Nat) (hCoprime : Nat.Coprime m B) (u : Units (ZMod (m * B))) :
    orderOf u = Nat.lcm (orderOf (unitReduction (dvd_mul_right m B) u))
      (orderOf (unitReduction (dvd_mul_left B m) u)) := by
  apply Nat.dvd_antisymm
  { apply orderOf_dvd_of_pow_eq_one
    apply (crt_power_eq_one m B hCoprime u _).mpr
    exact And.intro
      (orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_left _ _))
      (orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_right _ _)) }
  { have h := (crt_power_eq_one m B hCoprime u (orderOf u)).mp (pow_orderOf_eq_one u)
    exact Nat.lcm_dvd (orderOf_dvd_of_pow_eq_one h.1) (orderOf_dvd_of_pow_eq_one h.2) }

theorem maximal_order_lift_exists_iff (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) :
    (Exists (fun u : Units (ZMod (m * B)) =>
      And (unitReduction (dvd_mul_right m B) u = a)
        (orderOf u = Monoid.exponent (Units (ZMod (m * B)))))) <->
      Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
        Monoid.exponent (Units (ZMod (m * B))) := by
  classical
  constructor
  { intro h
    choose u hu using h
    apply Nat.dvd_antisymm
    { apply Nat.lcm_dvd
      { exact dvd_trans (Monoid.order_dvd_exponent a) (old_exponent_dvd m B hCoprime) }
      { exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
          (auxiliary_exponent_annihilates m B hCoprime) } }
    { rw [<- hu.2, orderOf_crt m B hCoprime u, hu.1]
      apply Nat.lcm_dvd (Nat.dvd_lcm_left _ _)
      exact dvd_trans (Monoid.order_dvd_exponent _) (Nat.dvd_lcm_right _ _) } }
  { intro h
    choose b hb using Monoid.exists_orderOf_eq_exponent
      (G := Units (ZMod B)) Monoid.ExponentExists.of_finite
    let u := (unitProductEquiv m B hCoprime).symm (Prod.mk a b)
    have hOld : unitReduction (dvd_mul_right m B) u = a := by
      rw [<- unitProductEquiv_fst m B hCoprime]
      exact congrArg Prod.fst ((unitProductEquiv m B hCoprime).apply_symm_apply (Prod.mk a b))
    have hAux : unitReduction (dvd_mul_left B m) u = b := by
      rw [<- unitProductEquiv_snd m B hCoprime]
      exact congrArg Prod.snd ((unitProductEquiv m B hCoprime).apply_symm_apply (Prod.mk a b))
    refine Exists.intro u (And.intro hOld ?_)
    rw [orderOf_crt m B hCoprime u, hOld, hAux, hb]
    exact h }

end PrimeFactorOscillations.CarmichaelMaximalOrderLifts
