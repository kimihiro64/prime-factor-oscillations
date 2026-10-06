/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Finite residue families followed by two independent prime inputs

A base family may have any finite nonempty state set at each prime. The
probability is defined by the actual residue count, including prime two.
Constant base values give the prime-pair endpoints with shifts zero and one.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations

structure FinitePrimeResidueFamily where
  State : Nat.Primes -> Type
  domain : forall p : Nat.Primes, Finset (State p)
  value : forall p : Nat.Primes, State p -> ZMod (p : Nat)
  nonempty : forall p : Nat.Primes, (domain p).Nonempty

namespace FinitePrimeResidueFamily

def zeroProbability (F : FinitePrimeResidueFamily) (p : Nat.Primes) : Real := by
  classical
  exact (((F.domain p).filter (fun a => F.value p a = 0)).card : Real) /
    ((F.domain p).card : Real)

def twoPrimeProbability (F : FinitePrimeResidueFamily) (p : Nat.Primes) : Real := by
  classical
  letI : NeZero (p : Nat) := NeZero.mk p.property.ne_zero
  let T := ((F.domain p).product (Finset.univ.erase (0 : ZMod (p : Nat)))).product
    (Finset.univ.erase (0 : ZMod (p : Nat)))
  exact ((T.filter
    (fun ab : Prod (Prod (F.State p) (ZMod (p : Nat))) (ZMod (p : Nat)) =>
      F.value p ab.1.1 + ab.1.2 + ab.2 = 0)).card : Real) /
        (((F.domain p).card : Real) * (((p : Nat) : Real) - 1) ^ 2)

end FinitePrimeResidueFamily

def constantPrimeResidueFamily (c : Int) : FinitePrimeResidueFamily where
  State := fun _ => Unit
  domain := fun _ => ({()} : Finset Unit)
  value := fun p _ => (c : ZMod (p : Nat))
  nonempty := fun _ => Finset.singleton_nonempty ()

end PrimeFactorOscillations
