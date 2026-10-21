/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliOddsOrder
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeCoordinateOrder
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassCoordinateProducts

/-! # Coefficient extremality of the literal capped-prime odds products -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorOscillations.PrimeClassSampling

theorem primeClassCoordinates_odds_product (P : Set Nat) (v : Nat -> Real) (X : Nat) :
    List.bernoulliOddsProduct (primeClassCoordinates P v X) =
      (primeClassPrefix P X).prod (fun p => 1 + Polynomial.C (v p) * Polynomial.X) := by
  rw [List.bernoulliOddsProduct, primeClassCoordinates_map, primeClassCoordinates_prod]

theorem greedyPrimeClass_local_odds_coefficient
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (v : Nat -> Real) (hv0 : forall p : Nat, Nat.Prime p -> 0 <= v p)
    (hmono : forall p q : Nat, Nat.Prime p -> Nat.Prime q -> p <= q -> v q <= v p)
    (r : Nat) :
    ((primeClassPrefix P (Nat.floor x)).prod
        (fun p => 1 + Polynomial.C (v p) * Polynomial.X)).coeff r <=
      ((primeClassPrefix greedyPrimeClass (Nat.floor x)).prod
        (fun p => 1 + Polynomial.C (v p) * Polynomial.X)).coeff r := by
  rw [<- primeClassCoordinates_odds_product, <- primeClassCoordinates_odds_product]
  exact List.bernoulliOddsProduct_coeff_mono_padded
    (primeClassCoordinates P v (Nat.floor x))
    (primeClassCoordinates greedyPrimeClass v (Nat.floor x))
    ((primeClassPrefix greedyPrimeClass (Nat.floor x)).card -
      (primeClassPrefix P (Nat.floor x)).card) r
    (greedyPrimeClass_local_coordinate_order P x hx hP v hv0 hmono)
    (primeClassCoordinates_nonneg P v (Nat.floor x) hv0)
    (primeClassCoordinates_nonneg greedyPrimeClass v (Nat.floor x) hv0)

end PrimeFactorOscillations.PrimeClassDeletion
