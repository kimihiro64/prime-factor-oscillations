/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PowerPolynomialLaw

/-!
# General Polynomial Detector

Polynomial-root Bernoulli laws with exact forced-prime reduction and degree-uniform comparison.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.GeneralPolynomialLaw

local instance (p : Nat.Primes) : NeZero (p : Nat) := NeZero.mk p.property.ne_zero

def reduction (P : Polynomial Int) (p : Nat.Primes) : Polynomial (ZMod (p : Nat)) :=
  P.map (Int.castRingHom (ZMod (p : Nat)))

def rootSet (P : Polynomial Int) (p : Nat.Primes) : Finset (ZMod (p : Nat)) := by
  classical
  exact Finset.univ.filter (fun x => (reduction P p).eval x = 0)

def unitRootSet (P : Polynomial Int) (p : Nat.Primes) : Finset (ZMod (p : Nat)) := by
  classical
  exact (rootSet P p).filter (fun x => Not (x = 0))

def rootCount (P : Polynomial Int) (p : Nat.Primes) : Nat := (rootSet P p).card
def unitRootCount (P : Polynomial Int) (p : Nat.Primes) : Nat := (unitRootSet P p).card

def effectiveCount (k q : Nat) : Nat := if k = q then 0 else k

theorem effectiveCount_le (k q : Nat) (h : k <= q) : effectiveCount k q <= q := by
  unfold effectiveCount
  split_ifs <;> omega

theorem effectiveCount_odds (k q : Nat) :
    ((effectiveCount k q : Nat) : Real) /
        ((q : Real) - effectiveCount k q) = (k : Real) / ((q : Real) - k) := by
  unfold effectiveCount
  split_ifs with h
  . subst k
    simp
  . rfl

theorem rootCount_le_prime (P : Polynomial Int) (p : Nat.Primes) :
    rootCount P p <= (p : Nat) := by
  unfold rootCount rootSet
  simpa only [Finset.card_univ, ZMod.card] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (ZMod (p : Nat))))
      (fun x => (reduction P p).eval x = 0))

theorem unitRootCount_le_predecessor (P : Polynomial Int) (p : Nat.Primes) :
    unitRootCount P p <= (p : Nat) - 1 := by
  classical
  have hs : unitRootSet P p <=
      (Finset.univ : Finset (ZMod (p : Nat))).erase 0 := by
    intro x hx
    exact Finset.mem_erase.mpr
      (And.intro ((Finset.mem_filter.mp hx).2) (Finset.mem_univ x))
  have h := Finset.card_le_card hs
  simpa only [unitRootCount, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod (p : Nat))),
    Finset.card_univ, ZMod.card] using h

theorem rootCount_le_degree (P : Polynomial Int) (p : Nat.Primes)
    (hP : Not (reduction P p = 0)) : rootCount P p <= P.natDegree := by
  classical
  letI : Fact (Nat.Prime (p : Nat)) := Fact.mk p.property
  have hs : rootSet P p = (reduction P p).roots.toFinset := by
    ext x
    simp only [rootSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot]
  unfold rootCount
  rw [hs]
  exact (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans Polynomial.natDegree_map_le)

theorem effective_integer_degree (P : Polynomial Int) (p : Nat.Primes) :
    effectiveCount (rootCount P p) (p : Nat) <= P.natDegree := by
  classical
  by_cases hz : reduction P p = 0
  . have hr : rootCount P p = (p : Nat) := by
      simp [rootCount, rootSet, hz, ZMod.card]
    simp [effectiveCount, hr]
  . unfold effectiveCount
    split_ifs
    . exact Nat.zero_le _
    . exact rootCount_le_degree P p hz

theorem effective_prime_degree (P : Polynomial Int) (p : Nat.Primes) :
    effectiveCount (unitRootCount P p) ((p : Nat) - 1) <= P.natDegree := by
  classical
  by_cases hz : reduction P p = 0
  . have hr : unitRootCount P p = (p : Nat) - 1 := by
      have hs : unitRootSet P p =
          (Finset.univ : Finset (ZMod (p : Nat))).erase 0 := by
        ext x
        simp [unitRootSet, rootSet, hz]
      unfold unitRootCount
      rw [hs, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod (p : Nat))),
        Finset.card_univ, ZMod.card]
    simp [effectiveCount, hr]
  . unfold effectiveCount
    split_ifs
    . exact Nat.zero_le _
    . exact (Finset.card_filter_le _ _).trans (rootCount_le_degree P p hz)

def integerLaw (P : Polynomial Int) (D : Nat) (hD : 0 < D)
    (hDegree : P.natDegree <= D) : PrimeClockLaw :=
  PrimeClockLaw.ofRootCounts
    (fun p => effectiveCount (rootCount P p) (p : Nat)) (fun p => (p : Nat)) D hD
    (fun p => effectiveCount_le _ _ (rootCount_le_prime P p))
    (fun p => (effective_integer_degree P p).trans hDegree)
    (fun p => Nat.sub_le _ _)

def primeLaw (P : Polynomial Int) (D : Nat) (hD : 0 < D)
    (hDegree : P.natDegree <= D) : PrimeClockLaw :=
  PrimeClockLaw.ofRootCounts
    (fun p => effectiveCount (unitRootCount P p) ((p : Nat) - 1))
    (fun p => (p : Nat) - 1) D hD
    (fun p => effectiveCount_le _ _ (unitRootCount_le_predecessor P p))
    (fun p => (effective_prime_degree P p).trans hDegree)
    (fun _ => le_rfl)

theorem integerLaw_weight (P : Polynomial Int) (D : Nat) (hD : 0 < D)
    (hDegree : P.natDegree <= D) (p : Nat.Primes) :
    (integerLaw P D hD hDegree).weight p =
      ((rootCount P p : Real) / (p : Nat)) /
        (1 - (rootCount P p : Real) / (p : Nat)) := by
  have hp : Not (((p : Nat) : Real) = 0) := by exact_mod_cast p.property.ne_zero
  change ((effectiveCount (rootCount P p) (p : Nat) : Nat) : Real) /
    ((p : Nat) - effectiveCount (rootCount P p) (p : Nat)) = _
  rw [effectiveCount_odds, div_div]
  congr 1
  field_simp [hp]

theorem primeLaw_weight (P : Polynomial Int) (D : Nat) (hD : 0 < D)
    (hDegree : P.natDegree <= D) (p : Nat.Primes) :
    (primeLaw P D hD hDegree).weight p =
      ((unitRootCount P p : Real) / ((p : Nat) - 1 : Nat)) /
        (1 - (unitRootCount P p : Real) / ((p : Nat) - 1 : Nat)) := by
  have hqNat : 0 < (p : Nat) - 1 := Nat.sub_pos_of_lt p.property.one_lt
  have hq : Not ((((p : Nat) - 1 : Nat) : Real) = 0) := by exact_mod_cast (Nat.ne_of_gt hqNat)
  change ((effectiveCount (unitRootCount P p) ((p : Nat) - 1) : Nat) : Real) /
    (((p : Nat) - 1 : Nat) - effectiveCount (unitRootCount P p) ((p : Nat) - 1)) = _
  rw [effectiveCount_odds, div_div]
  congr 1
  field_simp [hq]

theorem integerLaw_comparison (P : Polynomial Int) (D : Nat) (hD : 0 < D)
    (hDegree : P.natDegree <= D) (b : Real) (hb : 0 < b) :
    PowerPolynomialLaw.ComparisonClaim (integerLaw P D hD hDegree) b :=
  (integerLaw P D hD hDegree).exists_densityRatio_linearization b hb

theorem primeLaw_comparison (P : Polynomial Int) (D : Nat) (hD : 0 < D)
    (hDegree : P.natDegree <= D) (b : Real) (hb : 0 < b) :
    PowerPolynomialLaw.ComparisonClaim (primeLaw P D hD hDegree) b :=
  (primeLaw P D hD hDegree).exists_densityRatio_linearization b hb


end PrimeFactorOscillations.GeneralPolynomialLaw
