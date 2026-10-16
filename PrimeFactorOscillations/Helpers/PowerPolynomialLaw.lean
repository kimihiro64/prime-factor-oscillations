/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import PrimeFactorOscillations.Helpers.PrimeClockComparison
import PrimeFactorOscillations.Helpers.QuadraticMassRH

/-!
# Probability coefficient comparison for every power polynomial

Both integer and prime input laws for x^d-a use actual finite-field root counts. Forced local probabilities are retained in the exact rank-shift bridge.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations
open Filter

theorem nat_odds_scaled_le (q k : Nat) (hk : k <= q) :
    (q : Real) * ((k : Real) / ((q : Real) - k)) <=
      (k : Real) * ((k : Real) + 1) := by
  by_cases heq : k = q
  . subst k
    simp only [sub_self, div_zero, mul_zero]
    positivity
  . have hlt : k < q := lt_of_le_of_ne hk heq
    have hgapCast : (k : Real) + 1 <= q := by exact_mod_cast hlt
    have hgap : (1 : Real) <= (q : Real) - k := by linarith
    have hpos : 0 < (q : Real) - k := by linarith
    have hProd : 0 <= (k : Real) ^ 2 * (((q : Real) - k) - 1) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    have hNum : (q : Real) * k <=
        ((k : Real) * ((k : Real) + 1)) * ((q : Real) - k) := by
      nlinarith only [hProd]
    calc
      _ = ((q : Real) * k) / ((q : Real) - k) := by ring
      _ <= (((k : Real) * ((k : Real) + 1)) * ((q : Real) - k)) /
          ((q : Real) - k) := div_le_div_of_nonneg_right hNum hpos.le
      _ = _ := by field_simp [hpos.ne']

namespace PrimeClockLaw

def ofBoundedOdds (w : Nat.Primes -> Real) (D : Real) (hD : 0 < D)
    (hw : forall p, 0 <= w p)
    (hBound : forall p, w p <= D * primeProfileWeight (p : Nat)) : PrimeClockLaw where
  weight := w
  compensator := w
  scale := D
  error := 0
  scale_pos := hD
  error_nonneg := le_rfl
  weight_nonneg := hw
  compensator_nonneg := hw
  compensator_le := hBound
  quadratic_error := by intro p; simp

theorem rootOdds_le (rho q : Nat.Primes -> Nat) (M : Nat) (hM : 0 < M)
    (hRho : forall p, rho p <= q p)
    (hDegree : forall p, rho p <= M)
    (hDenom : forall p : Nat.Primes, (p : Nat) - 1 <= q p) (p : Nat.Primes) :
    (rho p : Real) / ((q p : Real) - rho p) <=
      ((M : Real) * ((M : Real) + 1)) * primeProfileWeight (p : Nat) := by
  have hDiff : 0 <= (q p : Real) - rho p := sub_nonneg.mpr (by exact_mod_cast hRho p)
  have hw : 0 <= (rho p : Real) / ((q p : Real) - rho p) :=
    div_nonneg (Nat.cast_nonneg _) hDiff
  have hNatPos : 0 < (p : Nat) - 1 := Nat.sub_pos_of_lt p.property.one_lt
  have hPredPos : (0 : Real) < ((p : Nat) - 1 : Nat) := by exact_mod_cast hNatPos
  have hPred : (((p : Nat) - 1 : Nat) : Real) <= q p := by exact_mod_cast hDenom p
  have h1 := mul_le_mul_of_nonneg_right hPred hw
  have h2 := nat_odds_scaled_le (q p) (rho p) (hRho p)
  have hDegreeR : (rho p : Real) <= M := by exact_mod_cast hDegree p
  have h3 : (rho p : Real) * ((rho p : Real) + 1) <=
      (M : Real) * ((M : Real) + 1) := by
    have hrhoNonneg : (0 : Real) <= rho p := Nat.cast_nonneg _
    have hMNonneg : (0 : Real) <= M := Nat.cast_nonneg _
    nlinarith
  have hProd : ((rho p : Real) / ((q p : Real) - rho p)) *
      (((p : Nat) - 1 : Nat) : Real) <= (M : Real) * ((M : Real) + 1) := by
    nlinarith only [h1, h2, h3]
  simp only [primeProfileWeight, mul_one_div]
  calc
    _ = (((rho p : Real) / ((q p : Real) - rho p)) *
        (((p : Nat) - 1 : Nat) : Real)) / (((p : Nat) - 1 : Nat) : Real) := by
          field_simp [hPredPos.ne']
    _ <= _ := div_le_div_of_nonneg_right hProd hPredPos.le

def ofRootCounts (rho q : Nat.Primes -> Nat) (M : Nat) (hM : 0 < M)
    (hRho : forall p, rho p <= q p)
    (hDegree : forall p, rho p <= M)
    (hDenom : forall p : Nat.Primes, (p : Nat) - 1 <= q p) : PrimeClockLaw :=
  ofBoundedOdds (fun p => (rho p : Real) / ((q p : Real) - rho p))
    ((M : Real) * ((M : Real) + 1)) (by
      have hMR : (0 : Real) < M := by exact_mod_cast hM
      exact mul_pos hMR (by linarith))
    (by intro p; exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hRho p)))
    (rootOdds_le rho q M hM hRho hDegree hDenom)

theorem rootCounts_weight_eq_probability_odds
    (rho q : Nat.Primes -> Nat) (M : Nat) (hM : 0 < M)
    (hRho : forall p, rho p <= q p)
    (hDegree : forall p, rho p <= M)
    (hDenom : forall p : Nat.Primes, (p : Nat) - 1 <= q p) (p : Nat.Primes) :
    (ofRootCounts rho q M hM hRho hDegree hDenom).weight p =
      ((rho p : Real) / q p) / (1 - (rho p : Real) / q p) := by
  have hPredPos : 0 < (p : Nat) - 1 := Nat.sub_pos_of_lt p.property.one_lt
  have hqPos : 0 < q p := hPredPos.trans_le (hDenom p)
  have hq : Not ((q p : Real) = 0) := by exact_mod_cast (Nat.ne_of_gt hqPos)
  change (rho p : Real) / ((q p : Real) - rho p) = _
  rw [div_div]
  congr 1
  field_simp [hq]

theorem probabilityMass_ratio_eq_densityRatio (law : PrimeClockLaw)
    (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (N r : Nat) (hr : 1 <= r) :
    let s := familyPrefixProbabilities eta N
    List.bernoulliMass s (s.count 1 + r - 1) /
      List.bernoulliMass s (s.count 1 + r) = law.densityRatio N r := by
  have hOne : forall a, List.Mem a (familyPrefixProbabilities eta N) -> a <= 1 := by
    intro a ha
    choose p hp using List.mem_map.mp ha
    rw [<- hp.2]
    exact hProb (p : Nat) p.property
  have hOdds :
      (((familyPrefixProbabilities eta N).map (fun a => a / (1 - a)) : List Real) :
        Multiset Real) = (primeProfilePrefixSet N).val.map law.weight := by
    simp only [familyPrefixProbabilities, List.map_map]
    rw [<- Multiset.map_coe, Finset.coe_toList]
    congr 1
    funext p
    exact (hWeight p).symm
  dsimp only
  rw [familyMass_ratio_eq_full_odds _ hOne r hr, hOdds]
  rfl

end PrimeClockLaw

namespace PowerPolynomialLaw

def rootSet (d : Nat) (a : Int) (p : Nat.Primes) : Finset (ZMod (p : Nat)) := by
  letI : Fact (Nat.Prime (p : Nat)) := Fact.mk p.property
  exact Finset.univ.filter (fun x : ZMod (p : Nat) => x ^ d = (a : ZMod (p : Nat)))

def unitRootSet (d : Nat) (a : Int) (p : Nat.Primes) : Finset (ZMod (p : Nat)) :=
  (rootSet d a p).filter (fun x => Not (x = 0))

def rootCount (d : Nat) (a : Int) (p : Nat.Primes) : Nat := (rootSet d a p).card
def unitRootCount (d : Nat) (a : Int) (p : Nat.Primes) : Nat := (unitRootSet d a p).card

theorem rootCount_le_degree (d : Nat) (a : Int) (hd : 0 < d) (p : Nat.Primes) :
    rootCount d a p <= d := by
  letI : Fact (Nat.Prime (p : Nat)) := Fact.mk p.property
  have heq : rootSet d a p = (Polynomial.nthRoots d (a : ZMod (p : Nat))).toFinset := by
    ext x
    simp only [rootSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Multiset.mem_toFinset, Polynomial.mem_nthRoots hd]
  unfold rootCount
  rw [heq]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots d _)

theorem rootCount_le_prime (d : Nat) (a : Int) (p : Nat.Primes) :
    rootCount d a p <= (p : Nat) := by
  letI : Fact (Nat.Prime (p : Nat)) := Fact.mk p.property
  unfold rootCount rootSet
  simpa only [Finset.card_univ, ZMod.card] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (ZMod (p : Nat))))
      (fun x => x ^ d = (a : ZMod (p : Nat))))

theorem unitRootCount_le_degree (d : Nat) (a : Int) (hd : 0 < d) (p : Nat.Primes) :
    unitRootCount d a p <= d :=
  (Finset.card_filter_le _ _).trans (rootCount_le_degree d a hd p)

theorem unitRootCount_le_predecessor (d : Nat) (a : Int) (p : Nat.Primes) :
    unitRootCount d a p <= (p : Nat) - 1 := by
  letI : Fact (Nat.Prime (p : Nat)) := Fact.mk p.property
  have hSub : unitRootSet d a p <=
      (Finset.univ : Finset (ZMod (p : Nat))).erase 0 := by
    intro x hx
    have h := (Finset.mem_filter.mp hx).2
    exact Finset.mem_erase.mpr (And.intro h (Finset.mem_univ x))
  have h := Finset.card_le_card hSub
  simpa only [unitRootCount, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod (p : Nat))),
    Finset.card_univ, ZMod.card] using h

def integerLaw (d : Nat) (a : Int) (hd : 0 < d) : PrimeClockLaw :=
  PrimeClockLaw.ofRootCounts (rootCount d a) (fun p => (p : Nat)) d hd
    (rootCount_le_prime d a) (rootCount_le_degree d a hd) (fun p => Nat.sub_le _ _)

def primeLaw (d : Nat) (a : Int) (hd : 0 < d) : PrimeClockLaw :=
  PrimeClockLaw.ofRootCounts (unitRootCount d a) (fun p => (p : Nat) - 1) d hd
    (unitRootCount_le_predecessor d a) (unitRootCount_le_degree d a hd) (fun _ => le_rfl)

def ComparisonClaim (law : PrimeClockLaw) (b : Real) : Prop :=
  exists r0 N0 : Nat, exists K : Real,
    0 < r0 /\ 1 <= N0 /\ 0 <= K /\
    forall r : Nat, r0 <= r -> forall N : Nat, N0 <= N ->
    forall L : Real, 2 <= L -> abs (law.arithmeticClock N - L) <= 1 ->
      (r : Real) / L <= b ->
      0 < law.prefixEsymm N r /\
      0 < Nat.factorialConvolution law.realCoefficient r L /\
      abs (law.densityRatio N r - law.referenceRatio r L -
        ((r : Real) / L ^ 2) * (L - law.arithmeticClock N)) <=
          K * (abs (L - law.arithmeticClock N) / L ^ 2 +
            1 / ((r : Real) * (N : Real)))

theorem integerLaw_comparison (d : Nat) (a : Int) (hd : 0 < d) (b : Real) (hb : 0 < b) :
    ComparisonClaim (integerLaw d a hd) b :=
  (integerLaw d a hd).exists_densityRatio_linearization b hb

theorem primeLaw_comparison (d : Nat) (a : Int) (hd : 0 < d) (b : Real) (hb : 0 < b) :
    ComparisonClaim (primeLaw d a hd) b :=
  (primeLaw d a hd).exists_densityRatio_linearization b hb

end PowerPolynomialLaw
end PrimeFactorOscillations
