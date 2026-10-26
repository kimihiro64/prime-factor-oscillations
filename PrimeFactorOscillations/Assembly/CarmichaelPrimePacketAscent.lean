/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPrimePacketSpectrum
import PrimeFactorOscillations.Assembly.CarmichaelSingleAscent

/-!
# One-pair RH criteria with prescribed prime-order character support

A return-image index of at least three keeps every future prime witness.
The label may vary, including label two. The exceptional index-two kernel
is characterized explicitly instead of being treated as uniformly positive.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelPrimePacketAscent

open Filter PrimeFactorUnimodality CarmichaelCorrelation CarmichaelPrimePacket
open PrimeOrderReturnLaw

theorem native_weight_bounds_of_coprime (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hIndex : 3 <= index q l) (p : Nat) (hCoprime : Nat.Coprime p q) :
    And ((3 / 4 : Real) <= carmichaelPrimeWeight q {l} p)
      (carmichaelPrimeWeight q {l} p <= 3 / 2) := by
  classical
  simp only [carmichaelPrimeWeight, dite_eq_left hCoprime]
  exact kernel_bounds_of_index_ge_three q l hDiv hIndex (ZMod.unitOfCoprime p hCoprime)

private theorem sample_coprime_eventually
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop) :
    Filter.Eventually (fun X : Nat => Nat.Coprime (primeAt (a X)) (q X)) atTop := by
  filter_upwards [hs, hSmooth] with X hPair hQ
  have hLow : X < primeAt (a X) := by
    have hNat : X <= primeAt (a X) - 1 := by exact_mod_cast hPair.2.2.1
    have hp := (prime_primeAt (a X)).two_le
    omega
  have hUnit := Nat.isUnit_largestPrimeFactor_of_le_cutoff
    (N := q X) (n := primeAt (a X)) (y := X)
    (prime_primeAt (a X)).pos hQ
    (by simpa only [Nat.largestPrimeFactor_of_prime (prime_primeAt (a X))] using hLow)
  have hActual : IsUnit (primeAt (a X) : ZMod (q X)) := by
    simpa only [Nat.largestPrimeFactor_of_prime (prime_primeAt (a X))] using hUnit
  exact (ZMod.isUnit_iff_coprime _ _).mp hActual

theorem sample_weight_bounds_eventually
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (l : Nat -> Nat.Primes)
    (hDiv : Filter.Eventually (fun X : Nat =>
      Dvd.dvd (l X : Nat) (Monoid.exponent (Units (ZMod (q X))))) atTop)
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop)
    (hIndex : Filter.Eventually (fun X : Nat => 3 <= index (q X) (l X)) atTop) :
    Filter.Eventually (fun X : Nat =>
      And ((3 / 4 : Real) <= carmichaelPrimeWeight (q X) {l X} (primeAt (a X)))
        (carmichaelPrimeWeight (q X) {l X} (primeAt (a X)) <= 3 / 2)) atTop := by
  filter_upwards [sample_coprime_eventually H a hs q hSmooth, hDiv, hIndex]
    with X hCoprime hD hI
  exact native_weight_bounds_of_coprime (q X) (l X) hD hI (primeAt (a X)) hCoprime

theorem riemannHypothesis_iff_eventually_primePacketAscent_bounded
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (l : Nat -> Nat.Primes)
    (hDiv : Filter.Eventually (fun X : Nat =>
      Dvd.dvd (l X : Nat) (Monoid.exponent (Units (ZMod (q X))))) atTop)
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop)
    (hIndex : Filter.Eventually (fun X : Nat => 3 <= index (q X) (l X)) atTop) :
    RiemannHypothesis <->
      exists C : Real, Filter.Eventually (fun X : Nat =>
        carmichaelSingleAscentExcess H a q (fun Y => {l Y}) X <= C) atTop := by
  have hHalf : Filter.Eventually (fun X : Nat =>
      (1 / 2 : Real) <= carmichaelPrimeWeight (q X) {l X} (primeAt (a X))) atTop := by
    filter_upwards [sample_weight_bounds_eventually H a hs q l hDiv hSmooth hIndex] with X hX
    exact (by norm_num : (1 / 2 : Real) <= 3 / 4).trans hX.1
  simpa only [carmichaelSingleAscentExcess] using
    riemannHypothesis_iff_eventually_singleWeightedAscent_bounded H a hs
      (fun X => carmichaelPrimeWeight (q X) {l X} (primeAt (a X))) hHalf

theorem riemannHypothesis_iff_eventually_primePacketAscent_nonpos
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (l : Nat -> Nat.Primes)
    (hDiv : Filter.Eventually (fun X : Nat =>
      Dvd.dvd (l X : Nat) (Monoid.exponent (Units (ZMod (q X))))) atTop)
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop)
    (hIndex : Filter.Eventually (fun X : Nat => 3 <= index (q X) (l X)) atTop) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat =>
        carmichaelSingleAscentExcess H a q (fun Y => {l Y}) X <= 0) atTop := by
  have hHalf : Filter.Eventually (fun X : Nat =>
      (1 / 2 : Real) <= carmichaelPrimeWeight (q X) {l X} (primeAt (a X))) atTop := by
    filter_upwards [sample_weight_bounds_eventually H a hs q l hDiv hSmooth hIndex] with X hX
    exact (by norm_num : (1 / 2 : Real) <= 3 / 4).trans hX.1
  simpa only [carmichaelSingleAscentExcess] using
    riemannHypothesis_iff_eventually_singleWeightedAscent_nonpos H a hs
      (fun X => carmichaelPrimeWeight (q X) {l X} (primeAt (a X))) hHalf

theorem primePacketAscent_unbounded_of_not_RH
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (l : Nat -> Nat.Primes)
    (hDiv : Filter.Eventually (fun X : Nat =>
      Dvd.dvd (l X : Nat) (Monoid.exponent (Units (ZMod (q X))))) atTop)
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop)
    (hIndex : Filter.Eventually (fun X : Nat => 3 <= index (q X) (l X)) atTop)
    (hNotRH : Not RiemannHypothesis) (C X0 : Real) :
    exists n : Nat, X0 < (n : Real) /\
      C < carmichaelSingleAscentExcess H a q (fun Y => {l Y}) n := by
  have hHalf : Filter.Eventually (fun X : Nat =>
      (1 / 2 : Real) <= carmichaelPrimeWeight (q X) {l X} (primeAt (a X))) atTop := by
    filter_upwards [sample_weight_bounds_eventually H a hs q l hDiv hSmooth hIndex] with X hX
    exact (by norm_num : (1 / 2 : Real) <= 3 / 4).trans hX.1
  simpa only [carmichaelSingleAscentExcess] using
    singleWeightedAscent_unbounded_of_not_RH H a hs
      (fun X => carmichaelPrimeWeight (q X) {l X} (primeAt (a X))) hHalf hNotRH C X0

theorem label_eq_two_of_index_two (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hTwo : index q l = 2) : (l : Nat) = 2 := by
  have hLow := l.property.two_le
  have hHigh := divisor_le_returnIndex (G := Units (ZMod q)) (l : Nat) hDiv
  change (l : Nat) <= index q l at hHigh
  omega

theorem kernel_index_two_zero_iff_not_return (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hTwo : index q l = 2) (u : Units (ZMod q)) :
    kernel (weight q l) u = 0 <->
      Not (u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1) := by
  by_cases hReturn : u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1
  . rw [kernel_of_return q l hDiv u hReturn, hTwo]
    norm_num [hReturn]
  . rw [kernel_of_not_return q l hDiv u hReturn, hTwo]
    norm_num [hReturn]

theorem exists_kernel_zero_of_index_two (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hTwo : index q l = 2) :
    exists u : Units (ZMod q), kernel (weight q l) u = 0 := by
  classical
  have hWitness : exists u : Units (ZMod q),
      Not (u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1) := by
    by_contra hNo
    have hEvery (u : Units (ZMod q)) :
        u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1 := by
      by_contra hReturn
      exact hNo (Exists.intro u hReturn)
    have hZero (u : Units (ZMod q)) : weight q l u = 0 := by
      simp [weight, vacancyWeight, vacancy_iff_not_return, hEvery u]
    have hSum : CarmichaelCorrelation.weightSum (weight q l) = 0 := by
      unfold CarmichaelCorrelation.weightSum
      simp_rw [hZero]
      simp
    exact (ne_of_gt (weightSum_pos q l hDiv)) hSum
  choose u hu using hWitness
  exact Exists.intro u ((kernel_index_two_zero_iff_not_return q l hDiv hTwo u).mpr hu)

end PrimeFactorOscillations.CarmichaelPrimePacketAscent
