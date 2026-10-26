/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelBinaryCompletion

/-!
# Mean-one two-phase completion and its all-packet RH criterion

The probability density is the average of the two original phase densities.
Its scaled proof weight is kept separate. Normalization, the full signed
consumer and both directions of the RH criterion retain all sampling premises.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelBinaryProbability

open Filter PrimeFactorUnimodality CarmichaelCorrelation CarmichaelBinaryCompletion

def normalizedKernel (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (g : Units (ZMod q)) : Real :=
  (kernel (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S) g +
    kernel (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S)
      (completionPhase q * g)) / 2

theorem normalizedKernel_sum (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q)))) :
    Finset.univ.sum (normalizedKernel q S) = (Fintype.card (Units (ZMod q)) : Real) := by
  classical
  let w := vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S
  have hMean := kernel_mean_one w (canonical_vacancy_weightSum_pos S hDiv)
  have hn : Not ((Fintype.card (Units (ZMod q)) : Real) = 0) := by
    exact_mod_cast Fintype.card_ne_zero
  have hRaw : Finset.univ.sum (fun g : Units (ZMod q) => kernel w g) =
      (Fintype.card (Units (ZMod q)) : Real) := by
    simpa only [one_mul] using (div_eq_iff hn).mp hMean
  have hShift : Finset.univ.sum (fun g : Units (ZMod q) =>
      kernel w (completionPhase q * g)) =
        Finset.univ.sum (fun g : Units (ZMod q) => kernel w g) := by
    simpa using Equiv.sum_comp (Equiv.mulLeft (completionPhase q))
      (fun g : Units (ZMod q) => kernel w g)
  change Finset.univ.sum (fun g : Units (ZMod q) =>
    (kernel w g + kernel w (completionPhase q * g)) / 2) = _
  rw [<- Finset.sum_div, Finset.sum_add_distrib, hShift, hRaw]
  ring

theorem normalizedKernel_mean_one (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q)))) :
    (Finset.univ.sum (normalizedKernel q S)) /
      (Fintype.card (Units (ZMod q)) : Real) = 1 := by
  rw [normalizedKernel_sum q S hDiv]
  apply div_self
  exact_mod_cast Fintype.card_ne_zero

theorem normalizedKernel_floor (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (g : Units (ZMod q)) :
    (3 / 16 : Real) <= normalizedKernel q S g := by
  have h := completionPhase_cover q S hDiv g
  unfold normalizedKernel
  linarith

def normalizedPrimeWeight (q : Nat) [NeZero q] (S : Finset Nat.Primes) (n : Nat) : Real :=
  (3 / 8 : Real) * completedPrimeWeight q S n

theorem normalizedPrimeWeight_eq_average (q : Nat) [NeZero q]
    (S : Finset Nat.Primes) (n : Nat) :
    normalizedPrimeWeight q S n =
      (carmichaelPrimeWeight q S n + phasePrimeWeight q S (completionPhase q) n) / 2 := by
  unfold normalizedPrimeWeight completedPrimeWeight
  ring

theorem normalizedPrimeWeight_eq_kernel_of_coprime (q : Nat) [NeZero q]
    (S : Finset Nat.Primes) (n : Nat) (hn : Nat.Coprime n q) :
    normalizedPrimeWeight q S n = normalizedKernel q S (ZMod.unitOfCoprime n hn) := by
  classical
  rw [normalizedPrimeWeight_eq_average]
  simp only [carmichaelPrimeWeight, phasePrimeWeight, dite_eq_left hn, normalizedKernel]

def normalizedLocalAscentExcess (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes) (X : Nat) : Real :=
  weightedLocalAscentExcess H m a
    (fun Y i => normalizedPrimeWeight (q Y) (S Y) (primeAt (a Y i))) X

theorem normalizedLocalAscentExcess_eq_scaled
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes) (X : Nat) :
    normalizedLocalAscentExcess H m a q S X =
      (3 / 8 : Real) * completedLocalAscentExcess H m a q S X := by
  unfold normalizedLocalAscentExcess completedLocalAscentExcess weightedLocalAscentExcess
    normalizedPrimeWeight completedLocalAscentWeight
  simp only [Finset.mul_sum, mul_assoc]

theorem normalizedLocalAscentExcess_common_lower
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (X : Nat)
    (hCount : (m X : Real) / 2 <= (localAscentUnitIndices m a X (q X)).card)
    (B : Real) (hB : 0 <= B)
    (hPoint : forall i, B <= localAscentPairExcess H X (a X i)) :
    3 * (m X : Real) * B / 32 <= normalizedLocalAscentExcess H m a q S X := by
  have h := completedLocalAscentExcess_common_lower H m a q S hDiv X hCount B hB hPoint
  rw [normalizedLocalAscentExcess_eq_scaled]
  nlinarith

theorem normalizedLocalAscentExcess_unbounded_of_not_RH
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop)
    (hNotRH : Not RiemannHypothesis) (C X0 : Real) (hC : 0 < C) :
    exists n : Nat, X0 < (n : Real) /\
      C * (n : Real) ^ (7 / 10 : Real) < normalizedLocalAscentExcess H m a q S n := by
  choose n hn hEx using completedLocalAscentExcess_unbounded_of_not_RH
    H m a hs q S hDiv hBudget hNotRH ((8 / 3 : Real) * C) X0 (by positivity)
  refine Exists.intro n (And.intro hn ?_)
  rw [normalizedLocalAscentExcess_eq_scaled]
  nlinarith

theorem riemannHypothesis_iff_normalizedLocalAscentExcess_nonpos
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop) :
    RiemannHypothesis <-> Filter.Eventually
      (fun X : Nat => normalizedLocalAscentExcess H m a q S X <= 0) atTop := by
  have hCriterion := riemannHypothesis_iff_completedLocalAscentExcess_nonpos
    H m a hs q S hDiv hBudget
  constructor
  . intro hRH
    filter_upwards [hCriterion.mp hRH] with X hX
    rw [normalizedLocalAscentExcess_eq_scaled]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) hX
  . intro hEvent
    apply hCriterion.mpr
    filter_upwards [hEvent] with X hX
    rw [normalizedLocalAscentExcess_eq_scaled] at hX
    linarith

theorem riemannHypothesis_iff_normalizedLocalAscentExcess_power_upper
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop) :
    RiemannHypothesis <-> exists C : Real, 0 < C /\ Filter.Eventually
      (fun X : Nat => normalizedLocalAscentExcess H m a q S X <=
        C * (X : Real) ^ (7 / 10 : Real)) atTop := by
  constructor
  . intro hRH
    refine Exists.intro 1 (And.intro (by norm_num) ?_)
    filter_upwards [((riemannHypothesis_iff_normalizedLocalAscentExcess_nonpos
      H m a hs q S hDiv hBudget).mp hRH)] with X hX
    have hNon := Real.rpow_nonneg (Nat.cast_nonneg X) (7 / 10 : Real)
    simpa only [one_mul] using hX.trans hNon
  . intro h
    choose C hC hEvent using h
    by_contra hNotRH
    choose N hN using eventually_atTop.mp hEvent
    choose n hn hEx using normalizedLocalAscentExcess_unbounded_of_not_RH
      H m a hs q S hDiv hBudget hNotRH C (N : Real) hC
    have hnN : N <= n := by exact_mod_cast hn.le
    exact (not_lt_of_ge (hN n hnN)) hEx

end PrimeFactorOscillations.CarmichaelBinaryProbability
