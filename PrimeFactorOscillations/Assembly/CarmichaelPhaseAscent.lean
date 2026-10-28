/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPhaseKernel
import PrimeFactorOscillations.Helpers.WeightedLocalizedAscentCriterion

/-!
# Local ascent criteria for the actual Gauss-phase kernel

The full inducing modulus N supplies the nonunit mask and witness budget.
Its prime divisor q supplies the Gauss phase and kernel. The complete
signed local ascent excess is retained. The existing local sampling
hypothesis is explicit; no infinitude of twins is substituted for it.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelPhaseAscent
open Filter PrimeFactorUnimodality CarmichaelPhaseKernel

def primeWeight (N q : Nat) [NeZero N] [NeZero q] [Fact (Nat.Prime q)]
    (hqN : Dvd.dvd q N) (l : Nat.Primes) (psi : AddChar (ZMod q) Complex)
    (p : Nat) : Real := by
  classical
  exact if h : Nat.Coprime p N then
    phaseKernel q l (DirichletEvenGaussPhase.phase q psi)
      (ZMod.unitsMap hqN (ZMod.unitOfCoprime p h))
    else 0

theorem primeWeight_nonneg (N q : Nat) [NeZero N] [NeZero q] [Fact (Nat.Prime q)]
    (hqN : Dvd.dvd q N) (l : Nat.Primes) (psi : AddChar (ZMod q) Complex)
    (hPsi : psi.IsPrimitive)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hThree : 3 <= CarmichaelPrimePacket.index q l) (p : Nat) :
    0 <= primeWeight N q hqN l psi p := by
  classical
  unfold primeWeight
  split_ifs with h
  . exact (by norm_num : (0 : Real) <= 1 / 2).trans
      (actual_gauss_kernel_ge_half q psi hPsi l hDiv hThree _)
  . exact le_rfl

theorem primeWeight_ge_half (N q : Nat) [NeZero N] [NeZero q] [Fact (Nat.Prime q)]
    (hqN : Dvd.dvd q N) (l : Nat.Primes) (psi : AddChar (ZMod q) Complex)
    (hPsi : psi.IsPrimitive)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hThree : 3 <= CarmichaelPrimePacket.index q l) (p : Nat)
    (hp : Nat.Coprime p N) :
    (1 / 2 : Real) <= primeWeight N q hqN l psi p := by
  classical
  simp only [primeWeight, dite_eq_left hp]
  exact actual_gauss_kernel_ge_half q psi hPsi l hDiv hThree _

def localWeight (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (N q : Nat -> Nat) [forall X, NeZero (N X)] [forall X, NeZero (q X)]
    [forall X, Fact (Nat.Prime (q X))]
    (hqN : forall X, Dvd.dvd (q X) (N X)) (l : Nat -> Nat.Primes)
    (psi : (X : Nat) -> AddChar (ZMod (q X)) Complex)
    (X : Nat) (i : Fin (m X)) : Real :=
  primeWeight (N X) (q X) (hqN X) (l X) (psi X) (primeAt (a X i))

def excess (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (N q : Nat -> Nat) [forall X, NeZero (N X)] [forall X, NeZero (q X)]
    [forall X, Fact (Nat.Prime (q X))]
    (hqN : forall X, Dvd.dvd (q X) (N X)) (l : Nat -> Nat.Primes)
    (psi : (X : Nat) -> AddChar (ZMod (q X)) Complex) (X : Nat) : Real :=
  weightedLocalAscentExcess H m a (localWeight m a N q hqN l psi) X

theorem unit_weights (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (N q : Nat -> Nat) [forall X, NeZero (N X)] [forall X, NeZero (q X)]
    [forall X, Fact (Nat.Prime (q X))]
    (hqN : forall X, Dvd.dvd (q X) (N X)) (l : Nat -> Nat.Primes)
    (psi : (X : Nat) -> AddChar (ZMod (q X)) Complex)
    (hPsi : forall X, (psi X).IsPrimitive)
    (hDiv : forall X, Dvd.dvd (l X : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hThree : forall X, 3 <= CarmichaelPrimePacket.index (q X) (l X)) :
    LocalAscentUnitWeights m a N (localWeight m a N q hqN l psi) := by
  intro X i
  exact And.intro
    (primeWeight_nonneg (N X) (q X) (hqN X) (l X) (psi X)
      (hPsi X) (hDiv X) (hThree X) _)
    (fun hp => primeWeight_ge_half (N X) (q X) (hqN X) (l X) (psi X)
      (hPsi X) (hDiv X) (hThree X) _ hp)

theorem unbounded_of_not_RH
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (N q : Nat -> Nat) [forall X, NeZero (N X)] [forall X, NeZero (q X)]
    [forall X, Fact (Nat.Prime (q X))]
    (hqN : forall X, Dvd.dvd (q X) (N X)) (l : Nat -> Nat.Primes)
    (psi : (X : Nat) -> AddChar (ZMod (q X)) Complex)
    (hPsi : forall X, (psi X).IsPrimitive)
    (hDiv : forall X, Dvd.dvd (l X : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hThree : forall X, 3 <= CarmichaelPrimePacket.index (q X) (l X))
    (hBudget : Filter.Eventually (fun X : Nat => N X <= X ^ (m X / 2)) atTop)
    (hNotRH : Not RiemannHypothesis) (C X0 : Real) (hC : 0 < C) :
    exists n : Nat, X0 < (n : Real) /\
      C * (n : Real) ^ (7 / 10 : Real) < excess H m a N q hqN l psi n := by
  have hQ : Filter.Eventually (fun X : Nat =>
      And (0 < N X) (N X <= X ^ (m X / 2))) atTop := by
    filter_upwards [hBudget] with X hX
    exact And.intro (Nat.pos_of_ne_zero (NeZero.ne (N X))) hX
  exact weightedLocalAscentExcess_unbounded_of_not_RH H m a hs N _
    (unit_weights m a N q hqN l psi hPsi hDiv hThree) hQ hNotRH C X0 hC

theorem rh_iff_eventually_nonpos
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (N q : Nat -> Nat) [forall X, NeZero (N X)] [forall X, NeZero (q X)]
    [forall X, Fact (Nat.Prime (q X))]
    (hqN : forall X, Dvd.dvd (q X) (N X)) (l : Nat -> Nat.Primes)
    (psi : (X : Nat) -> AddChar (ZMod (q X)) Complex)
    (hPsi : forall X, (psi X).IsPrimitive)
    (hDiv : forall X, Dvd.dvd (l X : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hThree : forall X, 3 <= CarmichaelPrimePacket.index (q X) (l X))
    (hBudget : Filter.Eventually (fun X : Nat => N X <= X ^ (m X / 2)) atTop) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat => excess H m a N q hqN l psi X <= 0) atTop := by
  have hQ : Filter.Eventually (fun X : Nat =>
      And (0 < N X) (N X <= X ^ (m X / 2))) atTop := by
    filter_upwards [hBudget] with X hX
    exact And.intro (Nat.pos_of_ne_zero (NeZero.ne (N X))) hX
  exact riemannHypothesis_iff_eventually_weightedLocalAscentExcess_nonpos H m a hs N _
    (unit_weights m a N q hqN l psi hPsi hDiv hThree) hQ

theorem rh_iff_eventually_power_upper
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (N q : Nat -> Nat) [forall X, NeZero (N X)] [forall X, NeZero (q X)]
    [forall X, Fact (Nat.Prime (q X))]
    (hqN : forall X, Dvd.dvd (q X) (N X)) (l : Nat -> Nat.Primes)
    (psi : (X : Nat) -> AddChar (ZMod (q X)) Complex)
    (hPsi : forall X, (psi X).IsPrimitive)
    (hDiv : forall X, Dvd.dvd (l X : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hThree : forall X, 3 <= CarmichaelPrimePacket.index (q X) (l X))
    (hBudget : Filter.Eventually (fun X : Nat => N X <= X ^ (m X / 2)) atTop) :
    RiemannHypothesis <-> exists C : Real, 0 < C /\
      Filter.Eventually (fun X : Nat =>
        excess H m a N q hqN l psi X <= C * (X : Real) ^ (7 / 10 : Real)) atTop := by
  have hQ : Filter.Eventually (fun X : Nat =>
      And (0 < N X) (N X <= X ^ (m X / 2))) atTop := by
    filter_upwards [hBudget] with X hX
    exact And.intro (Nat.pos_of_ne_zero (NeZero.ne (N X))) hX
  exact riemannHypothesis_iff_eventually_weightedLocalAscentExcess_power_upper H m a hs N _
    (unit_weights m a N q hqN l psi hPsi hDiv hThree) hQ

end PrimeFactorOscillations.CarmichaelPhaseAscent
