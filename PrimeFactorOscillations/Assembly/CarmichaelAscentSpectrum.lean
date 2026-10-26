/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelAscentCriterion
import PrimeFactorOscillations.Assembly.CarmichaelDirichletProduct

/-!
# The complete signed ascent criterion in native character coordinates

The actual prime inputs and the full actual-minus-reference ascent counts
are retained. Integer native multiplicities resolve the original observable
exactly, including its principal row. The original RH criteria keep their
sampling, activity, oddness and natural-number modulus budget hypotheses.
-/


set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelAscentSpectrum

open CarmichaelIntegralSpectrum CarmichaelPermutationKernel Filter PrimeFactorUnimodality

local instance characterDecidableEq (q : Nat) : DecidableEq (DirichletCharacter Complex q) :=
  Classical.typeDecidableEq _

def characterRow (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    [forall X, NeZero (q X)] (X : Nat)
    (chi : DirichletCharacter Complex (q X)) : Complex :=
  Finset.univ.sum (fun i : Fin (m X) =>
    chi (primeAt (a X i) : ZMod (q X)) *
      (localAscentPairExcess H X (a X i) : Complex))

def packet (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes) (X : Nat) : Complex :=
  Finset.univ.sum (fun chi : DirichletCharacter Complex (q X) =>
    (multiplicity (S X) chi : Complex) * characterRow H m a q X chi)

def normalizedExcess (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes) (X : Nat) : Real :=
  (packet H m a q S X).re /
    (normalization (G := Units (ZMod (q X))) (S X) : Real)

theorem scaled_excess_eq_packet (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes) (X : Nat)
    (hDiv : forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X))))) :
    (normalization (G := Units (ZMod (q X))) (S X) : Complex) *
      (carmichaelLocalAscentExcess H m a q S X : Complex) = packet H m a q S X := by
  classical
  have hCast : (carmichaelLocalAscentExcess H m a q S X : Complex) =
      Finset.univ.sum (fun i : Fin (m X) =>
        (carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) : Complex) *
          (localAscentPairExcess H X (a X i) : Complex)) := by
    unfold carmichaelLocalAscentExcess weightedLocalAscentExcess carmichaelLocalAscentWeight
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  calc
    _ = Finset.univ.sum (fun i : Fin (m X) =>
        ((normalization (G := Units (ZMod (q X))) (S X) : Complex) *
          (carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) : Complex)) *
            (localAscentPairExcess H X (a X i) : Complex)) := by
      rw [hCast, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (mul_assoc _ _ _).symm
    _ = Finset.univ.sum (fun i : Fin (m X) =>
        Finset.univ.sum (fun chi : DirichletCharacter Complex (q X) =>
          (multiplicity (S X) chi : Complex) * chi (primeAt (a X i) : ZMod (q X))) *
            (localAscentPairExcess H X (a X i) : Complex)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z : Complex => z * (localAscentPairExcess H X (a X i) : Complex))
        (natural_character_expansion (S X) hDiv (primeAt (a X i)))
    _ = _ := by
      unfold packet characterRow
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro chi _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_assoc _ _ _

theorem normalizedExcess_eq_original (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X))))) :
    normalizedExcess H m a q S = carmichaelLocalAscentExcess H m a q S := by
  funext X
  have hM : (0 : Real) < normalization (G := Units (ZMod (q X))) (S X) := by
    exact_mod_cast normalization_pos (S X) (hDiv X)
  have hScale :
      (normalization (G := Units (ZMod (q X))) (S X) : Real) *
        carmichaelLocalAscentExcess H m a q S X = (packet H m a q S X).re := by
    have hc :
        (((normalization (G := Units (ZMod (q X))) (S X) : Real) *
          carmichaelLocalAscentExcess H m a q S X : Real) : Complex) = packet H m a q S X := by
      push_cast
      exact scaled_excess_eq_packet H m a q S X (hDiv X)
    simpa only [Complex.ofReal_re] using congrArg Complex.re hc
  unfold normalizedExcess
  rw [<- hScale]
  apply (div_eq_iff (ne_of_gt hM)).mpr
  exact mul_comm _ _

theorem riemannHypothesis_iff_packet_nonpos (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall p : S X, Not ((p.val : Nat) = 2))
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop) :
    RiemannHypothesis <-> Filter.Eventually
      (fun X : Nat => normalizedExcess H m a q S X <= 0) atTop := by
  rw [normalizedExcess_eq_original H m a q S hDiv]
  exact riemannHypothesis_iff_eventually_carmichaelLocalAscentExcess_nonpos
    H m a hs q S hDiv hOdd hBudget

theorem riemannHypothesis_iff_packet_power_upper (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall p : S X, Not ((p.val : Nat) = 2))
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop) :
    RiemannHypothesis <-> exists C : Real, 0 < C /\
      Filter.Eventually (fun X : Nat =>
        normalizedExcess H m a q S X <= C * (X : Real) ^ (7 / 10 : Real)) atTop := by
  rw [normalizedExcess_eq_original H m a q S hDiv]
  exact riemannHypothesis_iff_eventually_carmichaelLocalAscentExcess_power_upper
    H m a hs q S hDiv hOdd hBudget

theorem packet_unbounded_of_not_RH (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall p : S X, Not ((p.val : Nat) = 2))
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop)
    (hNotRH : Not RiemannHypothesis) (C X0 : Real) (hC : 0 < C) :
    exists n : Nat, X0 < (n : Real) /\
      C * (n : Real) ^ (7 / 10 : Real) < normalizedExcess H m a q S n := by
  rw [normalizedExcess_eq_original H m a q S hDiv]
  exact carmichaelLocalAscentExcess_unbounded_of_not_RH
    H m a hs q S hDiv hOdd hBudget hNotRH C X0 hC


theorem packet_im_eq_zero (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes) (X : Nat)
    (hDiv : forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X))))) :
    (packet H m a q S X).im = 0 := by
  rw [<- scaled_excess_eq_packet H m a q S X hDiv]
  simp

theorem packet_eq_principal_add (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes) (X : Nat)
    (hDiv : forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X))))) :
    packet H m a q S X =
      (normalization (G := Units (ZMod (q X))) (S X) : Complex) *
        characterRow H m a q X (1 : DirichletCharacter Complex (q X)) +
      (Finset.univ.erase (1 : DirichletCharacter Complex (q X))).sum
        (fun chi => (multiplicity (S X) chi : Complex) * characterRow H m a q X chi) := by
  classical
  have h := Finset.add_sum_erase
    (Finset.univ : Finset (DirichletCharacter Complex (q X)))
    (fun chi => (multiplicity (S X) chi : Complex) * characterRow H m a q X chi)
    (Finset.mem_univ (1 : DirichletCharacter Complex (q X)))
  change Finset.univ.sum
    (fun chi => (multiplicity (S X) chi : Complex) * characterRow H m a q X chi) = _
  simpa only [multiplicity_principal (S X) hDiv] using h.symm

theorem odd_packet_eq_nonquadratic (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes) (X : Nat)
    (hDiv : forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall p : S X, Not ((p.val : Nat) = 2)) :
    packet H m a q S X =
      (CarmichaelDirichletProduct.nonquadraticCharacters (q X)).sum
        (fun chi => (multiplicity (S X) chi : Complex) * characterRow H m a q X chi) := by
  classical
  unfold packet
  rw [CarmichaelDirichletProduct.nonquadraticCharacters, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro chi _
  by_cases h : chi = 1 \/
      Not (forall u : Units (ZMod (q X)), (chi (u : ZMod (q X))) ^ 2 = 1)
  . rw [ite_eq_left h]
  . have hChi : Not (chi = 1) := fun he => h (Or.inl he)
    have hSquare : forall u : Units (ZMod (q X)), (chi (u : ZMod (q X))) ^ 2 = 1 := by
      by_contra he
      exact h (Or.inr he)
    rw [ite_eq_right h, odd_multiplicity_quadratic_zero (S X) hDiv hOdd chi hChi hSquare,
      Nat.cast_zero, zero_mul]

end PrimeFactorOscillations.CarmichaelAscentSpectrum
