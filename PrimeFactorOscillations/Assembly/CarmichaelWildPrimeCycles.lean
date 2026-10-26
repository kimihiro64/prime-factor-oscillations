/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelWildAverages
import PrimeFactorOscillations.Assembly.PrimeConstellationRH

/-!
# Original odd-wild kernel balance on full labelled prime cycles

The actual p vertices are retained. The canonical RH comparison and the
independent recurrence premise are unchanged; every depth and unit phase
has exact native weight sum p on each sufficiently large selected cycle.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWildPrimeCycles

open CarmichaelPrimePacket CarmichaelCorrelation CarmichaelWildAverages

local instance primeLabelNeZero (l : Nat.Primes) : NeZero (l : Nat) :=
  NeZero.mk l.property.ne_zero

def wildProgressionShape (l : Nat.Primes) (t : Nat) : Fin (l : Nat) -> Nat :=
  fun i => i.val * (l : Nat) * t

def nativeCycleBalance (l : Nat.Primes) (t n : Nat) : Prop :=
  exists hn : Nat.Coprime n (l : Nat),
    forall a : Nat, forall c : Units (ZMod ((l : Nat) ^ (a + 2))),
      Finset.univ.sum (fun i : Fin (l : Nat) =>
        kernel (weight ((l : Nat) ^ (a + 2)) l)
          (c * nativePositionUnit l a n t i.val hn)) = ((l : Nat) : Real)

theorem wildProgressionShape_injective (l : Nat.Primes) (t : Nat)
    (ht : Nat.Coprime t (l : Nat)) :
    Function.Injective (wildProgressionShape l t) := by
  have ht0 : Not (t = 0) := by
    intro h
    subst t
    have hOne : (l : Nat) = 1 := by simpa using ht.symm
    exact l.property.ne_one hOne
  have hPos : 0 < (l : Nat) * t := Nat.mul_pos l.property.pos (Nat.pos_of_ne_zero ht0)
  intro i j h
  apply Fin.ext
  apply Nat.eq_of_mul_eq_mul_right hPos
  simpa only [wildProgressionShape, mul_assoc] using h

theorem wildProgressionShape_bound (l : Nat.Primes) (t : Nat) (i : Fin (l : Nat)) :
    wildProgressionShape l t i <= ((l : Nat) - 1) * (l : Nat) * t := by
  have hi : i.val <= (l : Nat) - 1 := by have h := i.isLt; omega
  exact Nat.mul_le_mul_right t (Nat.mul_le_mul_right (l : Nat) hi)

theorem actual_prime_cycle_balanced (l : Nat.Primes) (hTwo : Not ((l : Nat) = 2))
    (t : Nat) (ht : Nat.Coprime t (l : Nat))
    (sigma : Equiv.Perm Nat.Primes) (q : Nat) (hq : (l : Nat) + 1 <= q)
    (hc : PrimeShapeCycleAt (wildProgressionShape l t) sigma q) :
    nativeCycleBalance l t q := by
  have hPrime : Nat.Prime q := by
    simpa [wildProgressionShape] using hc.prime_offsets (0 : Fin (l : Nat))
  have hNot : Not (Dvd.dvd q (l : Nat)) := by
    intro h
    have hLe := Nat.le_of_dvd l.property.pos h
    omega
  have hn : Nat.Coprime q (l : Nat) := hPrime.coprime_iff_not_dvd.mpr hNot
  refine Exists.intro hn ?_
  intro a c
  exact native_progression_sum l a hTwo q t hn ht c

/-- RH does not supply recurrence of this fixed full prime shape. -/
theorem recurrent_wild_prime_progression_and_rh_iff_balanced_transport
    (l : Nat.Primes) (hTwo : Not ((l : Nat) = 2))
    (t : Nat) (ht : Nat.Coprime t (l : Nat)) (alpha : Real) (ha : 0 < alpha) :
    (RiemannHypothesis /\ RecurrentPrimeShape (wildProgressionShape l t)) <->
      (exists sigma : Equiv.Perm Nat.Primes,
        exists hdispl : forall p : Nat.Primes,
          abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <=
            (((l : Nat) - 1) * (l : Nat) * t : Nat),
        (forall N : Nat, exists q : Nat, N <= q /\
          PrimeShapeCycleAt (wildProgressionShape l t) sigma q /\ nativeCycleBalance l t q) /\
        Filter.Eventually (fun N : Nat =>
          let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
          (boundedPrimePermutationLaw sigma (((l : Nat) - 1) * (l : Nat) * t) hdispl).densityRatio
            N r <
              canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N))
          Filter.atTop) := by
  have hOriginal := recurrent_prime_shape_and_rh_iff_canonical_cycle_transport
    (wildProgressionShape l t) (wildProgressionShape_injective l t ht)
    (((l : Nat) - 1) * (l : Nat) * t) (wildProgressionShape_bound l t) alpha ha
  constructor
  . intro hBoth
    choose sigma hdispl hCycles hSign using hOriginal.mp hBoth
    refine Exists.intro sigma (Exists.intro hdispl (And.intro ?_ hSign))
    intro N
    choose q hq hc using hCycles (max N ((l : Nat) + 1))
    refine Exists.intro q (And.intro ((le_max_left N ((l : Nat) + 1)).trans hq)
      (And.intro hc ?_))
    exact actual_prime_cycle_balanced l hTwo t ht sigma q
      ((le_max_right N ((l : Nat) + 1)).trans hq) hc
  . intro hBalanced
    choose sigma hdispl hCycles hSign using hBalanced
    apply hOriginal.mpr
    refine Exists.intro sigma (Exists.intro hdispl (And.intro ?_ hSign))
    intro N
    choose q hq hc hBalance using hCycles N
    exact Exists.intro q (And.intro hq hc)

end PrimeFactorOscillations.CarmichaelWildPrimeCycles
