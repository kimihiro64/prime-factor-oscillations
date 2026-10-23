/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CarmichaelSeed
import PrimeFactorOscillations.Helpers.PrimeOrderReturnIndex

/-!
# Exact return indices on separated Carmichael seeds

The complete squarefree unit group is retained. The distinguished prime
has period divisible by four; every auxiliary period has gcd two with it.
This proves exact image-size attainment, including the prime-two label.
No external infinitude result or RH assumption is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelReturnAttainment

open PrimeOrderReturnIndex PrimeOrderReturnLaw

/-- The common factor two still permits shortening every auxiliary period. -/
theorem auxiliary_even_period (a m L : Nat)
    (ha : Dvd.dvd a L) (hm : Dvd.dvd m L)
    (hFour : Dvd.dvd 4 a) (hg : Nat.gcd a m = 2) :
    Dvd.dvd m (L / 2) := by
  have hTwo : Dvd.dvd 2 L :=
    dvd_trans (by decide : Dvd.dvd 2 4) (dvd_trans hFour ha)
  choose t ht using hFour
  have hIdentity : 2 * Nat.lcm a m = a * m := by
    simpa only [hg] using Nat.gcd_mul_lcm a m
  have hRight : a * m = 4 * t * m := by rw [ht]
  have hLcm : Nat.lcm a m = (2 * m) * t := by
    nlinarith only [hIdentity, hRight]
  have hDouble : Dvd.dvd (2 * m) L :=
    dvd_trans (Exists.intro t hLcm) (Nat.lcm_dvd ha hm)
  apply Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2)
  rw [Nat.mul_div_cancel' hTwo]
  exact hDouble

/-- A distinguished separated prime is the only period lost by shortening. -/
theorem separated_period_returnIndex (c : Nat) [NeZero c] (hSq : Squarefree c)
    (q : c.primeFactors) (hq : 5 <= (q.val : Nat))
    (hFour : Dvd.dvd 4 ((q.val : Nat) - 1))
    (hMinus : forall p : c.primeFactors, Not (p = q) ->
      Dvd.dvd ((q.val : Nat) - 1) ((p.val : Nat) + 1))
    (l : Nat.Primes) (hlQ : Dvd.dvd (l : Nat) ((q.val : Nat) - 1)) :
    returnIndex (G := Units (ZMod c)) (Monoid.exponent (Units (ZMod c))) (l : Nat) =
      (l : Nat) := by
  classical
  let L := Monoid.exponent (Units (ZMod c))
  have hPos : 0 < L := Nat.pos_of_ne_zero (Monoid.exponent_ne_zero_of_finite (G := Units (ZMod c)))
  have hPeriods : forall p : c.primeFactors, Dvd.dvd ((p.val : Nat) - 1) L := by
    intro p
    dsimp [L]
    rw [squarefree_unit_exponent c hSq]
    exact Finset.dvd_lcm (Finset.mem_univ p)
  have hlL : Dvd.dvd (l : Nat) L := dvd_trans hlQ (hPeriods q)
  have hOther : forall p : c.primeFactors, Not (p = q) ->
      Dvd.dvd ((p.val : Nat) - 1) (L / (l : Nat)) := by
    intro p hpq
    have hp := (Nat.mem_primeFactors.mp p.property).1
    by_cases hlTwo : (l : Nat) = 2
    { rw [hlTwo]
      exact auxiliary_even_period _ _ L (hPeriods q) (hPeriods p) hFour
        (CarmichaelSeed.shifted_period_gcd_eq_two _ _ hq hFour
          (Nat.le_of_lt hp.one_lt) (hMinus p hpq)) }
    { have hNot := CarmichaelSeed.odd_label_absent_from_seed_factor _ _ _ hq hFour
        (Nat.le_of_lt hp.one_lt) (hMinus p hpq) l.property hlTwo hlQ
      have hCoprime : Nat.Coprime ((p.val : Nat) - 1) (l : Nat) :=
        (l.property.coprime_iff_not_dvd.mpr hNot).symm
      apply hCoprime.dvd_of_dvd_mul_right
      rw [Nat.div_mul_cancel hlL]
      exact hPeriods p }
  have hLost : Not (Dvd.dvd ((q.val : Nat) - 1) (L / (l : Nat))) := by
    intro hQ
    have hLcmDiv : Dvd.dvd
        (Finset.univ.lcm (fun p : c.primeFactors => (p.val : Nat) - 1))
        (L / (l : Nat)) := by
      apply Finset.lcm_dvd
      intro p _
      by_cases hpq : p = q
      { rw [hpq]
        exact hQ }
      { exact hOther p hpq }
    have hDiv : Dvd.dvd L (L / (l : Nat)) := by
      simpa only [<- squarefree_unit_exponent c hSq] using hLcmDiv
    have hQuotPos : 0 < L / (l : Nat) :=
      Nat.div_pos (Nat.le_of_dvd hPos hlL) l.property.pos
    have hLe := Nat.le_of_dvd hQuotPos hDiv
    exact (Nat.not_le_of_gt (Nat.div_lt_self hPos l.property.one_lt)) hLe
  change returnIndex (G := Units (ZMod c)) L (l : Nat) = (l : Nat)
  rw [squarefree_unit_returnIndex c hSq]
  calc
    Finset.univ.prod (fun p : c.primeFactors =>
        ((p.val : Nat) - 1) / Nat.gcd ((p.val : Nat) - 1) (L / (l : Nat))) =
        ((q.val : Nat) - 1) / Nat.gcd ((q.val : Nat) - 1) (L / (l : Nat)) := by
      apply Finset.prod_eq_single q
      { intro p _ hpq
        have hp := (Nat.mem_primeFactors.mp p.property).1
        rw [Nat.gcd_eq_left (hOther p hpq),
          Nat.div_self (Nat.sub_pos_of_lt hp.one_lt)] }
      { intro h
        exact False.elim (h (Finset.mem_univ q)) }
    _ = (l : Nat) := by
      rw [local_period_ratio _ L l (by omega) (hPeriods q) hlL, ite_eq_right hLost]

/-- Every binary return pattern attains the one-coordinate prime law. -/
theorem separated_period_return_law (c : Nat) [NeZero c] (hSq : Squarefree c)
    (q : c.primeFactors) (hq : 5 <= (q.val : Nat))
    (hFour : Dvd.dvd 4 ((q.val : Nat) - 1))
    (hMinus : forall p : c.primeFactors, Not (p = q) ->
      Dvd.dvd ((q.val : Nat) - 1) ((p.val : Nat) + 1))
    (S : Finset Nat.Primes)
    (hLabels : forall l : S, Dvd.dvd (l.val : Nat) ((q.val : Nat) - 1))
    (bits : S -> Bool) :
    returnPatternProbability (G := Units (ZMod c))
        (Monoid.exponent (Units (ZMod c))) S bits =
      Finset.univ.prod (fun l : S => if bits l then 1 / ((l.val : Nat) : Real)
        else 1 - 1 / ((l.val : Nat) : Real)) := by
  classical
  have hDiv : forall l : S,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod c))) := by
    intro l
    apply dvd_trans (hLabels l)
    rw [squarefree_unit_exponent c hSq]
    exact Finset.dvd_lcm (Finset.mem_univ q)
  rw [modular_unit_returnPatternProbability c S hDiv bits]
  apply Finset.prod_congr rfl
  intro l _
  rw [separated_period_returnIndex c hSq q hq hFour hMinus l.val (hLabels l)]

/-- The complete negative-one seed is both Korselt-certified and an exact
native full-unit probability attainer, including the even prime label. -/
theorem negative_one_seed_return_law (q B : Nat) [NeZero (q * B)]
    (hqPrime : Nat.Prime q) (hq : 5 <= q)
    (hFour : Dvd.dvd 4 (q - 1)) (hB : 1 < B) (hSq : Squarefree B)
    (hCoprime : Nat.Coprime q B) (hOdd : Nat.Coprime 2 B)
    (hEven : Even B.primeFactors.card)
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (q - 1) (p + 1))
    (hHalf : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd ((p - 1) / 2) (q * B - 1)) :
    And (CarmichaelSeed.KorseltCertificate (q * B))
      (forall (S : Finset Nat.Primes)
        (hLabels : forall l : S, Dvd.dvd (l.val : Nat) (q - 1))
        (bits : S -> Bool),
        returnPatternProbability (G := Units (ZMod (q * B)))
            (Monoid.exponent (Units (ZMod (q * B)))) S bits =
          Finset.univ.prod (fun l : S => if bits l then 1 / ((l.val : Nat) : Real)
            else 1 - 1 / ((l.val : Nat) : Real))) := by
  classical
  have hCert := CarmichaelSeed.negative_one_seed_korselt q B hqPrime hq
    hFour hB hSq hCoprime hOdd hEven hFactors hHalf
  apply And.intro hCert
  intro S hLabels bits
  let qCoord : (q * B).primeFactors := Subtype.mk q
    (Nat.mem_primeFactors.mpr
      (And.intro hqPrime (And.intro (dvd_mul_right q B) (NeZero.ne (q * B)))))
  have hMinus : forall p : (q * B).primeFactors, Not (p = qCoord) ->
      Dvd.dvd ((qCoord.val : Nat) - 1) ((p.val : Nat) + 1) := by
    intro p hpq
    have hp := Nat.mem_primeFactors.mp p.property
    have hpB : Dvd.dvd (p.val : Nat) B := by
      rcases hp.1.dvd_mul.mp hp.2.1 with hpQ | hpB
      { rcases hqPrime.eq_one_or_self_of_dvd (p.val : Nat) hpQ with hOne | hEq
        { have hLarge := hp.1.one_lt
          omega }
        { exact False.elim (hpq (Subtype.ext hEq)) } }
      { exact hpB }
    exact hFactors (p.val : Nat) hp.1 hpB
  exact separated_period_return_law (q * B) hCert.2.2.1 qCoord hq hFour
    hMinus S hLabels bits

end PrimeFactorOscillations.CarmichaelReturnAttainment
