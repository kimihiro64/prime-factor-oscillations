/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.GCD.BigOperators
import PrimeFactorOscillations.Helpers.CarmichaelReturnAttainment

/-!
# Native return profiles under separated squarefree extensions

The new canonical exponent is a coprime multiple of the original one.
Old prime-order image indices are therefore preserved; auxiliary factors
have an explicitly isolated contribution at the exceptional even label.
No external seed existence theorem is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelProfileExtension

open PrimeOrderReturnLaw PrimeOrderReturnIndex CarmichaelSeed CarmichaelReturnAttainment

theorem gcd_mul_coprime_right (a N K : Nat) (h : Nat.Coprime a K) :
    Nat.gcd a (N * K) = Nat.gcd a N := by
  apply Nat.dvd_antisymm
  { apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    have hCoprime := Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left a (N * K)) h
    exact hCoprime.dvd_of_dvd_mul_right (Nat.gcd_dvd_right a (N * K)) }
  { exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
      (dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) K) }

/-- Coprime enlargement does not change any original shortened gcd. -/
theorem shortened_gcd_coprime_multiplier (a L K l : Nat)
    (hCoprime : Nat.Coprime a K) (hDiv : Dvd.dvd l L) :
    Nat.gcd a ((L * K) / l) = Nat.gcd a (L / l) := by
  rw [Nat.mul_comm L K, Nat.mul_div_assoc K hDiv, Nat.mul_comm K (L / l)]
  exact gcd_mul_coprime_right a (L / l) K hCoprime

/-- Negative-one auxiliary factors have odd half-periods coprime to L. -/
theorem auxiliary_half_period (p L : Nat) (hp : 1 <= p)
    (hMinus : Dvd.dvd (4 * L) (p + 1)) :
    And (Dvd.dvd 2 (p - 1))
      (And (Odd ((p - 1) / 2)) (Nat.Coprime L ((p - 1) / 2))) := by
  have hFour : Dvd.dvd 4 (p + 1) := dvd_trans (dvd_mul_right 4 L) hMinus
  have hMod : p % 4 = 3 := by
    have h := Nat.mod_eq_zero_of_dvd hFour
    omega
  have hTwo : Dvd.dvd 2 (p - 1) := Nat.dvd_of_mod_eq_zero (by omega)
  refine And.intro hTwo (And.intro (Nat.odd_iff.mpr (by omega)) ?_)
  have hLPlus : Dvd.dvd L ((p - 1) / 2 + 1) := by
    choose t ht using hMinus
    have hEq : p + 1 = 2 * (2 * L * t) := by nlinarith only [ht]
    have hHalf : (p - 1) / 2 + 1 = 2 * L * t := by omega
    refine Exists.intro (2 * t) ?_
    calc
      (p - 1) / 2 + 1 = 2 * L * t := hHalf
      _ = L * (2 * t) := by ring
  change Nat.gcd L ((p - 1) / 2) = 1
  apply Nat.dvd_one.mp
  have h := Nat.dvd_sub
    (dvd_trans (Nat.gcd_dvd_left L ((p - 1) / 2)) hLPlus)
    (Nat.gcd_dvd_right L ((p - 1) / 2))
  have hEq : (p - 1) / 2 + 1 - (p - 1) / 2 = 1 := by omega
  rwa [hEq] at h

theorem prime_period_dvd_exponent (c : Nat) [NeZero c] (hSq : Squarefree c)
    (p : Nat) (hp : Nat.Prime p) (hpDiv : Dvd.dvd p c) :
    Dvd.dvd (p - 1) (Monoid.exponent (Units (ZMod c))) := by
  classical
  rw [squarefree_unit_exponent c hSq]
  let pCoord : c.primeFactors :=
    Subtype.mk p (Nat.mem_primeFactors.mpr (And.intro hp (And.intro hpDiv (NeZero.ne c))))
  exact Finset.dvd_lcm (Finset.mem_univ pCoord)

theorem exponent_dvd_of_prime_periods (c : Nat) [NeZero c] (hSq : Squarefree c)
    (N : Nat)
    (hPeriods : forall p : Nat, Nat.Prime p -> Dvd.dvd p c -> Dvd.dvd (p - 1) N) :
    Dvd.dvd (Monoid.exponent (Units (ZMod c))) N := by
  classical
  rw [squarefree_unit_exponent c hSq]
  apply Finset.lcm_dvd
  intro p _
  have hp := Nat.mem_primeFactors.mp p.property
  exact hPeriods (p.val : Nat) hp.1 hp.2.1

def halfPeriodProduct (B : Nat) : Nat :=
  Finset.univ.prod (fun p : B.primeFactors => ((p.val : Nat) - 1) / 2)

theorem half_period_dvd_product (B p : Nat) (hp : Nat.Prime p)
    (hpDiv : Dvd.dvd p B) (hB : Not (B = 0)) :
    Dvd.dvd ((p - 1) / 2) (halfPeriodProduct B) := by
  classical
  let pCoord : B.primeFactors :=
    Subtype.mk p (Nat.mem_primeFactors.mpr (And.intro hp (And.intro hpDiv hB)))
  exact Finset.dvd_prod_of_mem
    (fun r : B.primeFactors => ((r.val : Nat) - 1) / 2) (Finset.mem_univ pCoord)

theorem half_period_product_coprime (L B : Nat)
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * L) (p + 1)) :
    Nat.Coprime L (halfPeriodProduct B) := by
  classical
  apply Nat.Coprime.prod_right
  intro p _
  have hp := Nat.mem_primeFactors.mp p.property
  exact (auxiliary_half_period (p.val : Nat) L
    (Nat.le_of_lt hp.1.one_lt) (hFactors _ hp.1 hp.2.1)).2.2

/-- The actual new canonical exponent has only a coprime multiplier. -/
theorem exponent_coprime_multiplier (m B : Nat) [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1)) :
    exists K : Nat, And (Nat.Coprime K (Monoid.exponent (Units (ZMod m))))
      (Monoid.exponent (Units (ZMod (m * B))) =
        Monoid.exponent (Units (ZMod m)) * K) := by
  classical
  let L := Monoid.exponent (Units (ZMod m))
  let E := Monoid.exponent (Units (ZMod (m * B)))
  let P := halfPeriodProduct B
  have hSqNew : Squarefree (m * B) := (Nat.squarefree_mul hCoprime).mpr (And.intro hSqM hSqB)
  have hPos : 0 < L := Nat.pos_of_ne_zero (Monoid.exponent_ne_zero_of_finite (G := Units (ZMod m)))
  have hLE : Dvd.dvd L E := by
    apply exponent_dvd_of_prime_periods m hSqM E
    intro p hp hpM
    exact prime_period_dvd_exponent (m * B) hSqNew p hp
      (dvd_trans hpM (dvd_mul_right m B))
  have hEW : Dvd.dvd E (L * P) := by
    apply exponent_dvd_of_prime_periods (m * B) hSqNew (L * P)
    intro p hp hpNew
    cases hp.dvd_mul.mp hpNew with
    | inl hpM =>
      exact dvd_mul_of_dvd_left (prime_period_dvd_exponent m hSqM p hp hpM) P
    | inr hpB =>
      have hAux := auxiliary_half_period p L (Nat.le_of_lt hp.one_lt) (hFactors p hp hpB)
      have hProd := Nat.mul_dvd_mul hTwo
        (half_period_dvd_product B p hp hpB (NeZero.ne B))
      rwa [Nat.mul_div_cancel' hAux.1] at hProd
  have hCop : Nat.Coprime L P := half_period_product_coprime L B hFactors
  choose K hK using hLE
  have hKP : Dvd.dvd K P := by
    apply Nat.dvd_of_mul_dvd_mul_left hPos
    rwa [hK] at hEW
  exact Exists.intro K (And.intro (Nat.Coprime.of_dvd_left hKP hCop.symm) hK)

theorem auxiliary_period_gcd_two (p L : Nat) (hp : 1 <= p)
    (hTwo : Dvd.dvd 2 L) (hMinus : Dvd.dvd (4 * L) (p + 1)) :
    Nat.gcd L (p - 1) = 2 := by
  have hMinusL : Dvd.dvd L (p + 1) := dvd_trans (dvd_mul_left L 4) hMinus
  apply Nat.dvd_antisymm
  { have h := Nat.dvd_sub
      (dvd_trans (Nat.gcd_dvd_left L (p - 1)) hMinusL)
      (Nat.gcd_dvd_right L (p - 1))
    have hEq : p + 1 - (p - 1) = 2 := by omega
    rwa [hEq] at h }
  { exact Nat.dvd_gcd hTwo (auxiliary_half_period p L hp hMinus).1 }

/-- At a singly-even original period, the shortened new period stays odd. -/
theorem enlarged_half_odd (L K : Nat) (hTwo : Dvd.dvd 2 L)
    (hFour : Not (Dvd.dvd 4 L)) (hCoprime : Nat.Coprime K L) :
    Odd ((L * K) / 2) := by
  have hLOdd : Odd (L / 2) := by
    apply Nat.odd_iff.mpr
    have hEven := Nat.mod_eq_zero_of_dvd hTwo
    have hNot : Not (L % 4 = 0) := by
      intro h
      exact hFour (Nat.dvd_of_mod_eq_zero h)
    omega
  have hKOdd : Odd K :=
    Nat.coprime_two_left.mp (Nat.Coprime.of_dvd_left hTwo hCoprime.symm)
  rw [Nat.mul_comm L K, Nat.mul_div_assoc K hTwo]
  exact hKOdd.mul hLOdd

/-- An added cyclic coordinate contributes only at the exceptional prime two. -/
theorem auxiliary_image_factor (p L E K : Nat) (hp : Nat.Prime p)
    (hTwo : Dvd.dvd 2 L) (hLE : Dvd.dvd L E)
    (hE : E = L * K) (hCoprime : Nat.Coprime K L)
    (hMinus : Dvd.dvd (4 * L) (p + 1))
    (hpE : Dvd.dvd (p - 1) E) (l : Nat.Primes) (hlL : Dvd.dvd (l : Nat) L) :
    (p - 1) / Nat.gcd (p - 1) (E / (l : Nat)) =
      if And ((l : Nat) = 2) (Not (Dvd.dvd 4 L)) then 2 else 1 := by
  have hpPos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hGcd := auxiliary_period_gcd_two p L (Nat.le_of_lt hp.one_lt) hTwo hMinus
  have hlE : Dvd.dvd (l : Nat) E := dvd_trans hlL hLE
  by_cases hLabel : (l : Nat) = 2
  { by_cases hFour : Dvd.dvd 4 L
    { have hSurvive : Dvd.dvd (p - 1) (E / 2) :=
        auxiliary_even_period L (p - 1) E hLE hpE hFour hGcd
      rw [hLabel, Nat.gcd_eq_left hSurvive, Nat.div_self hpPos]
      simp only [hFour, not_true_eq_false, and_false, ite_false] }
    { have hOdd : Odd (E / 2) := by
        rw [hE]
        exact enlarged_half_odd L K hTwo hFour hCoprime
      have hLost : Not (Dvd.dvd (p - 1) (E / 2)) := by
        intro hDiv
        have hEven := Nat.mod_eq_zero_of_dvd
          (dvd_trans (auxiliary_half_period p L (Nat.le_of_lt hp.one_lt) hMinus).1 hDiv)
        have hOddMod := Nat.odd_iff.mp hOdd
        omega
      rw [local_period_ratio (p - 1) E l hpPos hpE hlE, hLabel, ite_eq_right hLost]
      simp only [hFour, not_false_eq_true, and_self, ite_true] } }
  { have hNot : Not (Dvd.dvd (l : Nat) (p - 1)) := by
      intro hDiv
      have h := Nat.dvd_gcd hlL hDiv
      rw [hGcd] at h
      have hLe := Nat.le_of_dvd (by decide : 0 < 2) h
      have hLower := l.property.two_le
      exact hLabel (by omega)
    have hCop : Nat.Coprime (p - 1) (l : Nat) :=
      (l.property.coprime_iff_not_dvd.mpr hNot).symm
    have hSurvive : Dvd.dvd (p - 1) (E / (l : Nat)) := by
      apply hCop.dvd_of_dvd_mul_right
      rw [Nat.div_mul_cancel hlE]
      exact hpE
    rw [Nat.gcd_eq_left hSurvive, Nat.div_self hpPos]
    simp only [hLabel, false_and, ite_false] }

theorem squarefree_index_finset (c : Nat) [NeZero c] (hSq : Squarefree c) (L l : Nat) :
    returnIndex (G := Units (ZMod c)) L l =
      c.primeFactors.prod (fun p : Nat => (p - 1) / Nat.gcd (p - 1) (L / l)) := by
  classical
  rw [squarefree_unit_returnIndex c hSq]
  exact Finset.prod_coe_sort c.primeFactors
    (fun p : Nat => (p - 1) / Nat.gcd (p - 1) (L / l))

/-- Exact full old-packet image formula, including the exceptional even growth. -/
theorem extension_returnIndex (m B : Nat) [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (l : Nat.Primes) (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod m)))) :
    returnIndex (G := Units (ZMod (m * B)))
        (Monoid.exponent (Units (ZMod (m * B)))) (l : Nat) =
      returnIndex (G := Units (ZMod m)) (Monoid.exponent (Units (ZMod m))) (l : Nat) *
        (if And ((l : Nat) = 2) (Not (Dvd.dvd 4 (Monoid.exponent (Units (ZMod m)))))
         then 2 ^ B.primeFactors.card else 1) := by
  classical
  let L := Monoid.exponent (Units (ZMod m))
  let E := Monoid.exponent (Units (ZMod (m * B)))
  have hSqNew : Squarefree (m * B) := (Nat.squarefree_mul hCoprime).mpr (And.intro hSqM hSqB)
  choose K hK using exponent_coprime_multiplier m B hSqM hSqB hCoprime hTwo hFactors
  have hLE : Dvd.dvd L E := Exists.intro K hK.2
  have hOld : forall p : Nat, Membership.mem m.primeFactors p ->
      (p - 1) / Nat.gcd (p - 1) (E / (l : Nat)) =
        (p - 1) / Nat.gcd (p - 1) (L / (l : Nat)) := by
    intro p hpMem
    have hp := Nat.mem_primeFactors.mp hpMem
    have hPeriod := prime_period_dvd_exponent m hSqM p hp.1 hp.2.1
    have hCop : Nat.Coprime (p - 1) K := Nat.Coprime.of_dvd_left hPeriod hK.1.symm
    change (p - 1) / Nat.gcd (p - 1) (E / (l : Nat)) = _
    rw [show E = L * K from hK.2, shortened_gcd_coprime_multiplier _ L K _ hCop hl]
  have hAux : forall p : Nat, Membership.mem B.primeFactors p ->
      (p - 1) / Nat.gcd (p - 1) (E / (l : Nat)) =
        if And ((l : Nat) = 2) (Not (Dvd.dvd 4 L)) then 2 else 1 := by
    intro p hpMem
    have hp := Nat.mem_primeFactors.mp hpMem
    exact auxiliary_image_factor p L E K hp.1 hTwo hLE hK.2 hK.1
      (hFactors p hp.1 hp.2.1)
      (prime_period_dvd_exponent (m * B) hSqNew p hp.1
        (dvd_trans hp.2.1 (dvd_mul_left B m))) l hl
  have hDisjoint : Disjoint m.primeFactors B.primeFactors :=
    (Nat.disjoint_primeFactors (NeZero.ne m) (NeZero.ne B)).mpr hCoprime
  rw [squarefree_index_finset (m * B) hSqNew, hCoprime.primeFactors_mul,
    Finset.prod_union hDisjoint, squarefree_index_finset m hSqM]
  change m.primeFactors.prod (fun p : Nat => (p - 1) / Nat.gcd (p - 1) (E / (l : Nat))) *
      B.primeFactors.prod (fun p : Nat => (p - 1) / Nat.gcd (p - 1) (E / (l : Nat))) = _
  rw [Finset.prod_congr rfl hOld, Finset.prod_congr rfl hAux, Finset.prod_const]
  split_ifs <;> simp [L]

/-- Every joint pattern, with the exact even-label inflation retained. -/
theorem extension_returnPatternProbability (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod m))))
    (bits : S -> Bool) :
    returnPatternProbability (G := Units (ZMod (m * B)))
        (Monoid.exponent (Units (ZMod (m * B)))) S bits =
      Finset.univ.prod (fun l : S =>
        let d := returnIndex (G := Units (ZMod m))
          (Monoid.exponent (Units (ZMod m))) (l.val : Nat) *
          (if And ((l.val : Nat) = 2) (Not (Dvd.dvd 4 (Monoid.exponent (Units (ZMod m)))))
           then 2 ^ B.primeFactors.card else 1)
        if bits l then 1 / (d : Real) else 1 - 1 / (d : Real)) := by
  classical
  choose K hK using exponent_coprime_multiplier m B hSqM hSqB hCoprime hTwo hFactors
  have hDivNew : forall l : S,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (m * B)))) := by
    intro l
    exact dvd_trans (hDiv l) (Exists.intro K hK.2)
  rw [modular_unit_returnPatternProbability (m * B) S hDivNew bits]
  apply Finset.prod_congr rfl
  intro l _
  rw [extension_returnIndex m B hSqM hSqB hCoprime hTwo hFactors l.val (hDiv l)]

/-- All original labels have exactly the same native law when four divides L. -/
theorem extension_preserves_return_patterns (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hFour : Dvd.dvd 4 (Monoid.exponent (Units (ZMod m))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod m))))
    (bits : S -> Bool) :
    returnPatternProbability (G := Units (ZMod (m * B)))
        (Monoid.exponent (Units (ZMod (m * B)))) S bits =
      returnPatternProbability (G := Units (ZMod m))
        (Monoid.exponent (Units (ZMod m))) S bits := by
  have hTwo := dvd_trans (by decide : Dvd.dvd 2 4) hFour
  rw [extension_returnPatternProbability m B hSqM hSqB hCoprime hTwo hFactors S hDiv bits,
    modular_unit_returnPatternProbability m S hDiv bits]
  simp only [hFour, not_true_eq_false, and_false, ite_false, mul_one]

/-- Complete finite Carmichael consumer; m need not be a distinguished prime. -/
theorem negative_one_extension_korselt (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hM : KorseltCertificate m)
    (hL : 4 <= Monoid.exponent (Units (ZMod m)))
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hB : 1 < B) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hEven : Even B.primeFactors.card)
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (hHalf : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd ((p - 1) / 2) (m * B - 1)) :
    KorseltCertificate (m * B) := by
  classical
  let L := Monoid.exponent (Units (ZMod m))
  letI : NeZero L := NeZero.mk (Monoid.exponent_ne_zero_of_finite (G := Units (ZMod m)))
  have hLarge : 2 < m * B := by
    have h := Nat.mul_le_mul (show 3 <= m from by have hm := hM.1; omega)
      (show 2 <= B by omega)
    omega
  have hComposite : Not (Nat.Prime (m * B)) := by
    intro hPrime
    have hChoices := hPrime.eq_one_or_self_of_dvd m (dvd_mul_right m B)
    have hStrict : m < m * B := by
      simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hB (by have hm := hM.1; omega)
    cases hChoices with
    | inl hOne => have hm := hM.1; omega
    | inr hEq => omega
  have hSquarefree : Squarefree (m * B) :=
    (Nat.squarefree_mul hCoprime).mpr (And.intro hM.2.2.1 hSqB)
  have hOldPeriod : Dvd.dvd L (m - 1) :=
    exponent_dvd_of_prime_periods m hM.2.2.1 (m - 1) hM.2.2.2
  have hMOne : (m : ZMod L) = 1 := by
    have hz := (CharP.cast_eq_zero_iff (ZMod L) L (m - 1)).mpr hOldPeriod
    rw [Nat.cast_sub (by have hm := hM.1; omega), Nat.cast_one] at hz
    exact sub_eq_zero.mp hz
  have hBOne : (B : ZMod L) = 1 := by
    have hFactorsL : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
        Dvd.dvd L (p + 1) := by
      intro p hp hpB
      exact dvd_trans (dvd_mul_left L 4) (hFactors p hp hpB)
    have h := seed_product_returns_one (L + 1) B (by dsimp [L]; omega) hSqB hEven (by
      simpa only [Nat.add_sub_cancel] using hFactorsL)
    simpa only [Nat.add_sub_cancel] using h
  have hNewOne : ((m * B : Nat) : ZMod L) = 1 := by
    rw [Nat.cast_mul, hMOne, hBOne, mul_one]
  have hNewPeriod : Dvd.dvd L (m * B - 1) := by
    apply (CharP.cast_eq_zero_iff (ZMod L) L (m * B - 1)).mp
    rw [Nat.cast_sub (show 1 <= m * B by omega), Nat.cast_one, hNewOne, sub_self]
  have hTwoNew : Dvd.dvd 2 (m * B - 1) := dvd_trans hTwo hNewPeriod
  refine And.intro hLarge (And.intro hComposite (And.intro hSquarefree ?_))
  intro p hp hpDiv
  cases hp.dvd_mul.mp hpDiv with
  | inl hpM =>
    exact dvd_trans (prime_period_dvd_exponent m hM.2.2.1 p hp hpM) hNewPeriod
  | inr hpB =>
    have hAux := auxiliary_half_period p L (Nat.le_of_lt hp.one_lt) (hFactors p hp hpB)
    have hProd := (Nat.coprime_two_left.mpr hAux.2.1).mul_dvd_of_dvd_of_dvd
      hTwoNew (hHalf p hp hpB)
    rwa [Nat.mul_div_cancel' hAux.1] at hProd

/-- A full Carmichael extension with exact preservation of every old packet. -/
theorem carmichael_profile_extension (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hM : KorseltCertificate m)
    (hFour : Dvd.dvd 4 (Monoid.exponent (Units (ZMod m))))
    (hB : 1 < B) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hEven : Even B.primeFactors.card)
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (hHalf : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd ((p - 1) / 2) (m * B - 1)) :
    And (KorseltCertificate (m * B))
      (forall (S : Finset Nat.Primes)
        (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod m))))
        (bits : S -> Bool),
        returnPatternProbability (G := Units (ZMod (m * B)))
            (Monoid.exponent (Units (ZMod (m * B)))) S bits =
          returnPatternProbability (G := Units (ZMod m))
            (Monoid.exponent (Units (ZMod m))) S bits) := by
  have hTwo := dvd_trans (by decide : Dvd.dvd 2 4) hFour
  have hL : 4 <= Monoid.exponent (Units (ZMod m)) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Monoid.exponent_ne_zero_of_finite (G := Units (ZMod m)))) hFour
  refine And.intro
    (negative_one_extension_korselt m B hM hL hTwo hB hSqB hCoprime hEven hFactors hHalf) ?_
  intro S hDiv bits
  exact extension_preserves_return_patterns m B hM.2.2.1 hSqB hCoprime hFour hFactors S hDiv bits

end PrimeFactorOscillations.CarmichaelProfileExtension
