/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Carmichael seeds with a separated prime-order coordinate

These are the finite arithmetic consumers of Larsen's negative-one seed
construction. They retain the even prime: auxiliary factors are 3 modulo
4, while the distinguished prime is 1 modulo 4. A Korselt certificate is
proved from the seed assumptions. No infinitude theorem, unit-group
probability law, or RH equivalence is asserted in this module.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.CarmichaelSeed

/-- The complete finite arithmetic content of Korselt's criterion. -/
def KorseltCertificate (n : Nat) : Prop :=
  And (2 < n) (And (Not (Nat.Prime n))
    (And (Squarefree n) (forall p : Nat, Nat.Prime p ->
      Dvd.dvd p n -> Dvd.dvd (p - 1) (n - 1))))

/-- Negative-one seed factors share exactly the unavoidable factor two. -/
theorem shifted_period_gcd_eq_two (q p : Nat) (_hq : 5 <= q)
    (hFour : Dvd.dvd 4 (q - 1)) (hp : 1 <= p)
    (hMinus : Dvd.dvd (q - 1) (p + 1)) :
    Nat.gcd (q - 1) (p - 1) = 2 := by
  have hTwoQ : Dvd.dvd 2 (q - 1) := dvd_trans (by decide : Dvd.dvd 2 4) hFour
  have hTwoPlus : Dvd.dvd 2 (p + 1) := dvd_trans hTwoQ hMinus
  have hTwoP : Dvd.dvd 2 (p - 1) := by
    have h := Nat.dvd_sub hTwoPlus (by decide : Dvd.dvd 2 2)
    have heq : p + 1 - 2 = p - 1 := by omega
    rwa [heq] at h
  apply Nat.dvd_antisymm
  { have h1 := dvd_trans (Nat.gcd_dvd_left (q - 1) (p - 1)) hMinus
    have h2 := Nat.gcd_dvd_right (q - 1) (p - 1)
    have h := Nat.dvd_sub h1 h2
    have heq : p + 1 - (p - 1) = 2 := by omega
    rwa [heq] at h }
  { exact Nat.dvd_gcd hTwoQ hTwoP }

theorem seed_factor_mod_four (q p : Nat) (hFour : Dvd.dvd 4 (q - 1))
    (hMinus : Dvd.dvd (q - 1) (p + 1)) : p % 4 = 3 := by
  have h := dvd_trans hFour hMinus
  have hm := Nat.mod_eq_zero_of_dvd h
  omega

/-- No odd prime order in the distinguished coordinate occurs elsewhere. -/
theorem odd_label_absent_from_seed_factor (q p l : Nat) (hq : 5 <= q)
    (hFour : Dvd.dvd 4 (q - 1)) (hp : 1 <= p)
    (hMinus : Dvd.dvd (q - 1) (p + 1)) (hl : Nat.Prime l)
    (hlTwo : Not (l = 2)) (hlQ : Dvd.dvd l (q - 1)) :
    Not (Dvd.dvd l (p - 1)) := by
  intro hlP
  have h := Nat.dvd_gcd hlQ hlP
  rw [shifted_period_gcd_eq_two q p hq hFour hp hMinus] at h
  have hle : l <= 2 := Nat.le_of_dvd (by decide : 0 < 2) h
  have hlLower : 2 <= l := hl.two_le
  exact hlTwo (by omega)

/-- The even number of negative-one factors restores the full q-1 period. -/
theorem seed_product_returns_one (q B : Nat) (_hq : 5 <= q)
    (hSq : Squarefree B) (hEven : Even B.primeFactors.card)
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (q - 1) (p + 1)) :
    (B : ZMod (q - 1)) = 1 := by
  classical
  haveI : NeZero (q - 1) := NeZero.mk (by omega)
  have hRoots : forall p : Nat, Membership.mem B.primeFactors p ->
      (p : ZMod (q - 1)) = -1 := by
    intro p hp
    have hf := Nat.mem_primeFactors.mp hp
    have hz : ((p + 1 : Nat) : ZMod (q - 1)) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod (q - 1)) (q - 1) (p + 1)).mpr
        (hFactors p hf.1 hf.2.1)
    simp only [Nat.cast_add, Nat.cast_one] at hz
    apply sub_eq_zero.mp
    simpa only [sub_neg_eq_add] using hz
  have hPow : (-1 : ZMod (q - 1)) ^ B.primeFactors.card = 1 := by
    cases hEven with
    | intro k hk =>
      rw [hk, <- two_mul, pow_mul]
      simp
  calc
    (B : ZMod (q - 1)) = B.primeFactors.prod (fun p => (p : ZMod (q - 1))) := by
      have h := congrArg (fun n : Nat => (n : ZMod (q - 1)))
        (Nat.prod_primeFactors_of_squarefree hSq).symm
      simpa only [Nat.cast_prod] using h
    _ = B.primeFactors.prod (fun _ => (-1 : ZMod (q - 1))) :=
      Finset.prod_congr rfl hRoots
    _ = (-1 : ZMod (q - 1)) ^ B.primeFactors.card := Finset.prod_const _
    _ = 1 := hPow

/-- The complete seed, including the half-period and parity conditions,
produces an actual Korselt certificate; no prime-two condition is dropped. -/
theorem negative_one_seed_korselt (q B : Nat) (hqPrime : Nat.Prime q)
    (hq : 5 <= q) (hFour : Dvd.dvd 4 (q - 1)) (hB : 1 < B)
    (hSq : Squarefree B) (hCoprime : Nat.Coprime q B)
    (hOdd : Nat.Coprime 2 B) (hEven : Even B.primeFactors.card)
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (q - 1) (p + 1))
    (hHalf : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd ((p - 1) / 2) (q * B - 1)) :
    KorseltCertificate (q * B) := by
  classical
  haveI : NeZero (q - 1) := NeZero.mk (by omega)
  have hLarge : 2 < q * B := by
    have h := Nat.mul_le_mul hq (show 2 <= B by omega)
    omega
  have hSquarefree : Squarefree (q * B) :=
    (Nat.squarefree_mul hCoprime).mpr (And.intro hqPrime.prime.squarefree hSq)
  have hComposite : Not (Nat.Prime (q * B)) := by
    intro hPrime
    have hChoices := hPrime.eq_one_or_self_of_dvd q (dvd_mul_right q B)
    have hStrict : q < q * B := by
      simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hB hqPrime.pos
    cases hChoices with
    | inl hOne => omega
    | inr hEq => omega
  have hQOne : (q : ZMod (q - 1)) = 1 := by
    have heq : q = (q - 1) + 1 := by omega
    calc
      (q : ZMod (q - 1)) = (((q - 1) + 1 : Nat) : ZMod (q - 1)) := congrArg _ heq
      _ = 1 := by simp
  have hBOne := seed_product_returns_one q B hq hSq hEven hFactors
  have hCOne : ((q * B : Nat) : ZMod (q - 1)) = 1 := by
    rw [Nat.cast_mul, hQOne, hBOne, mul_one]
  have hQPeriod : Dvd.dvd (q - 1) (q * B - 1) := by
    apply (CharP.cast_eq_zero_iff (ZMod (q - 1)) (q - 1) (q * B - 1)).mp
    rw [Nat.cast_sub (show 1 <= q * B by omega), Nat.cast_one, hCOne, sub_self]
  have hOddProduct : Odd (q * B) :=
    (hqPrime.odd_of_ne_two (by omega)).mul (Nat.coprime_two_left.mp hOdd)
  have hTwoPeriod : Dvd.dvd 2 (q * B - 1) := by
    have hm := Nat.odd_iff.mp hOddProduct
    apply Nat.dvd_of_mod_eq_zero
    omega
  refine And.intro hLarge (And.intro hComposite (And.intro hSquarefree ?_))
  intro p hp hpDiv
  cases hp.dvd_mul.mp hpDiv with
  | inl hpQ =>
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqPrime).mp hpQ
    rw [heq]
    exact hQPeriod
  | inr hpB =>
    have hm := seed_factor_mod_four q p hFour (hFactors p hp hpB)
    have hHalfOdd : Odd ((p - 1) / 2) := Nat.odd_iff.mpr (by omega)
    have hProduct := (Nat.coprime_two_left.mpr hHalfOdd).mul_dvd_of_dvd_of_dvd
      hTwoPeriod (hHalf p hp hpB)
    have heq : 2 * ((p - 1) / 2) = p - 1 := by omega
    rwa [heq] at hProduct

end PrimeFactorOscillations.CarmichaelSeed
