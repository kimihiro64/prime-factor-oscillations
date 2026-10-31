/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerGapWindows
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerSignatureWindow

/-!
# Rigidity of actual finite-field signature returns at integer gap frames

The original pair law uses A=-h*n and B=h*(n+h). Its known negative-unit
phase is cancelled explicitly before applying the uniform signature theorem.
On the existing unbounded least-gap frames, any actual integer prime-pair
return preserving both coordinates is the same pair and the same gap.
This supplies no new pair recurrence and no numerical bound for the gap.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

open Filter IntegerQuadraticCharacter FiniteFieldIntegerCharacter
open FiniteFieldIntegerWindowTransfer FiniteFieldIntegerGapWindows
open PrimeProfileRigidity

def originalSignatureMatch (Q n h m k : Nat) : Prop :=
  forall p : Nat, forall hp : Nat.Prime p,
    preciseCore Q < p -> p <= preciseCore Q * preciseCore Q ->
    letI : Fact (Nat.Prime p) := Fact.mk hp
    And
      (FiniteField.QuadraticPairTwistEuler.characterA (n : ZMod p) (h : ZMod p) =
        FiniteField.QuadraticPairTwistEuler.characterA (m : ZMod p) (k : ZMod p))
      (FiniteField.QuadraticPairTwistEuler.characterB (n : ZMod p) (h : ZMod p) =
        FiniteField.QuadraticPairTwistEuler.characterB (m : ZMod p) (k : ZMod p))

theorem numerator_kernel_neg_matching (D E : Int) (p : Nat)
    (hp : Nat.Prime p) (hp2 : Not (p = 2))
    (hm : numeratorKernel (-D) p = numeratorKernel (-E) p) :
    numeratorKernel D p = numeratorKernel E p := by
  have : Fact (Nat.Prime p) := Fact.mk hp
  have hsq : numeratorKernel (-1) p ^ 2 = 1 := by
    rw [numerator_kernel_prime _ p hp2]
    exact_mod_cast quadraticChar_sq_one
      (by simp : Not (((-1 : Int) : ZMod p) = 0))
  have hnon : Not (numeratorKernel (-1) p = 0) := by
    intro hz
    rw [hz] at hsq
    norm_num at hsq
  rw [show -D = (-1) * D by ring, show -E = (-1) * E by ring,
    numerator_kernel_mul_numerators, numerator_kernel_mul_numerators] at hm
  have hzero : numeratorKernel (-1) p *
      (numeratorKernel D p - numeratorKernel E p) = 0 := by
    rw [mul_sub, hm, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hnon)

theorem original_signature_implies_positive (Q n h m k p : Nat)
    (hp : Nat.Prime p) (hp2 : Not (p = 2))
    (hKp : preciseCore Q < p) (hpK : p <= preciseCore Q * preciseCore Q)
    (hm : originalSignatureMatch Q n h m k) :
    And
      (numeratorKernel ((h : Int) * (n : Int)) p =
        numeratorKernel ((k : Int) * (m : Int)) p)
      (numeratorKernel ((h : Int) * ((n + h : Nat) : Int)) p =
        numeratorKernel ((k : Int) * ((m + k : Nat) : Int)) p) := by
  have : Fact (Nat.Prime p) := Fact.mk hp
  have hdata := hm p hp hKp hpK
  have hA : numeratorKernel (-((h : Int) * (n : Int))) p =
      numeratorKernel (-((k : Int) * (m : Int))) p := by
    rw [<- integer_characterA h n p hp2, <- integer_characterA k m p hp2]
    exact_mod_cast hdata.1
  have hB : numeratorKernel ((h : Int) * ((n + h : Nat) : Int)) p =
      numeratorKernel ((k : Int) * ((m + k : Nat) : Int)) p := by
    rw [<- integer_characterB h n p hp2, <- integer_characterB k m p hp2]
    exact_mod_cast hdata.2
  exact And.intro (numerator_kernel_neg_matching _ _ p hp hp2 hA) hB

theorem eventually_actual_pair_signature_rigidity (H : Nat) (hH : 0 < H) :
    Filter.Eventually (fun Q : Nat =>
      forall n m h k : Nat,
        Nat.Prime n -> Nat.Prime (n + h) -> Nat.Prime m -> Nat.Prime (m + k) ->
        0 < h -> 0 < k -> h <= H -> k <= H ->
        Q < n -> Q < m -> n + h <= Q * Q -> m + k <= Q * Q ->
        originalSignatureMatch Q n h m k -> And (n = m) (h = k)) atTop := by
  filter_upwards [eventually_prime_pair_signature_rigidity H hH,
    precise_core_tendsto_atTop.eventually_ge_atTop 3] with Q hQ hK
  intro n m h k hn hnh hm hmk hh hk hhH hkH hQn hQm hnQ hmQ hmatch
  apply hQ n m h k hn hnh hm hmk hh hk hhH hkH hQn hQm hnQ hmQ
  intro p hp hKp hpK
  exact original_signature_implies_positive Q n h m k p hp (by omega) hKp hpK hmatch

theorem unbounded_least_gap_signature_rigid_frames (R : Nat) :
    exists Q i : Nat, And (R <= Q) (And (leastGapFrame Q i)
      (forall m k : Nat, Nat.Prime m -> Nat.Prime (m + k) ->
        0 < k -> k <= leastRecurringPrimeGap -> Q < m -> m + k <= Q * Q ->
        originalSignatureMatch Q (Q + 1) leastRecurringPrimeGap m k ->
        And (m = Q + 1) (k = leastRecurringPrimeGap))) := by
  have hH : 0 < leastRecurringPrimeGap := by
    have hh := two_le_leastRecurringPrimeGap
    omega
  choose Q0 hQ0 using eventually_atTop.mp
    (eventually_actual_pair_signature_rigidity leastRecurringPrimeGap hH)
  choose Q i hRQ hf using unbounded_least_gap_positive_windows (max R Q0)
  have hQge : Q0 <= Q := (le_max_right _ _).trans hRQ
  have hRge : R <= Q := (le_max_left _ _).trans hRQ
  refine Exists.intro Q (Exists.intro i (And.intro hRge (And.intro hf ?_)))
  intro m k hm hmk hk hkH hQm hmQ hmatch
  have hn : Nat.Prime (Q + 1) := by
    rw [<- hf.2.2.2.2.2.1]
    exact PrimeFactorUnimodality.prime_primeAt i
  have hnh : Nat.Prime (Q + 1 + leastRecurringPrimeGap) := by
    rw [<- hf.2.2.2.2.2.2.1]
    exact PrimeFactorUnimodality.prime_primeAt (i + 1)
  have hnQ : Q + 1 + leastRecurringPrimeGap <= Q * Q := by
    have hHQ := hf.2.2.2.2.1
    have hQ6 := hf.1
    nlinarith only [hHQ, hQ6]
  have he := hQ0 Q hQge (Q + 1) m leastRecurringPrimeGap k hn hnh hm hmk
    hH hk (Nat.le_refl _) hkH (by omega) hQm hnQ hmQ hmatch
  exact And.intro he.1.symm he.2.symm

end PrimeFactorOscillations.FiniteFieldIntegerSignature
