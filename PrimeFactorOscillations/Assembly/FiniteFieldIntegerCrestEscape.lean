/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldPolynomialHeight

/-!
# Superpolynomial height of quartic CRT crests

Every integer attaining the proved quartic logarithmic crest scale
eventually exceeds each fixed power of the prime cutoff. For each
positive even shift a single family of actual CRT residues retains its
quartic lower bound and works for every polynomial degree. This is
height separation, not a lower bound for integer prime-pair mass.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerCrestEscape

open FiniteFieldIntegerMass
open FiniteFieldIntegerPrimes
open FiniteFieldIntegerExtrema
open FiniteFieldPolynomialHeight
open Filter

theorem quartic_crests_escape_polynomial_height (h : Nat) (hh : 0 < h) :
    forall m : Nat, exists Q0 : Nat, forall Q : Nat, Q0 <= Q ->
      And (13 <= Q) (And (h < Q)
        (forall n : Nat,
          lowerConstant h * (Real.log (Q : Real)) ^ 4 <= actualPacket (h : Int) Q n ->
            Q ^ m < n)) := by
  let A : Real := Classical.choose exists_uniform_polynomial_height_amplitude
  have hA := Classical.choose_spec exists_uniform_polynomial_height_amplitude
  have hApos : 0 < A := hA.1
  intro m
  let N : Nat := Classical.choose (hA.2 m)
  have hN := Classical.choose_spec (hA.2 m)
  let D : Real := A * (64 * (m : Real) + 641)
  have hD : 0 < D := by dsimp [D]; positivity
  have hc : 0 < lowerConstant h := lower_constant_pos h
  have hNat : Tendsto (fun Q : Nat => (Q : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlim : Tendsto
      (fun Q : Nat => Real.log (Real.log (Q : Real)) / Real.log (Q : Real))
      atTop (nhds 0) := by
    have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp
      (Real.tendsto_log_atTop.comp hNat)
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using ht
  have hsmall : Filter.Eventually
      (fun Q : Nat => Real.log (Real.log (Q : Real)) / Real.log (Q : Real) <
        lowerConstant h / D) atTop :=
    hlim.eventually (Iio_mem_nhds (div_pos hc hD))
  let R : Nat := Classical.choose (Filter.eventually_atTop.mp hsmall)
  have hR := Classical.choose_spec (Filter.eventually_atTop.mp hsmall)
  let Q0 : Nat := max N (max R (h + 13))
  refine Exists.intro Q0 ?_
  intro Q hQ
  have hNQ : N <= Q := by dsimp [Q0] at hQ; omega
  have hRQ : R <= Q := by dsimp [Q0] at hQ; omega
  have hQ13 : 13 <= Q := by dsimp [Q0] at hQ; omega
  have hhQ : h < Q := by dsimp [Q0] at hQ; omega
  refine And.intro hQ13 (And.intro hhQ ?_)
  intro n hcrest
  by_contra hnot
  have hnQ : n <= Q ^ m := by omega
  have hL : 0 < Real.log (Q : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q from by omega))
  have hcrestpos : 0 < lowerConstant h * (Real.log (Q : Real)) ^ 4 :=
    mul_pos hc (pow_pos hL 4)
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    have hz := actual_packet_zero_of_prime_divisor (h : Int) Q n 2
      (by decide : Nat.Prime 2) (by omega) (by rw [hn0]; exact dvd_zero 2)
    rw [hz] at hcrest
    linarith only [hcrestpos, hcrest]
  have hu := hN Q hNQ h n hh hhQ hn hnQ
  change actualPacket (h : Int) Q n <=
    D * (Real.log (Q : Real)) ^ 3 * Real.log (Real.log (Q : Real)) at hu
  have hs := mul_lt_mul_of_pos_right (hR Q hRQ) (mul_pos hL hD)
  have hlinear :
      D * Real.log (Real.log (Q : Real)) < lowerConstant h * Real.log (Q : Real) := by
    calc
      _ = (Real.log (Real.log (Q : Real)) / Real.log (Q : Real)) *
          (Real.log (Q : Real) * D) := by field_simp [ne_of_gt hL]
      _ < (lowerConstant h / D) * (Real.log (Q : Real) * D) := hs
      _ = _ := by field_simp [ne_of_gt hD]
  have hstrict := mul_lt_mul_of_pos_right hlinear (pow_pos hL 3)
  nlinarith only [hu, hcrest, hstrict]

theorem exists_superpolynomial_integer_crest_family (h : Nat)
    (hh : 0 < h) (heven : Dvd.dvd 2 h) :
    exists a : Nat -> Nat, And
      (forall Q : Nat, 13 <= Q ->
        And (a Q < primePeriod Q)
          (And
            (forall t : Nat, lowerConstant h * (Real.log (Q : Real)) ^ 4 <=
              actualPacket (h : Int) Q (a Q + primePeriod Q * t))
            (forall n : Nat, actualPacket (h : Int) Q n <=
              replacementConstant * (Real.log (Q : Real)) ^ 4)))
      (forall m : Nat, exists Q0 : Nat, forall Q : Nat, Q0 <= Q -> forall t : Nat,
        Q ^ m < a Q + primePeriod Q * t) := by
  let a : Nat -> Nat := fun Q =>
    if hQ : 13 <= Q then
      Classical.choose (integer_packet_sharp_fourth_power h Q hh heven hQ)
    else 0
  have ha (Q : Nat) (hQ : 13 <= Q) :
      And (a Q < primePeriod Q)
        (And
          (forall t : Nat, lowerConstant h * (Real.log (Q : Real)) ^ 4 <=
            actualPacket (h : Int) Q (a Q + primePeriod Q * t))
          (forall n : Nat, actualPacket (h : Int) Q n <=
            replacementConstant * (Real.log (Q : Real)) ^ 4)) := by
    simpa only [a, dite_eq_left hQ] using
      Classical.choose_spec (integer_packet_sharp_fourth_power h Q hh heven hQ)
  refine Exists.intro a (And.intro ha ?_)
  intro m
  let Q0 : Nat := Classical.choose (quartic_crests_escape_polynomial_height h hh m)
  have hQ0 := Classical.choose_spec (quartic_crests_escape_polynomial_height h hh m)
  refine Exists.intro Q0 ?_
  intro Q hQ t
  have hf := hQ0 Q hQ
  exact hf.2.2 (a Q + primePeriod Q * t) ((ha Q hf.1).2.1 t)

end PrimeFactorOscillations.FiniteFieldIntegerCrestEscape
