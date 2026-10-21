/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderCapacityConverse

/-!
# The convergence exponent and the two strict decoding regions

The infimum is over positive exponents of the actual prime-class
series. Its existence and every use of conditional completeness retain
an actual convergent exponent. Equality at the decoding endpoint is
deliberately not asserted.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

noncomputable def primeClassConvergentExponents (P : Set Nat) : Set Real :=
  fun s => And (0 < s) (Summable (classPowerWeight P s))

noncomputable def primeClassConvergenceExponent (P : Set Nat) : Real :=
  sInf (primeClassConvergentExponents P)

theorem primeClassConvergentExponents_bddBelow (P : Set Nat) :
    BddBelow (primeClassConvergentExponents P) := by
  exact Exists.intro 0 (fun s hs => le_of_lt hs.1)

theorem primeClassConvergenceExponent_le
    (P : Set Nat) (s : Real) (hs : 0 < s)
    (hsum : Summable (classPowerWeight P s)) :
    primeClassConvergenceExponent P <= s := by
  exact csInf_le (primeClassConvergentExponents_bddBelow P) (And.intro hs hsum)

theorem primeClassConvergenceExponent_nonneg
    (P : Set Nat) (s : Real) (hs : 0 < s)
    (hsum : Summable (classPowerWeight P s)) :
    0 <= primeClassConvergenceExponent P := by
  exact le_csInf (Exists.intro s (And.intro hs hsum)) (fun t ht => le_of_lt ht.1)

theorem classPowerWeight_summable_above_convergenceExponent
    (P : Set Nat) (s0 s : Real) (hs0 : 0 < s0)
    (hsum0 : Summable (classPowerWeight P s0))
    (hs : primeClassConvergenceExponent P < s) :
    Summable (classPowerWeight P s) := by
  have hnonempty : (primeClassConvergentExponents P).Nonempty :=
    Exists.intro s0 (And.intro hs0 hsum0)
  choose t ht using exists_lt_of_csInf_lt hnonempty hs
  exact classPowerWeight_summable_mono P t s (le_of_lt ht.2) ht.1.2

theorem integerDecoderAdmissible_convergenceExponent_le_inverse
    (P : Set Nat) (h : Rat) (had : integerDecoderAdmissible P h) :
    primeClassConvergenceExponent P <= 1 / (h : Real) := by
  have hh : (0 : Real) < (h : Real) := by exact_mod_cast had.1
  by_contra hnot
  have hlt : 1 / (h : Real) < primeClassConvergenceExponent P := lt_of_not_ge hnot
  choose s hs using exists_between hlt
  have hs0 : 0 < s := lt_trans (one_div_pos.mpr hh) hs.1
  have hsum := integerDecoderAdmissible_summable_above_inverse P h had s hs.1
  have hle := primeClassConvergenceExponent_le P s hs0 hsum
  linarith

theorem integerDecoderAdmissible_below_critical_exponent
    (P : Set Nat) (s0 : Real) (hs0 : 0 < s0) (hs01 : s0 < 1)
    (hsum0 : Summable (classPowerWeight P s0))
    (h : Rat) (hh : 0 < h)
    (hcritical : (h : Real) * primeClassConvergenceExponent P < 1) :
    integerDecoderAdmissible P h := by
  have hhR : (0 : Real) < (h : Real) := by exact_mod_cast hh
  have htau0 := primeClassConvergenceExponent_nonneg P s0 hs0 hsum0
  have htau1 : primeClassConvergenceExponent P < 1 :=
    lt_of_le_of_lt (primeClassConvergenceExponent_le P s0 hs0 hsum0) hs01
  have hunit : (h : Real) * (1 / (h : Real)) = 1 := by field_simp
  have htauInv : primeClassConvergenceExponent P < 1 / (h : Real) := by nlinarith
  choose s hs using exists_between (lt_min htau1 htauInv)
  have hspos : 0 < s := lt_of_le_of_lt htau0 hs.1
  have hs1 : s < 1 := (lt_min_iff.mp hs.2).1
  have hspower : (h : Real) * s < 1 := by
    have hsinv := (lt_min_iff.mp hs.2).2
    nlinarith
  exact integerDecoderAdmissible_of_summable_power P s h hspos hs1
    (classPowerWeight_summable_above_convergenceExponent P s0 s hs0 hsum0 hs.1)
    hh hspower

theorem integerDecoder_not_admissible_above_critical_exponent
    (P : Set Nat) (h : Rat)
    (hcritical : 1 < (h : Real) * primeClassConvergenceExponent P) :
    Not (integerDecoderAdmissible P h) := by
  intro had
  have hh : (0 : Real) < (h : Real) := by exact_mod_cast had.1
  have hle := integerDecoderAdmissible_convergenceExponent_le_inverse P h had
  have hunit : (h : Real) * (1 / (h : Real)) = 1 := by field_simp
  nlinarith

theorem integerDecoderAdmissible_of_zero_convergenceExponent
    (P : Set Nat) (s0 : Real) (hs0 : 0 < s0) (hs01 : s0 < 1)
    (hsum0 : Summable (classPowerWeight P s0))
    (htau : primeClassConvergenceExponent P = 0) (h : Rat) (hh : 0 < h) :
    integerDecoderAdmissible P h := by
  apply integerDecoderAdmissible_below_critical_exponent P s0 hs0 hs01 hsum0 h hh
  rw [htau, mul_zero]
  norm_num

end PrimeFactorOscillations.PrimeClassSampling
