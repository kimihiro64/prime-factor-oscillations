/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassConvergenceExponent

/-!
# Exact capacity of the actual sampled polynomial sign decoder

Capacity is the extended nonnegative supremum of the positive rational
powers that really decode all sufficiently large samples. The zero
convergence exponent gives infinite capacity, with no claim about whether
the class itself is finite or infinite.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

noncomputable def integerDecoderCapacity (P : Set Nat) : ENNReal :=
  sSup (fun y => exists h : Rat, And (integerDecoderAdmissible P h)
    (y = ENNReal.ofReal (h : Real)))

theorem ofReal_admissible_le_integerDecoderCapacity
    (P : Set Nat) (h : Rat) (had : integerDecoderAdmissible P h) :
    ENNReal.ofReal (h : Real) <= integerDecoderCapacity P := by
  exact le_sSup (Exists.intro h (And.intro had rfl))

theorem integerDecoderCapacity_eq_of_positive_convergenceExponent
    (P : Set Nat) (s0 : Real) (hs0 : 0 < s0) (hs01 : s0 < 1)
    (hsum0 : Summable (classPowerWeight P s0))
    (htau : 0 < primeClassConvergenceExponent P) :
    integerDecoderCapacity P = ENNReal.ofReal (1 / primeClassConvergenceExponent P) := by
  have hupper : integerDecoderCapacity P <=
      ENNReal.ofReal (1 / primeClassConvergenceExponent P) := by
    apply sSup_le
    intro y hy
    choose h hh using hy
    rw [hh.2]
    apply ENNReal.ofReal_le_ofReal
    have hhR : (0 : Real) < (h : Real) := by exact_mod_cast hh.1.1
    have hle := integerDecoderAdmissible_convergenceExponent_le_inverse P h hh.1
    have hunit : (h : Real) * (1 / (h : Real)) = 1 := by field_simp
    have htunit : primeClassConvergenceExponent P *
        (1 / primeClassConvergenceExponent P) = 1 := by field_simp
    nlinarith
  have hlower : ENNReal.ofReal (1 / primeClassConvergenceExponent P) <=
      integerDecoderCapacity P := by
    apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have htarget : 0 < 1 / primeClassConvergenceExponent P := one_div_pos.mpr htau
    have hrr : (r : Real) < 1 / primeClassConvergenceExponent P := by
      apply (ENNReal.ofReal_lt_ofReal_iff htarget).mp
      simpa only [ENNReal.ofReal_coe_nnreal] using hr
    choose h hh using exists_rat_btwn hrr
    have hhR : (0 : Real) < (h : Real) := lt_of_le_of_lt (NNReal.coe_nonneg r) hh.1
    have hhQ : (0 : Rat) < h := by exact_mod_cast hhR
    have hunit : primeClassConvergenceExponent P *
        (1 / primeClassConvergenceExponent P) = 1 := by field_simp
    have had := integerDecoderAdmissible_below_critical_exponent P s0 hs0 hs01 hsum0
      h hhQ (by nlinarith)
    have hrh : (r : ENNReal) <= ENNReal.ofReal (h : Real) := by
      simpa only [ENNReal.ofReal_coe_nnreal] using
        ENNReal.ofReal_le_ofReal (le_of_lt hh.1)
    exact hrh.trans (ofReal_admissible_le_integerDecoderCapacity P h had)
  exact le_antisymm hupper hlower

theorem integerDecoderCapacity_eq_top_of_zero_convergenceExponent
    (P : Set Nat) (s0 : Real) (hs0 : 0 < s0) (hs01 : s0 < 1)
    (hsum0 : Summable (classPowerWeight P s0))
    (htau : primeClassConvergenceExponent P = 0) :
    integerDecoderCapacity P = Top.top := by
  apply le_antisymm le_top
  apply ENNReal.le_of_forall_nnreal_lt
  intro r _
  choose h hh using exists_rat_gt (r : Real)
  have hhR : (0 : Real) < (h : Real) := lt_of_le_of_lt (NNReal.coe_nonneg r) hh
  have hhQ : (0 : Rat) < h := by exact_mod_cast hhR
  have had := integerDecoderAdmissible_of_zero_convergenceExponent P s0 hs0 hs01 hsum0
    htau h hhQ
  have hrh : (r : ENNReal) <= ENNReal.ofReal (h : Real) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (le_of_lt hh)
  exact hrh.trans (ofReal_admissible_le_integerDecoderCapacity P h had)

theorem integerDecoderCapacity_eq_inverse_convergenceExponent
    (P : Set Nat) (s0 : Real) (hs0 : 0 < s0) (hs01 : s0 < 1)
    (hsum0 : Summable (classPowerWeight P s0)) :
    integerDecoderCapacity P = Inv.inv (ENNReal.ofReal (primeClassConvergenceExponent P)) := by
  by_cases htau : primeClassConvergenceExponent P = 0
  case pos =>
    rw [htau, ENNReal.ofReal_zero]
    simpa only [ENNReal.inv_zero] using
      integerDecoderCapacity_eq_top_of_zero_convergenceExponent P s0 hs0 hs01 hsum0 htau
  case neg =>
    have htaupos : 0 < primeClassConvergenceExponent P :=
      lt_of_le_of_ne (primeClassConvergenceExponent_nonneg P s0 hs0 hsum0) (Ne.symm htau)
    rw [integerDecoderCapacity_eq_of_positive_convergenceExponent P s0 hs0 hs01 hsum0 htaupos]
    rw [one_div, ENNReal.ofReal_inv_of_pos htaupos]

end PrimeFactorOscillations.PrimeClassSampling
