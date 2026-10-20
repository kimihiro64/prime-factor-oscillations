/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticSquarefree
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticDivisorMean

/-!
# QuadraticGaussCoefficient

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.QuadraticGaussCoefficient

open QuadraticCarrierPacket QuadraticDivisorMean IntegerQuadraticPrefix

def gaussFactor (n : Nat) : Complex :=
  if h : 1 < n then
    letI : NeZero n := NeZero.mk (Nat.ne_of_gt (lt_trans Nat.zero_lt_one h))
    gaussSum (IntegerQuadraticCharacter.character n h) ZMod.stdAddChar
  else 1

theorem gaussFactor_one : gaussFactor 1 = 1 := by
  simp [gaussFactor]

theorem gaussFactor_norm (n : Nat) (hn : 0 < n)
    (ho : Odd n) (hs : Squarefree n) :
    norm (gaussFactor n) = Real.sqrt (n : Real) := by
  classical
  letI : NeZero n := NeZero.mk (Nat.ne_of_gt hn)
  unfold gaussFactor
  split_ifs with h
  . exact IntegerQuadraticSquarefree.squarefree_gauss_norm
      n h ho hs ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar n)
  . have h1 : n = 1 := Nat.le_antisymm (Nat.le_of_not_gt h) hn
    subst n
    norm_num

theorem unit_gauss_sum :
    (Finset.univ : Finset (ZMod 1)).sum
      (fun x => kernel x.val 1 * ZMod.stdAddChar x) = gaussFactor 1 := by
  have hz (x : ZMod 1) : x = 0 := Subsingleton.elim _ _
  simp [kernel, gaussFactor, hz]

def jacobiFactor (k : Int) (n : Nat) : Complex := (jacobiSym k n : Complex)

theorem jacobiFactor_norm_le_one (k : Int) (n : Nat) :
    norm (jacobiFactor k n) <= 1 := by
  rcases jacobiSym.trichotomy k n with h0 | h1 | hm
  . simp [jacobiFactor, h0]
  . simp [jacobiFactor, h1]
  . simp [jacobiFactor, hm]

def inverseCoefficient (a : Nat -> Complex) (k : Int) (n : Nat) : Complex :=
  a n * (gaussFactor n / (n : Complex)) * jacobiFactor k n

def rootCoefficient (a : Nat -> Complex) (k : Int) (n : Nat) : Complex :=
  a n * (gaussFactor n / (Real.sqrt (n : Real) : Complex)) * jacobiFactor k n

theorem rootCoefficient_norm (a : Nat -> Complex) (k : Int) (n : Nat)
    (hn : 0 < n) (ho : Odd n) (hs : Squarefree n) :
    norm (rootCoefficient a k n) <= norm (a n) := by
  have hp : 0 < Real.sqrt (n : Real) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hn)
  simp only [rootCoefficient, norm_mul, norm_div,
    gaussFactor_norm n hn ho hs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (ne_of_gt hp), mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (jacobiFactor_norm_le_one k n)

theorem inverseCoefficient_norm_sq (a : Nat -> Complex) (k : Int) (n : Nat)
    (hn : 0 < n) (ho : Odd n) (hs : Squarefree n) :
    norm (inverseCoefficient a k n) ^ 2 <= norm (a n) ^ 2 / (n : Real) := by
  have hp : 0 < (n : Real) := by exact_mod_cast hn
  have hk : norm (jacobiFactor k n) ^ 2 <= 1 := by
    have h := mul_self_le_mul_self (norm_nonneg _) (jacobiFactor_norm_le_one k n)
    simpa only [pow_two, one_mul] using h
  calc
    _ = norm (a n) ^ 2 * ((n : Real) / (n : Real) ^ 2) *
        norm (jacobiFactor k n) ^ 2 := by
      simp only [inverseCoefficient, norm_mul, norm_div,
        gaussFactor_norm n hn ho hs, Complex.norm_natCast,
        mul_pow, div_pow, Real.sq_sqrt hp.le]
    _ <= norm (a n) ^ 2 * ((n : Real) / (n : Real) ^ 2) :=
      mul_le_of_le_one_right (by positivity) hk
    _ = norm (a n) ^ 2 / (n : Real) := by
      field_simp

theorem rootCoefficient_mass (e N : Nat) (k : Int) (S : Finset Nat)
    (a : Nat -> Complex)
    (hS : forall n, Membership.mem S n -> Membership.mem (columns N) n) :
    maskedMass e S (rootCoefficient a k) <= maskedMass e S a := by
  unfold maskedMass
  apply Finset.sum_le_sum
  intro n hn
  have hp := columns_bounds N n (hS n hn)
  have hc := (Finset.mem_filter.mp (hS n hn)).2
  split_ifs
  . have h := mul_self_le_mul_self (norm_nonneg _)
      (rootCoefficient_norm a k n hp.1 hc.1 hc.2)
    simpa only [pow_two] using h
  . exact le_refl _

theorem inverseCoefficient_mass (e N : Nat) (k : Int) (S : Finset Nat)
    (a : Nat -> Complex) (U : Real) (hU : 0 < U)
    (hS : forall n, Membership.mem S n -> Membership.mem (columns N) n)
    (hLower : forall n, Membership.mem S n -> U <= (n : Real)) :
    maskedMass e S (inverseCoefficient a k) <=
      (1 / U) * maskedMass e S a := by
  unfold maskedMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hp := columns_bounds N n (hS n hn)
  have hc := (Finset.mem_filter.mp (hS n hn)).2
  split_ifs
  . calc
      _ <= norm (a n) ^ 2 / (n : Real) :=
        inverseCoefficient_norm_sq a k n hp.1 hc.1 hc.2
      _ <= norm (a n) ^ 2 / U :=
        div_le_div_of_nonneg_left (sq_nonneg _) hU (hLower n hn)
      _ = (1 / U) * norm (a n) ^ 2 := by ring
  . simp only [mul_zero]
    exact le_refl _

end PrimeFactorOscillations.QuadraticGaussCoefficient

