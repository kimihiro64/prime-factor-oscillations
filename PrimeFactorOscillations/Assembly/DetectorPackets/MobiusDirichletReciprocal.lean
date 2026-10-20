/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.NumberTheory.LSeries.Convolution
import PrimeFactorOscillations.Assembly.DetectorPackets.DirichletCompanionIdentity
import PrimeFactorOscillations.Proof.DetectorPackets.DepletedMobius

/-!
# MobiusDirichletReciprocal

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
open PrimeFactorOscillations.DepletedMobius

namespace PrimeFactorOscillations.MobiusDirichlet

def characterArithmetic {q : Nat} (chi : DirichletCharacter Complex q) :
    ArithmeticFunction Complex :=
  twist (fun n : Nat => chi (n : ZMod q))
    (ArithmeticFunction.zeta : ArithmeticFunction Int)

def mobiusArithmetic {q : Nat} (chi : DirichletCharacter Complex q) :
    ArithmeticFunction Complex :=
  twist (fun n : Nat => chi (n : ZMod q)) ArithmeticFunction.moebius

theorem characterArithmetic_eq {q : Nat} (chi : DirichletCharacter Complex q)
    (n : Nat) (hn : Not (n = 0)) :
    characterArithmetic chi n = chi (n : ZMod q) := by
  simp [characterArithmetic, twist, hn]

theorem twist_one_character {q : Nat} (chi : DirichletCharacter Complex q) :
    twist (fun n : Nat => chi (n : ZMod q))
      (1 : ArithmeticFunction Int) = 1 := by
  ext n
  by_cases hn : n = 1
  . subst n
    simp [twist]
  . simp [twist, ArithmeticFunction.one_apply, hn]

theorem mobius_mul_character {q : Nat} (chi : DirichletCharacter Complex q) :
    mobiusArithmetic chi * characterArithmetic chi = 1 := by
  unfold mobiusArithmetic characterArithmetic
  rw [<- twist_mul (fun n : Nat => chi (n : ZMod q))
    (fun m n => by simp only [Nat.cast_mul, map_mul]),
    ArithmeticFunction.moebius_mul_coe_zeta]
  exact twist_one_character chi

theorem mobius_coefficient_norm_le {q : Nat} (chi : DirichletCharacter Complex q)
    (n : Nat) :
    norm ((ArithmeticFunction.moebius n : Complex) * chi (n : ZMod q)) <= 1 := by
  have hmu : norm (ArithmeticFunction.moebius n : Complex) <= 1 := by
    by_cases hn : Squarefree n
    . simp [ArithmeticFunction.moebius_apply_of_squarefree hn]
    . simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  rw [norm_mul]
  exact (mul_le_mul hmu (chi.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

theorem mobius_LSeriesSummable {q : Nat} (chi : DirichletCharacter Complex q)
    (s : Complex) (hs : 1 < s.re) :
    LSeriesSummable (mobiusArithmetic chi) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
  intro n _
  exact mobius_coefficient_norm_le chi n

theorem character_LSeriesSummable {q : Nat} (chi : DirichletCharacter Complex q)
    (s : Complex) (hs : 1 < s.re) :
    LSeriesSummable (characterArithmetic chi) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
  intro n hn
  rw [characterArithmetic_eq chi n hn]
  exact chi.norm_le_one _

theorem LSeries_arithmetic_one (s : Complex) :
    LSeries (1 : ArithmeticFunction Complex) s = 1 := by
  unfold LSeries
  rw [tsum_eq_single 1]
  . simp [LSeries.term, ArithmeticFunction.one_apply]
  . intro n hn
    simp [LSeries.term, ArithmeticFunction.one_apply, hn]

theorem mobius_LSeries_mul_LFunction {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (s : Complex) (hs : 1 < s.re) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    LSeries (mobiusArithmetic chi) s * DirichletCharacter.LFunction chi s = 1 := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  have hplain : LSeries (characterArithmetic chi) s =
      DirichletCharacter.LFunction chi s := by
    rw [chi.LFunction_eq_LSeries hs]
    exact LSeries_congr (fun hn => characterArithmetic_eq chi _ hn) s
  rw [<- hplain, <- ArithmeticFunction.LSeries_mul'
    (mobius_LSeriesSummable chi s hs) (character_LSeriesSummable chi s hs),
    mobius_mul_character]
  exact LSeries_arithmetic_one s

theorem mobius_LSeries_eq_inverse {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (s : Complex) (hs : 1 < s.re) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    LSeries (fun n : Nat =>
      (ArithmeticFunction.moebius n : Complex) * chi (n : ZMod q)) s =
      Inv.inv (DirichletCharacter.LFunction chi s) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  have hm := mobius_LSeries_mul_LFunction chi hq s hs
  have hL : Not (DirichletCharacter.LFunction chi s = 0) := by
    intro hz
    rw [hz, mul_zero] at hm
    norm_num at hm
  have heq : LSeries (mobiusArithmetic chi) s =
      1 / DirichletCharacter.LFunction chi s := (eq_div_iff hL).mpr hm
  simpa [mobiusArithmetic, twist, one_div] using heq

end PrimeFactorOscillations.MobiusDirichlet
