/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Definitions.Reversals

/-!
# Ascent inclusion is insufficient for maximal reversal monotonicity

An explicit pair of real sequences has inclusion of all ascent indices,
yet the first has two strictly separated reversals and the second does
not. This refutes the generic combinatorial implication; no claim is
made that these finite patterns arise from prime-factor densities.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

private def reversalCounterActual (i : Nat) : Real :=
  if i = 0 then 3 else if i <= 3 then (i : Real)
    else if i <= 6 then (i : Real) - 3 else 3

private def reversalCounterReference (i : Nat) : Real :=
  if i = 0 then 3 else (i : Real)

theorem ascent_inclusion_does_not_preserve_reversal_count :
    exists f g : Nat -> Real,
      (forall i : Nat, f i < f (i + 1) -> g i < g (i + 1)) /\
      HasAtLeastReversals f 2 /\ Not (HasAtLeastReversals g 2) := by
  let f := reversalCounterActual
  let g := reversalCounterReference
  refine Exists.intro f (Exists.intro g (And.intro ?_ (And.intro ?_ ?_)))
  . intro i hi
    have hi0 : Not (i = 0) := by
      intro he
      subst i
      norm_num [f, reversalCounterActual] at hi
    dsimp [g, reversalCounterReference]
    rw [if_neg hi0]
    exact_mod_cast (show i < i + 1 by omega)
  . let d : Fin 2 -> Nat := fun i => if i.val = 0 then 0 else 3
    let a : Fin 2 -> Nat := fun i => if i.val = 0 then 1 else 4
    refine Exists.intro d (Exists.intro a (And.intro ?_ ?_))
    next =>
      intro i
      have hi : i.val = 0 \/ i.val = 1 := by have hh := i.isLt; omega
      rcases hi with h0 | h1
      . have he : i = 0 := Fin.ext h0
        subst i
        norm_num [IsReversal, d, a, f, reversalCounterActual]
      . have he : i = 1 := Fin.ext h1
        subst i
        norm_num [IsReversal, d, a, f, reversalCounterActual]
    next =>
      intro i j hij
      have hi : i.val = 0 := by have hh := j.isLt; change i.val < j.val at hij; omega
      have hj : j.val = 1 := by have hh := j.isLt; change i.val < j.val at hij; omega
      have hi0 : i = 0 := Fin.ext hi
      have hj1 : j = 1 := Fin.ext hj
      subst i
      subst j
      norm_num [d, a]
  . intro h
    choose d a hReversal hSeparation using h
    have hdZero : forall i : Fin 2, d i = 0 := by
      intro i
      by_contra hn
      have hDesc := (hReversal i).2.1
      dsimp [g, reversalCounterReference] at hDesc
      rw [if_neg hn] at hDesc
      norm_num at hDesc
    have hSep := hSeparation (0 : Fin 2) (1 : Fin 2) (by decide)
    rw [hdZero] at hSep
    omega

end PrimeFactorOscillations
