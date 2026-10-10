/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The finite quintic coefficient recurrence and its periodic cone

This module checks the arithmetic model from BBFH, equation (5), at cover
degree five. The independent analytic identification with a spherical
Whittaker function is not asserted here. This proves no global reflection
identity, large sieve, or zero-free region.

The finite domain is exactly (Fin 5)^3: the model's period is five in each
coordinate. Every reflection is checked, and explicit paths prove uniqueness
on the 24-state support. The parity estimates apply to all natural indices.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Metaplectic.Quintic

/-- Three residue coordinates in the period-five model. -/
abbrev State := Prod (Fin 5) (Prod (Fin 5) (Fin 5))

/-- Twice the absolute-value exponent and the two Gauss-factor exponents.
Unsupported classes are `none`. -/
def row (s : State) : Option (Prod Int (Prod Int Int)) :=
  match s.1.val, s.2.1.val, s.2.2.val with
  | 0, 0, 0 => some (0, 0, 0)
  | 0, 0, 1 => some (0, 1, 0)
  | 0, 1, 0 => some (0, 1, 1)
  | 0, 1, 3 => some (2, 1, 0)
  | 0, 2, 2 => some (2, 1, 1)
  | 0, 2, 3 => some (2, 2, 1)
  | 1, 0, 0 => some (0, 1, 0)
  | 1, 0, 2 => some (1, 1, 1)
  | 1, 1, 1 => some (1, 2, -1)
  | 1, 1, 3 => some (2, 2, 0)
  | 1, 3, 1 => some (3, 1, 0)
  | 1, 3, 2 => some (3, 2, 0)
  | 2, 0, 1 => some (1, 1, 1)
  | 2, 0, 2 => some (1, 2, 1)
  | 2, 2, 0 => some (2, 1, 1)
  | 2, 2, 2 => some (3, 1, 2)
  | 2, 3, 1 => some (3, 2, 0)
  | 2, 3, 3 => some (4, 2, 1)
  | 3, 1, 0 => some (2, 1, 0)
  | 3, 1, 1 => some (2, 2, 0)
  | 3, 2, 0 => some (2, 2, 1)
  | 3, 2, 3 => some (4, 2, 0)
  | 3, 3, 2 => some (4, 2, 1)
  | 3, 3, 3 => some (4, 3, 1)
  | _, _, _ => none

def supported (s : State) : Prop := (row s).isSome = true

instance (s : State) : Decidable (supported s) := inferInstanceAs
  (Decidable ((row s).isSome = true))

def squaredPower (s : State) : Int := ((row s).getD (0, 0, 0)).1

/-- Simple reflections, numbered zero through two. -/
def reflect (s : State) (i : Fin 3) : State :=
  let a := s.1.val
  let b := s.2.1.val
  let c := s.2.2.val
  match i.val with
  | 0 => (Fin.ofNat 5 (8 - a), Fin.ofNat 5 (1 + a + b), s.2.2)
  | 1 => (Fin.ofNat 5 (1 + a + b), Fin.ofNat 5 (8 - b),
      Fin.ofNat 5 (1 + b + c))
  | _ => (s.1, Fin.ofNat 5 (1 + b + c), Fin.ofNat 5 (8 - c))

/-- Exact change of the squared absolute-value exponent. -/
def powerChange (s : State) (i : Fin 3) : Int :=
  let a := s.1.val
  let b := s.2.1.val
  let c := s.2.2.val
  match i.val with
  | 0 => -2 + if 1 + a + b < 5 then 4 else 0
  | 1 => (if 5 <= 1 + a + b then -3 else 0) +
      if 1 + b + c < 5 then 3 else 0
  | _ => 2 + if 5 <= 1 + b + c then -4 else 0

def phaseChange (s : State) (i : Fin 3) : Prod Int Int :=
  let k := if i.val = 0 then s.1.val else if i.val = 1 then s.2.1.val else s.2.2.val
  match k with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (0, -1)
  | _ => (-1, 0)

/-- The complete recurrence, including both Gauss phases. -/
theorem row_reflect : forall (s : State) (i : Fin 3), supported s ->
    row (reflect s i) = some
      (squaredPower s + powerChange s i,
       ((row s).getD (0, 0, 0)).2.1 + (phaseChange s i).1,
       ((row s).getD (0, 0, 0)).2.2 + (phaseChange s i).2) := by
  decide

theorem supported_reflect (s : State) (i : Fin 3) (h : supported s) :
    supported (reflect s i) := by
  unfold supported
  rw [row_reflect s i h]
  rfl

theorem squaredPower_reflect (s : State) (i : Fin 3) (h : supported s) :
    squaredPower (reflect s i) = squaredPower s + powerChange s i := by
  unfold squaredPower
  rw [row_reflect s i h]
  rfl

/-- Paths from zero, used after the finite-domain reduction. -/
def path (s : State) : List (Fin 3) :=
  match s.1.val, s.2.1.val, s.2.2.val with
  | 0, 0, 1 => [0, 1, 2]
  | 0, 1, 0 => [1, 0, 2, 1]
  | 0, 1, 3 => [2]
  | 0, 2, 2 => [0, 1]
  | 0, 2, 3 => [0, 1, 0, 2, 1]
  | 1, 0, 0 => [2, 1, 0]
  | 1, 0, 2 => [1, 2]
  | 1, 1, 1 => [0, 2, 1]
  | 1, 1, 3 => [1, 2, 1, 0]
  | 1, 3, 1 => [1]
  | 1, 3, 2 => [0, 1, 2, 1]
  | 2, 0, 1 => [1, 0]
  | 2, 0, 2 => [0, 1, 2, 1, 0]
  | 2, 2, 0 => [2, 1]
  | 2, 2, 2 => [1, 0, 2]
  | 2, 3, 1 => [0, 2, 1, 0]
  | 2, 3, 3 => [1, 2, 1]
  | 3, 1, 0 => [0]
  | 3, 1, 1 => [0, 1, 0, 2]
  | 3, 2, 0 => [1, 0, 2, 1, 0]
  | 3, 2, 3 => [0, 2]
  | 3, 3, 2 => [0, 1, 0]
  | 3, 3, 3 => [0, 1, 0, 2, 1, 0]
  | _, _, _ => []

theorem path_reaches : forall s : State, supported s ->
    (path s).foldl reflect (0, 0, 0) = s := by decide

/-- A solution of the exponent recurrence is uniquely determined on the support. -/
theorem squaredPower_unique (f : State -> Int) (hzero : f (0, 0, 0) = 0)
    (hstep : forall s i, supported s -> f (reflect s i) = f s + powerChange s i)
    (s : State) (hs : supported s) : f s = squaredPower s := by
  have hwalk : forall (w : List (Fin 3)) (t : State), supported t ->
      f t = squaredPower t -> f (w.foldl reflect t) = squaredPower (w.foldl reflect t) := by
    intro w
    induction w with
    | nil => intro t _ h; exact h
    | cons i w ih =>
      intro t ht heq
      apply ih (reflect t i) (supported_reflect t i ht)
      rw [hstep t i ht, squaredPower_reflect t i ht, heq]
  have h := hwalk (path s) (0, 0, 0) (by decide) hzero
  rw [path_reaches s hs] at h
  exact h

/-- Distinct shifted diagonal weights, including the fourth weight zero. -/
def distinctWeights (s : State) : Prop :=
  let a := (s.1.val + s.2.1.val + s.2.2.val + 3) % 5
  let b := (s.2.1.val + s.2.2.val + 2) % 5
  let c := (s.2.2.val + 1) % 5
  Not (a = b) /\ Not (a = c) /\ Not (a = 0) /\
    Not (b = c) /\ Not (b = 0) /\ Not (c = 0)

instance (s : State) : Decidable (distinctWeights s) := by
  unfold distinctWeights
  infer_instance

theorem supported_iff_distinct : forall s : State,
    supported s <-> distinctWeights s := by decide

theorem support_card : (Finset.univ.filter supported).card = 24 := by decide

/-- Determinant height exponent. -/
def height (a b c : Nat) : Nat := a + 2 * b + 3 * c

def baseDefect (s : State) : Int :=
  (height s.1.val s.2.1.val s.2.2.val : Int) - squaredPower s

theorem baseDefect_bounds : forall s : State, supported s ->
    0 <= baseDefect s /\
    (Not (s = (0, 0, 0)) -> 1 <= baseDefect s) /\
    (Not (s = (0, 0, 0)) -> height s.1.val s.2.1.val s.2.2.val % 2 = 0 ->
      2 <= baseDefect s) := by decide

/-- Residue of an arbitrary, unbounded triple. -/
def residue (a b c : Nat) : State := (Fin.ofNat 5 a, Fin.ofNat 5 b, Fin.ofNat 5 c)

/-- The periodically extended arithmetic model. Its representation-theoretic
identification is a separate obligation. -/
def fullSquaredPower (a b c : Nat) : Int :=
  squaredPower (residue a b c) + 3 * (a / 5 : Nat) + 4 * (b / 5 : Nat) +
    3 * (c / 5 : Nat)

def defect (a b c : Nat) : Int := (height a b c : Int) - fullSquaredPower a b c

/-- Exact period costs for every natural triple, without a finite cutoff. -/
theorem defect_decomposition (a b c : Nat) :
    defect a b c = baseDefect (residue a b c) +
      2 * (a / 5 : Nat) + 6 * (b / 5 : Nat) + 12 * (c / 5 : Nat) := by
  have ha := Nat.mod_add_div a 5
  have hb := Nat.mod_add_div b 5
  have hc := Nat.mod_add_div c 5
  simp only [defect, fullSquaredPower, baseDefect, height, residue,
    Fin.val_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

theorem defect_pos (a b c : Nat) (hs : supported (residue a b c))
    (hn : Not (a = 0 /\ b = 0 /\ c = 0)) : 1 <= defect a b c := by
  have hbase := baseDefect_bounds (residue a b c) hs
  rw [defect_decomposition]
  by_cases hz : residue a b c = (0, 0, 0)
  case pos =>
    have ha := congrArg (fun s : State => s.1.val) hz
    have hb := congrArg (fun s : State => s.2.1.val) hz
    have hc := congrArg (fun s : State => s.2.2.val) hz
    simp only [residue, Fin.val_ofNat, Fin.val_zero] at ha hb hc
    have hda := Nat.mod_add_div a 5
    have hdb := Nat.mod_add_div b 5
    have hdc := Nat.mod_add_div c 5
    omega
  case neg =>
    have hp := hbase.2.1 hz
    omega

/-- Native quadratic parity 101: every nonconstant even term has two units of decay. -/
theorem defect_even (a b c : Nat) (hs : supported (residue a b c))
    (hn : Not (a = 0 /\ b = 0 /\ c = 0)) (he : height a b c % 2 = 0) :
    2 <= defect a b c := by
  have hbase := baseDefect_bounds (residue a b c) hs
  rw [defect_decomposition]
  by_cases hp : a / 5 + b / 5 + c / 5 = 0
  case pos =>
    have ha : a / 5 = 0 := by omega
    have hb : b / 5 = 0 := by omega
    have hc : c / 5 = 0 := by omega
    have hma := Nat.mod_add_div a 5
    have hmb := Nat.mod_add_div b 5
    have hmc := Nat.mod_add_div c 5
    have hz : Not (residue a b c = (0, 0, 0)) := by
      intro hz
      have h1 := congrArg (fun s : State => s.1.val) hz
      have h2 := congrArg (fun s : State => s.2.1.val) hz
      have h3 := congrArg (fun s : State => s.2.2.val) hz
      simp only [residue, Fin.val_ofNat, Fin.val_zero] at h1 h2 h3
      omega
    have he' : height (residue a b c).1.val (residue a b c).2.1.val
        (residue a b c).2.2.val % 2 = 0 := by
      simp only [height] at he
      change (a % 5 + 2 * (b % 5) + 3 * (c % 5)) % 2 = 0
      omega
    have hbound := hbase.2.2 hz he'
    simp only [ha, hb, hc, Nat.cast_zero, mul_zero, add_zero]
    exact hbound
  case neg => omega

/-- Finite numerator of the absolute local mass, including every supported class. -/
def numerator {R : Type*} [CommSemiring R] (x : R) : R :=
  Finset.univ.sum (fun s : State => if supported s then x ^ (baseDefect s).toNat else 0)

/-- Exact determinant-height numerator; no residue class has been omitted. -/
theorem numerator_factorization {R : Type*} [CommSemiring R] (x : R) :
    numerator x = (1 + x) * (1 + x ^ 2 + x ^ 4) *
      (1 + x ^ 3 + x ^ 6 + x ^ 9) := by
  norm_num [numerator, Fintype.sum_prod_type, Fin.sum_univ_succ, supported,
    baseDefect, height, squaredPower, row]
  ring

/-- The numerator cancels the three period factors algebraically. -/
theorem numerator_period_identity {R : Type*} [CommRing R] (x : R) :
    numerator x * ((1 - x) * (1 - x ^ 2) * (1 - x ^ 3)) =
      (1 - x ^ 2) * (1 - x ^ 6) * (1 - x ^ 12) := by
  rw [numerator_factorization]
  ring

end Metaplectic.Quintic
