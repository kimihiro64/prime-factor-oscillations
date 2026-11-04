/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The complete twelvefold G2 functional-coordinate model

The source coordinates are Whittaker-functional coordinates in Gao's
convention, not spherical Fourier coefficients. This module checks the
48-state arithmetic model and both unbounded period directions. The
representation-theoretic identification is a separate, cited input.
No global transformation, character estimate, or zero-free bound is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Metaplectic.G2Twelve

abbrev State := Prod (Fin 12) (Fin 4)

def row (s : State) : Option Nat :=
  match s.1.val, s.2.val with
  | 0, 0 => some 0
  | 1, 0 => some 1
  | 0, 1 => some 1
  | 1, 2 => some 2
  | 4, 1 => some 2
  | 6, 2 => some 3
  | 4, 0 => some 1
  | 6, 1 => some 2
  | 9, 0 => some 2
  | 10, 1 => some 3
  | 9, 2 => some 3
  | 10, 2 => some 4
  | _, _ => none

def supported (s : State) : Prop := (row s).isSome = true

instance (s : State) : Decidable (supported s) :=
  inferInstanceAs (Decidable ((row s).isSome = true))

def degree (s : State) : Nat := (row s).getD 0

def reflectedA (s : State) (i : Fin 2) : Int :=
  if i.val = 0 then 1 - (s.1.val : Int) + 3 * s.2.val else s.1.val

def reflectedB (s : State) (i : Fin 2) : Int :=
  if i.val = 0 then s.2.val else 1 + (s.1.val : Int) - s.2.val

def reflect (s : State) (i : Fin 2) : State :=
  (Fin.ofNat 12 ((reflectedA s i % 12).toNat),
   Fin.ofNat 4 ((reflectedB s i % 4).toNat))

/-- Exact exponent change after reduction to the fixed rectangle. -/
def degreeChange (s : State) (i : Fin 2) : Int :=
  let pairing : Int := if i.val = 0 then 2 * (s.1.val : Int) - 3 * s.2.val
    else -(s.1.val : Int) + 2 * s.2.val
  let period : Int := if i.val = 0 then 12 else 4
  1 - 2 * ((pairing + period - 1) / period) -
    2 * (reflectedA s i / 12 + reflectedB s i / 4)

theorem supported_reflect : forall (s : State) (i : Fin 2),
    supported s -> supported (reflect s i) := by decide

theorem degree_reflect : forall (s : State) (i : Fin 2), supported s ->
    (degree (reflect s i) : Int) = (degree s : Int) + degreeChange s i := by decide

theorem support_card : (Finset.univ.filter supported).card = 12 := by decide

def path (s : State) : List (Fin 2) :=
  match s.1.val, s.2.val with
  | 1, 0 => [0]
  | 0, 1 => [1]
  | 1, 2 => [0, 1]
  | 4, 1 => [1, 0]
  | 6, 2 => [0, 1, 0]
  | 4, 0 => [1, 0, 1]
  | 6, 1 => [0, 1, 0, 1]
  | 9, 0 => [1, 0, 1, 0]
  | 10, 1 => [0, 1, 0, 1, 0]
  | 9, 2 => [1, 0, 1, 0, 1]
  | 10, 2 => [0, 1, 0, 1, 0, 1]
  | _, _ => []

theorem path_reaches : forall s : State, supported s ->
    (path s).foldl reflect (0, 0) = s := by decide

/-- The exponent table is forced by the two root recurrences. -/
theorem degree_unique (f : State -> Int) (hzero : f (0, 0) = 0)
    (hstep : forall s i, supported s -> f (reflect s i) = f s + degreeChange s i)
    (s : State) (hs : supported s) : f s = degree s := by
  have hwalk : forall (w : List (Fin 2)) (t : State), supported t ->
      f t = degree t -> f (w.foldl reflect t) = degree (w.foldl reflect t) := by
    intro w
    induction w with
    | nil => intro t _ h; exact h
    | cons i w ih =>
      intro t ht heq
      apply ih (reflect t i) (supported_reflect t i ht)
      rw [hstep t i ht, degree_reflect t i ht, heq]
  have h := hwalk (path s) (0, 0) (by decide) hzero
  rw [path_reaches s hs] at h
  exact h

def numerator {R : Type*} [CommSemiring R] (x : R) : R :=
  Finset.univ.sum (fun s : State => if supported s then x ^ degree s else 0)

theorem numerator_factorization {R : Type*} [CommSemiring R] (x : R) :
    numerator x = (1 + x) ^ 2 * (1 + x + x ^ 2) := by
  norm_num [numerator, Fintype.sum_prod_type, Fin.sum_univ_succ,
    supported, degree, row]
  ring

theorem numerator_period_identity {R : Type*} [CommRing R] (x : R) :
    numerator x * (1 - x) ^ 3 = (1 - x ^ 2) ^ 2 * (1 - x ^ 3) := by
  rw [numerator_factorization]
  ring

abbrev Period := Prod Nat Nat
abbrev MassIndex := Prod State Period

def baseTerm (x : Real) (s : State) : Real :=
  if supported s then x ^ degree s else 0

def periodTerm (x : Real) (p : Period) : Real :=
  x ^ (2 * p.1 + 2 * p.2)

def massTerm (x : Real) (j : MassIndex) : Real :=
  baseTerm x j.1 * periodTerm x j.2

private theorem square_lt_one (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    x ^ 2 < 1 := by nlinarith

theorem periodTerm_hasSum (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    HasSum (periodTerm x) ((1 - x ^ 2) ^ (-1 : Int) * (1 - x ^ 2) ^ (-1 : Int)) := by
  have h := hasSum_geometric_of_lt_one (pow_nonneg hx 2) (square_lt_one x hx hx1)
  have hn : 0 <= (fun n : Nat => (x ^ 2) ^ n) := fun n => pow_nonneg (pow_nonneg hx 2) n
  have hp := h.mul h (h.summable.mul_of_nonneg h.summable hn hn)
  simp only [zpow_neg_one]
  apply hp.congr_fun
  intro p
  simp only [periodTerm, pow_add, pow_mul]

theorem massTerm_hasSum (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    HasSum (massTerm x) ((1 - x ^ 3) / (1 - x) ^ 3) := by
  have hb := hasSum_fintype (baseTerm x)
  have hp := periodTerm_hasSum x hx hx1
  have hnb : 0 <= baseTerm x := by
    intro s
    unfold baseTerm
    split
    next => exact pow_nonneg hx _
    next => exact le_rfl
  have hnp : 0 <= periodTerm x := fun p => pow_nonneg hx _
  have hs := hb.mul hp (hb.summable.mul_of_nonneg hp.summable hnb hnp)
  have hn1 : Not (1 - x = 0) := ne_of_gt (sub_pos.mpr hx1)
  have hn2 : Not (1 - x ^ 2 = 0) := ne_of_gt (sub_pos.mpr (square_lt_one x hx hx1))
  have heq : numerator x * ((1 - x ^ 2) ^ (-1 : Int) *
      (1 - x ^ 2) ^ (-1 : Int)) = (1 - x ^ 3) / (1 - x) ^ 3 := by
    simp only [zpow_neg_one]
    field_simp [hn1, hn2]
    exact numerator_period_identity x
  rw [<- heq]
  exact hs

/-- Four independent Gauss exponents and the quadratic Gauss sign. -/
abbrev Phase := Prod Int (Prod Int (Prod Int (Prod Int (Fin 2))))

def phase (s : State) : Phase :=
  match s.1.val, s.2.val with
  | 1, 0 => (1, 0, 0, 0, 0)
  | 0, 1 => (0, 1, 0, 0, 0)
  | 1, 2 => (1, 0, 0, 0, 1)
  | 4, 1 => (0, 1, 1, 0, 0)
  | 6, 2 => (1, 0, 0, 1, 1)
  | 4, 0 => (0, 0, 1, 0, 0)
  | 6, 1 => (1, -1, 0, 1, 1)
  | 9, 0 => (0, 0, 1, 1, 0)
  | 10, 1 => (1, -1, 1, 1, 1)
  | 9, 2 => (0, 0, 1, 1, 1)
  | 10, 2 => (1, 0, 1, 1, 1)
  | _, _ => (0, 0, 0, 0, 0)

def phaseAdd (p r : Phase) : Phase :=
  (p.1 + r.1, p.2.1 + r.2.1, p.2.2.1 + r.2.2.1,
   p.2.2.2.1 + r.2.2.2.1, Fin.ofNat 2 (p.2.2.2.2.val + r.2.2.2.2.val))

def gaussPhase (n : Int) : Phase :=
  match (n % 12).toNat with
  | 1 => (1, 0, 0, 0, 0)
  | 11 => (-1, 0, 0, 0, 0)
  | 3 => (0, 1, 0, 0, 0)
  | 9 => (0, -1, 0, 0, 0)
  | 4 => (0, 0, 1, 0, 0)
  | 8 => (0, 0, -1, 0, 0)
  | 5 => (0, 0, 0, 1, 0)
  | 7 => (0, 0, 0, -1, 0)
  | 6 => (0, 0, 0, 0, 1)
  | _ => (0, 0, 0, 0, 0)

def gaussArgument (s : State) (i : Fin 2) : Int :=
  if i.val = 0 then 1 - (2 * (s.1.val : Int) - 3 * s.2.val)
  else 3 * (1 - (-(s.1.val : Int) + 2 * s.2.val))

/-- Every root edge retains the normalized Gauss factor, including its sign. -/
theorem phase_reflect : forall (s : State) (i : Fin 2), supported s ->
    phase (reflect s i) = phaseAdd (phase s) (gaussPhase (gaussArgument s i)) := by
  decide

theorem gaussArgument_nonzero : forall (s : State) (i : Fin 2), supported s ->
    Not (gaussArgument s i % 12 = 0) := by decide

/-- Every required Gauss factor is represented by the five retained phases.
In particular the unused order-six factors G2 and G10 are never replaced by one. -/
theorem gaussArgument_allowed : forall (s : State) (i : Fin 2), supported s ->
    let r := gaussArgument s i % 12
    r = 1 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/
      r = 7 \/ r = 8 \/ r = 9 \/ r = 11 := by decide

def quadraticClass (s : State) : Fin 12 :=
  Fin.ofNat 12 (((s.1.val : Int) ^ 2 - 3 * s.1.val * s.2.val +
    3 * (s.2.val : Int) ^ 2) % 12).toNat

def twistClass (s : State) : Fin 12 :=
  let p := phase s
  Fin.ofNat 12 ((p.1 + 3 * p.2.1 + 4 * p.2.2.1 +
    5 * p.2.2.2.1 + 6 * p.2.2.2.2.val) % 12).toNat

/-- Additive-character rescaling is graded by the actual G2 quadratic form. -/
theorem twistClass_eq_quadraticClass : forall s : State, supported s ->
    twistClass s = quadraticClass s := by decide

/-- Exactly six additive-twist classes, each with two supported coordinates. -/
theorem twistClass_fiber_card : forall r : Fin 12,
    (Finset.univ.filter (fun s : State => supported s /\ twistClass s = r)).card =
      if r.val = 0 \/ r.val = 1 \/ r.val = 3 \/ r.val = 4 \/
          r.val = 7 \/ r.val = 9 then 2 else 0 := by decide

def phaseValue {R : Type*} [Field R] (g h j k e : R) (p : Phase) : R :=
  g ^ p.1 * h ^ p.2.1 * j ^ p.2.2.1 * k ^ p.2.2.2.1 * e ^ p.2.2.2.2.val

def signedBase {R : Type*} [Field R] (t g h j k e : R) (s : State) : R :=
  if supported s then t ^ degree s * phaseValue g h j k e (phase s) else 0

def signedNumerator {R : Type*} [Field R] (t g h j k e X Y : R) : R :=
  Finset.univ.sum (fun s : State => signedBase t g h j k e s * X ^ s.1.val * Y ^ s.2.val)

/-- Complete signed numerator, without replacing Gauss phases by magnitudes. -/
theorem signedNumerator_factorization {R : Type*} [Field R]
    (t g h j k e X Y : R) (hh : Not (h = 0)) :
    signedNumerator t g h j k e X Y =
      (1 + t * j * X ^ 4) * (1 + t * h * Y) *
        (1 + t ^ 2 * (g * k * e) / h * X ^ 6 * Y) +
      t * X * (g + t * j * k * X ^ 8) * (1 + t * e * Y ^ 2) := by
  norm_num [signedNumerator, signedBase, phaseValue, phase, degree, supported, row,
    Fintype.sum_prod_type, Fin.sum_univ_succ, zpow_neg_one]
  field_simp [hh]
  ring

def twistNumerator {R : Type*} [Field R] (t g h j k e z : R) : R :=
  Finset.univ.sum (fun s : State => signedBase t g h j k e s * z ^ (twistClass s).val)

/-- The six surviving coherent pairs after additive-character grading. -/
theorem twistNumerator_six_pairs {R : Type*} [Field R]
    (t g h j k e z : R) (hg : Not (g = 0)) (hh : Not (h = 0))
    (he : Not (e = 0)) :
    twistNumerator t g h j k e z =
      (1 + t ^ 3 * (g * k * e)) * (1 + t * j * z ^ 4) +
      t * (g * z + h * z ^ 3) * (1 + t ^ 2 * (k * e * j / h)) +
      t ^ 2 * (g * e * z ^ 7 + (g * k * e) / h * z ^ 9) *
        (1 + h * j / (g * e)) := by
  norm_num [twistNumerator, signedBase, phaseValue, phase, degree, supported, row,
    twistClass, Fintype.sum_prod_type, Fin.sum_univ_succ, zpow_neg_one]
  field_simp [hg, hh, he]
  ring

def coordinates (p : MassIndex) : Period :=
  (p.1.1.val + 12 * p.2.1, p.1.2.val + 4 * p.2.2)

def packetOf (n : Period) : MassIndex :=
  ((Fin.ofNat 12 n.1, Fin.ofNat 4 n.2), n.1 / 12, n.2 / 4)

theorem packetOf_coordinates (p : MassIndex) : packetOf (coordinates p) = p := by
  have ha := p.1.1.isLt
  have hb := p.1.2.isLt
  simp only [packetOf, coordinates, Prod.ext_iff, Fin.ext_iff, Fin.val_ofNat]
  omega

theorem coordinates_packetOf (n : Period) : coordinates (packetOf n) = n := by
  have ha := Nat.mod_add_div n.1 12
  have hb := Nat.mod_add_div n.2 4
  simp only [packetOf, coordinates, Prod.ext_iff, Fin.val_ofNat]
  omega

def packetEquiv : Equiv MassIndex Period where
  toFun := coordinates
  invFun := packetOf
  left_inv := packetOf_coordinates
  right_inv := coordinates_packetOf

def localTerm (x : Real) (n : Period) : Real := massTerm x (packetOf n)

/-- The energy identity covers every pair of natural coordinates exactly once. -/
theorem localTerm_hasSum (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    HasSum (localTerm x) ((1 - x ^ 3) / (1 - x) ^ 3) := by
  exact packetEquiv.symm.hasSum_iff.mpr (massTerm_hasSum x hx hx1)

end Metaplectic.G2Twelve
