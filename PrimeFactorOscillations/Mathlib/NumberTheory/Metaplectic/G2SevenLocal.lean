/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2TwelveLocal

/-!
# The sevenfold G2 signed functional-coordinate model

All 49 central classes and every supported short/long root edge are
checked. Only single normalized Gauss factors or their inverses remain.
The full coherent grade-zero channel is phase free; no CM interpretation
or global spherical coefficient is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Metaplectic.G2Seven

abbrev State := Prod (Fin 7) (Fin 7)

def row (s : State) : Option Nat :=
  match s.1.val, s.2.val with
  | 0, 0 => some 0
  | 1, 0 => some 1
  | 0, 1 => some 1
  | 1, 2 => some 2
  | 4, 1 => some 2
  | 6, 2 => some 3
  | 4, 4 => some 3
  | 6, 5 => some 4
  | 2, 4 => some 2
  | 3, 5 => some 3
  | 2, 6 => some 3
  | 3, 6 => some 4
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
  (Fin.ofNat 7 ((reflectedA s i % 7).toNat),
   Fin.ofNat 7 ((reflectedB s i % 7).toNat))

def degreeChange (s : State) (i : Fin 2) : Int :=
  let pairing : Int := if i.val = 0 then 2 * (s.1.val : Int) - 3 * s.2.val
    else -(s.1.val : Int) + 2 * s.2.val
  1 - 2 * ((pairing + 6) / 7) -
    2 * (reflectedA s i / 7 + reflectedB s i / 7)

theorem supported_reflect : forall (s : State) (i : Fin 2),
    supported s -> supported (reflect s i) := by decide

theorem degree_reflect : forall (s : State) (i : Fin 2), supported s ->
    (degree (reflect s i) : Int) = (degree s : Int) + degreeChange s i := by decide

theorem support_card : (Finset.univ.filter supported).card = 12 := by decide

abbrev Phase := Prod Int (Prod Int Int)

def phase (s : State) : Phase :=
  match s.1.val, s.2.val with
  | 1, 0 => (1, 0, 0)
  | 0, 1 => (0, 0, 1)
  | 6, 2 => (0, -1, 0)
  | 4, 4 => (0, 1, 0)
  | 3, 5 => (0, 0, -1)
  | 2, 6 => (-1, 0, 0)
  | _, _ => (0, 0, 0)

def phaseAdd (p r : Phase) : Phase :=
  (p.1 + r.1, p.2.1 + r.2.1, p.2.2 + r.2.2)

def gaussPhase (n : Int) : Phase :=
  match (n % 7).toNat with
  | 1 => (1, 0, 0)
  | 6 => (-1, 0, 0)
  | 2 => (0, 1, 0)
  | 5 => (0, -1, 0)
  | 3 => (0, 0, 1)
  | 4 => (0, 0, -1)
  | _ => (0, 0, 0)

def gaussArgument (s : State) (i : Fin 2) : Int :=
  if i.val = 0 then 1 - (2 * (s.1.val : Int) - 3 * s.2.val)
  else 3 * (1 - (-(s.1.val : Int) + 2 * s.2.val))

theorem phase_reflect : forall (s : State) (i : Fin 2), supported s ->
    phase (reflect s i) = phaseAdd (phase s) (gaussPhase (gaussArgument s i)) := by decide

theorem gaussArgument_nonzero : forall (s : State) (i : Fin 2), supported s ->
    Not (gaussArgument s i % 7 = 0) := by decide

def quadraticClass (s : State) : Fin 7 :=
  Fin.ofNat 7 (((s.1.val : Int) ^ 2 - 3 * s.1.val * s.2.val +
    3 * (s.2.val : Int) ^ 2) % 7).toNat

def twistClass (s : State) : Fin 7 :=
  let p := phase s
  Fin.ofNat 7 ((p.1 + 2 * p.2.1 + 3 * p.2.2) % 7).toNat

theorem twistClass_eq_quadraticClass : forall s : State, supported s ->
    twistClass s = quadraticClass s := by decide

theorem twistClass_fiber_card : forall r : Fin 7,
    (Finset.univ.filter (fun s : State => supported s /\ twistClass s = r)).card =
      if r.val = 0 then 6 else 1 := by decide

/-- Every same-grade overlap has exactly the same Gauss phase. -/
theorem sameGrade_samePhase : forall s r : State, supported s -> supported r ->
    twistClass s = twistClass r -> phase s = phase r := by decide

def phaseValue {R : Type*} [Field R] (g h j : R) (p : Phase) : R :=
  g ^ p.1 * h ^ p.2.1 * j ^ p.2.2

def signedBase {R : Type*} [Field R] (t g h j : R) (s : State) : R :=
  if supported s then t ^ degree s * phaseValue g h j (phase s) else 0

def signedNumerator {R : Type*} [Field R] (t g h j X Y : R) : R :=
  Finset.univ.sum (fun s : State => signedBase t g h j s * X ^ s.1.val * Y ^ s.2.val)

theorem signedNumerator_factorization {R : Type*} [Field R] (t g h j X Y : R) :
    signedNumerator t g h j X Y =
      (1 + t ^ 2 * X ^ 2 * Y ^ 4) * (1 + t ^ 2 * X * Y ^ 2 + t ^ 2 * X ^ 4 * Y) +
      t * (g * X + j * Y) + t ^ 3 *
        (h * X ^ 4 * Y ^ 4 + h ^ (-1 : Int) * X ^ 6 * Y ^ 2 +
          j ^ (-1 : Int) * X ^ 3 * Y ^ 5 + g ^ (-1 : Int) * X ^ 2 * Y ^ 6) := by
  norm_num [signedNumerator, signedBase, phaseValue, phase, degree, supported, row,
    Fintype.sum_prod_type, Fin.sum_univ_succ, zpow_neg_one]
  ring

def baseTerm (x : Real) (s : State) : Real :=
  if supported s then x ^ degree s else 0

def numerator (x : Real) : Real := Finset.univ.sum (baseTerm x)

theorem numerator_factorization (x : Real) :
    numerator x = (1 + x) ^ 2 * (1 + 2 * x ^ 2) := by
  norm_num [numerator, baseTerm, degree, supported, row,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

abbrev Period := Prod Nat Nat
abbrev MassIndex := Prod State Period

def massTerm (x : Real) (p : MassIndex) : Real :=
  baseTerm x p.1 * G2Twelve.periodTerm x p.2

theorem massTerm_hasSum (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    HasSum (massTerm x) ((1 + 2 * x ^ 2) / (1 - x) ^ 2) := by
  have hb := hasSum_fintype (baseTerm x)
  have hp := G2Twelve.periodTerm_hasSum x hx hx1
  have hnb : 0 <= baseTerm x := by
    intro s
    unfold baseTerm
    split
    next => exact pow_nonneg hx _
    next => exact le_rfl
  have hnp : 0 <= G2Twelve.periodTerm x := fun p => pow_nonneg hx _
  have hs := hb.mul hp (hb.summable.mul_of_nonneg hp.summable hnb hnp)
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hn1 : Not (1 - x = 0) := ne_of_gt (sub_pos.mpr hx1)
  have hn2 : Not (1 - x ^ 2 = 0) := ne_of_gt (sub_pos.mpr hx2)
  have heq : numerator x * ((1 - x ^ 2) ^ (-1 : Int) *
      (1 - x ^ 2) ^ (-1 : Int)) = (1 + 2 * x ^ 2) / (1 - x) ^ 2 := by
    rw [numerator_factorization]
    simp only [zpow_neg_one]
    field_simp [hn1, hn2]
    ring
  rw [<- heq]
  exact hs

def coordinates (p : MassIndex) : Period :=
  (p.1.1.val + 7 * p.2.1, p.1.2.val + 7 * p.2.2)

def packetOf (n : Period) : MassIndex :=
  ((Fin.ofNat 7 n.1, Fin.ofNat 7 n.2), n.1 / 7, n.2 / 7)

theorem packetOf_coordinates (p : MassIndex) : packetOf (coordinates p) = p := by
  have ha := p.1.1.isLt
  have hb := p.1.2.isLt
  simp only [packetOf, coordinates, Prod.ext_iff, Fin.ext_iff, Fin.val_ofNat]
  omega

theorem coordinates_packetOf (n : Period) : coordinates (packetOf n) = n := by
  have ha := Nat.mod_add_div n.1 7
  have hb := Nat.mod_add_div n.2 7
  simp only [packetOf, coordinates, Prod.ext_iff, Fin.val_ofNat]
  omega

def packetEquiv : Equiv MassIndex Period where
  toFun := coordinates
  invFun := packetOf
  left_inv := packetOf_coordinates
  right_inv := coordinates_packetOf


def localTerm (x : Real) (n : Period) : Real := massTerm x (packetOf n)

theorem localTerm_hasSum (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    HasSum (localTerm x) ((1 + 2 * x ^ 2) / (1 - x) ^ 2) := by
  exact packetEquiv.symm.hasSum_iff.mpr (massTerm_hasSum x hx hx1)

end Metaplectic.G2Seven
