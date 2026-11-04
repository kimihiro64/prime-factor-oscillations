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
# The complete eightfold Sp4 functional-coordinate model

The coroots are numbered short first, reversing Gao's C2 numbering.
The full central lattice is 4Z times 4Z; the root sublattice has periods
8 and 4. The extra central value is sigma * t, with sigma squared equal
to one. This arithmetic model retains that sign and every period.
Its identification with Whittaker-functional coordinates is an ordinary
representation-theoretic input, not a theorem about spherical coefficients.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Metaplectic.Sp4Eight

abbrev State := Prod (Fin 4) (Fin 4)

def row (s : State) : Option Nat :=
  match s.1.val, s.2.val with
  | 0, 0 => some 0
  | 1, 0 => some 1
  | 0, 1 => some 1
  | 1, 2 => some 2
  | 3, 1 => some 2
  | 0, 2 => some 2
  | 3, 3 => some 3
  | 0, 3 => some 3
  | _, _ => none

def supported (s : State) : Prop := (row s).isSome = true

instance (s : State) : Decidable (supported s) :=
  inferInstanceAs (Decidable ((row s).isSome = true))

def degree (s : State) : Nat := (row s).getD 0

def reflectedA (s : State) (i : Fin 2) : Int :=
  if i.val = 0 then 1 - (s.1.val : Int) + 2 * s.2.val else s.1.val

def reflectedB (s : State) (i : Fin 2) : Int :=
  if i.val = 0 then s.2.val else 1 + (s.1.val : Int) - s.2.val

def reflect (s : State) (i : Fin 2) : State :=
  (Fin.ofNat 4 ((reflectedA s i % 4).toNat),
   Fin.ofNat 4 ((reflectedB s i % 4).toNat))

def degreeChange (s : State) (i : Fin 2) : Int :=
  let pairing : Int := if i.val = 0 then 2 * (s.1.val : Int) - 2 * s.2.val
    else -(s.1.val : Int) + 2 * s.2.val
  let period : Int := if i.val = 0 then 8 else 4
  1 - 2 * ((pairing + period - 1) / period) -
    (reflectedA s i / 4 + 2 * (reflectedB s i / 4))

theorem supported_reflect : forall (s : State) (i : Fin 2),
    supported s -> supported (reflect s i) := by decide

theorem degree_reflect : forall (s : State) (i : Fin 2), supported s ->
    (degree (reflect s i) : Int) = (degree s : Int) + degreeChange s i := by decide

theorem support_card : (Finset.univ.filter supported).card = 8 := by decide

/-- Three Gauss exponents, the quadratic sign, and the extra central sign. -/
abbrev Phase := Prod Int (Prod Int (Prod Int (Prod (Fin 2) (Fin 2))))

def phase (s : State) : Phase :=
  match s.1.val, s.2.val with
  | 1, 0 => (1, 0, 0, 0, 0)
  | 0, 1 => (0, 1, 0, 0, 0)
  | 1, 2 => (1, 0, 0, 1, 0)
  | 3, 1 => (0, 1, 1, 0, 0)
  | 0, 2 => (1, 0, 1, 1, 1)
  | 3, 3 => (0, 1, 1, 1, 0)
  | 0, 3 => (1, 1, 1, 1, 1)
  | _, _ => (0, 0, 0, 0, 0)

def phaseAdd (p r : Phase) : Phase :=
  (p.1 + r.1, p.2.1 + r.2.1, p.2.2.1 + r.2.2.1,
   Fin.ofNat 2 (p.2.2.2.1.val + r.2.2.2.1.val),
   Fin.ofNat 2 (p.2.2.2.2.val + r.2.2.2.2.val))

def gaussPhase (n : Int) : Phase :=
  match (n % 8).toNat with
  | 1 => (1, 0, 0, 0, 0)
  | 7 => (-1, 0, 0, 0, 0)
  | 2 => (0, 1, 0, 0, 0)
  | 6 => (0, -1, 0, 0, 0)
  | 3 => (0, 0, 1, 0, 0)
  | 5 => (0, 0, -1, 0, 0)
  | 4 => (0, 0, 0, 1, 0)
  | _ => (0, 0, 0, 0, 0)

def gaussArgument (s : State) (i : Fin 2) : Int :=
  if i.val = 0 then 1 - (2 * (s.1.val : Int) - 2 * s.2.val)
  else 2 * (1 - (-(s.1.val : Int) + 2 * s.2.val))

def centralCorrection (s : State) (i : Fin 2) : Phase :=
  (0, 0, 0, 0, Fin.ofNat 2 ((reflectedA s i / 4) % 2).toNat)

/-- The central correction is essential: it is absent from the G2 model. -/
theorem phase_reflect : forall (s : State) (i : Fin 2), supported s ->
    phaseAdd (phase (reflect s i)) (centralCorrection s i) =
      phaseAdd (phase s) (gaussPhase (gaussArgument s i)) := by decide

theorem gaussArgument_nonzero : forall (s : State) (i : Fin 2), supported s ->
    Not (gaussArgument s i % 8 = 0) := by decide

def quadraticClass (s : State) : Fin 8 :=
  Fin.ofNat 8 (((s.1.val : Int) ^ 2 - 2 * s.1.val * s.2.val +
    2 * (s.2.val : Int) ^ 2) % 8).toNat

def twistClass (s : State) : Fin 8 :=
  let p := phase s
  Fin.ofNat 8 ((p.1 + 2 * p.2.1 + 3 * p.2.2.1 +
    4 * p.2.2.2.1.val) % 8).toNat

theorem twistClass_eq_quadraticClass : forall s : State, supported s ->
    twistClass s = quadraticClass s := by decide

theorem twistClass_fiber_card : forall r : Fin 8,
    (Finset.univ.filter (fun s : State => supported s /\ twistClass s = r)).card =
      if r.val = 0 \/ r.val = 1 \/ r.val = 2 \/ r.val = 5 then 2 else 0 := by decide

def phaseValue {R : Type*} [Field R] (g h j e sigma : R) (p : Phase) : R :=
  g ^ p.1 * h ^ p.2.1 * j ^ p.2.2.1 *
    e ^ p.2.2.2.1.val * sigma ^ p.2.2.2.2.val

def signedBase {R : Type*} [Field R] (t g h j e sigma : R) (s : State) : R :=
  if supported s then t ^ degree s * phaseValue g h j e sigma (phase s) else 0

def signedNumerator {R : Type*} [Field R] (t g h j e sigma X Y : R) : R :=
  Finset.univ.sum (fun s : State => signedBase t g h j e sigma s * X ^ s.1.val * Y ^ s.2.val)

/-- The complete polynomial before any periods or phase averaging. -/
theorem signedNumerator_factorization {R : Type*} [Field R]
    (t g h j e sigma X Y : R) :
    signedNumerator t g h j e sigma X Y =
      (1 + t * h * Y) * (1 + sigma * t ^ 2 * g * j * e * Y ^ 2) +
      t * g * X * (1 + t * e * Y ^ 2) +
      t ^ 2 * h * j * X ^ 3 * Y * (1 + t * e * Y ^ 2) := by
  norm_num [signedNumerator, signedBase, phaseValue, phase, degree, supported, row,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

def baseTerm (x : Real) (s : State) : Real :=
  if supported s then x ^ degree s else 0

def numerator (x : Real) : Real := Finset.univ.sum (baseTerm x)

theorem numerator_eq (x : Real) :
    numerator x = 1 + 2 * x + 3 * x ^ 2 + 2 * x ^ 3 := by
  norm_num [numerator, baseTerm, degree, supported, row,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem numerator_period_identity (x : Real) :
    numerator x * (1 - x) = (1 + x + 2 * x ^ 2) * (1 - x ^ 2) := by
  rw [numerator_eq]
  ring

abbrev Period := Prod Nat Nat
abbrev MassIndex := Prod State Period

def periodTerm (x : Real) (p : Period) : Real := x ^ (p.1 + 2 * p.2)

def massTerm (x : Real) (j : MassIndex) : Real :=
  baseTerm x j.1 * periodTerm x j.2

theorem periodTerm_hasSum (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    HasSum (periodTerm x) ((1 - x) ^ (-1 : Int) * (1 - x ^ 2) ^ (-1 : Int)) := by
  have hx2 : x ^ 2 < 1 := by nlinarith
  have h1 := hasSum_geometric_of_lt_one hx hx1
  have h2 := hasSum_geometric_of_lt_one (pow_nonneg hx 2) hx2
  have hn1 : 0 <= (fun n : Nat => x ^ n) := fun n => pow_nonneg hx n
  have hn2 : 0 <= (fun n : Nat => (x ^ 2) ^ n) :=
    fun n => pow_nonneg (pow_nonneg hx 2) n
  have hp := h1.mul h2 (h1.summable.mul_of_nonneg h2.summable hn1 hn2)
  simp only [zpow_neg_one]
  apply hp.congr_fun
  intro p
  simp only [periodTerm, pow_add, pow_mul]

theorem massTerm_hasSum (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    HasSum (massTerm x) ((1 + x + 2 * x ^ 2) / (1 - x) ^ 2) := by
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
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hn1 : Not (1 - x = 0) := ne_of_gt (sub_pos.mpr hx1)
  have hn2 : Not (1 - x ^ 2 = 0) := ne_of_gt (sub_pos.mpr hx2)
  have heq : numerator x * ((1 - x) ^ (-1 : Int) *
      (1 - x ^ 2) ^ (-1 : Int)) = (1 + x + 2 * x ^ 2) / (1 - x) ^ 2 := by
    simp only [zpow_neg_one]
    field_simp [hn1, hn2]
    convert numerator_period_identity x using 1 <;> ring
  rw [<- heq]
  exact hs

def coordinates (p : MassIndex) : Period :=
  (p.1.1.val + 4 * p.2.1, p.1.2.val + 4 * p.2.2)

def packetOf (n : Period) : MassIndex :=
  ((Fin.ofNat 4 n.1, Fin.ofNat 4 n.2), n.1 / 4, n.2 / 4)

theorem packetOf_coordinates (p : MassIndex) : packetOf (coordinates p) = p := by
  have ha := p.1.1.isLt
  have hb := p.1.2.isLt
  simp only [packetOf, coordinates, Prod.ext_iff, Fin.ext_iff, Fin.val_ofNat]
  omega

theorem coordinates_packetOf (n : Period) : coordinates (packetOf n) = n := by
  have ha := Nat.mod_add_div n.1 4
  have hb := Nat.mod_add_div n.2 4
  simp only [packetOf, coordinates, Prod.ext_iff, Fin.val_ofNat]
  omega

def packetEquiv : Equiv MassIndex Period where
  toFun := coordinates
  invFun := packetOf
  left_inv := packetOf_coordinates
  right_inv := coordinates_packetOf

def localTerm (x : Real) (n : Period) : Real := massTerm x (packetOf n)

/-- All natural coordinate pairs, with no period direction truncated. -/
theorem localTerm_hasSum (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    HasSum (localTerm x) ((1 + x + 2 * x ^ 2) / (1 - x) ^ 2) := by
  exact packetEquiv.symm.hasSum_iff.mpr (massTerm_hasSum x hx hx1)

end Metaplectic.Sp4Eight
