/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.QuinticLocal

/-!
# The complete absolute mass of the quintic arithmetic model

The index retains every supported residue and every nonnegative period in
all three coordinates. The series is proved convergent, not interpreted as
a formal rational function. Identification with a global moving-twist
reflection is outside this statement.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Metaplectic.Quintic

abbrev Period := Prod Nat (Prod Nat Nat)
abbrev MassIndex := Prod State Period

/-- All three period generators, with determinant-height decay costs. -/
def periodTerm (x : Real) (p : Period) : Real :=
  x ^ (2 * p.1 + 6 * p.2.1 + 12 * p.2.2)

def baseTerm (x : Real) (s : State) : Real :=
  if supported s then x ^ (baseDefect s).toNat else 0

def massTerm (x : Real) (j : MassIndex) : Real := baseTerm x j.1 * periodTerm x j.2

private theorem power_lt_one (x : Real) (hx : 0 <= x) (hx1 : x < 1)
    (n : Nat) (hn : 0 < n) : x ^ n < 1 := by
  have hpow (k : Nat) : x ^ (k + 1) <= x := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        x ^ (k + 1 + 1) = x ^ (k + 1) * x := pow_succ x (k + 1)
        _ <= x ^ (k + 1) * 1 := mul_le_mul_of_nonneg_left hx1.le (pow_nonneg hx _)
        _ = x ^ (k + 1) := mul_one _
        _ <= x := ih
  cases n with
  | zero => omega
  | succ n => exact lt_of_le_of_lt (hpow n) hx1

theorem periodTerm_hasSum (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    HasSum (periodTerm x)
      ((1 - x ^ 2) ^ (-1 : Int) *
        ((1 - x ^ 6) ^ (-1 : Int) * (1 - x ^ 12) ^ (-1 : Int))) := by
  have h2 := hasSum_geometric_of_lt_one (pow_nonneg hx 2) (power_lt_one x hx hx1 2 (by decide))
  have h6 := hasSum_geometric_of_lt_one (pow_nonneg hx 6) (power_lt_one x hx hx1 6 (by decide))
  have h12 := hasSum_geometric_of_lt_one (pow_nonneg hx 12) (power_lt_one x hx hx1 12 (by decide))
  have hn2 : 0 <= (fun n : Nat => (x ^ 2) ^ n) := fun n => pow_nonneg (pow_nonneg hx 2) n
  have hn6 : 0 <= (fun n : Nat => (x ^ 6) ^ n) := fun n => pow_nonneg (pow_nonneg hx 6) n
  have hn12 : 0 <= (fun n : Nat => (x ^ 12) ^ n) := fun n => pow_nonneg (pow_nonneg hx 12) n
  have h612 := h6.mul h12 (h6.summable.mul_of_nonneg h12.summable hn6 hn12)
  have hn612 : 0 <= (fun p : Prod Nat Nat => (x ^ 6) ^ p.1 * (x ^ 12) ^ p.2) :=
    fun p => mul_nonneg (hn6 p.1) (hn12 p.2)
  have h := h2.mul h612 (h2.summable.mul_of_nonneg h612.summable hn2 hn612)
  simp only [zpow_neg_one]
  apply h.congr_fun
  intro p
  simp only [periodTerm, pow_add, pow_mul]
  ring

theorem massTerm_hasSum_periods (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    HasSum (massTerm x)
      (numerator x * ((1 - x ^ 2) ^ (-1 : Int) *
        ((1 - x ^ 6) ^ (-1 : Int) * (1 - x ^ 12) ^ (-1 : Int)))) := by
  have hb := hasSum_fintype (baseTerm x)
  have hp := periodTerm_hasSum x hx hx1
  have hnb : 0 <= baseTerm x := by
    intro s
    unfold baseTerm
    split
    next => exact pow_nonneg hx _
    next => exact le_rfl
  have hnp : 0 <= periodTerm x := fun p => pow_nonneg hx _
  exact hb.mul hp (hb.summable.mul_of_nonneg hp.summable hnb hnp)

/-- Exact sum of the complete convergent series after period-factor cancellation. -/
theorem massTerm_hasSum (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    HasSum (massTerm x) (((1 - x) * (1 - x ^ 2) * (1 - x ^ 3)) ^ (-1 : Int)) := by
  have h2 : x ^ 2 < 1 := power_lt_one x hx hx1 2 (by decide)
  have h3 : x ^ 3 < 1 := power_lt_one x hx hx1 3 (by decide)
  have h6 : x ^ 6 < 1 := power_lt_one x hx hx1 6 (by decide)
  have h12 : x ^ 12 < 1 := power_lt_one x hx hx1 12 (by decide)
  have hne1 : Not (1 - x = 0) := ne_of_gt (sub_pos.mpr hx1)
  have hne2 : Not (1 - x ^ 2 = 0) := ne_of_gt (sub_pos.mpr h2)
  have hne3 : Not (1 - x ^ 3 = 0) := ne_of_gt (sub_pos.mpr h3)
  have hne6 : Not (1 - x ^ 6 = 0) := ne_of_gt (sub_pos.mpr h6)
  have hne12 : Not (1 - x ^ 12 = 0) := ne_of_gt (sub_pos.mpr h12)
  have heq : numerator x * ((1 - x ^ 2) ^ (-1 : Int) *
      ((1 - x ^ 6) ^ (-1 : Int) * (1 - x ^ 12) ^ (-1 : Int))) =
      ((1 - x) * (1 - x ^ 2) * (1 - x ^ 3)) ^ (-1 : Int) := by
    rw [numerator_factorization]
    simp only [zpow_neg_one]
    field_simp [hne1, hne2, hne3, hne6, hne12]
    ring
  rw [<- heq]
  exact massTerm_hasSum_periods x hx hx1

/-- Native determinant height on the complete residue-period index. -/
def packetHeight (j : MassIndex) : Nat :=
  height j.1.1.val j.1.2.1.val j.1.2.2.val + 5 * height j.2.1 j.2.2.1 j.2.2.2

def packetDegree (j : MassIndex) : Nat :=
  (baseDefect j.1).toNat + 2 * j.2.1 + 6 * j.2.2.1 + 12 * j.2.2.2

theorem massTerm_eq_power (x : Real) (j : MassIndex) (hs : supported j.1) :
    massTerm x j = x ^ packetDegree j := by
  simp [massTerm, baseTerm, periodTerm, packetDegree, hs, pow_add, mul_assoc]

theorem massTerm_nonneg (x : Real) (hx : 0 <= x) (j : MassIndex) :
    0 <= massTerm x j := by
  unfold massTerm baseTerm periodTerm
  split
  next => exact mul_nonneg (pow_nonneg hx _) (pow_nonneg hx _)
  next => simp

theorem packetDegree_bounds (j : MassIndex) (hs : supported j.1)
    (hh : 0 < packetHeight j) :
    1 <= packetDegree j /\ (packetHeight j % 2 = 0 -> 2 <= packetDegree j) := by
  have hb := baseDefect_bounds j.1 hs
  by_cases hz : j.2.1 + j.2.2.1 + j.2.2.2 = 0
  case pos =>
    have ha : j.2.1 = 0 := by omega
    have hc : j.2.2.1 = 0 := by omega
    have hd : j.2.2.2 = 0 := by omega
    have hn : Not (j.1 = (0, 0, 0)) := by
      intro hzero
      simp [packetHeight, hzero, ha, hc, hd, height] at hh
    have hpos := hb.2.1 hn
    constructor
    case left => unfold packetDegree; omega
    case right =>
      intro he
      have he' : height j.1.1.val j.1.2.1.val j.1.2.2.val % 2 = 0 := by
        simpa [packetHeight, ha, hc, hd, height] using he
      have hbound := hb.2.2 hn he'
      unfold packetDegree
      omega
  case neg => unfold packetDegree; omega

def filteredTerm (P : MassIndex -> Prop) [DecidablePred P] (x : Real) (j : MassIndex) : Real :=
  if P j then massTerm x j else 0

private theorem power_mono (x y : Real) (hx : 0 <= x) (hxy : x <= y) (n : Nat) :
    x ^ n <= y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hxy hx (pow_nonneg (le_trans hx hxy) n)

private theorem power_scaling (x r : Real) (hx : 0 <= x) (hxr : x <= r)
    (d k : Nat) (hkd : k <= d) : r ^ k * x ^ d <= x ^ k * r ^ d := by
  have h := power_mono x r hx hxr (d - k)
  have he : d = k + (d - k) := by omega
  rw [he, pow_add, pow_add]
  have hm := mul_le_mul_of_nonneg_left h
    (mul_nonneg (pow_nonneg (le_trans hx hxr) k) (pow_nonneg hx k))
  nlinarith only [hm]

theorem massTerm_hasSum_radius : HasSum (massTerm (3 / 4)) (4096 / 259) := by
  convert massTerm_hasSum (3 / 4) (by norm_num) (by norm_num) using 1
  norm_num

/-- A complete sector bound from its minimum decay degree. The support and
all periodic terms remain present; convergence is supplied by the full series. -/
theorem filtered_mass_bound (P : MassIndex -> Prop) [DecidablePred P]
    (k : Nat) (hdegree : forall j, P j -> supported j.1 -> k <= packetDegree j)
    (x : Real) (hx : 0 <= x) (hxr : x <= 3 / 4) :
    Summable (filteredTerm P x) /\
      (3 / 4 : Real) ^ k * tsum (filteredTerm P x) <= x ^ k * (4096 / 259) := by
  have hx1 : x < 1 := lt_of_le_of_lt hxr (by norm_num)
  have hnn (j : MassIndex) : 0 <= filteredTerm P x j := by
    unfold filteredTerm
    split
    next => exact massTerm_nonneg x hx j
    next => exact le_rfl
  have hle (j : MassIndex) : filteredTerm P x j <= massTerm x j := by
    unfold filteredTerm
    split
    next => exact le_rfl
    next => exact massTerm_nonneg x hx j
  have hs := Summable.of_nonneg_of_le hnn hle (massTerm_hasSum x hx hx1).summable
  refine And.intro hs ?_
  have hc (j : MassIndex) : (3 / 4 : Real) ^ k * filteredTerm P x j <=
      x ^ k * massTerm (3 / 4) j := by
    by_cases hp : P j
    case pos =>
      simp only [filteredTerm, hp, ite_true]
      by_cases ht : supported j.1
      case pos =>
        rw [massTerm_eq_power x j ht, massTerm_eq_power (3 / 4) j ht]
        exact power_scaling x (3 / 4) hx hxr (packetDegree j) k (hdegree j hp ht)
      case neg => simp [massTerm, baseTerm, ht]
    case neg =>
      simp only [filteredTerm, hp, ite_false, mul_zero]
      exact mul_nonneg (pow_nonneg hx k) (massTerm_nonneg (3 / 4) (by norm_num) j)
  have ht := Summable.tsum_le_tsum hc (hs.mul_left ((3 / 4 : Real) ^ k))
    (massTerm_hasSum_radius.summable.mul_left (x ^ k))
  simpa only [tsum_mul_left, massTerm_hasSum_radius.tsum_eq] using ht

/-- The entire odd native-parity mass, with a uniform constant. -/
theorem odd_mass_bound (x : Real) (hx : 0 <= x) (hxr : x <= 3 / 4) :
    Summable (filteredTerm (fun j => packetHeight j % 2 = 1) x) /\
      tsum (filteredTerm (fun j => packetHeight j % 2 = 1) x) <= 29 * x := by
  have h := filtered_mass_bound (fun j => packetHeight j % 2 = 1) 1
    (fun j hj hs => (packetDegree_bounds j hs (by omega)).1) x hx hxr
  refine And.intro h.1 ?_
  have hb := h.2
  norm_num only [pow_one] at hb
  nlinarith

/-- The entire nonconstant even native-parity mass, including square masks. -/
theorem even_mass_bound (x : Real) (hx : 0 <= x) (hxr : x <= 3 / 4) :
    Summable (filteredTerm (fun j => 0 < packetHeight j /\ packetHeight j % 2 = 0) x) /\
      tsum (filteredTerm (fun j => 0 < packetHeight j /\ packetHeight j % 2 = 0) x)
        <= 29 * x ^ 2 := by
  have h := filtered_mass_bound (fun j => 0 < packetHeight j /\ packetHeight j % 2 = 0) 2
    (fun j hj hs => (packetDegree_bounds j hs hj.1).2 hj.2) x hx hxr
  refine And.intro h.1 ?_
  have hb := h.2
  norm_num only [show (3 / 4 : Real) ^ 2 = 9 / 16 by norm_num] at hb
  nlinarith [sq_nonneg x]

/-- The original, unbounded three-coordinate index represented by a packet. -/
def coordinates (j : MassIndex) : Period :=
  (j.1.1.val + 5 * j.2.1,
   j.1.2.1.val + 5 * j.2.2.1,
   j.1.2.2.val + 5 * j.2.2.2)

def packetOf (n : Period) : MassIndex :=
  (residue n.1 n.2.1 n.2.2, n.1 / 5, n.2.1 / 5, n.2.2 / 5)

theorem packetOf_coordinates (j : MassIndex) : packetOf (coordinates j) = j := by
  have ha := j.1.1.isLt
  have hb := j.1.2.1.isLt
  have hc := j.1.2.2.isLt
  simp only [packetOf, coordinates, residue, Prod.ext_iff, Fin.ext_iff, Fin.val_ofNat]
  omega

theorem coordinates_packetOf (n : Period) : coordinates (packetOf n) = n := by
  have ha := Nat.mod_add_div n.1 5
  have hb := Nat.mod_add_div n.2.1 5
  have hc := Nat.mod_add_div n.2.2 5
  simp only [packetOf, coordinates, residue, Prod.ext_iff, Fin.val_ofNat]
  omega

/-- No overlap or omitted natural index in the residue-period expansion. -/
def packetEquiv : Equiv MassIndex Period where
  toFun := coordinates
  invFun := packetOf
  left_inv := packetOf_coordinates
  right_inv := coordinates_packetOf

/-- The complete normalized local coefficient model on its original indices. -/
def localTerm (x : Real) (n : Period) : Real :=
  if supported (residue n.1 n.2.1 n.2.2) then x ^ (defect n.1 n.2.1 n.2.2).toNat else 0

theorem massTerm_packetOf (x : Real) (n : Period) :
    massTerm x (packetOf n) = localTerm x n := by
  by_cases hs : supported (residue n.1 n.2.1 n.2.2)
  case pos =>
    rw [massTerm_eq_power x (packetOf n) hs]
    simp only [localTerm, hs, ite_true]
    congr 1
    have hb := (baseDefect_bounds (residue n.1 n.2.1 n.2.2) hs).1
    rw [defect_decomposition]
    dsimp only [packetDegree, packetOf]
    omega
  case neg => simp [massTerm, baseTerm, packetOf, localTerm, hs]

theorem packetHeight_packetOf (n : Period) :
    packetHeight (packetOf n) = height n.1 n.2.1 n.2.2 := by
  have ha := Nat.mod_add_div n.1 5
  have hb := Nat.mod_add_div n.2.1 5
  have hc := Nat.mod_add_div n.2.2 5
  simp only [packetHeight, packetOf, residue, height, Fin.val_ofNat]
  omega

/-- Convergence and exact sum on all original natural coordinate triples. -/
theorem localTerm_hasSum (x : Real) (hx : 0 <= x) (hx1 : x < 1) :
    HasSum (localTerm x) (((1 - x) * (1 - x ^ 2) * (1 - x ^ 3)) ^ (-1 : Int)) := by
  have h := packetEquiv.symm.hasSum_iff.mpr (massTerm_hasSum x hx hx1)
  apply h.congr_fun
  intro n
  exact (massTerm_packetOf x n).symm

def localFilteredTerm (P : Nat -> Prop) [DecidablePred P] (x : Real) (n : Period) : Real :=
  if P (height n.1 n.2.1 n.2.2) then localTerm x n else 0

private theorem transfer_filtered (P : Nat -> Prop) [DecidablePred P] (x s : Real)
    (h : HasSum (filteredTerm (fun j => P (packetHeight j)) x) s) :
    HasSum (localFilteredTerm P x) s := by
  have ht := packetEquiv.symm.hasSum_iff.mpr h
  apply ht.congr_fun
  intro n
  change localFilteredTerm P x n = filteredTerm (fun j => P (packetHeight j)) x (packetOf n)
  simp only [localFilteredTerm, filteredTerm, packetHeight_packetOf, massTerm_packetOf]

theorem local_odd_mass_bound (x : Real) (hx : 0 <= x) (hxr : x <= 3 / 4) :
    Summable (localFilteredTerm (fun h => h % 2 = 1) x) /\
      tsum (localFilteredTerm (fun h => h % 2 = 1) x) <= 29 * x := by
  have h := odd_mass_bound x hx hxr
  have ht := transfer_filtered (fun h => h % 2 = 1) x _ h.1.hasSum
  refine And.intro ht.summable ?_
  rw [ht.tsum_eq]
  exact h.2

theorem local_even_mass_bound (x : Real) (hx : 0 <= x) (hxr : x <= 3 / 4) :
    Summable (localFilteredTerm (fun h => 0 < h /\ h % 2 = 0) x) /\
      tsum (localFilteredTerm (fun h => 0 < h /\ h % 2 = 0) x) <= 29 * x ^ 2 := by
  have h := even_mass_bound x hx hxr
  have ht := transfer_filtered (fun h => 0 < h /\ h % 2 = 0) x _ h.1.hasSum
  refine And.intro ht.summable ?_
  rw [ht.tsum_eq]
  exact h.2

private theorem inverse_sqrt_radius (q : Real) (hq : 2 <= q) :
    0 <= 1 / Real.sqrt q /\ 1 / Real.sqrt q <= 3 / 4 := by
  have hpos : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  have hs := Real.sq_sqrt (show 0 <= q by linarith)
  have hlow : (4 / 3 : Real) <= Real.sqrt q := by nlinarith
  have hinv : 0 <= 1 / Real.sqrt q := (one_div_pos.mpr hpos).le
  have hprod : (1 / Real.sqrt q) * Real.sqrt q = 1 := by
    field_simp [ne_of_gt hpos]
  refine And.intro hinv ?_
  nlinarith

/-- Uniform odd local mass for every real norm q at least two. -/
theorem local_odd_mass_norm_bound (q : Real) (hq : 2 <= q) :
    Summable (localFilteredTerm (fun h => h % 2 = 1) (1 / Real.sqrt q)) /\
      tsum (localFilteredTerm (fun h => h % 2 = 1) (1 / Real.sqrt q)) <=
        29 / Real.sqrt q := by
  have hr := inverse_sqrt_radius q hq
  simpa only [div_eq_mul_inv, one_mul] using local_odd_mass_bound (1 / Real.sqrt q) hr.1 hr.2

/-- Uniform nonconstant even mass; the square support has not been erased. -/
theorem local_even_mass_norm_bound (q : Real) (hq : 2 <= q) :
    Summable (localFilteredTerm (fun h => 0 < h /\ h % 2 = 0) (1 / Real.sqrt q)) /\
      tsum (localFilteredTerm (fun h => 0 < h /\ h % 2 = 0) (1 / Real.sqrt q)) <= 29 / q := by
  have hr := inverse_sqrt_radius q hq
  have h := local_even_mass_bound (1 / Real.sqrt q) hr.1 hr.2
  have hs : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt (by linarith)
  have heq : 29 * (1 / Real.sqrt q) ^ 2 = 29 / q := by
    rw [div_pow, one_pow, hs]
    ring
  rw [heq] at h
  exact h

end Metaplectic.Quintic
