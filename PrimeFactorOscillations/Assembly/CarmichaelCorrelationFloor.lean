/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelCorrelationLocal

/-!
# A universal lower floor for every odd return-correlation probe

The exact local product is compared with a telescoping product over all
integer positions. No modulus-dependent minimum or prime-base density
hypothesis is used. Odd label packets keep every unit with weight at least one half.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelCorrelationFloor

open CarmichaelCorrelation CarmichaelCorrelationLocal PrimeOrderReturnLaw

theorem localFactor_closed (d : Nat) (hd : 2 <= d) (b : Bool) :
    localFactor d b = 1 + ((if b then (d : Real) else 0) - 1) / ((d : Real) - 1) ^ 2 := by
  have hD : (1 : Real) < d := by exact_mod_cast (show 1 < d by omega)
  have h0 : Not ((d : Real) = 0) := ne_of_gt (zero_lt_one.trans hD)
  have h1 : Not ((d : Real) - 1 = 0) := sub_ne_zero.mpr (ne_of_gt hD)
  cases b <;> simp [localFactor] <;> field_simp [h0, h1] <;> ring

theorem localFactor_lower (d : Nat) (hd : 2 <= d) (b : Bool) :
    1 - 1 / ((d : Real) - 1) ^ 2 <= localFactor d b := by
  rw [localFactor_closed d hd b]
  cases b
  . change 1 - 1 / ((d : Real) - 1) ^ 2 <= 1 + (0 - 1) / ((d : Real) - 1) ^ 2
    ring_nf
    exact le_rfl
  . change 1 - 1 / ((d : Real) - 1) ^ 2 <= 1 + ((d : Real) - 1) / ((d : Real) - 1) ^ 2
    rw [sub_div]
    have h := div_nonneg (Nat.cast_nonneg d) (sq_nonneg ((d : Real) - 1))
    linarith

def telescopeFactor (k : Nat) : Real :=
  1 - 1 / ((k : Real) + 2) ^ 2

theorem telescopeFactor_bounds (k : Nat) :
    And (0 <= telescopeFactor k) (telescopeFactor k <= 1) := by
  have hk : (0 : Real) <= k := Nat.cast_nonneg _
  have hd : 0 < ((k : Real) + 2) ^ 2 := by positivity
  have hden : 1 <= ((k : Real) + 2) ^ 2 := by nlinarith
  have h := (div_le_one hd).mpr hden
  have h0 := div_nonneg (show (0 : Real) <= 1 by norm_num) (sq_nonneg ((k : Real) + 2))
  exact And.intro (by unfold telescopeFactor; linarith) (by unfold telescopeFactor; linarith)

theorem telescope_product (n : Nat) :
    (Finset.range n).prod telescopeFactor = ((n : Real) + 2) / (2 * ((n : Real) + 1)) := by
  induction n with
  | zero => norm_num [telescopeFactor]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    unfold telescopeFactor
    push_cast
    have h1 : Not ((n : Real) + 1 = 0) := by positivity
    have h2 : Not ((n : Real) + 2 = 0) := by positivity
    field_simp [h1, h2]
    ring

theorem telescope_product_ge_half (n : Nat) :
    (1 / 2 : Real) <= (Finset.range n).prod telescopeFactor := by
  rw [telescope_product]
  have h1 : Not ((n : Real) + 1 = 0) := by positivity
  calc
    (1 / 2 : Real) = ((n : Real) + 1) / (2 * ((n : Real) + 1)) := by field_simp
    _ <= _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem product_unit_bounds {I : Type*} (T : Finset I) (f : I -> Real)
    (hf : forall i, Membership.mem T i -> And (0 <= f i) (f i <= 1)) :
    And (0 <= T.prod f) (T.prod f <= 1) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have hp := hf i (Finset.mem_insert_self i T)
    have hr := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi]
    exact And.intro (mul_nonneg hp.1 hr.1)
      (by simpa only [one_mul] using mul_le_mul hp.2 hr.2 hr.1 zero_le_one)

theorem product_mono_nonnegative {I : Type*} (T : Finset I) (f g : I -> Real)
    (hf : forall i, Membership.mem T i -> 0 <= f i)
    (hfg : forall i, Membership.mem T i -> f i <= g i) :
    T.prod f <= T.prod g := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have hfi := hf i (Finset.mem_insert_self i T)
    have hgi := hfg i (Finset.mem_insert_self i T)
    have hRest := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact mul_le_mul hgi hRest
      (Finset.prod_nonneg (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
      (hfi.trans hgi)

theorem product_subset_lower {I : Type*} [DecidableEq I]
    (T R : Finset I) (hSub : T <= R) (f : I -> Real)
    (hf : forall i, Membership.mem R i -> And (0 <= f i) (f i <= 1)) :
    R.prod f <= T.prod f := by
  have hOutside := (product_unit_bounds (SDiff.sdiff R T) f
    (fun i hi => hf i (Finset.mem_sdiff.mp hi).1)).2
  have hInside : 0 <= T.prod f :=
    Finset.prod_nonneg (fun i hi => (hf i (hSub hi)).1)
  calc
    R.prod f = (SDiff.sdiff R T).prod f * T.prod f := (Finset.prod_sdiff hSub).symm
    _ <= 1 * T.prod f := mul_le_mul_of_nonneg_right hOutside hInside
    _ = T.prod f := one_mul _

theorem finite_telescope_floor (T : Finset Nat) :
    (1 / 2 : Real) <= T.prod telescopeFactor := by
  classical
  let n := T.sup id + 1
  have hSub : T <= Finset.range n := by
    intro k hk
    have hTop : k <= T.sup id := Finset.le_sup (f := fun n : Nat => n) hk
    exact Finset.mem_range.mpr (by dsimp [n]; omega)
  exact (telescope_product_ge_half n).trans
    (product_subset_lower T (Finset.range n) hSub telescopeFactor
      (fun k _ => telescopeFactor_bounds k))

theorem localFactor_prime_floor (p : Nat.Primes) (hp : 3 <= (p : Nat))
    (d : Nat) (hd : (p : Nat) <= d) (b : Bool) :
    telescopeFactor ((p : Nat) - 3) <= localFactor d b := by
  have hD : 2 <= d := by omega
  have hpR : (2 : Real) < p := by exact_mod_cast (show 2 < (p : Nat) by omega)
  have hdR : (p : Real) <= d := by exact_mod_cast hd
  have hSq : ((p : Real) - 1) ^ 2 <= ((d : Real) - 1) ^ 2 := by nlinarith
  have hInv := one_div_le_one_div_of_le (sq_pos_of_pos (by linarith : 0 < (p : Real) - 1)) hSq
  have hEq : telescopeFactor ((p : Nat) - 3) = 1 - 1 / ((p : Real) - 1) ^ 2 := by
    unfold telescopeFactor
    rw [Nat.cast_sub hp, Nat.cast_ofNat]
    ring
  rw [hEq]
  exact (sub_le_sub_left hInv 1).trans (localFactor_lower d hD b)

/-- A modulus-uniform floor: no unit can disappear from an odd packet's correlation probe. -/
theorem canonical_odd_kernel_ge_half {G : Type*} [CommGroup G] [Fintype G]
    (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (hOdd : forall p : S, Not ((p.val : Nat) = 2)) (g : G) :
    (1 / 2 : Real) <= kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g := by
  classical
  have hThree (p : S) : 3 <= (p.val : Nat) := by
    have hp := p.val.property.two_le
    have hn := hOdd p
    omega
  let T : Finset Nat := S.image (fun p : Nat.Primes => (p : Nat) - 3)
  have hInj : forall p, Membership.mem S p -> forall q, Membership.mem S q ->
      (p : Nat) - 3 = (q : Nat) - 3 -> p = q := by
    intro p hp q hq hEq
    apply Subtype.ext
    have hp3 := hThree (Subtype.mk p hp)
    have hq3 := hThree (Subtype.mk q hq)
    change 3 <= (p : Nat) at hp3
    change 3 <= (q : Nat) at hq3
    change (p : Nat) = (q : Nat)
    omega
  have hImage : T.prod telescopeFactor =
      S.prod (fun p : Nat.Primes => telescopeFactor ((p : Nat) - 3)) := by
    rw [Finset.prod_image hInj]
  have hAttach : Finset.univ.prod (fun p : S => telescopeFactor ((p.val : Nat) - 3)) =
      T.prod telescopeFactor := by
    rw [hImage]
    exact Finset.prod_attach S (fun p : Nat.Primes => telescopeFactor ((p : Nat) - 3))
  have hLow := (finite_telescope_floor T).trans_eq hAttach.symm
  rw [canonical_kernel_eq_product S hDiv g]
  exact hLow.trans (product_mono_nonnegative Finset.univ
    (fun p : S => telescopeFactor ((p.val : Nat) - 3))
    (fun p : S => localFactor (returnIndex (G := G) (Monoid.exponent G) (p.val : Nat))
      (returnBit (Monoid.exponent G) (p.val : Nat) g))
    (fun p _ => (telescopeFactor_bounds _).1)
    (fun p _ => localFactor_prime_floor p.val (hThree p) _
      (divisor_le_returnIndex (G := G) _ (hDiv p)) _))

/-- Every finite unit sample retains a fixed fraction of its total witness mass. -/
theorem unit_sample_mass_lower {G I : Type*} [CommGroup G] [Fintype G]
    (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (hOdd : forall p : S, Not ((p.val : Nat) = 2))
    (T : Finset I) (u : I -> G) :
    (T.card : Real) / 2 <=
      T.sum (fun i => kernel (vacancyWeight (G := G) (Monoid.exponent G) S) (u i)) := by
  calc
    (T.card : Real) / 2 = T.sum (fun _ : I => (1 / 2 : Real)) := by
      simp [div_eq_mul_inv]
    _ <= _ := Finset.sum_le_sum (fun i _ => canonical_odd_kernel_ge_half S hDiv hOdd (u i))

/-- A common positive excursion survives the full arithmetic weighting. -/
theorem weighted_signal_lower {G I : Type*} [CommGroup G] [Fintype G]
    (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (hOdd : forall p : S, Not ((p.val : Nat) = 2))
    (T : Finset I) (u : I -> G) (z : I -> Real) (B : Real) (hB : 0 <= B)
    (hz : forall i, Membership.mem T i -> B <= z i) :
    B * (T.card : Real) / 2 <=
      T.sum (fun i => kernel (vacancyWeight (G := G) (Monoid.exponent G) S) (u i) * z i) := by
  let K : I -> Real := fun i => kernel (vacancyWeight (G := G) (Monoid.exponent G) S) (u i)
  have hMass := unit_sample_mass_lower S hDiv hOdd T u
  have hPoint (i : I) (hi : Membership.mem T i) : B * K i <= K i * z i := by
    have hK : 0 <= K i := (by norm_num : (0 : Real) <= 1 / 2).trans
      (canonical_odd_kernel_ge_half S hDiv hOdd (u i))
    simpa only [mul_comm B (K i)] using mul_le_mul_of_nonneg_left (hz i hi) hK
  calc
    B * (T.card : Real) / 2 = B * ((T.card : Real) / 2) := by ring
    _ <= B * T.sum K := mul_le_mul_of_nonneg_left hMass hB
    _ = T.sum (fun i => B * K i) := Finset.mul_sum T K B
    _ <= _ := Finset.sum_le_sum hPoint

end PrimeFactorOscillations.CarmichaelCorrelationFloor
