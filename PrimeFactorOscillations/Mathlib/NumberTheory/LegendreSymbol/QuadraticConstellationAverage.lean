/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairEnergy
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPolynomialPairs
/-!
# Exact optimal laws from tagged quadratic constellations

For an arbitrary finite labelled shape, independent scalar tags in the
constant coefficients of actual monic quadratics synthesize the uniform
conditional law on the admissible constants. The linear coefficient is
shared by all members. The proof retains zero tags, repeated shape entries,
and the zero-normalizer case, and works in every odd finite field.

The second moment is the sharp support energy. An exact squared-deviation
identity proves minimality and uniqueness among all real mean-one laws
on the same support. No Hasse bound, RH, CRT limit, or integer
short-window mass estimate is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def quadraticNonsquareCount : Int :=
  Finset.univ.sum (fun x : F => if IsSquare x then 0 else 1)

theorem twice_quadraticNonsquareCount (hF : Not (ringChar F = 2)) :
    2 * quadraticNonsquareCount (F := F) = (Fintype.card F : Int) - 1 := by
  unfold quadraticNonsquareCount
  rw [Finset.mul_sum]
  simp_rw [twice_nonsquare_indicator]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [quadraticChar_sum_zero hF]
  simp

theorem quadraticNonsquareCount_pos (hF : Not (ringChar F = 2)) :
    0 < quadraticNonsquareCount (F := F) := by
  have hc : 2 <= Fintype.card F := by
    have hi := Finset.card_le_card (Finset.subset_univ ({(0 : F), 1} : Finset F))
    simpa using hi
  have hi : (2 : Int) <= (Fintype.card F : Int) := by exact_mod_cast hc
  have hn := twice_quadraticNonsquareCount (F := F) hF
  linarith only [hi, hn]

theorem monicQuadratic_scaled_constant_count (hF : Not (ringChar F = 2))
    (b c : F) :
    (Finset.univ.sum fun t : F =>
      if Irreducible (monicQuadratic b (t * c)) then (1 : Int) else 0) =
        if Not (c = 0) then quadraticNonsquareCount (F := F) else 0 := by
  by_cases hc : c = 0
  . subst c
    have hs : IsSquare (b ^ 2) := Exists.intro b (by ring)
    simp [monicQuadratic_irreducible_iff_nonsquare hF, hs]
  . have hfour : Not ((4 : F) = 0) := by
      have h4 : (4 : F) = (2 : F) ^ 2 := by ring
      rw [h4]
      exact pow_ne_zero 2 (two_ne_zero_of_odd hF)
    have hfc : Not (4 * c = 0) := mul_ne_zero hfour hc
    let e : Equiv F F :=
      { toFun := fun t => b ^ 2 - 4 * (t * c)
        invFun := fun x => (b ^ 2 - x) / (4 * c)
        left_inv := by intro t; field_simp [hfc]; ring
        right_inv := by intro x; field_simp [hfc]; ring }
    simp only [ite_eq_left hc, monicQuadratic_irreducible_iff_nonsquare hF, ite_not]
    change (Finset.univ.sum fun t : F =>
      if IsSquare (e t) then (0 : Int) else 1) = _
    exact Equiv.sum_comp e (fun x : F => if IsSquare x then (0 : Int) else 1)

variable {J : Type*} [Fintype J] [DecidableEq J]

def constellationAdmissible (H : J -> F) : Finset F :=
  Finset.univ.filter (fun c => forall j, Not (c + H j = 0))

omit [DecidableEq J] in
theorem mem_constellationAdmissible (H : J -> F) (c : F) :
    Membership.mem (constellationAdmissible H) c <->
      forall j, Not (c + H j = 0) := by
  simp [constellationAdmissible]

def taggedConstellationCount (H : J -> F) (c : F) : Int :=
  Finset.univ.sum (fun b : F =>
    Finset.univ.sum (fun t : J -> F =>
      if forall j, Irreducible (monicQuadratic b (t j * (c + H j)))
        then 1 else 0))

theorem taggedConstellationCount_eq (hF : Not (ringChar F = 2))
    (H : J -> F) (c : F) :
    taggedConstellationCount H c =
      if Membership.mem (constellationAdmissible H) c
        then (Fintype.card F : Int) *
          quadraticNonsquareCount (F := F) ^ Fintype.card J
        else 0 := by
  have hprod (b : F) :
      (Finset.univ.sum fun t : J -> F =>
        if forall j, Irreducible (monicQuadratic b (t j * (c + H j)))
          then (1 : Int) else 0) =
      if forall j, Not (c + H j = 0)
        then quadraticNonsquareCount (F := F) ^ Fintype.card J else 0 := by
    have hind (t : J -> F) :
        (if forall j, Irreducible (monicQuadratic b (t j * (c + H j)))
          then (1 : Int) else 0) =
        Finset.univ.prod (fun j : J =>
          if Irreducible (monicQuadratic b (t j * (c + H j))) then 1 else 0) := by
      symm
      simpa only [Finset.prod_const_one] using
        (Fintype.prod_ite_zero (p := fun j : J =>
          Irreducible (monicQuadratic b (t j * (c + H j))))
          (f := fun _ : J => (1 : Int)))
    simp_rw [hind]
    rw [<- Fintype.prod_sum (fun (j : J) (s : F) =>
      if Irreducible (monicQuadratic b (s * (c + H j))) then (1 : Int) else 0)]
    simp_rw [monicQuadratic_scaled_constant_count hF]
    rw [Fintype.prod_ite_zero]
    simp only [Finset.prod_const, Finset.card_univ]
  unfold taggedConstellationCount
  simp_rw [hprod]
  simp only [mem_constellationAdmissible]
  split_ifs <;> simp

theorem sum_taggedConstellationCount (hF : Not (ringChar F = 2))
    (H : J -> F) :
    (Finset.univ.sum fun c : F => taggedConstellationCount H c) =
      ((constellationAdmissible H).card : Int) *
        ((Fintype.card F : Int) *
          quadraticNonsquareCount (F := F) ^ Fintype.card J) := by
  simp_rw [taggedConstellationCount_eq hF]
  rw [<- Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hs : Finset.univ.filter (fun c => Membership.mem (constellationAdmissible H) c) =
      constellationAdmissible H := by ext c; simp
  rw [hs]


def flatSupportWeight {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (c : I) : Real :=
  if Membership.mem A c then (Fintype.card I : Real) / (A.card : Real) else 0

theorem sum_supported_constant {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (k : Real) :
    (Finset.univ.sum fun c : I => if Membership.mem A c then k else 0) =
      (A.card : Real) * k := by
  rw [<- Finset.sum_filter]
  have hs : Finset.univ.filter (fun c => Membership.mem A c) = A := by ext c; simp
  rw [hs]
  simp

theorem flatSupportWeight_mean_one {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : A.Nonempty) :
    (1 / (Fintype.card I : Real)) * (Finset.univ.sum (flatSupportWeight A)) = 1 := by
  have ha : 0 < (A.card : Real) := by exact_mod_cast Finset.card_pos.mpr hA
  have hb : (A.card : Real) <= (Fintype.card I : Real) := by
    exact_mod_cast Finset.card_le_univ A
  have hq : 0 < (Fintype.card I : Real) := lt_of_lt_of_le ha hb
  unfold flatSupportWeight
  rw [sum_supported_constant]
  field_simp [ne_of_gt ha, ne_of_gt hq]

theorem flatSupportWeight_energy {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : A.Nonempty) :
    (1 / (Fintype.card I : Real)) *
        (Finset.univ.sum fun c : I => (flatSupportWeight A c) ^ 2) =
      (Fintype.card I : Real) / (A.card : Real) := by
  have ha : 0 < (A.card : Real) := by exact_mod_cast Finset.card_pos.mpr hA
  have hb : (A.card : Real) <= (Fintype.card I : Real) := by
    exact_mod_cast Finset.card_le_univ A
  have hq : 0 < (Fintype.card I : Real) := lt_of_lt_of_le ha hb
  have hp (c : I) :
      (flatSupportWeight A c) ^ 2 =
        if Membership.mem A c then
          ((Fintype.card I : Real) / (A.card : Real)) ^ 2 else 0 := by
    by_cases hc : Membership.mem A c <;> simp [flatSupportWeight, hc]
  simp_rw [hp]
  rw [sum_supported_constant]
  field_simp [ne_of_gt ha, ne_of_gt hq]

theorem supported_energy_identity {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : A.Nonempty) (w : I -> Real)
    (hsupp : forall c, Not (Membership.mem A c) -> w c = 0)
    (hmean : (1 / (Fintype.card I : Real)) * Finset.univ.sum w = 1) :
    (1 / (Fintype.card I : Real)) *
        (Finset.univ.sum fun c : I => (w c) ^ 2) =
      (Fintype.card I : Real) / (A.card : Real) +
        (1 / (Fintype.card I : Real)) *
          (A.sum fun c : I =>
            (w c - (Fintype.card I : Real) / (A.card : Real)) ^ 2) := by
  let q : Real := Fintype.card I
  let a : Real := A.card
  let k : Real := q / a
  have ha : 0 < a := by dsimp [a]; exact_mod_cast Finset.card_pos.mpr hA
  have hb : a <= q := by
    dsimp [a, q]
    exact_mod_cast Finset.card_le_univ A
  have hq : 0 < q := lt_of_lt_of_le ha hb
  have hw : Finset.univ.sum w = q := by
    calc
      _ = q * ((1 / q) * Finset.univ.sum w) := by field_simp [ne_of_gt hq]
      _ = q := by rw [hmean, mul_one]
  have hsw : A.sum w = q := by
    calc
      _ = Finset.univ.sum w :=
        Finset.sum_subset (Finset.subset_univ A) (by intro c _ hc; exact hsupp c hc)
      _ = q := hw
  have hsq : (A.sum fun c => (w c) ^ 2) =
      Finset.univ.sum (fun c => (w c) ^ 2) := by
    apply Finset.sum_subset (Finset.subset_univ A)
    intro c _ hc
    rw [hsupp c hc]
    norm_num
  have hp (c : I) : (w c - k) ^ 2 = (w c) ^ 2 - (2 * k) * w c + k ^ 2 := by ring
  have hexp : (A.sum fun c => (w c - k) ^ 2) =
      (Finset.univ.sum fun c => (w c) ^ 2) - 2 * k * q + a * k ^ 2 := by
    simp_rw [hp]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      <- Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    rw [hsq, hsw]
  change (1 / q) * (Finset.univ.sum fun c : I => (w c) ^ 2) =
    q / a + (1 / q) * (A.sum fun c => (w c - k) ^ 2)
  rw [hexp]
  dsimp [k]
  field_simp [ne_of_gt ha, ne_of_gt hq]
  ring

theorem supported_energy_minimum {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : A.Nonempty) (w : I -> Real)
    (hsupp : forall c, Not (Membership.mem A c) -> w c = 0)
    (hmean : (1 / (Fintype.card I : Real)) * Finset.univ.sum w = 1) :
    (Fintype.card I : Real) / (A.card : Real) <=
      (1 / (Fintype.card I : Real)) *
        (Finset.univ.sum fun c : I => (w c) ^ 2) := by
  rw [supported_energy_identity A hA w hsupp hmean]
  apply le_add_of_nonneg_right
  apply mul_nonneg
  . exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  . exact Finset.sum_nonneg (fun c _ => sq_nonneg _)



theorem sum_taggedConstellationCount_pos_iff (hF : Not (ringChar F = 2))
    (H : J -> F) :
    0 < (Finset.univ.sum fun c : F => taggedConstellationCount H c) <->
      (constellationAdmissible H).Nonempty := by
  rw [sum_taggedConstellationCount hF]
  have hq : 0 < (Fintype.card F : Int) := by exact_mod_cast Fintype.card_pos
  have hn := quadraticNonsquareCount_pos (F := F) hF
  have hk : 0 < (Fintype.card F : Int) *
      quadraticNonsquareCount (F := F) ^ Fintype.card J := mul_pos hq (pow_pos hn _)
  constructor
  . intro hp
    by_contra ha
    have hz : (constellationAdmissible H).card = 0 := by
      simpa only [Finset.card_pos] using Nat.eq_zero_of_not_pos
        (by simpa only [Finset.card_pos] using ha)
    rw [hz] at hp
    norm_num at hp
  . intro ha
    have hc : 0 < ((constellationAdmissible H).card : Int) := by
      exact_mod_cast Finset.card_pos.mpr ha
    exact mul_pos hc hk

def taggedConstellationWeight (H : J -> F) (c : F) : Real :=
  (Fintype.card F : Real) * (taggedConstellationCount H c : Real) /
    ((Finset.univ.sum fun z : F => taggedConstellationCount H z) : Real)

theorem taggedConstellationWeight_eq_flat (hF : Not (ringChar F = 2))
    (H : J -> F) (c : F) :
    taggedConstellationWeight H c = flatSupportWeight (constellationAdmissible H) c := by
  let q : Real := Fintype.card F
  let N : Real := quadraticNonsquareCount (F := F)
  let K : Real := q * N ^ Fintype.card J
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos
  have hn : 0 < N := by
    dsimp [N]
    exact_mod_cast quadraticNonsquareCount_pos (F := F) hF
  have hk : Not (K = 0) := ne_of_gt (mul_pos hq (pow_pos hn _))
  have hcount : (taggedConstellationCount H c : Real) =
      if Membership.mem (constellationAdmissible H) c then K else 0 := by
    rw [taggedConstellationCount_eq hF]
    split_ifs <;> simp [K, q, N]
  have htotal : ((Finset.univ.sum fun z : F => taggedConstellationCount H z) : Real) =
      ((constellationAdmissible H).card : Real) * K := by
    dsimp [K, q, N]
    exact_mod_cast sum_taggedConstellationCount hF H
  unfold taggedConstellationWeight
  rw [hcount, htotal]
  by_cases hc : Membership.mem (constellationAdmissible H) c
  . have ha : 0 < ((constellationAdmissible H).card : Real) := by
      exact_mod_cast Finset.card_pos.mpr (Exists.intro c hc)
    simp only [ite_eq_left hc, flatSupportWeight]
    change q * K / (((constellationAdmissible H).card : Real) * K) =
      q / ((constellationAdmissible H).card : Real)
    field_simp [hk, ne_of_gt ha]
  . simp [hc, flatSupportWeight]

theorem taggedConstellationWeight_mean_one (hF : Not (ringChar F = 2))
    (H : J -> F) (hA : (constellationAdmissible H).Nonempty) :
    (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum (taggedConstellationWeight H)) = 1 := by
  simp_rw [taggedConstellationWeight_eq_flat hF]
  exact flatSupportWeight_mean_one _ hA

theorem taggedConstellationWeight_energy (hF : Not (ringChar F = 2))
    (H : J -> F) (hA : (constellationAdmissible H).Nonempty) :
    (1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F => (taggedConstellationWeight H c) ^ 2) =
      (Fintype.card F : Real) / ((constellationAdmissible H).card : Real) := by
  simp_rw [taggedConstellationWeight_eq_flat hF]
  exact flatSupportWeight_energy _ hA

theorem taggedConstellationWeight_pos_iff (hF : Not (ringChar F = 2))
    (H : J -> F) (c : F) :
    0 < taggedConstellationWeight H c <->
      forall j, Not (c + H j = 0) := by
  rw [taggedConstellationWeight_eq_flat hF]
  by_cases hc : Membership.mem (constellationAdmissible H) c
  . have ha : 0 < ((constellationAdmissible H).card : Real) := by
      exact_mod_cast Finset.card_pos.mpr (Exists.intro c hc)
    have hq : 0 < (Fintype.card F : Real) := by exact_mod_cast Fintype.card_pos
    simp only [flatSupportWeight, ite_eq_left hc]
    exact iff_of_true (div_pos hq ha) ((mem_constellationAdmissible H c).mp hc)
  . have hh : Not (forall j, Not (c + H j = 0)) := by
      intro hp
      exact hc ((mem_constellationAdmissible H c).mpr hp)
    simp [flatSupportWeight, hc, hh]


theorem supported_energy_minimum_iff {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : A.Nonempty) (w : I -> Real)
    (hsupp : forall c, Not (Membership.mem A c) -> w c = 0)
    (hmean : (1 / (Fintype.card I : Real)) * Finset.univ.sum w = 1) :
    (1 / (Fintype.card I : Real)) *
        (Finset.univ.sum fun c : I => (w c) ^ 2) =
      (Fintype.card I : Real) / (A.card : Real) <->
        w = flatSupportWeight A := by
  have ha : 0 < (A.card : Real) := by exact_mod_cast Finset.card_pos.mpr hA
  have hb : (A.card : Real) <= (Fintype.card I : Real) := by
    exact_mod_cast Finset.card_le_univ A
  have hq : 0 < (Fintype.card I : Real) := lt_of_lt_of_le ha hb
  constructor
  . intro he
    have hi := supported_energy_identity A hA w hsupp hmean
    have hz : (1 / (Fintype.card I : Real)) *
        (A.sum fun c : I =>
          (w c - (Fintype.card I : Real) / (A.card : Real)) ^ 2) = 0 := by
      linarith only [hi, he]
    have hs : (A.sum fun c : I =>
        (w c - (Fintype.card I : Real) / (A.card : Real)) ^ 2) = 0 :=
      (mul_eq_zero.mp hz).resolve_left (div_ne_zero one_ne_zero (ne_of_gt hq))
    apply funext
    intro c
    by_cases hc : Membership.mem A c
    . have hle := Finset.single_le_sum (fun z (_ : Membership.mem A z) =>
        sq_nonneg (w z - (Fintype.card I : Real) / (A.card : Real))) hc
      rw [hs] at hle
      have heq : w c - (Fintype.card I : Real) / (A.card : Real) = 0 :=
        sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
      simpa [flatSupportWeight, hc] using sub_eq_zero.mp heq
    . simpa [flatSupportWeight, hc] using hsupp c hc
  . intro he
    rw [he, flatSupportWeight_energy A hA]

theorem constellationAdmissible_eq_compl
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {J : Type*} [Fintype J] [DecidableEq J] (H : J -> F) :
    constellationAdmissible H =
      Compl.compl (Finset.univ.image (fun j : J => -H j)) := by
  ext c
  rw [mem_constellationAdmissible, Finset.mem_compl]
  constructor
  . intro hc hm
    choose j hj using Finset.mem_image.mp hm
    apply hc j
    rw [<- hj.2]
    ring
  . intro hc j hz
    apply hc
    apply Finset.mem_image.mpr
    refine Exists.intro j (And.intro (Finset.mem_univ j) ?_)
    calc
      -H j = (c + H j) - H j := by rw [hz]; ring
      _ = c := by ring

theorem card_constellationAdmissible
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {J : Type*} [Fintype J] [DecidableEq J] (H : J -> F) :
    (constellationAdmissible H).card =
      Fintype.card F - (Finset.univ.image (fun j : J => -H j)).card := by
  rw [constellationAdmissible_eq_compl, Finset.card_compl]

theorem taggedConstellationWeight_minimum
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {J : Type*} [Fintype J] [DecidableEq J]
    (hF : Not (ringChar F = 2)) (H : J -> F)
    (hA : (constellationAdmissible H).Nonempty) (w : F -> Real)
    (hsupp : forall c, Not (Membership.mem (constellationAdmissible H) c) -> w c = 0)
    (hmean : (1 / (Fintype.card F : Real)) * Finset.univ.sum w = 1) :
    (1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F => (taggedConstellationWeight H c) ^ 2) <=
      (1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F => (w c) ^ 2) /\
    ((1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F => (w c) ^ 2) =
      (1 / (Fintype.card F : Real)) *
        (Finset.univ.sum fun c : F => (taggedConstellationWeight H c) ^ 2) <->
      w = taggedConstellationWeight H) := by
  have hfun : taggedConstellationWeight H =
      flatSupportWeight (constellationAdmissible H) :=
    funext (taggedConstellationWeight_eq_flat hF H)
  rw [taggedConstellationWeight_energy hF H hA, hfun]
  exact And.intro (supported_energy_minimum _ hA w hsupp hmean)
    (supported_energy_minimum_iff _ hA w hsupp hmean)

theorem tagged_constellation_packet_mean_one
    {I : Type*} [Fintype I] [DecidableEq I]
    (K : I -> Type*) [forall i, Field (K i)] [forall i, Fintype (K i)]
    [forall i, DecidableEq (K i)]
    (J : I -> Type*) [forall i, Fintype (J i)] [forall i, DecidableEq (J i)]
    (H : (i : I) -> J i -> K i)
    (hodd : forall i, Not (ringChar (K i) = 2))
    (hA : forall i, (constellationAdmissible (H i)).Nonempty) :
    (Finset.univ.prod fun i : I => 1 / (Fintype.card (K i) : Real)) *
      (Finset.univ.sum fun x : (i : I) -> K i =>
        Finset.univ.prod fun i : I => taggedConstellationWeight (H i) (x i)) = 1 := by
  rw [<- Fintype.prod_sum (fun (i : I) (c : K i) =>
    taggedConstellationWeight (H i) c), <- Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  exact taggedConstellationWeight_mean_one (hodd i) (H i) (hA i)

theorem tagged_constellation_packet_energy
    {I : Type*} [Fintype I] [DecidableEq I]
    (K : I -> Type*) [forall i, Field (K i)] [forall i, Fintype (K i)]
    [forall i, DecidableEq (K i)]
    (J : I -> Type*) [forall i, Fintype (J i)] [forall i, DecidableEq (J i)]
    (H : (i : I) -> J i -> K i)
    (hodd : forall i, Not (ringChar (K i) = 2))
    (hA : forall i, (constellationAdmissible (H i)).Nonempty) :
    (Finset.univ.prod fun i : I => 1 / (Fintype.card (K i) : Real)) *
      (Finset.univ.sum fun x : (i : I) -> K i =>
        (Finset.univ.prod fun i : I => taggedConstellationWeight (H i) (x i)) ^ 2) =
      Finset.univ.prod (fun i : I =>
        (Fintype.card (K i) : Real) / ((constellationAdmissible (H i)).card : Real)) := by
  rw [QuadraticPairEnergy.product_space_energy K
    (fun i c => taggedConstellationWeight (H i) c)]
  apply Finset.prod_congr rfl
  intro i _
  exact taggedConstellationWeight_energy (hodd i) (H i) (hA i)

theorem tagged_constellation_packet_eq_flat
    {I : Type*} [Fintype I] [DecidableEq I]
    (K : I -> Type*) [forall i, Field (K i)] [forall i, Fintype (K i)]
    [forall i, DecidableEq (K i)]
    (J : I -> Type*) [forall i, Fintype (J i)] [forall i, DecidableEq (J i)]
    (H : (i : I) -> J i -> K i)
    (hodd : forall i, Not (ringChar (K i) = 2))
    (x : (i : I) -> K i) :
    (Finset.univ.prod fun i : I => taggedConstellationWeight (H i) (x i)) =
      if forall i, forall j, Not (x i + H i j = 0)
        then Finset.univ.prod (fun i : I =>
          (Fintype.card (K i) : Real) / ((constellationAdmissible (H i)).card : Real))
        else 0 := by
  calc
    _ = Finset.univ.prod (fun i : I =>
        flatSupportWeight (constellationAdmissible (H i)) (x i)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact taggedConstellationWeight_eq_flat (hodd i) (H i) (x i)
    _ = _ := by
      unfold flatSupportWeight
      rw [Fintype.prod_ite_zero]
      simp only [mem_constellationAdmissible]

end FiniteField
