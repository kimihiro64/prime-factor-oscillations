/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.RamanujanProductEnergy

/-!
# RamanujanWeightedPhysical

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

set_option maxHeartbeats 2200000

noncomputable section
namespace OAI.SevenEighths.RamanujanIncidenceGram
open scoped Classical BigOperators
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "PairId" => Prod Id Id

theorem rectangular_pair_count (P : Finset PairId) (U B : Real)
    (hU : 1 <= U) (hB : 1 <= B)
    (hP : forall p, Membership.mem P p ->
      Not (p.1 = 0) /\ Not (p.2 = 0) /\
      (p.1.absNorm : Real) <= U /\ (p.2.absNorm : Real) <= B) :
    (P.card : Real) <= 16384 * U * B := by
  let A := P.image Prod.fst
  let D := P.image Prod.snd
  have hsub : forall p, Membership.mem P p -> Membership.mem (A.product D) p := by
    intro p hp
    exact Finset.mem_product.mpr (And.intro
      (Finset.mem_image_of_mem Prod.fst hp)
      (Finset.mem_image_of_mem Prod.snd hp))
  have hA : (A.card : Real) <= 128 * U := by
    apply DescentFiberCost.finite_ideal_count_real A U hU
    . intro I hI
      choose p hp he using Finset.mem_image.mp hI
      simpa only [<-he, Ideal.zero_eq_bot] using (hP p hp).1
    . intro I hI
      choose p hp he using Finset.mem_image.mp hI
      simpa only [<-he] using (hP p hp).2.2.1
  have hD : (D.card : Real) <= 128 * B := by
    apply DescentFiberCost.finite_ideal_count_real D B hB
    . intro I hI
      choose p hp he using Finset.mem_image.mp hI
      simpa only [<-he, Ideal.zero_eq_bot] using (hP p hp).2.1
    . intro I hI
      choose p hp he using Finset.mem_image.mp hI
      simpa only [<-he] using (hP p hp).2.2.2
  have hc : (P.card : Real) <= (A.card : Real) * (D.card : Real) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product A D)
  have hh := mul_le_mul hA hD (Nat.cast_nonneg D.card) (by positivity)
  nlinarith

theorem dyadic_coefficient_mass (P : Finset PairId) (U B : Real)
    (hU : 1 <= U) (hB : 1 <= B)
    (hP : forall p, Membership.mem P p ->
      Not (p.1 = 0) /\ Not (p.2 = 0) /\
      (p.1.absNorm : Real) <= U /\ (p.2.absNorm : Real) <= B)
    (hlower : forall p, Membership.mem P p ->
      U / 2 <= (p.1.absNorm : Real) /\ B / 2 <= (p.2.absNorm : Real))
    (amplitude : P -> Complex) (ha : forall p, norm (amplitude p) <= 1) :
    (Finset.univ.sum fun p : P =>
      norm (amplitude p /
        ((Real.sqrt (p.val.1.absNorm : Real) : Complex) *
          (p.val.2.absNorm : Complex))) ^ 2) <= 131072 / B := by
  have hU0 : Not (U = 0) := ne_of_gt (lt_of_lt_of_le zero_lt_one hU)
  have hB0 : Not (B = 0) := ne_of_gt (lt_of_lt_of_le zero_lt_one hB)
  have hpoint (p : P) :
      norm (amplitude p /
        ((Real.sqrt (p.val.1.absNorm : Real) : Complex) *
          (p.val.2.absNorm : Complex))) ^ 2 <= 8 / (U * B ^ 2) := by
    have hi := (hlower p.val p.property).1
    have hj := (hlower p.val p.property).2
    have hI0 : 0 <= (p.val.1.absNorm : Real) := Nat.cast_nonneg _
    have hJ0 : 0 <= (p.val.2.absNorm : Real) := Nat.cast_nonneg _
    have hJ2 : (B / 2) ^ 2 <= (p.val.2.absNorm : Real) ^ 2 := by
      have hh := mul_le_mul hj hj (by positivity : 0 <= B / 2) hJ0
      simpa only [pow_two] using hh
    have hden := mul_le_mul hi hJ2 (sq_nonneg (B / 2)) hI0
    have hb0 : 0 < U / 2 * (B / 2) ^ 2 := by positivity
    have hn : norm (amplitude p) ^ 2 <= 1 := by
      nlinarith [ha p, norm_nonneg (amplitude p)]
    have hs : norm (amplitude p /
        ((Real.sqrt (p.val.1.absNorm : Real) : Complex) *
          (p.val.2.absNorm : Complex))) ^ 2 =
        norm (amplitude p) ^ 2 /
          ((p.val.1.absNorm : Real) * (p.val.2.absNorm : Real) ^ 2) := by
      rw [norm_div, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), Complex.norm_natCast,
        div_pow, mul_pow, Real.sq_sqrt hI0]
    rw [hs]
    calc
      _ <= 1 / ((p.val.1.absNorm : Real) * (p.val.2.absNorm : Real) ^ 2) :=
        div_le_div_of_nonneg_right hn (by positivity)
      _ <= 1 / (U / 2 * (B / 2) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) hb0 hden
      _ = 8 / (U * B ^ 2) := by field_simp [hU0, hB0]; ring
  have hsum := Finset.sum_le_sum (fun p (_ : Membership.mem Finset.univ p) => hpoint p)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_coe] at hsum
  have hc := rectangular_pair_count P U B hU hB hP
  have hh := mul_le_mul_of_nonneg_right hc
    (by positivity : 0 <= 8 / (U * B ^ 2))
  have he : (16384 * U * B) * (8 / (U * B ^ 2)) = 131072 / B := by
    field_simp [hU0, hB0]
    ring
  exact hsum.trans (hh.trans_eq he)

theorem weighted_fourth_energy (eps : Real) (heps : 0 < eps) :
    Exists fun K : Real => 0 < K /\
    forall (P : Finset PairId) (C : Finset Id) (U B Q : Real),
    1 <= U -> 1 <= B -> 1 <= Q ->
    (forall p, Membership.mem P p ->
      Not (p.1 = 0) /\ Not (p.2 = 0) /\
      (p.1.absNorm : Real) <= U /\ (p.2.absNorm : Real) <= B) ->
    (forall p, Membership.mem P p ->
      U / 2 <= (p.1.absNorm : Real) /\ B / 2 <= (p.2.absNorm : Real)) ->
    (forall q, Membership.mem C q -> Squarefree q /\ (q.absNorm : Real) <= Q) ->
    forall (phase : P -> C -> Complex), (forall p q, norm (phase p q) <= 1) ->
    forall (amplitude : P -> Complex), (forall p, norm (amplitude p) <= 1) ->
    (Finset.univ.sum fun q : C =>
      norm (Finset.univ.sum fun p : P =>
        phase p q * fourthPacket (p.val.1 * p.val.2 ^ 3) q.val *
          (amplitude p / ((Real.sqrt (p.val.1.absNorm : Real) : Complex) *
            (p.val.2.absNorm : Complex)))) ^ 2) <=
      K * U * (U * B * Q) ^ eps := by
  choose K hK hb using fourth_product_dual_energy eps heps
  refine Exists.intro (131072 * K) (And.intro (by positivity) ?_)
  intro P C U B Q hU hB hQ hP hlower hC phase hp amplitude ha
  have hB0 : Not (B = 0) := ne_of_gt (lt_of_lt_of_le zero_lt_one hB)
  have hmass := dyadic_coefficient_mass P U B hU hB hP hlower amplitude ha
  have he := hb P C U B Q hU hB hQ hP hC phase hp
    (fun p => amplitude p / ((Real.sqrt (p.val.1.absNorm : Real) : Complex) *
      (p.val.2.absNorm : Complex)))
  have hh := mul_le_mul_of_nonneg_left hmass
    (by positivity : 0 <= K * (U * B) * (U * B * Q) ^ eps)
  have hx : K * (U * B) * (U * B * Q) ^ eps * (131072 / B) =
      (131072 * K) * U * (U * B * Q) ^ eps := by
    field_simp [hB0]
  exact he.trans (hh.trans_eq hx)

theorem weighted_fourth_mean (eps : Real) (heps : 0 < eps) :
    Exists fun K : Real => 0 < K /\
    forall (P : Finset PairId) (C : Finset Id) (U B Q : Real),
    1 <= U -> 1 <= B -> 1 <= Q ->
    (forall p, Membership.mem P p ->
      Not (p.1 = 0) /\ Not (p.2 = 0) /\
      (p.1.absNorm : Real) <= U /\ (p.2.absNorm : Real) <= B) ->
    (forall p, Membership.mem P p ->
      U / 2 <= (p.1.absNorm : Real) /\ B / 2 <= (p.2.absNorm : Real)) ->
    (forall q, Membership.mem C q -> Squarefree q /\ (q.absNorm : Real) <= Q) ->
    forall (phase : P -> C -> Complex), (forall p q, norm (phase p q) <= 1) ->
    forall (amplitude : P -> Complex), (forall p, norm (amplitude p) <= 1) ->
    norm ((Finset.univ.sum fun q : C =>
      (Finset.univ.sum fun p : P =>
        phase p q * fourthPacket (p.val.1 * p.val.2 ^ 3) q.val *
          (amplitude p / ((Real.sqrt (p.val.1.absNorm : Real) : Complex) *
            (p.val.2.absNorm : Complex))))) / (Q : Complex)) ^ 2 <=
      K * (U / Q) * (U * B * Q) ^ eps := by
  choose K hK hb using weighted_fourth_energy eps heps
  refine Exists.intro (128 * K) (And.intro (by positivity) ?_)
  intro P C U B Q hU hB hQ hP hlower hC phase hp amplitude ha
  have hQ0 : Not (Q = 0) := ne_of_gt (lt_of_lt_of_le zero_lt_one hQ)
  let v : C -> Complex := fun q =>
    Finset.univ.sum fun p : P =>
      phase p q * fourthPacket (p.val.1 * p.val.2 ^ 3) q.val *
        (amplitude p / ((Real.sqrt (p.val.1.absNorm : Real) : Complex) *
          (p.val.2.absNorm : Complex)))
  have hv : (Finset.univ.sum fun q : C => norm (v q) ^ 2) <=
      K * U * (U * B * Q) ^ eps :=
    hb P C U B Q hU hB hQ hP hlower hC phase hp amplitude ha
  have hc : (C.card : Real) <= 128 * Q := by
    apply DescentFiberCost.finite_ideal_count_real C Q hQ
    . intro q hq
      simpa only [Ideal.zero_eq_bot] using (hC q hq).1.ne_zero
    . exact fun q hq => (hC q hq).2
  have hcs : norm (Finset.univ.sum v) ^ 2 <=
      (C.card : Real) * (Finset.univ.sum fun q : C => norm (v q) ^ 2) := by
    have hnorm := norm_sum_le Finset.univ v
    have hs0 : 0 <= (Finset.univ.sum fun q : C => norm (v q)) :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsq : norm (Finset.univ.sum v) ^ 2 <=
        (Finset.univ.sum fun q : C => norm (v q)) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hnorm hnorm (norm_nonneg _) hs0
    have he := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : C => (1 : Real)) (fun q => norm (v q))
    have he' : (Finset.univ.sum fun q : C => norm (v q)) ^ 2 <=
        (C.card : Real) * (Finset.univ.sum fun q : C => norm (v q) ^ 2) := by
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, Fintype.card_coe] using he
    exact hsq.trans he'
  have hh := mul_le_mul hc hv
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (by positivity : 0 <= 128 * Q)
  have he : norm (Finset.univ.sum v / (Q : Complex)) ^ 2 =
      norm (Finset.univ.sum v) ^ 2 / Q ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_pow]
  change norm (Finset.univ.sum v / (Q : Complex)) ^ 2 <= _
  rw [he]
  calc
    _ <= ((128 * Q) * (K * U * (U * B * Q) ^ eps)) / Q ^ 2 :=
      div_le_div_of_nonneg_right (hcs.trans hh) (sq_nonneg Q)
    _ = _ := by field_simp [hQ0]

end OAI.SevenEighths.RamanujanIncidenceGram
