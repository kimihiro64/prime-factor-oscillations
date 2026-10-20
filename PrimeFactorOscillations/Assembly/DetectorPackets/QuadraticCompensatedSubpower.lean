/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticCompensatedEstimate

/-!
# QuadraticCompensatedSubpower

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

namespace PrimeFactorOscillations.QuadraticCompensatedSubpower

open QuadraticCarrierPacket QuadraticCoprimeMean IntegerQuadraticPrefix
open QuadraticDivisorMean QuadraticBoundaryMean QuadraticMainTermCancellation
open QuadraticPrincipalBoundary QuadraticCompensatedEstimate

theorem powerset_card_le_divisors (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p) :
    G.powerset.card <= (subsetProduct G).divisors.card := by
  have hOne : forall p, Membership.mem G p -> 1 <= p :=
    fun p hp => (hG p hp).one_le
  have hd : 0 < subsetProduct G :=
    subsetProduct_one_le G G hOne (Finset.mem_powerset.mpr (fun _ h => h))
  apply Finset.card_le_card_of_injOn subsetProduct
  . intro D hD
    apply Nat.mem_divisors.mpr
    refine And.intro ?_ (Nat.ne_of_gt hd)
    exact Finset.prod_dvd_prod_of_subset D G id (Finset.mem_powerset.mp hD)
  . intro D hD E hE hDE
    have hpD : (subsetProduct D).primeFactors = D :=
      Nat.primeFactors_prod (fun p hp => hG p ((Finset.mem_powerset.mp hD) hp))
    have hpE : (subsetProduct E).primeFactors = E :=
      Nat.primeFactors_prod (fun p hp => hG p ((Finset.mem_powerset.mp hE) hp))
    have h := congrArg Nat.primeFactors hDE
    simpa only [hpD, hpE] using h

theorem tag_count_subpower (eps : Real) (heps : 0 < eps) :
    exists A : Real, 0 < A /\
      forall (G : Finset Nat),
      (forall p, Membership.mem G p -> Nat.Prime p) ->
      (G.powerset.card : Real) ^ 2 + (G.powerset.card : Real) <=
        A * (subsetProduct G : Real) ^ eps := by
  choose C hC hc using divisor_card_subpower (eps / 2) (by linarith)
  refine Exists.intro (2 * C ^ 2) (And.intro (by positivity) ?_)
  intro G hG
  have hd : 0 < subsetProduct G :=
    subsetProduct_one_le G G (fun p hp => (hG p hp).one_le)
      (Finset.mem_powerset.mpr (fun _ h => h))
  have hdR : 0 < (subsetProduct G : Real) := by exact_mod_cast hd
  have hcard : (G.powerset.card : Real) <=
      C * (subsetProduct G : Real) ^ (eps / 2) :=
    (Nat.cast_le.mpr (powerset_card_le_divisors G hG)).trans (hc _ hd)
  have hpN : 0 < G.powerset.card :=
    Finset.card_pos.mpr (Exists.intro (EmptyCollection.emptyCollection : Finset Nat)
      (Finset.mem_powerset.mpr (Finset.empty_subset G)))
  have hp : (1 : Real) <= (G.powerset.card : Real) := by
    exact_mod_cast (show 1 <= G.powerset.card from hpN)
  have ht : ((subsetProduct G : Real) ^ (eps / 2)) ^ 2 =
      (subsetProduct G : Real) ^ eps := by
    rw [sq, <- Real.rpow_add hdR]
    congr 1
    ring
  have hsquare : (G.powerset.card : Real) ^ 2 <=
      C ^ 2 * (subsetProduct G : Real) ^ eps := by
    calc
      _ <= (C * (subsetProduct G : Real) ^ (eps / 2)) ^ 2 := by
        simpa only [sq] using
          (mul_self_le_mul_self (show (0 : Real) <= (G.powerset.card : Real) by positivity) hcard)
      _ = _ := by rw [mul_pow, ht]
  calc
    _ <= 2 * (G.powerset.card : Real) ^ 2 := by nlinarith
    _ <= 2 * (C ^ 2 * (subsetProduct G : Real) ^ eps) :=
      mul_le_mul_of_nonneg_left hsquare (by norm_num)
    _ = _ := by ring

theorem compensated_main_subpower (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (G V : Finset Nat) (K N1 N2 : Nat)
        (S T : Finset Nat) (a b : Nat -> Complex),
      0 < K ->
      (forall p, Membership.mem G p -> Nat.Prime p /\ Odd p) ->
      (forall v, Membership.mem V v ->
        0 < v /\ Odd v /\ Squarefree v /\ Nat.Coprime v (subsetProduct G)) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      norm (alpha G V K (weightedForm S T a b) -
        beta G V K (weightedForm S T a b)) <=
        C * (subsetProduct G : Real) ^ eps *
          ((max N1 N2 : Nat) : Real) ^ eps * (1 / Real.sqrt (K : Real)) *
            meanCap (K * (subsetProduct G) ^ 2) N1 N2 S T a b := by
  choose A hA ha using tag_count_subpower eps heps
  choose C hC hc using compensated_main_bound eps heps
  refine Exists.intro (A * C) (And.intro (mul_pos hA hC) ?_)
  intro G V K N1 N2 S T a b hK hG hV hS hT
  let L := (1 / Real.sqrt (K : Real)) *
    (C * ((max N1 N2 : Nat) : Real) ^ eps *
      meanCap (K * (subsetProduct G) ^ 2) N1 N2 S T a b)
  have hL : 0 <= L := by
    dsimp only [L, meanCap]
    positivity
  have hcount := ha G (fun p hp => (hG p hp).1)
  calc
    _ <= ((G.powerset.card : Real) ^ 2 + (G.powerset.card : Real)) * L :=
      hc G V K N1 N2 S T a b hK hG hV hS hT
    _ <= (A * (subsetProduct G : Real) ^ eps) * L :=
      mul_le_mul_of_nonneg_right hcount hL
    _ = _ := by dsimp only [L]; ring

theorem meanCap_adjoint (M N : Nat) (S : Finset Nat) (a : Nat -> Complex) :
    meanCap M N N S S a (fun n => star (a n)) =
      prefixNorm M N * S.sum (fun n => norm (a n) ^ 2) := by
  have hstar : maskedMass 1 S (fun n => star (a n)) = maskedMass 1 S a := by
    unfold maskedMass
    simp only [norm_star]
  have hB : 0 <= prefixNorm M N := by
    unfold prefixNorm
    exact sq_nonneg _
  unfold meanCap
  rw [hstar, Real.mul_self_sqrt (mul_nonneg hB (maskedMass_nonneg 1 S a))]
  congr 1
  simp only [maskedMass, Nat.one_dvd, ite_true]

theorem arithmetic_principal_difference (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (G V : Finset Nat) (K N : Nat)
        (S : Finset Nat) (a : Nat -> Complex),
      0 < K ->
      (forall p, Membership.mem G p -> Nat.Prime p /\ Odd p) ->
      (forall v, Membership.mem V v ->
        0 < v /\ Odd v /\ Squarefree v /\ Nat.Coprime v (subsetProduct G)) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N) n) ->
      norm (arithmeticAlpha G V K (weightedForm S S a (fun n => star (a n))) -
        arithmeticBeta G V K (weightedForm S S a (fun n => star (a n)))) <=
        C * (subsetProduct G : Real) ^ eps * (N : Real) ^ eps *
          (1 / Real.sqrt (K : Real)) *
            (prefixNorm (K * (subsetProduct G) ^ 2) N *
              S.sum (fun n => norm (a n) ^ 2)) := by
  choose C hC hc using compensated_main_subpower eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro G V K N S a hK hG hV hS
  rw [arithmeticAlpha_eq G V K (fun p hp => (hG p hp).1),
    arithmeticBeta_eq G V K (fun p hp => (hG p hp).1)]
  simpa only [max_self, meanCap_adjoint] using
    hc G V K N N S S a (fun n => star (a n)) hK hG hV hS hS

end PrimeFactorOscillations.QuadraticCompensatedSubpower
