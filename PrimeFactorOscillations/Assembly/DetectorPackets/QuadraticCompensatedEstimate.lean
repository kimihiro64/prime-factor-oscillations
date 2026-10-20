/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticPrincipalBoundary

/-!
# QuadraticCompensatedEstimate

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

namespace PrimeFactorOscillations.QuadraticCompensatedEstimate

open QuadraticCarrierPacket QuadraticCoprimeMean IntegerQuadraticPrefix
open QuadraticDivisorMean QuadraticBoundaryMean QuadraticMainTermCancellation
open QuadraticPrincipalBoundary

def boundaryRowSum (G V : Finset Nat) (K q : Nat) (D : Finset Nat)
    (P : Nat -> Prop) (S T : Finset Nat) (a b : Nat -> Complex) : Complex :=
  V.sum (fun v => if P v then
    boundaryWeight G K (weightedForm S T a b) (q ^ 2 * (subsetProduct D * v)) else 0)

theorem boundary_tag_bound (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (G V : Finset Nat) (K N1 N2 q : Nat) (D : Finset Nat)
        (P : Nat -> Prop) (S T : Finset Nat) (a b : Nat -> Complex),
      0 < K -> 1 <= q -> D <= G ->
      (forall p, Membership.mem G p -> Nat.Prime p /\ Odd p) ->
      (forall v, Membership.mem V v ->
        0 < v /\ Odd v /\ Squarefree v /\ Nat.Coprime v (subsetProduct G)) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      norm (boundaryRowSum G V K q D P S T a b) <=
        (1 / Real.sqrt (K : Real)) *
          (C * ((max N1 N2 : Nat) : Real) ^ eps *
            meanCap (K * (subsetProduct G) ^ 2) N1 N2 S T a b) := by
  choose C hC hc using weighted_tag_mean eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro G V K N1 N2 q D P S T a b hK hq hDG hG hV hS hT
  let M := K * (subsetProduct G) ^ 2
  let F := V.filter (fun v => P v /\
    K < q ^ 2 * (subsetProduct D * v) /\ q ^ 2 * (subsetProduct D * v) <= M)
  have heq : boundaryRowSum G V K q D P S T a b =
      F.sum (fun v => weightedForm S T a b (q ^ 2 * (subsetProduct D * v))) := by
    unfold boundaryRowSum
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    unfold boundaryWeight
    dsimp only [M]
    by_cases hPv : P v
    case pos =>
      rw [ite_eq_left hPv]
      by_cases hW : K < q ^ 2 * (subsetProduct D * v) /\
          q ^ 2 * (subsetProduct D * v) <= K * (subsetProduct G) ^ 2
      case pos =>
        rw [ite_eq_left hW, ite_eq_left (And.intro hPv hW)]
      case neg =>
        rw [ite_eq_right hW, ite_eq_right (fun h => hW h.2)]
    case neg =>
      rw [ite_eq_right hPv, ite_eq_right (fun h => hPv h.1)]
  have hd : 0 < subsetProduct D :=
    subsetProduct_one_le G D (fun p hp => (hG p hp).1.one_le) (Finset.mem_powerset.mpr hDG)
  have hq2 : 1 <= q ^ 2 := by nlinarith
  have hrows : forall v, Membership.mem F v ->
      Membership.mem (columns M) (subsetProduct D * v) := by
    intro v hv
    have h := Finset.mem_filter.mp hv
    have hup : subsetProduct D * v <= M := by
      calc
        _ = 1 * (subsetProduct D * v) := by ring
        _ <= q ^ 2 * (subsetProduct D * v) := Nat.mul_le_mul_right _ hq2
        _ <= M := h.2.2.2
    exact lifted_columns G D hDG hG M v (hV v h.1) hup
  have hfreq : forall v, Membership.mem F v -> K <= q ^ 2 * (subsetProduct D * v) := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2.2.1.le
  have hb := hc M N1 N2 K q (subsetProduct D) hK hd F S T a b hrows hfreq hS hT
  rw [heq]
  exact (norm_sum_le _ _).trans hb

theorem alpha_reordered (G V : Finset Nat) (K : Nat) (f : Nat -> Complex) :
    alpha G V K f = G.powerset.sum (fun E => G.powerset.sum (fun B =>
      V.sum (fun v => if subsetProduct B * v <= K then
        (-1 : Complex) ^ E.card * f (subsetProduct E * subsetProduct B * v) else 0))) := by
  unfold alpha
  rw [Finset.sum_comm (s := V) (t := G.powerset)]
  apply Finset.sum_congr rfl
  intro E hE
  exact Finset.sum_comm

theorem beta_reordered (G V : Finset Nat) (K : Nat) (f : Nat -> Complex) :
    beta G V K f = G.powerset.sum (fun D =>
      V.sum (fun v => if v <= K then
        (-1 : Complex) ^ D.card * f ((subsetProduct D) ^ 2 * v) else 0)) := by
  unfold beta
  exact Finset.sum_comm

theorem scalar_filter_sum (V : Finset Nat) (P : Nat -> Prop) (c : Complex)
    (f : Nat -> Complex) :
    V.sum (fun v => if P v then c * f v else 0) =
      c * V.sum (fun v => if P v then f v else 0) := by
  simp only [Finset.mul_sum, mul_ite, mul_zero]

theorem compensated_main_bound (eps : Real) (heps : 0 < eps) :
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
        (((G.powerset.card : Nat) : Real) ^ 2 + (G.powerset.card : Real)) *
          ((1 / Real.sqrt (K : Real)) *
            (C * ((max N1 N2 : Nat) : Real) ^ eps *
              meanCap (K * (subsetProduct G) ^ 2) N1 N2 S T a b)) := by
  choose C hC hc using boundary_tag_bound eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro G V K N1 N2 S T a b hK hG hV hS hT
  let f := boundaryWeight G K (weightedForm S T a b)
  let L := (1 / Real.sqrt (K : Real)) *
    (C * ((max N1 N2 : Nat) : Real) ^ eps *
      meanCap (K * (subsetProduct G) ^ 2) N1 N2 S T a b)
  let atag := fun E B : Finset Nat =>
    V.sum (fun v => if subsetProduct B * v <= K then
      (-1 : Complex) ^ E.card * f (subsetProduct E * subsetProduct B * v) else 0)
  let btag := fun D : Finset Nat =>
    V.sum (fun v => if v <= K then
      (-1 : Complex) ^ D.card * f ((subsetProduct D) ^ 2 * v) else 0)
  have hOne : forall p, Membership.mem G p -> 1 <= p :=
    fun p hp => (hG p hp).1.one_le
  have hAlphaTag (E B : Finset Nat)
      (he : Membership.mem G.powerset E) (hb : Membership.mem G.powerset B) :
      norm (atag E B) <= L := by
    have hEG := Finset.mem_powerset.mp he
    have hBG := Finset.mem_powerset.mp hb
    have hIG : Inter.inter E B <= G := by
      intro p hp
      exact hEG (Finset.mem_inter.mp hp).1
    have hq : 1 <= subsetProduct (Inter.inter E B) :=
      subsetProduct_one_le G (Inter.inter E B) hOne (Finset.mem_powerset.mpr hIG)
    have hDG := exclusive_subset G E B hEG hBG
    have heq (v : Nat) : subsetProduct E * subsetProduct B * v =
        (subsetProduct (Inter.inter E B)) ^ 2 *
          (subsetProduct (exclusive E B) * v) := by
      rw [product_square_split]
      ring
    have hid : atag E B =
        (-1 : Complex) ^ E.card *
          boundaryRowSum G V K (subsetProduct (Inter.inter E B)) (exclusive E B)
            (fun v => subsetProduct B * v <= K) S T a b := by
      dsimp only [atag]
      unfold boundaryRowSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hcut : subsetProduct B * v <= K
      . rw [if_pos hcut, if_pos hcut, heq v]
      . rw [if_neg hcut, if_neg hcut, mul_zero]
    rw [hid, norm_mul]
    simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact hc G V K N1 N2 (subsetProduct (Inter.inter E B)) (exclusive E B)
      (fun v => subsetProduct B * v <= K) S T a b hK hq hDG hG hV hS hT
  have hBetaTag (D : Finset Nat) (hd : Membership.mem G.powerset D) :
      norm (btag D) <= L := by
    have hq : 1 <= subsetProduct D := subsetProduct_one_le G D hOne hd
    have hbound := hc G V K N1 N2 (subsetProduct D)
      (EmptyCollection.emptyCollection : Finset Nat) (fun v => v <= K)
      S T a b hK hq (Finset.empty_subset G) hG hV hS hT
    have hid : btag D =
        (-1 : Complex) ^ D.card *
          boundaryRowSum G V K (subsetProduct D)
            (EmptyCollection.emptyCollection : Finset Nat) (fun v => v <= K)
            S T a b := by
      dsimp only [btag]
      unfold boundaryRowSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hcut : v <= K
      . rw [if_pos hcut, if_pos hcut]
        simp only [subsetProduct, Finset.prod_empty, one_mul, f]
      . rw [if_neg hcut, if_neg hcut, mul_zero]
    rw [hid, norm_mul]
    simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact hbound
  have hAlpha : norm (alpha G V K f) <= (G.powerset.card : Real) ^ 2 * L := by
    rw [alpha_reordered]
    change norm (G.powerset.sum (fun E => G.powerset.sum (atag E))) <= _
    calc
      _ <= G.powerset.sum (fun E => norm (G.powerset.sum (atag E))) :=
        norm_sum_le _ _
      _ <= G.powerset.sum (fun E => G.powerset.sum (fun B => norm (atag E B))) := by
        apply Finset.sum_le_sum
        intro E he
        exact norm_sum_le _ _
      _ <= G.powerset.sum (fun _ => G.powerset.sum (fun _ => L)) := by
        apply Finset.sum_le_sum
        intro E he
        apply Finset.sum_le_sum
        intro B hb
        exact hAlphaTag E B he hb
      _ = (G.powerset.card : Real) ^ 2 * L := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hBeta : norm (beta G V K f) <= (G.powerset.card : Real) * L := by
    rw [beta_reordered]
    change norm (G.powerset.sum btag) <= _
    calc
      _ <= G.powerset.sum (fun D => norm (btag D)) := norm_sum_le _ _
      _ <= G.powerset.sum (fun _ => L) := by
        apply Finset.sum_le_sum
        intro D hd
        exact hBetaTag D hd
      _ = (G.powerset.card : Real) * L := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hid := compensated_boundary_identity G V K hOne (weightedForm S T a b)
  calc
    _ = norm (alpha G V K f - beta G V K f) := congrArg norm hid
    _ <= norm (alpha G V K f) + norm (beta G V K f) := norm_sub_le _ _
    _ <= (G.powerset.card : Real) ^ 2 * L + (G.powerset.card : Real) * L :=
      add_le_add hAlpha hBeta
    _ = _ := by ring

end PrimeFactorOscillations.QuadraticCompensatedEstimate
