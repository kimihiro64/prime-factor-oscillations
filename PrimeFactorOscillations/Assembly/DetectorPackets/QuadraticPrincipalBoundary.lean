/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticBoundaryMean

/-!
# QuadraticPrincipalBoundary

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

namespace PrimeFactorOscillations.QuadraticPrincipalBoundary

open QuadraticCarrierPacket QuadraticCoprimeMean IntegerQuadraticPrefix
open QuadraticDivisorMean QuadraticBoundaryMean QuadraticMainTermCancellation

def rowForm (S T : Finset Nat) (a b : Nat -> Complex) (w : Nat) : Complex :=
  coprimeForm S T (fun n => a n * kernel w n) (fun m => b m * kernel w m)

def weightedForm (S T : Finset Nat) (a b : Nat -> Complex) (w : Nat) : Complex :=
  rowForm S T a b w / (Real.sqrt (w : Real) : Complex)

def meanCap (M N1 N2 : Nat) (S T : Finset Nat) (a b : Nat -> Complex) : Real :=
  Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
    Real.sqrt (prefixNorm M N2 * maskedMass 1 T b)

theorem weightedForm_norm_le (S T : Finset Nat) (a b : Nat -> Complex)
    (K w : Nat) (hK : 0 < K) (hw : K <= w) :
    norm (weightedForm S T a b w) <=
      (1 / Real.sqrt (K : Real)) * norm (rowForm S T a b w) := by
  have hKR : 0 < (K : Real) := by exact_mod_cast hK
  have hle : (K : Real) <= (w : Real) := by exact_mod_cast hw
  have hs := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hKR) (Real.sqrt_le_sqrt hle)
  unfold weightedForm
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (w : Real))]
  calc
    _ = (1 / Real.sqrt (w : Real)) * norm (rowForm S T a b w) := by ring
    _ <= _ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)

theorem weighted_tag_mean (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M N1 N2 K q d : Nat), 0 < K -> 0 < d ->
      forall (V S T : Finset Nat) (a b : Nat -> Complex),
      (forall v, Membership.mem V v -> Membership.mem (columns M) (d * v)) ->
      (forall v, Membership.mem V v -> K <= q ^ 2 * (d * v)) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      V.sum (fun v => norm (weightedForm S T a b (q ^ 2 * (d * v)))) <=
        (1 / Real.sqrt (K : Real)) *
          (C * ((max N1 N2 : Nat) : Real) ^ eps * meanCap M N1 N2 S T a b) := by
  choose C hC hc using square_row_mean eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro M N1 N2 K q d hK hd V S T a b hrows hfreq hS hT
  let R := V.image (fun v => d * v)
  have hR : forall r, Membership.mem R r -> Membership.mem (columns M) r := by
    intro r hr
    choose v hv using Finset.mem_image.mp hr
    rw [<- hv.2]
    exact hrows v hv.1
  have hinj : Set.InjOn (fun v => d * v) V := by
    intro v hv u hu heq
    exact Nat.eq_of_mul_eq_mul_left hd heq
  have hb := hc M N1 N2 q R S T a b hR hS hT
  have hsum : R.sum (fun r => norm (rowForm S T a b (q ^ 2 * r))) =
      V.sum (fun v => norm (rowForm S T a b (q ^ 2 * (d * v)))) :=
    Finset.sum_image hinj
  change R.sum (fun r => norm (rowForm S T a b (q ^ 2 * r))) <=
    C * ((max N1 N2 : Nat) : Real) ^ eps *
      Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
      Real.sqrt (prefixNorm M N2 * maskedMass 1 T b) at hb
  rw [hsum] at hb
  calc
    _ <= V.sum (fun v => (1 / Real.sqrt (K : Real)) *
        norm (rowForm S T a b (q ^ 2 * (d * v)))) := by
      apply Finset.sum_le_sum
      intro v hv
      exact weightedForm_norm_le S T a b K _ hK (hfreq v hv)
    _ = (1 / Real.sqrt (K : Real)) *
        V.sum (fun v => norm (rowForm S T a b (q ^ 2 * (d * v)))) :=
      (Finset.mul_sum _ _ _).symm
    _ <= _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [meanCap, mul_assoc] using hb

def exclusive (E B : Finset Nat) : Finset Nat := Union.union (SDiff.sdiff E B) (SDiff.sdiff B E)

theorem exclusive_subset (G E B : Finset Nat)
    (hE : E <= G) (hB : B <= G) : exclusive E B <= G := by
  intro p hp
  rcases Finset.mem_union.mp hp with he | hb
  . exact hE (Finset.mem_sdiff.mp he).1
  . exact hB (Finset.mem_sdiff.mp hb).1

theorem product_square_split (E B : Finset Nat) :
    subsetProduct E * subsetProduct B =
      (subsetProduct (Inter.inter E B)) ^ 2 * subsetProduct (exclusive E B) := by
  have he := Finset.prod_inter_mul_prod_sdiff E B id
  have hb := Finset.prod_inter_mul_prod_sdiff B E id
  rw [Finset.inter_comm B E] at hb
  have hd : Disjoint (E \ B) (B \ E) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_sdiff.mp hq).1
  calc
    _ = (subsetProduct (Inter.inter E B) * subsetProduct (E \ B)) * subsetProduct B :=
      congrArg (fun n : Nat => n * subsetProduct B) he.symm
    _ = (subsetProduct (Inter.inter E B) * subsetProduct (E \ B)) *
        (subsetProduct (Inter.inter E B) * subsetProduct (B \ E)) :=
      congrArg (fun n : Nat => (subsetProduct (Inter.inter E B) * subsetProduct (E \ B)) * n) hb.symm
    _ = _ := by
      unfold subsetProduct exclusive
      rw [Finset.prod_union hd]
      ring

theorem subsetProduct_squarefree (G D : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p) (hD : D <= G) :
    Squarefree (subsetProduct D) := by
  apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
  intro hz
  have hm := mobius_subset_product G D hG (Finset.mem_powerset.mpr hD)
  have hp : (-1 : Complex) ^ D.card = 0 := hm.symm.trans (by simp only [hz, Int.cast_zero])
  exact (pow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero : Not ((1 : Complex) = 0)))) hp

theorem subsetProduct_odd (D : Finset Nat)
    (hD : forall p, Membership.mem D p -> Odd p) : Odd (subsetProduct D) := by
  revert hD
  induction D using Finset.induction_on with
  | empty => intro _; simp [subsetProduct]
  | @insert p D hp ih =>
    intro hD
    rw [subsetProduct, Finset.prod_insert hp]
    exact Nat.odd_mul.mpr (And.intro (hD p (Finset.mem_insert_self p D))
      (ih (fun r hr => hD r (Finset.mem_insert_of_mem hr))))

theorem lifted_columns (G D : Finset Nat) (hD : D <= G)
    (hG : forall p, Membership.mem G p -> Nat.Prime p /\ Odd p)
    (M v : Nat)
    (hv : 0 < v /\ Odd v /\ Squarefree v /\ Nat.Coprime v (subsetProduct G))
    (hupper : subsetProduct D * v <= M) :
    Membership.mem (columns M) (subsetProduct D * v) := by
  have hd : 1 <= subsetProduct D :=
    subsetProduct_one_le G D (fun p hp => (hG p hp).1.one_le) (Finset.mem_powerset.mpr hD)
  have hdiv : Dvd.dvd (subsetProduct D) (subsetProduct G) :=
    Finset.prod_dvd_prod_of_subset D G id hD
  have hcop : Nat.Coprime (subsetProduct D) v :=
    (Nat.Coprime.of_dvd_right hdiv hv.2.2.2).symm
  have hsf : Squarefree (subsetProduct D * v) :=
    Nat.squarefree_mul_iff.mpr (And.intro hcop
      (And.intro (subsetProduct_squarefree G D (fun p hp => (hG p hp).1) hD) hv.2.2.1))
  have hodd : Odd (subsetProduct D * v) :=
    Nat.odd_mul.mpr (And.intro (subsetProduct_odd D (fun p hp => (hG p (hD hp)).2)) hv.2.1)
  apply Finset.mem_filter.mpr
  exact And.intro (Finset.mem_Icc.mpr (And.intro (Nat.mul_pos hd hv.1) hupper))
    (And.intro hodd hsf)

end PrimeFactorOscillations.QuadraticPrincipalBoundary
