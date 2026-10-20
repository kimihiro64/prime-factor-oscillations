/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.LowKernelQuotientTransport

/-!
# CubeRowQuotientMean

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open scoped BigOperators
open Classical

namespace OAI.SevenEighths.CubeRowQuotientMean

open CanonicalRowCompletion CanonicalQuadraticSieve

universe u v

abbrev O := ActualEisensteinCubic.O

theorem idealRowHom_eq_pool
    (F : Finset (Ideal O))
    (hFpos : forall I, Membership.mem F I -> Not (I = 0))
    (hFgood : forall I, Membership.mem F I ->
      forall P, Membership.mem (UniqueFactorizationMonoid.normalizedFactors I) P ->
        Not (Membership.mem P ActualEisensteinCubic.lambda))
    (I : Ideal O) (hIF : Membership.mem F I) (hI : Squarefree I) (t : O) :
    idealRowHom t I = ConcretePrimeRowBridge.idealSexticRow F hFpos hFgood I t := by
  classical
  letI : forall i : ConcretePrimeRowBridge.primePool F,
      (i.val : Ideal O).IsMaximal := ConcretePrimeRowBridge.primePool_maximal F hFpos
  conv_lhs =>
    rw [show I = Finset.prod (ConcretePrimeRowBridge.idealSupport F I)
        (fun i => (i.val : Ideal O)) from
      (ConcretePrimeRowBridge.idealSupport_product_eq F hIF hI).symm]
    rw [map_prod]
  change Finset.prod _ _ = ActualEisensteinCubic.finiteSquarefreeRow _ _ _ t
  unfold ActualEisensteinCubic.finiteSquarefreeRow
  apply Finset.prod_congr rfl
  intro i hi
  exact idealRowHom_prime t i.val (ConcretePrimeRowBridge.primePool_good F hFgood i)

theorem cube_row_eq_quadratic (I : Ideal O) (hI : Admissible I) (t : O) :
    idealRowHom (t ^ 3) I = quadraticRow I t := by
  classical
  rw [idealRowHom_argument_pow t 3 I (admissible_supported hI)]
  unfold quadraticRow
  rw [dite_eq_left hI]
  congr 1
  exact idealRowHom_eq_pool {I} _ _ I (Finset.mem_singleton_self I) hI.2.1 t

theorem masked_cube_row (I : Ideal O) (hI : Admissible I) (m t : O) :
    idealRowHom (m ^ 6 * t ^ 3) I =
      (if IsCoprime I (Ideal.span {m}) then 1 else 0) * quadraticRow I t := by
  rw [idealRowHom_argument_mul, idealRowHom_sixth_mask m I (admissible_supported hI),
    cube_row_eq_quadratic I hI t]

theorem cube_row_product (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (t : O) :
    idealRowHom (t ^ 3) (I * J) = quadraticRow I t * quadraticRow J t := by
  rw [map_mul, cube_row_eq_quadratic I hI, cube_row_eq_quadratic J hJ]


theorem quadraticRow_inv (I : Ideal O) (hI : Admissible I) (t : O) :
    (quadraticRow I t) ^ (-1 : Int) = quadraticRow I t := by
  have h := canonical_quadraticRow_squared I hI t
  unfold idealZeroMask at h
  by_cases hp : exists P, Membership.mem (UniqueFactorizationMonoid.normalizedFactors I) P
      /\ Membership.mem P t
  case pos =>
    rw [if_pos hp] at h
    have hz := mul_self_eq_zero.mp h
    simp [hz]
  case neg =>
    rw [if_neg hp] at h
    simpa only [zpow_neg_one] using (inv_eq_of_mul_eq_one_left h)

theorem cube_row_inv (I : Ideal O) (hI : Admissible I) (t : O) :
    (idealRowHom (t ^ 3) I) ^ (-1 : Int) = idealRowHom (t ^ 3) I := by
  rw [cube_row_eq_quadratic I hI]
  exact quadraticRow_inv I hI t

def fiberCoeff {i : Type*} (s : Finset i) (col : i -> Ideal O)
    (a : i -> Complex) (K : Ideal O) : Complex :=
  Finset.sum (s.filter (fun j => col j = K)) a

theorem fiber_sum {i : Type*} (s : Finset i) (col : i -> Ideal O)
    (a : i -> Complex) (f : Ideal O -> Complex) :
    Finset.sum (s.image col) (fun K => f K * fiberCoeff s col a K) =
      Finset.sum s (fun j => f (col j) * a j) := by
  classical
  calc
    Finset.sum (s.image col) (fun K => f K * fiberCoeff s col a K) =
        Finset.sum (s.image col) (fun K =>
          Finset.sum (s.filter (fun j => col j = K)) (fun j => f (col j) * a j)) := by
      apply Finset.sum_congr rfl
      intro K hK
      rw [fiberCoeff, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = Finset.sum s (fun j => f (col j) * a j) := by
      rw [Finset.sum_fiberwise_eq_sum_filter]
      have hs : s.filter (fun j => Membership.mem (s.image col) (col j)) = s :=
        Finset.filter_eq_self.mpr (fun j hj => Finset.mem_image_of_mem col hj)
      rw [hs]

theorem paired_polynomial {i j : Type*} (A : Finset i) (B : Finset j)
    (I : i -> Ideal O) (J : j -> Ideal O) (a : i -> Complex) (b : j -> Complex)
    (hJ : forall y, Membership.mem B y -> Admissible (J y)) (t : O) :
    Finset.sum A (fun x => idealRowHom (t ^ 3) (I x) * a x) *
        Finset.sum B (fun y => (idealRowHom (t ^ 3) (J y)) ^ (-1 : Int) * b y) =
      Finset.sum (A.product B) (fun xy =>
        idealRowHom (t ^ 3) (I xy.1 * J xy.2) * (a xy.1 * b xy.2)) := by
  calc
    _ = Finset.sum A (fun x => Finset.sum B (fun y =>
        idealRowHom (t ^ 3) (I x * J y) * (a x * b y))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      rw [cube_row_inv (J y) (hJ y hy), map_mul]
      ring
    _ = _ := (Finset.sum_product A B (fun xy : Prod i j =>
      idealRowHom (t ^ 3) (I xy.1 * J xy.2) * (a xy.1 * b xy.2))).symm

theorem finite_cube_sieve (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M N : Real), 1 <= M -> 1 <= N ->
      forall {r : Type u} {i : Type v} [Fintype r]
        (rows : r -> Ideal O) (s : Finset i) (col : i -> Ideal O) (a : i -> Complex),
      Function.Injective rows ->
      (forall x, Admissible (rows x) /\ (Ideal.absNorm (rows x) : Real) <= M) ->
      (forall y, Membership.mem s y ->
        Admissible (col y) /\ (Ideal.absNorm (col y) : Real) <= N) ->
      Finset.sum Finset.univ (fun x =>
        norm (Finset.sum s (fun y =>
          idealRowHom ((CompletedGauss.primaryGenerator (rows x)) ^ 3) (col y) * a y)) ^ 2) <=
        C * (M * N) ^ eps * (M + N) *
          Finset.sum (s.image col) (fun K => norm (fiberCoeff s col a K) ^ 2) := by
  classical
  have existsC := finite_family_quadratic_large_sieve.{u, 0} eps heps
  let C := existsC.choose
  have hC := existsC.choose_spec.1
  have hCs := existsC.choose_spec.2
  refine Exists.intro C (And.intro hC ?_)
  intro M N hM hN r i hr rows s col a hrows hrow hcol
  let cols : (s.image col) -> Ideal O := fun K => K.val
  have hcols : Function.Injective cols := Subtype.val_injective
  have hcolBound : forall K : s.image col,
      Admissible (cols K) /\ (Ideal.absNorm (cols K) : Real) <= N := by
    intro K
    have h := Finset.mem_image.mp K.property
    let y := h.choose
    have hy := h.choose_spec.1
    have hyeq := h.choose_spec.2
    rw [show cols K = col y from hyeq.symm]
    exact hcol y hy
  have hb := hCs M N hM hN rows cols hrows hcols hrow hcolBound
    (fun K => fiberCoeff s col a K.val)
  calc
    _ = Finset.sum Finset.univ (fun x =>
        norm (Finset.sum Finset.univ (fun K : s.image col =>
          quadraticRow K.val (CompletedGauss.primaryGenerator (rows x)) *
            fiberCoeff s col a K.val)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      rw [Finset.sum_coe_sort (s.image col) (fun K : Ideal O =>
        quadraticRow K (CompletedGauss.primaryGenerator (rows x)) * fiberCoeff s col a K)]
      rw [fiber_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      rw [cube_row_eq_quadratic (col y) (hcol y hy).1]
    _ <= C * (M * N) ^ eps * (M + N) *
        Finset.sum Finset.univ (fun K : s.image col => norm (fiberCoeff s col a K.val) ^ 2) := hb
    _ = _ := by
      rw [Finset.sum_coe_sort (s.image col) (fun K : Ideal O => norm (fiberCoeff s col a K) ^ 2)]


def goodIndices {i : Type*} (s : Finset i) (col : i -> Ideal O) : Finset i :=
  s.filter (fun y => Admissible (col y))

def goodMass {i : Type*} (s : Finset i) (col : i -> Ideal O) (a : i -> Complex) : Real :=
  Finset.sum ((goodIndices s col).image col) (fun K =>
    norm (fiberCoeff (goodIndices s col) col a K) ^ 2)

def remainderPacket {i : Type*} (s : Finset i) (col : i -> Ideal O)
    (a : i -> Complex) (t : O) : Complex :=
  Finset.sum (s.filter (fun y => Not (Admissible (col y))))
    (fun y => idealRowHom (t ^ 3) (col y) * a y)

theorem packet_split {i : Type*} (s : Finset i) (col : i -> Ideal O)
    (a : i -> Complex) (t : O) :
    Finset.sum s (fun y => idealRowHom (t ^ 3) (col y) * a y) =
      Finset.sum (goodIndices s col) (fun y =>
        idealRowHom (t ^ 3) (col y) * a y) + remainderPacket s col a t := by
  exact (Finset.sum_filter_add_sum_filter_not s
    (fun y => Admissible (col y)) (fun y => idealRowHom (t ^ 3) (col y) * a y)).symm

theorem full_cube_sieve (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M N : Real), 1 <= M -> 1 <= N ->
      forall {r : Type u} {i : Type v} [Fintype r]
        (rows : r -> Ideal O) (s : Finset i) (col : i -> Ideal O) (a : i -> Complex),
      Function.Injective rows ->
      (forall x, Admissible (rows x) /\ (Ideal.absNorm (rows x) : Real) <= M) ->
      (forall y, Membership.mem s y -> (Ideal.absNorm (col y) : Real) <= N) ->
      Finset.sum Finset.univ (fun x =>
        norm (Finset.sum s (fun y =>
          idealRowHom ((CompletedGauss.primaryGenerator (rows x)) ^ 3) (col y) * a y)) ^ 2) <=
        2 * (C * (M * N) ^ eps * (M + N) * goodMass s col a) +
          2 * Finset.sum Finset.univ (fun x =>
            norm (remainderPacket s col a (CompletedGauss.primaryGenerator (rows x))) ^ 2) := by
  classical
  have hc := finite_cube_sieve.{u, v} eps heps
  let C := hc.choose
  have hC := hc.choose_spec.1
  have hCs := hc.choose_spec.2
  refine Exists.intro C (And.intro hC ?_)
  intro M N hM hN r i hr rows s col a hrows hrow hcol
  have hgood : forall y, Membership.mem (goodIndices s col) y ->
      Admissible (col y) /\ (Ideal.absNorm (col y) : Real) <= N := by
    intro y hy
    have h := Finset.mem_filter.mp hy
    exact And.intro h.2 (hcol y h.1)
  have hb := hCs M N hM hN rows (goodIndices s col) col a hrows hrow hgood
  have pointwise (x : r) :
      norm (Finset.sum s (fun y =>
        idealRowHom ((CompletedGauss.primaryGenerator (rows x)) ^ 3) (col y) * a y)) ^ 2 <=
      2 * norm (Finset.sum (goodIndices s col) (fun y =>
        idealRowHom ((CompletedGauss.primaryGenerator (rows x)) ^ 3) (col y) * a y)) ^ 2 +
      2 * norm (remainderPacket s col a (CompletedGauss.primaryGenerator (rows x))) ^ 2 := by
    rw [packet_split]
    let g := Finset.sum (goodIndices s col) (fun y =>
      idealRowHom ((CompletedGauss.primaryGenerator (rows x)) ^ 3) (col y) * a y)
    let e := remainderPacket s col a (CompletedGauss.primaryGenerator (rows x))
    have hn : norm (g + e) <= norm g + norm e := norm_add_le g e
    have hpos := norm_nonneg (g + e)
    have hg := norm_nonneg g
    have he := norm_nonneg e
    have hs := sq_nonneg (norm g - norm e)
    change norm (g + e) ^ 2 <= 2 * norm g ^ 2 + 2 * norm e ^ 2
    nlinarith
  have hs := Finset.sum_le_sum (fun x (_ : Membership.mem Finset.univ x) => pointwise x)
  rw [Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum] at hs
  change Finset.sum Finset.univ (fun x =>
    norm (Finset.sum (goodIndices s col) (fun y =>
      idealRowHom ((CompletedGauss.primaryGenerator (rows x)) ^ 3) (col y) * a y)) ^ 2) <=
    C * (M * N) ^ eps * (M + N) * goodMass s col a at hb
  linarith

def pairCol (p : Prod (Ideal O) (Ideal O)) : Ideal O := p.1 * p.2

def pairCoeff (a b : Ideal O -> Complex) (p : Prod (Ideal O) (Ideal O)) : Complex :=
  a p.1 * b p.2

def pairedPacket (A B : Finset (Ideal O)) (a b : Ideal O -> Complex) (t : O) : Complex :=
  Finset.sum A (fun I => idealRowHom (t ^ 3) I * a I) *
    Finset.sum B (fun J => (idealRowHom (t ^ 3) J) ^ (-1 : Int) * b J)

theorem paired_cube_sieve (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M U V : Real), 1 <= M -> 1 <= U -> 1 <= V ->
      forall {r : Type u} [Fintype r] (rows : r -> Ideal O)
        (A B : Finset (Ideal O)) (a b : Ideal O -> Complex),
      Function.Injective rows ->
      (forall x, Admissible (rows x) /\ (Ideal.absNorm (rows x) : Real) <= M) ->
      (forall I, Membership.mem A I -> (Ideal.absNorm I : Real) <= U) ->
      (forall J, Membership.mem B J ->
        Admissible J /\ (Ideal.absNorm J : Real) <= V) ->
      Finset.sum Finset.univ (fun x =>
        norm (pairedPacket A B a b (CompletedGauss.primaryGenerator (rows x))) ^ 2) <=
        2 * (C * (M * (U * V)) ^ eps * (M + U * V) *
          goodMass (A.product B) pairCol (pairCoeff a b)) +
        2 * Finset.sum Finset.univ (fun x =>
          norm (remainderPacket (A.product B) pairCol (pairCoeff a b)
            (CompletedGauss.primaryGenerator (rows x))) ^ 2) := by
  classical
  have hc := full_cube_sieve.{u, 0} eps heps
  let C := hc.choose
  have hC := hc.choose_spec.1
  have hCs := hc.choose_spec.2
  refine Exists.intro C (And.intro hC ?_)
  intro M U V hM hU hV r hr rows A B a b hrows hrow hA hB
  have hUV : 1 <= U * V := by nlinarith
  have hcol : forall p, Membership.mem (A.product B) p ->
      (Ideal.absNorm (pairCol p) : Real) <= U * V := by
    intro p hp
    have hmem := Finset.mem_product.mp hp
    have hleft := hA p.1 hmem.1
    have hright := (hB p.2 hmem.2).2
    change (Ideal.absNorm (p.1 * p.2) : Real) <= U * V
    rw [map_mul, Nat.cast_mul]
    exact mul_le_mul hleft hright (Nat.cast_nonneg _) (by linarith)
  have hb := hCs M (U * V) hM hUV rows (A.product B) pairCol (pairCoeff a b)
    hrows hrow hcol
  have heq (t : O) : pairedPacket A B a b t =
      Finset.sum (A.product B) (fun p =>
        idealRowHom (t ^ 3) (pairCol p) * pairCoeff a b p) :=
    paired_polynomial A B id id a b (fun J hJ => (hB J hJ).1) t
  simpa only [heq] using hb

end OAI.SevenEighths.CubeRowQuotientMean
