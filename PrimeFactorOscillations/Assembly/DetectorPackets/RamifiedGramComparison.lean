/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.GramJoint

/-!
# Signed ramified correlations

Common unit dilations preserve the prime-power correlation. Nonprincipal
ramified factors retain their signed Ramanujan factor, rather than being
replaced by their residue-field cardinality. These are estimates for the
Gauss component, not an improved bound on the full compensated probe.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open scoped Classical

namespace PrimeFactorOscillations.RamifiedGramComparison

open OAI OAI.SevenEighths
open ProbeGramCommon CenteredMomentCorrelation ActualEisensteinCubic CompletedGauss

local notation "Eis" => ActualEisensteinCubic.O
local notation "Id" => Ideal Eis

theorem localExtension_common_unit_dilation
    (P : Id) [P.IsMaximal] (hg : Not (Membership.mem P ConcretePrimeRowBridge.goodLambda))
    (c : Nat) (d n1 n2 k : Eis) (hd : Not (Membership.mem P d)) :
    localExtension P hg c (d * n1) (d * n2) k =
      localExtension P hg c n1 n2 k := by
  classical
  let : Fintype (HasQuotient.Quotient Eis P) := Fintype.ofFinite _
  let : Field (HasQuotient.Quotient Eis P) := Ideal.Quotient.field P
  have hd0 : Not (Ideal.Quotient.mk P d = 0) := by
    intro h
    exact hd (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hmem (n : Eis) :
      Membership.mem P (d * n) <-> Membership.mem P n := by
    constructor
    . intro h
      have hz : Ideal.Quotient.mk P d * Ideal.Quotient.mk P n = 0 := by
        rw [<- map_mul]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr h
      exact Ideal.Quotient.eq_zero_iff_mem.mp ((mul_eq_zero.mp hz).resolve_left hd0)
    . exact P.mul_mem_left d
  have hcorr (chi : MulChar (HasQuotient.Quotient Eis P) Complex)
      (x y z : HasQuotient.Quotient Eis P) :
      localCorrelation chi (Ideal.Quotient.mk P d * x)
        (Ideal.Quotient.mk P d * y) z = localCorrelation chi x y z := by
    by_cases hx : x = 0
    . by_cases hy : y = 0
      . simp only [hx, hy, mul_zero]
      . rw [hx, mul_zero, localCorrelation_first_zero chi (mul_ne_zero hd0 hy),
          localCorrelation_first_zero chi hy]
    . by_cases hy : y = 0
      . rw [hy, mul_zero, localCorrelation_second_zero chi (mul_ne_zero hd0 hx),
          localCorrelation_second_zero chi hx]
      . have hr : (Ideal.Quotient.mk P d * x) /
            (Ideal.Quotient.mk P d * y) = x / y := by
          field_simp
        rw [localCorrelation_units chi (mul_ne_zero hd0 hx) (mul_ne_zero hd0 hy),
          localCorrelation_units chi hx hy, hr]
  simp only [localExtension, hmem n1, hmem n2, map_mul]
  rw [hcorr]

theorem localExtension_nonprincipal_formula
    (P : Id) [P.IsMaximal] (hg : Not (Membership.mem P ConcretePrimeRowBridge.goodLambda))
    (c : Nat) (n1 n2 k : Eis)
    (hn1 : Not (Membership.mem P n1)) (hn2 : Not (Membership.mem P n2))
    (hchi : Not (actualSextic P hg ^ c = 1)) :
    localExtension P hg c n1 n2 k =
      ((Ideal.absNorm P : Complex) ^ (c - 1) *
        (actualSextic P hg ^ c)
          (Ideal.Quotient.mk P n1 / Ideal.Quotient.mk P n2)) *
        ((if Membership.mem P k then (Ideal.absNorm P : Complex) else 0) - 1) := by
  classical
  let : Fintype (HasQuotient.Quotient Eis P) := Fintype.ofFinite _
  let : Field (HasQuotient.Quotient Eis P) := Ideal.Quotient.field P
  have h1 : Not (Ideal.Quotient.mk P n1 = 0) := by
    intro h
    exact hn1 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have h2 : Not (Ideal.Quotient.mk P n2 = 0) := by
    intro h
    exact hn2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hb : Not (Membership.mem P n1 /\ Membership.mem P n2) :=
    fun h => hn1 h.1
  have hcard : Fintype.card (HasQuotient.Quotient Eis P) = Ideal.absNorm P := by
    simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [localExtension, ite_eq_right hb, localCorrelation_units _ h1 h2, hcard]
  by_cases hk : Membership.mem P k
  . have hz : Ideal.Quotient.mk P k = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hk
    simp only [hz, ite_true, ite_eq_left hk]
    ring
  . have hz : Not (Ideal.Quotient.mk P k = 0) := by
      intro h
      exact hk (Ideal.Quotient.eq_zero_iff_mem.mp h)
    simp only [ite_eq_right hz, ite_eq_right hchi, ite_eq_right hk]
    ring

theorem localExtension_nonprincipal_norm
    (P : Id) [P.IsMaximal] (hg : Not (Membership.mem P ConcretePrimeRowBridge.goodLambda))
    (c : Nat) (n1 n2 k : Eis)
    (hchi : Not (actualSextic P hg ^ c = 1)) (hk : Not (Membership.mem P k)) :
    norm (localExtension P hg c n1 n2 k) <=
      (Ideal.absNorm P : Real) ^ (c - 1) := by
  classical
  let : Fintype (HasQuotient.Quotient Eis P) := Fintype.ofFinite _
  let : Field (HasQuotient.Quotient Eis P) := Ideal.Quotient.field P
  have hk0 : Not (Ideal.Quotient.mk P k = 0) := by
    intro h
    exact hk (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hcorr :
      norm (localCorrelation (actualSextic P hg ^ c)
        (Ideal.Quotient.mk P n1) (Ideal.Quotient.mk P n2)
        (Ideal.Quotient.mk P k)) <= 1 := by
    by_cases h1 : Ideal.Quotient.mk P n1 = 0
    . by_cases h2 : Ideal.Quotient.mk P n2 = 0
      . simp [localCorrelation, fullCorrelation, h1, h2, Ne.symm hk0]
      . rw [h1, localCorrelation_first_zero _ h2]
        simp [hchi]
    . by_cases h2 : Ideal.Quotient.mk P n2 = 0
      . rw [h2, localCorrelation_second_zero _ h1]
        simp [hchi]
      . rw [localCorrelation_units _ h1 h2]
        simp only [ite_eq_right hk0, ite_eq_right hchi, norm_mul, norm_neg, norm_one, mul_one]
        exact FiniteRayExpansion.norm_char_le_one _ _
  unfold localExtension
  split_ifs
  . simp only [norm_zero]
    positivity
  . rw [norm_mul, norm_pow, Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left hcorr
      (pow_nonneg (Nat.cast_nonneg (Ideal.absNorm P)) (c - 1))).trans_eq (mul_one _)

universe u
variable {Iota : Type u} [Fintype Iota]

theorem globalExtension_common_unit_dilation
    (P : Iota -> Id) [forall i, (P i).IsMaximal]
    (hg : forall i, Not (Membership.mem (P i) ConcretePrimeRowBridge.goodLambda))
    (c : Iota -> Nat) (d n1 n2 k : Eis)
    (hd : forall i, Not (Membership.mem (P i) d)) :
    globalExtension P hg c (d * n1) (d * n2) k =
      globalExtension P hg c n1 n2 k := by
  classical
  unfold globalExtension
  apply Finset.prod_congr rfl
  intro i hi
  exact localExtension_common_unit_dilation (P i) (hg i) (c i) d n1 n2 k (hd i)

theorem globalExtension_nonprincipal_product
    (P : Iota -> Id) [forall i, (P i).IsMaximal]
    (hg : forall i, Not (Membership.mem (P i) ConcretePrimeRowBridge.goodLambda))
    (c : Iota -> Nat) (n1 n2 k : Eis)
    (hn1 : forall i, Not (Membership.mem (P i) n1))
    (hn2 : forall i, Not (Membership.mem (P i) n2))
    (hchi : forall i, Not (actualSextic (P i) (hg i) ^ c i = 1)) :
    globalExtension P hg c n1 n2 k =
      (Finset.univ.prod (fun i =>
        (Ideal.absNorm (P i) : Complex) ^ (c i - 1) *
          (actualSextic (P i) (hg i) ^ c i)
            (Ideal.Quotient.mk (P i) n1 / Ideal.Quotient.mk (P i) n2))) *
      (Finset.univ.prod (fun i =>
        (if Membership.mem (P i) k then (Ideal.absNorm (P i) : Complex) else 0) - 1)) := by
  classical
  unfold globalExtension
  rw [<- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact localExtension_nonprincipal_formula (P i) (hg i) (c i) n1 n2 k
    (hn1 i) (hn2 i) (hchi i)

theorem globalExtension_nonresonant_norm
    (P : Iota -> Id) [forall i, (P i).IsMaximal]
    (hg : forall i, Not (Membership.mem (P i) ConcretePrimeRowBridge.goodLambda))
    (c : Iota -> Nat) (n1 n2 k : Eis)
    (hchi : forall i, Not (actualSextic (P i) (hg i) ^ c i = 1))
    (hk : forall i, Not (Membership.mem (P i) k)) :
    norm (globalExtension P hg c n1 n2 k) <=
      Finset.univ.prod (fun i => (Ideal.absNorm (P i) : Real) ^ (c i - 1)) := by
  classical
  rw [globalExtension, norm_prod]
  have hp (s : Finset Iota) :
      s.prod (fun i => norm (localExtension (P i) (hg i) (c i) n1 n2 k)) <=
        s.prod (fun i => (Ideal.absNorm (P i) : Real) ^ (c i - 1)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact mul_le_mul
        (localExtension_nonprincipal_norm (P a) (hg a) (c a) n1 n2 k
          (hchi a) (hk a)) ih
        (Finset.prod_nonneg (fun i hi => norm_nonneg _))
        (pow_nonneg (Nat.cast_nonneg (Ideal.absNorm (P a))) (c a - 1))
  exact hp Finset.univ

end PrimeFactorOscillations.RamifiedGramComparison
