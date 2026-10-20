/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Analytic.Order
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.BernoulliProfileZeros

/-!
# Multiplicities of canonical Bernoulli profile zeros

A positive probability has a finite fibre. Splitting off that entire fibre
factors the canonical product into a power of one linear factor and an entire
tail that is nonzero at the selected root. Its zero order is therefore exactly
the fibre cardinality. Equality of profiles recovers all positive-probability
multiplicities, including repeated exceptional probabilities.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

/-- A nonzero value has a finite fibre in a square-summable real array. -/
theorem finite_fibre_of_summable_sq {I : Type*} (a : I -> Real)
    (hs : Summable (fun i => (a i) ^ 2)) (c : Real) (hc : 0 < c) :
    Set.Finite {i | a i = c} := by
  have hsmall : Filter.Eventually (fun i => (a i) ^ 2 < c ^ 2) Filter.cofinite :=
    hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (sq_pos_of_pos hc))
  apply (Filter.eventually_cofinite.mp hsmall).subset
  intro i hi
  change Not ((a i) ^ 2 < c ^ 2)
  rw [hi]
  exact lt_irrefl _

/-- Exact splitting by the full fibre of a selected positive probability. -/
theorem canonicalBernoulliProfile_fibre_factorization {I : Type*}
    (a : I -> Real) (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hs : Summable (fun i => (a i) ^ 2)) (c : Real) (hc : 0 < c) (z : Complex) :
    canonicalBernoulliProfile a z =
      canonicalBernoulliFactor c z ^ Nat.card {i // a i = c} *
        canonicalBernoulliProfile (fun i : {i // Not (a i = c)} => a i.val) z := by
  classical
  let S : Set I := {i | a i = c}
  let : Fintype S := (finite_fibre_of_summable_sq a hs c hc).fintype
  have hnorm := summable_norm_canonicalBernoulliFactor_sub_one a ha ha1 hs z
  have hS : Multipliable (fun i : S => canonicalBernoulliFactor (a i.val) z) := by
    have h := multipliable_one_add_of_summable
      (hnorm.comp_injective (Subtype.val_injective : Function.Injective (fun i : S => i.val)))
    simpa only [Function.comp_def, add_sub_cancel] using h
  have hSc : Multipliable (fun i : S.compl => canonicalBernoulliFactor (a i.val) z) := by
    have h := multipliable_one_add_of_summable
      (hnorm.comp_injective
        (Subtype.val_injective : Function.Injective (fun i : S.compl => i.val)))
    simpa only [Function.comp_def, add_sub_cancel] using h
  have hsplit := Multipliable.tprod_mul_tprod_compl
    (f := fun i => canonicalBernoulliFactor (a i) z) (s := S) hS hSc
  have hfinite : tprod (fun i : S => canonicalBernoulliFactor (a i.val) z) =
      canonicalBernoulliFactor c z ^ Nat.card S := by
    rw [tprod_fintype]
    calc
      Finset.univ.prod (fun i : S => canonicalBernoulliFactor (a i.val) z) =
          Finset.univ.prod (fun _ : S => canonicalBernoulliFactor c z) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [i.property]
      _ = canonicalBernoulliFactor c z ^ Nat.card S := by
        simp only [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  rw [hfinite] at hsplit
  exact hsplit.symm

/-- The factor belonging to a positive probability has a simple zero. -/
theorem analyticOrderAt_canonicalBernoulliFactor (c : Real) (hc : 0 < c) :
    analyticOrderAt (canonicalBernoulliFactor c) (1 - 1 / (c : Complex)) = 1 := by
  have hcC : Not ((c : Complex) = 0) := by exact_mod_cast ne_of_gt hc
  have hA : AnalyticAt Complex (canonicalBernoulliFactor c) (1 - 1 / (c : Complex)) := by
    unfold canonicalBernoulliFactor
    fun_prop
  apply (hA.analyticOrderAt_eq_natCast (n := 1)).2
  refine Exists.intro (fun z : Complex => (c : Complex) * exp (-(c : Complex) * (z - 1)))
    (And.intro ?_ (And.intro ?_ ?_))
  . fun_prop
  . exact mul_ne_zero hcC (exp_ne_zero _)
  . apply Filter.Eventually.of_forall
    intro z
    simp only [pow_one, smul_eq_mul]
    unfold canonicalBernoulliFactor
    field_simp
    ring

/-- The order of each profile zero retains the complete probability fibre. -/
theorem analyticOrderAt_canonicalBernoulliProfile {I : Type*}
    (a : I -> Real) (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hs : Summable (fun i => (a i) ^ 2)) (c : Real) (hc : 0 < c) :
    analyticOrderAt (canonicalBernoulliProfile a) (1 - 1 / (c : Complex)) =
      (Nat.card {i // a i = c} : ENat) := by
  let b : {i // Not (a i = c)} -> Real := fun i => a i.val
  have hb : forall i, 0 <= b i := fun i => ha i.val
  have hb1 : forall i, b i <= 1 := fun i => ha1 i.val
  have hbs : Summable (fun i => (b i) ^ 2) :=
    hs.comp_injective Subtype.val_injective
  let z0 : Complex := 1 - 1 / (c : Complex)
  have htail : AnalyticAt Complex (canonicalBernoulliProfile b) z0 :=
    (differentiable_canonicalBernoulliProfile b hb hb1 hbs).analyticAt z0
  have htailne : Not (canonicalBernoulliProfile b z0 = 0) := by
    intro hz
    have hroot := (canonicalBernoulliProfile_eq_zero_iff b hb hb1 hbs z0).mp hz
    let i := Classical.choose hroot
    have hi := Classical.choose_spec hroot
    have he := hi.2
    change 1 - 1 / (c : Complex) = 1 - 1 / (b i : Complex) at he
    have hinv : 1 / (c : Complex) = 1 / (b i : Complex) := by
      linear_combination -he
    have hcb : c = b i := by
      apply Complex.ofReal_injective
      apply inv_injective
      simpa only [one_div] using hinv
    exact i.property hcb.symm
  have hfactor : AnalyticAt Complex (canonicalBernoulliFactor c) z0 := by
    unfold canonicalBernoulliFactor
    fun_prop
  have hfun : canonicalBernoulliProfile a =
      (canonicalBernoulliFactor c) ^ Nat.card {i // a i = c} * canonicalBernoulliProfile b := by
    funext z
    exact canonicalBernoulliProfile_fibre_factorization a ha ha1 hs c hc z
  rw [hfun, analyticOrderAt_mul (hfactor.pow _) htail, analyticOrderAt_pow hfactor,
    analyticOrderAt_canonicalBernoulliFactor c hc,
    htail.analyticOrderAt_eq_zero.mpr htailne]
  simp

/-- Equal entire profiles determine every positive parameter multiplicity. -/
theorem card_fibre_eq_of_canonicalBernoulliProfile_eq {I J : Type*}
    (a : I -> Real) (b : J -> Real)
    (ha : forall i, 0 <= a i) (ha1 : forall i, a i <= 1)
    (hb : forall j, 0 <= b j) (hb1 : forall j, b j <= 1)
    (hsa : Summable (fun i => (a i) ^ 2)) (hsb : Summable (fun j => (b j) ^ 2))
    (hprofile : canonicalBernoulliProfile a = canonicalBernoulliProfile b)
    (c : Real) (hc : 0 < c) :
    Nat.card {i // a i = c} = Nat.card {j // b j = c} := by
  have horder := congrArg
    (fun f : Complex -> Complex => analyticOrderAt f (1 - 1 / (c : Complex))) hprofile
  rw [analyticOrderAt_canonicalBernoulliProfile a ha ha1 hsa c hc,
    analyticOrderAt_canonicalBernoulliProfile b hb hb1 hsb c hc] at horder
  exact_mod_cast horder

end Complex
