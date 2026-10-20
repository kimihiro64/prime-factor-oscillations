/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.Eisenstein.CompactEnergyFamilies

/-!
# EisensteinPrimeMark

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
Exact prime extraction for the actual Eisenstein Gauss coefficient.
The two directed residue factors are retained before cubic reciprocity.
The shared-prime coefficient is proved zero, so the residue label supplies
its own repeated-prime mask.
-/


noncomputable section
open scoped Classical BigOperators
open OAI

namespace PrimeFactorOscillations.EisensteinPrimeMark

abbrev Eis := ActualEisensteinCubic.O

def crossValue {I : Type} (p : I -> Eis)
    [forall i, (Ideal.span {p i}).IsMaximal]
    (hg : forall i, Not (Membership.mem (Ideal.span {p i})
      ActualEisensteinCubic.lambda)) (i j : I) : Complex :=
  ActualEisensteinCubic.canonicalSextic (Ideal.span {p i}) (hg i)
    (Ideal.Quotient.mk (Ideal.span {p i}) (p j))

def crossAll {I : Type} [Fintype I] (p : I -> Eis)
    [forall i, (Ideal.span {p i}).IsMaximal]
    (hg : forall i, Not (Membership.mem (Ideal.span {p i})
      ActualEisensteinCubic.lambda)) : Complex :=
  Finset.univ.prod (fun i => Finset.univ.prod
    (fun j => if i = j then 1 else crossValue p hg i j))

theorem crossAll_eq {I : Type} [Fintype I] (p : I -> Eis)
    [forall i, (Ideal.span {p i}).IsMaximal]
    (hg : forall i, Not (Membership.mem (Ideal.span {p i})
      ActualEisensteinCubic.lambda)) :
    crossAll p hg = FiniteGaussPhase.canonicalCrossFactor p hg := by
  unfold crossAll FiniteGaussPhase.canonicalCrossFactor
  apply Finset.prod_congr rfl
  intro i hi
  have he := Finset.prod_erase_mul (Finset.univ : Finset I)
    (fun j => if i = j then (1 : Complex) else crossValue p hg i j)
    (Finset.mem_univ i)
  simp only [ite_true, mul_one] at he
  rw [<- he]
  apply Finset.prod_congr rfl
  intro j hj
  have hn : Not (i = j) := Ne.symm (Finset.mem_erase.mp hj).1
  simp only [ite_eq_right hn, crossValue]

def localValue {I : Type} (p : I -> Eis)
    (hp : forall i, Not (p i = 0))
    [forall i, (Ideal.span {p i}).IsMaximal]
    (hg : forall i, Not (Membership.mem (Ideal.span {p i})
      ActualEisensteinCubic.lambda)) (i : I) : Complex :=
  star (FiniteGaussPhase.angularFactor (p i)) *
    ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
      (ActualEisensteinCubic.canonicalSextic (Ideal.span {p i}) (hg i) ^ 2)

theorem crossAll_option {I : Type} [Fintype I] (p : Option I -> Eis)
    [forall i, (Ideal.span {p i}).IsMaximal]
    (hg : forall i, Not (Membership.mem (Ideal.span {p i})
      ActualEisensteinCubic.lambda)) :
    crossAll p hg =
      crossAll (fun i => p (some i)) (fun i => hg (some i)) *
        Finset.univ.prod (fun i => crossValue p hg none (some i)) *
        Finset.univ.prod (fun i => crossValue p hg (some i) none) := by
  simp only [crossAll, Fintype.prod_option, Option.some.injEq,
    reduceCtorEq, ite_true, ite_false, one_mul]
  rw [Finset.prod_mul_distrib]
  dsimp only [crossValue]
  ring

theorem some_coprime {I : Type} (p : Option I -> Eis)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) :
    Pairwise (Function.onFun IsCoprime (fun i : I => Ideal.span {p (some i)})) := by
  intro i j hij
  exact hcop (fun h => hij (Option.some.inj h))

theorem canonical_prime_extraction {I : Type} [Fintype I]
    (p : Option I -> Eis) (hp : forall i, Not (p i = 0))
    [forall i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : forall i, Not (Membership.mem (Ideal.span {p i})
      ActualEisensteinCubic.lambda)) :
    FiniteGaussPhase.canonicalProductCoefficient p hp hcop hg =
      localValue p hp hg none *
        FiniteGaussPhase.canonicalProductCoefficient
          (fun i => p (some i)) (fun i => hp (some i))
          (some_coprime p hcop) (fun i => hg (some i)) *
        (Finset.univ.prod (fun i => crossValue p hg none (some i)) *
          Finset.univ.prod (fun i => crossValue p hg (some i) none)) ^ 2 := by
  have hf := FiniteGaussPhase.canonicalProductCoefficient_crt p hp hcop hg
  have hs := FiniteGaussPhase.canonicalProductCoefficient_crt
    (fun i => p (some i)) (fun i => hp (some i))
    (some_coprime p hcop) (fun i => hg (some i))
  rw [<- crossAll_eq p hg] at hf
  rw [<- crossAll_eq (fun i => p (some i)) (fun i => hg (some i))] at hs
  rw [hf, hs, crossAll_option, Fintype.prod_option]
  dsimp only [localValue]
  ring

theorem ideal_prime_extraction {I : Type} [Fintype I]
    (p : Option I -> Eis) (hp : forall i, Not (p i = 0))
    [forall i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : forall i, Not (Membership.mem (Ideal.span {p i})
      ActualEisensteinCubic.lambda))
    (hprimary : forall i, Dvd.dvd (ActualEisensteinCubic.lambda ^ 2) (p i - 1)) :
    CompletedGauss.squarefreeGaussCoefficient
        (Ideal.span {Finset.univ.prod p}) =
      localValue p hp hg none *
        CompletedGauss.squarefreeGaussCoefficient
          (Ideal.span {Finset.univ.prod (fun i => p (some i))}) *
        (Finset.univ.prod (fun i => crossValue p hg none (some i)) *
          Finset.univ.prod (fun i => crossValue p hg (some i) none)) ^ 2 := by
  rw [CompletedGauss.squarefreeGaussCoefficient_eq_canonicalProductCoefficient
      p hp hcop hg hprimary,
    CompletedGauss.squarefreeGaussCoefficient_eq_canonicalProductCoefficient
      (fun i => p (some i)) (fun i => hp (some i))
      (some_coprime p hcop) (fun i => hg (some i))
      (fun i => hprimary (some i))]
  exact canonical_prime_extraction p hp hcop hg

theorem repeated_prime_zero (P A : Ideal Eis) (hP : Prime P)
    (hPA : Dvd.dvd P A) :
    CompletedGauss.squarefreeGaussCoefficient (P * A) = 0 := by
  have hs : Not (Squarefree (P * A)) := by
    intro h
    exact hP.not_isUnit (h P (mul_dvd_mul_left P hPA))
  simp only [CompletedGauss.squarefreeGaussCoefficient, hs, false_and, dite_false]

theorem cross_phase_fourth {I : Type} [Fintype I]
    (p : Option I -> Eis)
    [forall i, (Ideal.span {p i}).IsMaximal]
    (hg : forall i, Not (Membership.mem (Ideal.span {p i})
      ActualEisensteinCubic.lambda))
    (hprimary : forall i, Dvd.dvd (ActualEisensteinCubic.lambda ^ 2) (p i - 1)) :
    (Finset.univ.prod (fun i => crossValue p hg none (some i)) *
      Finset.univ.prod (fun i => crossValue p hg (some i) none)) ^ 2 =
      Finset.univ.prod (fun i => crossValue p hg (some i) none) ^ 4 := by
  have he :
      Finset.univ.prod (fun i => crossValue p hg none (some i)) ^ 2 =
        Finset.univ.prod (fun i => crossValue p hg (some i) none) ^ 2 := by
    rw [<- Finset.prod_pow, <- Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i hi
    exact ActualEisensteinCubic.canonicalSextic_sq_reciprocity_primary
      (Ideal.span {p none}) (Ideal.span {p (some i)})
      (hg none) (hg (some i)) (p none) (p (some i)) rfl rfl
      (hprimary none) (hprimary (some i))
  rw [mul_pow, he]
  ring

theorem residue_label_eq {I : Type} [Fintype I]
    (p : Option I -> Eis)
    [forall i, (Ideal.span {p i}).IsMaximal]
    (hg : forall i, Not (Membership.mem (Ideal.span {p i})
      ActualEisensteinCubic.lambda)) :
    Finset.univ.prod (fun i => crossValue p hg (some i) none) =
      CanonicalRowCompletion.idealRowHom (p none)
        (Ideal.span {Finset.univ.prod (fun i => p (some i))}) := by
  have h := CanonicalRowCompletion.idealRowHom_product
    (fun i : I => p (some i)) (fun i => hg (some i))
    (Finset.univ : Finset I) (p none)
  change CanonicalRowCompletion.idealRowHom (p none)
      (Ideal.span {Finset.univ.prod (fun i => p (some i))}) =
    Finset.univ.prod (fun i => crossValue p hg (some i) none) at h
  exact h.symm

theorem ideal_prime_extraction_fourth {I : Type} [Fintype I]
    (p : Option I -> Eis) (hp : forall i, Not (p i = 0))
    [forall i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : forall i, Not (Membership.mem (Ideal.span {p i})
      ActualEisensteinCubic.lambda))
    (hprimary : forall i, Dvd.dvd (ActualEisensteinCubic.lambda ^ 2) (p i - 1)) :
    CompletedGauss.squarefreeGaussCoefficient
        (Ideal.span {Finset.univ.prod p}) =
      localValue p hp hg none *
        CompletedGauss.squarefreeGaussCoefficient
          (Ideal.span {Finset.univ.prod (fun i => p (some i))}) *
        CanonicalRowCompletion.idealRowHom (p none)
          (Ideal.span {Finset.univ.prod (fun i => p (some i))}) ^ 4 := by
  rw [ideal_prime_extraction p hp hcop hg hprimary,
    cross_phase_fourth p hg hprimary, residue_label_eq p hg]

theorem prime_label_zero (p : Eis) [(Ideal.span {p}).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) ActualEisensteinCubic.lambda))
    (A : Ideal Eis) (hPA : Dvd.dvd (Ideal.span {p}) A) :
    CanonicalRowCompletion.idealRowHom p A ^ 4 = 0 := by
  choose B hB using hPA
  have hz : CanonicalRowCompletion.idealRowHom p (Ideal.span {p}) = 0 := by
    rw [CanonicalRowCompletion.idealRowHom_prime p (Ideal.span {p}) hg,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)),
      MulChar.map_zero]
  rw [hB, map_mul, hz, zero_mul, zero_pow (by decide)]

end PrimeFactorOscillations.EisensteinPrimeMark

