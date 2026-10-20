/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianIdealNorm
import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianPoisson

/-!
# GaussianIdealPoisson

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
# Uniform Gaussian ideal Poisson estimate

The unit/ideal reindex follows the pinned OAI ReflectionBrackets argument.
The Gaussian specialization uses every nonzero ideal and exactly four units.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianIdealPoisson

open GaussianMobiusDivisors GaussianIdealNorm GaussianPoisson
open OAI.EisensteinSchwartzPoisson
open scoped BigOperators

abbrev NonzeroIdeal := {I : Ideal G // Not (I = 0)}
abbrev NonzeroElement := {z : G // Not (z = 0)}

def generator (I : NonzeroIdeal) : G :=
  Submodule.IsPrincipal.generator I.val

theorem generator_span (I : NonzeroIdeal) :
    Ideal.span ({generator I} : Set G) = I.val :=
  Submodule.IsPrincipal.span_singleton_generator I.val

theorem generator_ne_zero (I : NonzeroIdeal) : Not (generator I = 0) := by
  intro hz
  apply I.property
  rw [<- generator_span I, hz]
  exact Ideal.span_singleton_eq_bot.mpr rfl

theorem generator_norm (I : NonzeroIdeal) :
    (generator I).norm.natAbs = Ideal.absNorm I.val := by
  rw [<- principal_absNorm, generator_span]

theorem generator_norm_real (I : NonzeroIdeal) :
    ((generator I).norm : Real) = (Ideal.absNorm I.val : Real) := by
  rw [<- generator_norm, GaussianArithmetic.GaussianInt.natCast_natAbs_norm]

theorem span_unit_generator (u : Units G) (I : NonzeroIdeal) :
    Ideal.span ({(u : G) * generator I} : Set G) = I.val := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit]
  exact generator_span I

def unitIdealToElement (p : Prod (Units G) NonzeroIdeal) : NonzeroElement :=
  Subtype.mk ((p.1 : G) * generator p.2)
    (mul_ne_zero (Units.ne_zero p.1) (generator_ne_zero p.2))

theorem unitIdealToElement_injective : Function.Injective unitIdealToElement := by
  intro p q hpq
  have he : (p.1 : G) * generator p.2 = (q.1 : G) * generator q.2 :=
    congrArg Subtype.val hpq
  have hI : p.2 = q.2 := by
    apply Subtype.ext
    simpa only [span_unit_generator] using
      congrArg (fun z : G => Ideal.span ({z} : Set G)) he
  have hu : p.1 = q.1 := by
    apply Units.ext
    rw [hI] at he
    have hh : ((p.1 : G) - (q.1 : G)) * generator q.2 = 0 := by
      rw [sub_mul, he, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (generator_ne_zero q.2))
  exact Prod.ext hu hI

theorem unitIdealToElement_surjective : Function.Surjective unitIdealToElement := by
  intro z
  let I : NonzeroIdeal := Subtype.mk (Ideal.span ({z.val} : Set G)) (by
    intro hz
    apply z.property
    apply Ideal.span_singleton_eq_bot.mp
    exact hz)
  have ha : Associated (generator I) z.val :=
    Ideal.span_singleton_eq_span_singleton.mp (generator_span I)
  choose u hu using ha
  refine Exists.intro (Prod.mk u I) (Subtype.ext ?_)
  change (u : G) * generator I = z.val
  simpa only [mul_comm] using hu

def unitIdealEquiv : Equiv (Prod (Units G) NonzeroIdeal) NonzeroElement :=
  Equiv.ofBijective unitIdealToElement
    (And.intro unitIdealToElement_injective unitIdealToElement_surjective)

theorem tsum_nonzero_product (f : G -> Complex) :
    (tsum fun z : NonzeroElement => f z.val) =
      tsum (fun p : Prod (Units G) NonzeroIdeal => f ((p.1 : G) * generator p.2)) :=
  (unitIdealEquiv.tsum_eq (fun z : NonzeroElement => f z.val)).symm

theorem tsum_nonzero_unit_invariant (f : G -> Complex)
    (hf : Summable (fun z : NonzeroElement => f z.val))
    (hu : forall u : Units G, forall I : NonzeroIdeal,
      f ((u : G) * generator I) = f (generator I)) :
    (tsum fun z : NonzeroElement => f z.val) =
      (4 : Complex) * tsum (fun I : NonzeroIdeal => f (generator I)) := by
  have hp : Summable (fun p : Prod (Units G) NonzeroIdeal =>
      f ((p.1 : G) * generator p.2)) := unitIdealEquiv.summable_iff.mpr hf
  rw [tsum_nonzero_product, hp.tsum_prod]
  simp only [hu, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, units_card]
  norm_num

theorem embed_eq (z : G) : embed z = GaussianArithmetic.GaussianInt.toComplex z :=
  (GaussianArithmetic.GaussianInt.toComplex_def2 z).symm

theorem scaled_norm (X : Real) (hX : 0 < X) (z : G) :
    Complex.normSq (Inv.inv (Real.sqrt X : Complex) * embed z) =
      (z.norm : Real) / X := by
  rw [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal,
    <- pow_two, Real.sq_sqrt hX.le, embed_eq,
    <- GaussianArithmetic.GaussianInt.intCast_real_norm]
  ring

theorem scaled_summable (f : SchwartzMap Complex Complex) (X : Real) (hX : 0 < X) :
    Summable (fun z : G => f (Inv.inv (Real.sqrt X : Complex) * embed z)) := by
  have hs := plane_lattice_summable_norm (rescale f X hX)
  have hp : Summable (fun p : Prod Int Int =>
      f (Inv.inv (Real.sqrt X : Complex) * point p)) := by
    apply Summable.of_norm
    simpa only [rescale_apply, point] using hs
  exact integerCoordinates.toEquiv.summable_iff.mpr hp

theorem tsum_nonzero_eq (f : G -> Complex) (hzero : f 0 = 0) :
    (tsum fun z : NonzeroElement => f z.val) = tsum f := by
  classical
  change (tsum fun z : {z : G // Membership.mem {z : G | Not (z = 0)} z} => f z.val) =
    tsum f
  rw [tsum_subtype]
  apply tsum_congr
  intro z
  by_cases hz : z = 0
  . subst z
    simp [hzero]
  . simp [hz]

theorem radial_sum (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (hzero : W 0 = 0)
    (X : Real) (hX : 0 < X) :
    (tsum fun z : G => f (Inv.inv (Real.sqrt X : Complex) * embed z)) =
      (4 : Complex) * tsum (fun I : NonzeroIdeal => W ((Ideal.absNorm I.val : Real) / X)) := by
  let g : G -> Complex := fun z => f (Inv.inv (Real.sqrt X : Complex) * embed z)
  have hg (z : G) : g z = W ((z.norm : Real) / X) := by
    dsimp only [g]
    rw [hW, scaled_norm X hX]
  have h0 : g 0 = 0 := by
    rw [hg]
    simpa using hzero
  have hu (u : Units G) (I : NonzeroIdeal) : g ((u : G) * generator I) = g (generator I) := by
    rw [hg, hg, Zsqrtd.norm_mul, norm_of_isUnit (u : G) u.isUnit, one_mul]
  have ht := tsum_nonzero_unit_invariant g
    ((scaled_summable f X hX).subtype (fun z : G => Not (z = 0))) hu
  rw [tsum_nonzero_eq g h0] at ht
  calc
    _ = (4 : Complex) * tsum (fun I : NonzeroIdeal => g (generator I)) := ht
    _ = _ := by
      congr 1
      apply tsum_congr
      intro I
      rw [hg, generator_norm_real]

theorem uniform_ideal_error (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (hzero : W 0 = 0)
    (X : Real) (hX : 0 < X) :
    norm ((tsum fun I : NonzeroIdeal => W ((Ideal.absNorm I.val : Real) / X)) -
      ((X : Complex) / 4) * (FourierTransform.fourier f) 0) <= poissonBound f / 4 := by
  let S : Complex := tsum fun I : NonzeroIdeal => W ((Ideal.absNorm I.val : Real) / X)
  have h := uniform_gaussian_error f X hX
  rw [radial_sum f W hW hzero X hX] at h
  change norm ((4 : Complex) * S - (X : Complex) * (FourierTransform.fourier f) 0) <=
    poissonBound f at h
  have he : (4 : Complex) * (S - ((X : Complex) / 4) * (FourierTransform.fourier f) 0) =
      (4 : Complex) * S - (X : Complex) * (FourierTransform.fourier f) 0 := by ring
  rw [<- he, norm_mul] at h
  norm_num at h
  change norm (S - ((X : Complex) / 4) * (FourierTransform.fourier f) 0) <= poissonBound f / 4
  linarith

end PrimeFactorOscillations.GaussianIdealPoisson
