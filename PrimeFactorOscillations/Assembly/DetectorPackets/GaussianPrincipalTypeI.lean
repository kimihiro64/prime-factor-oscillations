/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianCoprimePoisson

/-!
# GaussianPrincipalTypeI

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
# Independent principal Type I bound for actual Gaussian ideals

The short Mobius factors, exact cofactor coprimality mask and Fourier main
remain coupled. This is an analytic component; no Type II moment or smaller
zero-free boundary is claimed.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianPrincipalTypeI

open GaussianMobiusDivisors GaussianIdealNorm GaussianPoisson GaussianIdealPoisson
open GaussianCoprimePoisson
open scoped BigOperators Classical

def twoPrime : Ideal G := Ideal.span ({(1 : G) + imaginaryUnit} : Set G)

theorem twoPrime_norm : Ideal.absNorm twoPrime = 2 := by
  rw [twoPrime, principal_absNorm]
  norm_num [imaginaryUnit, GaussianResidueField.imaginaryUnit, Zsqrtd.norm]

theorem twoPrime_ne_zero : Not (twoPrime = 0) := by
  intro hz
  have hn := Ideal.absNorm_eq_zero_iff.mpr hz
  rw [twoPrime_norm] at hn
  norm_num at hn

theorem twoPrime_square : twoPrime * twoPrime = Ideal.span ({(2 : G)} : Set G) := by
  have hg : ((1 : G) + imaginaryUnit) * ((1 : G) + imaginaryUnit) =
      (unitI : G) * (2 : G) := by
    apply Zsqrtd.ext <;>
      norm_num [unitI, imaginaryUnit, GaussianResidueField.imaginaryUnit]
  unfold twoPrime
  rw [Ideal.span_singleton_mul_span_singleton, hg,
    Ideal.span_singleton_mul_left_unit unitI.isUnit]

theorem ramified_mask (H I : Ideal G) :
    IsRelPrime (twoPrime * H) I <->
      IsRelPrime (Ideal.span ({(2 : G)} : Set G)) I /\ IsRelPrime H I := by
  rw [IsRelPrime.mul_left_iff, <- twoPrime_square, IsRelPrime.mul_left_iff]
  simp only [and_self]

theorem ideal_card_le (A : Finset NonzeroIdeal) (U : Nat) (hU : 1 <= U)
    (hA : forall I, Membership.mem A I -> Ideal.absNorm I.val <= U) :
    A.card <= 9 * U := by
  let m : {I : NonzeroIdeal // Membership.mem A I} ->
      {z : G // Membership.mem (GaussianLatticeCount.ball U) z} := fun I =>
    Subtype.mk (generator I.val) (by
      apply (GaussianLatticeCount.mem_ball U _).mpr
      have hn : (generator I.val).norm.natAbs <= U := by
        rw [generator_norm]
        exact hA I.val I.property
      have hi : ((generator I.val).norm.natAbs : Int) <= (U : Int) := by exact_mod_cast hn
      simpa only [GaussianArithmetic.GaussianInt.abs_natCast_norm] using hi)
  have hm : Function.Injective m := by
    intro I J h
    apply Subtype.ext
    exact GaussianCoprimePoisson.generator_injective (congrArg Subtype.val h)
  calc
    _ = Fintype.card {I : NonzeroIdeal // Membership.mem A I} := (Fintype.card_coe A).symm
    _ <= Fintype.card {z : G // Membership.mem (GaussianLatticeCount.ball U) z} :=
      Fintype.card_le_of_injective m hm
    _ = (GaussianLatticeCount.ball U).card := Fintype.card_coe _
    _ <= 9 * U := GaussianLatticeCount.ball_card_le U hU

def mu (I : NonzeroIdeal) : Complex := (UniqueFactorizationMonoid.moebius I.val : Complex)

def inverseSum (A : Finset NonzeroIdeal) : Complex :=
  A.sum fun I => mu I / (Ideal.absNorm I.val : Complex)

def typeI (A B : Finset NonzeroIdeal) (H : Ideal G) (D : Real) (W : Real -> Complex) :
    Complex :=
  A.sum fun a => B.sum fun b => mu a * mu b *
    maskedSum H W (D / ((Ideal.absNorm a.val : Real) * (Ideal.absNorm b.val : Real)))

def mainTerm (A B : Finset NonzeroIdeal) (H : Ideal G) (D : Real)
    (f : SchwartzMap Complex Complex) : Complex :=
  A.sum fun a => B.sum fun b => mu a * mu b *
    (((D / ((Ideal.absNorm a.val : Real) * (Ideal.absNorm b.val : Real)) : Real) : Complex) / 4) *
      (FourierTransform.fourier f) 0 * density H

theorem mainTerm_factored (A B : Finset NonzeroIdeal) (H : Ideal G) (D : Real)
    (f : SchwartzMap Complex Complex) :
    mainTerm A B H D f = ((D : Complex) / 4) * (FourierTransform.fourier f) 0 *
      density H * (inverseSum A * inverseSum B) := by
  unfold mainTerm inverseSum
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [div_eq_mul_inv, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast]
  ring

theorem error_card (A B : Finset NonzeroIdeal) (H : Ideal G) (hH : Not (H = 0))
    (D : Real) (hD : 0 < D) (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (hzero : W 0 = 0) :
    norm (typeI A B H D W - mainTerm A B H D f) <=
      (poissonBound f / 4) * ((divisors H).card : Real) * (A.card : Real) * (B.card : Real) := by
  let e : NonzeroIdeal -> NonzeroIdeal -> Complex := fun a b => mu a * mu b *
    (maskedSum H W (D / ((Ideal.absNorm a.val : Real) * (Ideal.absNorm b.val : Real))) -
      (((D / ((Ideal.absNorm a.val : Real) * (Ideal.absNorm b.val : Real)) : Real) : Complex) / 4) *
        (FourierTransform.fourier f) 0 * density H)
  have heq : typeI A B H D W - mainTerm A B H D f = A.sum (fun a => B.sum (e a)) := by
    unfold typeI mainTerm
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    dsimp only [e]
    ring
  have hp (a b : NonzeroIdeal) :
      norm (e a b) <= (poissonBound f / 4) * ((divisors H).card : Real) := by
    have hh := uniform_masked_error H hH f W hW hzero
      (D / ((Ideal.absNorm a.val : Real) * (Ideal.absNorm b.val : Real)))
      (div_pos hD (mul_pos (GaussianCoprimePoisson.norm_pos a.val a.property)
        (GaussianCoprimePoisson.norm_pos b.val b.property)))
    have hm : norm (mu a * mu b) <= 1 := by
      rw [norm_mul]
      simpa only [mu, one_mul] using
        mul_le_mul (mobius_norm_le_one a.val) (mobius_norm_le_one b.val)
          (norm_nonneg _) zero_le_one
    dsimp only [e]
    rw [norm_mul]
    exact (mul_le_mul hm hh (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [heq]
  calc
    _ <= A.sum (fun a => norm (B.sum (e a))) := norm_sum_le _ _
    _ <= A.sum (fun a => B.sum (fun b => norm (e a b))) :=
      Finset.sum_le_sum (fun a ha => norm_sum_le _ _)
    _ <= A.sum (fun _ => B.sum (fun _ =>
        (poissonBound f / 4) * ((divisors H).card : Real))) :=
      Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hp a b))
    _ = _ := by simp [mul_comm, mul_left_comm, mul_assoc]

theorem error_cutoffs (A B : Finset NonzeroIdeal) (H : Ideal G) (hH : Not (H = 0))
    (U V : Nat) (hU : 1 <= U) (hV : 1 <= V)
    (hA : forall I, Membership.mem A I -> Ideal.absNorm I.val <= U)
    (hB : forall I, Membership.mem B I -> Ideal.absNorm I.val <= V)
    (D : Real) (hD : 0 < D) (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (hzero : W 0 = 0) :
    norm (typeI A B H D W - mainTerm A B H D f) <=
      (81 / 4 : Real) * poissonBound f * ((divisors H).card : Real) * U * V := by
  have hC : 0 <= poissonBound f :=
    (norm_nonneg _).trans (uniform_gaussian_error f 1 zero_lt_one)
  have hcoeff : 0 <= (poissonBound f / 4) * ((divisors H).card : Real) := by positivity
  have hAc : (A.card : Real) <= 9 * (U : Real) := by exact_mod_cast ideal_card_le A U hU hA
  have hBc : (B.card : Real) <= 9 * (V : Real) := by exact_mod_cast ideal_card_le B V hV hB
  have hprod : (A.card : Real) * (B.card : Real) <= (9 * (U : Real)) * (9 * (V : Real)) :=
    mul_le_mul hAc hBc (by positivity) (by positivity)
  calc
    _ <= (poissonBound f / 4) * ((divisors H).card : Real) * (A.card : Real) * (B.card : Real) :=
      error_card A B H hH D hD f W hW hzero
    _ = ((poissonBound f / 4) * ((divisors H).card : Real)) *
        ((A.card : Real) * (B.card : Real)) := by ring
    _ <= ((poissonBound f / 4) * ((divisors H).card : Real)) *
        ((9 * (U : Real)) * (9 * (V : Real))) := mul_le_mul_of_nonneg_left hprod hcoeff
    _ = _ := by ring

end PrimeFactorOscillations.GaussianPrincipalTypeI
