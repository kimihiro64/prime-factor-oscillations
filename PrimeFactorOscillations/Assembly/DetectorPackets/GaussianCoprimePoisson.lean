/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianIdealPrincipalPacket

/-!
# GaussianCoprimePoisson

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
# Exact coprimality-masked Gaussian Poisson estimate

The mask is the full finite ideal-divisor Mobius sum. Every cofactor scale
is positive; repeated and ramified prime factors are not erased by hand.
The Fourier zero mode remains exact, without an asymptotic replacement.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianCoprimePoisson

open GaussianMobiusDivisors GaussianIdealNorm GaussianPoisson GaussianIdealPoisson
open GaussianIdealPrincipalPacket (idealSum)
open scoped BigOperators Classical

theorem gcd_ne_zero (B I : Ideal G) (hB : Not (B = 0)) :
    Not (gcd B I = 0) := by
  intro hg
  choose J hJ using gcd_dvd_left B I
  rw [hg, zero_mul] at hJ
  exact hB hJ

theorem coprime_iff_gcd_one (B I : Ideal G) :
    IsRelPrime B I <-> gcd B I = 1 := by
  constructor
  . intro h
    exact isUnit_iff_eq_one.mp (h (gcd_dvd_left B I) (gcd_dvd_right B I))
  . intro h E hEB hEI
    apply isUnit_of_dvd_one
    rw [<- h]
    exact dvd_gcd hEB hEI

theorem common_divisor_mask (B : Ideal G) (hB : Not (B = 0)) (I : NonzeroIdeal) :
    (divisors B).sum (fun E =>
      if Dvd.dvd E I.val then (UniqueFactorizationMonoid.moebius E : Complex) else 0) =
      if IsRelPrime B I.val then 1 else 0 := by
  classical
  have hg := gcd_ne_zero B I.val hB
  have hfilter : (divisors B).filter (fun E => Dvd.dvd E I.val) = divisors (gcd B I.val) := by
    ext E
    simp only [Finset.mem_filter, mem_divisors hB, mem_divisors hg]
    exact (dvd_gcd_iff E B I.val).symm
  calc
    _ = ((divisors B).filter (fun E => Dvd.dvd E I.val)).sum
        (fun E => (UniqueFactorizationMonoid.moebius E : Complex)) := by
      rw [Finset.sum_filter]
    _ = (divisors (gcd B I.val)).sum
        (fun E => (UniqueFactorizationMonoid.moebius E : Complex)) := by rw [hfilter]
    _ = if gcd B I.val = 1 then 1 else 0 := sum_mobius_divisors _ hg
    _ = _ := by simp only [coprime_iff_gcd_one]

def multipleMap (E : Ideal G) (hE : Not (E = 0)) (I : NonzeroIdeal) :
    {J : NonzeroIdeal // Dvd.dvd E J.val} :=
  Subtype.mk (Subtype.mk (E * I.val) (mul_ne_zero hE I.property))
    (Exists.intro I.val rfl)

theorem multipleMap_injective (E : Ideal G) (hE : Not (E = 0)) :
    Function.Injective (multipleMap E hE) := by
  intro I J h
  apply Subtype.ext
  exact IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hE
    (congrArg (fun K => K.val.val) h)

theorem multipleMap_surjective (E : Ideal G) (hE : Not (E = 0)) :
    Function.Surjective (multipleMap E hE) := by
  intro I
  choose J hJ using I.property
  have hJ0 : Not (J = 0) := by
    intro hz
    apply I.val.property
    rw [hJ, hz, mul_zero]
  refine Exists.intro (Subtype.mk J hJ0) (Subtype.ext (Subtype.ext ?_))
  exact hJ.symm

def multipleEquiv (E : Ideal G) (hE : Not (E = 0)) :
    Equiv NonzeroIdeal {J : NonzeroIdeal // Dvd.dvd E J.val} :=
  Equiv.ofBijective (multipleMap E hE)
    (And.intro (multipleMap_injective E hE) (multipleMap_surjective E hE))

theorem norm_pos (E : Ideal G) (hE : Not (E = 0)) : 0 < (Ideal.absNorm E : Real) := by
  have hn : 0 < Ideal.absNorm E :=
    Nat.pos_iff_ne_zero.mpr (fun hz => hE (Ideal.absNorm_eq_zero_iff.mp hz))
  exact_mod_cast hn

theorem multiples_sum (E : Ideal G) (hE : Not (E = 0))
    (W : Real -> Complex) (X : Real) (hX : 0 < X) :
    (tsum fun I : NonzeroIdeal =>
      if Dvd.dvd E I.val then W ((Ideal.absNorm I.val : Real) / X) else 0) =
      idealSum W (X / (Ideal.absNorm E : Real)) := by
  classical
  have hsub :
      (tsum fun I : {I : NonzeroIdeal // Dvd.dvd E I.val} =>
        W ((Ideal.absNorm I.val.val : Real) / X)) =
      tsum (fun I : NonzeroIdeal =>
        if Dvd.dvd E I.val then W ((Ideal.absNorm I.val : Real) / X) else 0) := by
    exact tsum_subtype (fun I : NonzeroIdeal => Dvd.dvd E I.val)
      (fun I : NonzeroIdeal => W ((Ideal.absNorm I.val : Real) / X))
  rw [<- hsub]
  have hreindex := (multipleEquiv E hE).tsum_eq
    (fun I : {I : NonzeroIdeal // Dvd.dvd E I.val} =>
      W ((Ideal.absNorm I.val.val : Real) / X))
  rw [<- hreindex]
  apply tsum_congr
  intro I
  change W ((Ideal.absNorm (E * I.val) : Real) / X) =
    W ((Ideal.absNorm I.val : Real) / (X / (Ideal.absNorm E : Real)))
  rw [map_mul, Nat.cast_mul]
  congr 1
  field_simp [ne_of_gt hX, ne_of_gt (norm_pos E hE)]

theorem generator_injective : Function.Injective generator := by
  intro I J h
  apply Subtype.ext
  rw [<- generator_span I, <- generator_span J, h]

theorem ideal_summable (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (X : Real) (hX : 0 < X) :
    Summable (fun I : NonzeroIdeal => W ((Ideal.absNorm I.val : Real) / X)) := by
  have hs := (scaled_summable f X hX).comp_injective generator_injective
  apply hs.congr
  intro I
  change f (Inv.inv (Real.sqrt X : Complex) * embed (generator I)) =
    W ((Ideal.absNorm I.val : Real) / X)
  rw [hW, scaled_norm X hX, generator_norm_real]

def maskedSum (B : Ideal G) (W : Real -> Complex) (X : Real) : Complex := by
  classical
  exact tsum fun I : NonzeroIdeal =>
    if IsRelPrime B I.val then W ((Ideal.absNorm I.val : Real) / X) else 0

def density (B : Ideal G) : Complex :=
  (divisors B).sum fun E => (UniqueFactorizationMonoid.moebius E : Complex) /
    (Ideal.absNorm E : Complex)

theorem maskedSum_eq (B : Ideal G) (hB : Not (B = 0))
    (W : Real -> Complex) (X : Real) (hX : 0 < X)
    (hs : Summable (fun I : NonzeroIdeal => W ((Ideal.absNorm I.val : Real) / X))) :
    maskedSum B W X = (divisors B).sum (fun E =>
      (UniqueFactorizationMonoid.moebius E : Complex) *
        idealSum W (X / (Ideal.absNorm E : Real))) := by
  classical
  let F : Ideal G -> NonzeroIdeal -> Complex := fun E I =>
    (UniqueFactorizationMonoid.moebius E : Complex) *
      (if Dvd.dvd E I.val then W ((Ideal.absNorm I.val : Real) / X) else 0)
  have hsum (E : Ideal G) : Summable (F E) := by
    exact (hs.indicator {I : NonzeroIdeal | Dvd.dvd E I.val}).mul_left
      (UniqueFactorizationMonoid.moebius E : Complex)
  have hswap (S : Finset (Ideal G)) :
      Summable (fun I => S.sum (fun E => F E I)) /\
      (tsum fun I => S.sum (fun E => F E I)) = S.sum (fun E => tsum (F E)) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert E S hES ih =>
      constructor
      . simpa only [Finset.sum_insert hES] using (hsum E).add ih.1
      . simp only [Finset.sum_insert hES]
        rw [(hsum E).tsum_add ih.1, ih.2]
  have hpoint (I : NonzeroIdeal) :
      (if IsRelPrime B I.val then W ((Ideal.absNorm I.val : Real) / X) else 0) =
        (divisors B).sum (fun E => F E I) := by
    symm
    calc
      _ = ((divisors B).sum (fun E =>
          if Dvd.dvd E I.val then (UniqueFactorizationMonoid.moebius E : Complex) else 0)) *
            W ((Ideal.absNorm I.val : Real) / X) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro E hE
        by_cases hd : Dvd.dvd E I.val <;> simp [F, hd]
      _ = _ := by
        rw [common_divisor_mask B hB I]
        by_cases hr : IsRelPrime B I.val <;> simp [hr]
  calc
    _ = tsum (fun I => (divisors B).sum (fun E => F E I)) := tsum_congr hpoint
    _ = (divisors B).sum (fun E => tsum (F E)) := (hswap _).2
    _ = _ := by
      apply Finset.sum_congr rfl
      intro E hE
      simp only [F, tsum_mul_left]
      rw [multiples_sum E (divisor_ne_zero hB hE) W X hX]

theorem uniform_masked_error (B : Ideal G) (hB : Not (B = 0))
    (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (hzero : W 0 = 0)
    (X : Real) (hX : 0 < X) :
    norm (maskedSum B W X -
      ((X : Complex) / 4) * (FourierTransform.fourier f) 0 * density B) <=
      (poissonBound f / 4) * ((divisors B).card : Real) := by
  classical
  have heq : maskedSum B W X -
      ((X : Complex) / 4) * (FourierTransform.fourier f) 0 * density B =
      (divisors B).sum (fun E => (UniqueFactorizationMonoid.moebius E : Complex) *
        (idealSum W (X / (Ideal.absNorm E : Real)) -
          (((X / (Ideal.absNorm E : Real) : Real) : Complex) / 4) *
            (FourierTransform.fourier f) 0)) := by
    rw [maskedSum_eq B hB W X hX (ideal_summable f W hW X hX)]
    unfold density
    rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro E hE
    rw [Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  have hp (E : Ideal G) (hE : Membership.mem (divisors B) E) :
      norm ((UniqueFactorizationMonoid.moebius E : Complex) *
        (idealSum W (X / (Ideal.absNorm E : Real)) -
          (((X / (Ideal.absNorm E : Real) : Real) : Complex) / 4) *
            (FourierTransform.fourier f) 0)) <= poissonBound f / 4 := by
    have hh := uniform_ideal_error f W hW hzero (X / (Ideal.absNorm E : Real))
      (div_pos hX (norm_pos E (divisor_ne_zero hB hE)))
    rw [norm_mul]
    exact (mul_le_mul (mobius_norm_le_one E) hh (norm_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  rw [heq]
  calc
    _ <= (divisors B).sum (fun E => norm ((UniqueFactorizationMonoid.moebius E : Complex) *
        (idealSum W (X / (Ideal.absNorm E : Real)) -
          (((X / (Ideal.absNorm E : Real) : Real) : Complex) / 4) *
            (FourierTransform.fourier f) 0))) := norm_sum_le _ _
    _ <= (divisors B).sum (fun _ => poissonBound f / 4) := Finset.sum_le_sum hp
    _ = _ := by simp [mul_comm]

end PrimeFactorOscillations.GaussianCoprimePoisson
