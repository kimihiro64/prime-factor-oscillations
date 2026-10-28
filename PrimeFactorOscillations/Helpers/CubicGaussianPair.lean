/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicGaussianUnit
import PrimeFactorOscillations.Helpers.CubicInertPhase

/-!
# Actual Gaussian Poisson transfer for native cubic pairs

Matches the pinned periodic Gaussian Poisson theorem to the paper's exact
Gaussian normalization and native cubic Gauss factors. The pair identity
holds for every admissible coprime pair and every positive Gaussian rate,
without a global real Schwartz-window premise. Finite trace phases and
all row coefficients are retained. This is a physical theta transfer;
it does not bound the prime-sampled reciprocal-L arithmetic packet.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CubicGaussianPair
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT EisensteinEmbedding CubicSieve
open CubicReciprocalGaussian ProbeRadialMellin
local notation "Eis" => ActualEisensteinCubic.O

theorem gaussian_rescale (a : Real) (z : Complex) :
    GaussianTheta.gaussian (2 * a / Real.sqrt 3) z = gaussian a z := by
  unfold GaussianTheta.gaussian gaussian paperConstant
  congr 1
  push_cast
  ring

theorem periodic_gaussian (c : Eis) (hc : Not (c = 0))
    (P : HasQuotient.Quotient Eis (Ideal.span {c}) -> Complex)
    (a : Real) (ha : 0 < a) :
    letI : Finite (HasQuotient.Quotient Eis (Ideal.span {c})) := finite_quotient_span hc
    letI : Fintype (HasQuotient.Quotient Eis (Ideal.span {c})) := Fintype.ofFinite _
    (tsum fun z : Eis => P (Ideal.Quotient.mk (Ideal.span {c}) z) *
      gaussian a (eisEmbedding z)) =
      ((1 / (a * norm (eisEmbedding c) ^ 2) : Real) : Complex) *
        tsum (fun h : Eis =>
          (Finset.univ.sum (fun r : HasQuotient.Quotient Eis (Ideal.span {c}) =>
            P r * (TraceCharacter.traceCharacter c hc)
              (Ideal.Quotient.mk (Ideal.span {c}) h * r))) *
            gaussian (1 / (a * norm (eisEmbedding c) ^ 2)) (eisEmbedding h)) := by
  letI : NeZero c := NeZero.mk hc
  letI : Finite (HasQuotient.Quotient Eis (Ideal.span {c})) := finite_quotient_span hc
  letI : Fintype (HasQuotient.Quotient Eis (Ideal.span {c})) := Fintype.ofFinite _
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hn : Not (norm (eisEmbedding c) = 0) :=
    norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc)
  have hrate : 0 < 2 * a / Real.sqrt 3 := div_pos (by positivity) hs
  have hp := GaussianTheta.periodic_gaussian_poisson c P (2 * a / Real.sqrt 3) hrate
  have hPref : 2 / (Real.sqrt 3 *
      ((2 * a / Real.sqrt 3) * norm (eisEmbedding c) ^ 2)) =
      1 / (a * norm (eisEmbedding c) ^ 2) := by
    field_simp [hs.ne', ha.ne', hn]
  have hDual : 4 / (3 * ((2 * a / Real.sqrt 3) * norm (eisEmbedding c) ^ 2)) =
      2 * (1 / (a * norm (eisEmbedding c) ^ 2)) / Real.sqrt 3 := by
    have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    field_simp [hs.ne', ha.ne', hn]
    nlinarith only [hs2]
  rw [hPref, hDual] at hp
  simpa only [gaussian_rescale] using hp

def gaussianPair (I J : Ideal Eis) (a : Real) : Complex :=
  tsum fun z : Eis => (star (cubicRow I z) * cubicRow J z) *
    gaussian a (eisEmbedding z)

theorem gaussian_pair_poisson (I J : Ideal Eis)
    (hI : Admissible I) (hJ : Admissible J) (hcop : IsCoprime I J)
    (a : Real) (ha : 0 < a) :
    gaussianPair I J a =
      (star (gaussTwo I hI.2) * gaussTwo J hJ.2) /
        ((a : Complex) * (CubicPairReflection.pairScale I J : Complex)) *
          gaussianPair J I (1 / (a * CubicPairReflection.pairScale I J ^ 2)) := by
  let c := primaryGenerator I * primaryGenerator J
  have hc : Not (c = 0) := mul_ne_zero hI.2 hJ.2
  letI : Finite (HasQuotient.Quotient Eis (Ideal.span {c})) := finite_quotient_span hc
  letI : Fintype (HasQuotient.Quotient Eis (Ideal.span {c})) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (pairPrime_modulus I J hI hJ)
  letI : Fintype (HasQuotient.Quotient Eis (Finset.univ.prod (pairPrime I J))) :=
    Fintype.ofEquiv (HasQuotient.Quotient Eis (Ideal.span {c})) e.toEquiv
  letI (P : Sum (PrimeIndex I) (PrimeIndex J)) :
      Fintype (HasQuotient.Quotient Eis (pairPrime I J P)) := Fintype.ofFinite _
  let row := pairPrincipalRow I J hI hJ hcop
  let psi := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let G := Finset.univ.sum (fun r : HasQuotient.Quotient Eis (Ideal.span {c}) =>
    row r * psi r)
  have ht (h : Eis) :
      Finset.univ.sum (fun r : HasQuotient.Quotient Eis (Ideal.span {c}) =>
        row r * psi (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
      (cubicRow I h * star (cubicRow J h)) * G := by
    have hh := canonical_principal_gauss_transform_of_nontrivial (pairPrime I J)
      (pairPrime_coprime I J hI hJ hcop) (pairPrime_good I J hI hJ)
      (pairExponent I J) (pairExponent_nonprincipal I J hI hJ) c
      (pairPrime_modulus I J hI hJ) psi (Ideal.Quotient.mk (Ideal.span {c}) h)
    change Finset.univ.sum (fun r => row r *
      psi (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
        star (pairPrincipalRow I J hI hJ hcop (Ideal.Quotient.mk _ h)) * G at hh
    rw [pairPrincipalRow_mk I J hI hJ hcop h, star_mul, star_star,
      mul_comm (star (cubicRow J h)) (cubicRow I h)] at hh
    exact hh
  have hp := periodic_gaussian c hc row a ha
  change (tsum fun z : Eis => row (Ideal.Quotient.mk (Ideal.span {c}) z) *
      gaussian a (eisEmbedding z)) =
    ((1 / (a * norm (eisEmbedding c) ^ 2) : Real) : Complex) *
      tsum (fun h : Eis => (Finset.univ.sum (fun r =>
        row r * psi (Ideal.Quotient.mk (Ideal.span {c}) h * r))) *
          gaussian (1 / (a * norm (eisEmbedding c) ^ 2)) (eisEmbedding h)) at hp
  have hsum : (tsum fun h : Eis =>
      (Finset.univ.sum (fun r => row r *
        psi (Ideal.Quotient.mk (Ideal.span {c}) h * r))) *
          gaussian (1 / (a * norm (eisEmbedding c) ^ 2)) (eisEmbedding h)) =
      G * gaussianPair J I (1 / (a * norm (eisEmbedding c) ^ 2)) := by
    calc
      _ = tsum (fun h : Eis => ((cubicRow I h * star (cubicRow J h)) * G) *
          gaussian (1 / (a * norm (eisEmbedding c) ^ 2)) (eisEmbedding h)) :=
        tsum_congr (fun h => congrArg
          (fun z : Complex => z *
            gaussian (1 / (a * norm (eisEmbedding c) ^ 2)) (eisEmbedding h)) (ht h))
      _ = _ := by
        unfold gaussianPair
        rw [<- tsum_mul_left]
        apply tsum_congr
        intro h
        ring
  have hrow (z : Eis) : row (Ideal.Quotient.mk (Ideal.span {c}) z) =
      star (cubicRow I z) * cubicRow J z :=
    pairPrincipalRow_mk I J hI hJ hcop z
  have hleft : (tsum fun z : Eis => row (Ideal.Quotient.mk (Ideal.span {c}) z) *
      gaussian a (eisEmbedding z)) = gaussianPair I J a :=
    tsum_congr (fun z => congrArg
      (fun x : Complex => x * gaussian a (eisEmbedding z)) (hrow z))
  have hCombined : gaussianPair I J a =
      ((1 / (a * norm (eisEmbedding c) ^ 2) : Real) : Complex) *
        (G * gaussianPair J I (1 / (a * norm (eisEmbedding c) ^ 2))) :=
    hleft.symm.trans (hp.trans (congrArg
      (fun x : Complex => ((1 / (a * norm (eisEmbedding c) ^ 2) : Real) : Complex) * x)
        hsum))
  rw [hCombined]
  have hn : Not ((norm (eisEmbedding c) : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc))
  have hGauss := pairPrincipalGauss_separation I J hI hJ hcop
  change G / (norm (eisEmbedding c) : Complex) =
    star (gaussTwo I hI.2) * gaussTwo J hJ.2 at hGauss
  have hG := (div_eq_iff hn).mp hGauss
  change ((1 / (a * norm (eisEmbedding c) ^ 2) : Real) : Complex) *
      (G * gaussianPair J I (1 / (a * norm (eisEmbedding c) ^ 2))) =
    (star (gaussTwo I hI.2) * gaussTwo J hJ.2) /
      ((a : Complex) * (norm (eisEmbedding c) : Complex)) *
        gaussianPair J I (1 / (a * norm (eisEmbedding c) ^ 2))
  rw [hG]
  push_cast
  have haC : Not ((a : Complex) = 0) := by exact_mod_cast ha.ne'
  field_simp [hn, haC]
  <;> ring

end PrimeFactorOscillations.CubicGaussianPair
