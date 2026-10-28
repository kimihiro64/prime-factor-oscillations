/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicInertArithmetic

/-!
# Actual native cubic phases and inert-pair cancellation

Identifies the native Gauss cube with its canonical normalization and proves
self-dual cancellation and the uniform XH estimate for distinct inert primes.
The anti-Fourier window premise remains explicit; no global zero-free gain
or prime-carrier transfer is claimed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CubicInertPhase

open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT EisensteinEmbedding CubicSieve
open EisensteinSchwartzPoisson CubicPairReflection
local notation "Eis" => ActualEisensteinCubic.O

theorem negative_prime_primary (p : Nat) (hmod : p % 3 = 2) :
    Dvd.dvd (lambda ^ 2) (-(p : Eis) - 1) := by
  have hrel : omega ^ 2 + omega + 1 = 0 := by
    simpa only [IsCyclotomicExtension.Rat.Three.coe_eta, omega] using
      (IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
        (IsCyclotomicExtension.zeta_spec 3 Rat ActualEisensteinCubic.K))
  have hl : lambda ^ 2 = -3 * omega := by
    dsimp [lambda]
    linear_combination hrel
  have hn : p + 1 = 3 * (p / 3 + 1) := by
    have h := Nat.mod_add_div p 3
    omega
  have he : (p : Eis) + 1 = 3 * ((p / 3 + 1 : Nat) : Eis) := by exact_mod_cast hn
  refine Exists.intro (((p / 3 + 1 : Nat) : Eis) * omega ^ 2) ?_
  rw [hl]
  have hm : (-3 * omega) * (((p / 3 + 1 : Nat) : Eis) * omega ^ 2) =
      -3 * ((p / 3 + 1 : Nat) : Eis) * omega ^ 3 := by ring
  rw [hm, omega_primitive.pow_eq_one, mul_one]
  linear_combination -he

theorem rational_primaryGenerator (p : Nat) (hp : Nat.Prime p) (hmod : p % 3 = 2) :
    primaryGenerator (Ideal.span {(p : Eis)}) = -(p : Eis) := by
  have hn : Not (-(p : Eis) = 0) := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have h := primaryGenerator_span (-(p : Eis)) hn (negative_prime_primary p hmod)
  simpa only [Ideal.span_singleton_neg] using h

theorem eisLam_star : star eisLam = -eisLam := by
  have he : eisLam = (Real.sqrt 3 : Complex) * Complex.I := by
    dsimp [eisLam, omega3]
    ring
  rw [he]
  change (starRingEnd Complex) ((Real.sqrt 3 : Complex) * Complex.I) = _
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem breveE_conjugate (z : Complex) :
    ShortDraftTrace.breveE (star z) = ShortDraftTrace.breveE z := by
  change Complex.exp (2 * (Real.pi : Complex) * Complex.I * (star z + star (star z))) =
    Complex.exp (2 * (Real.pi : Complex) * Complex.I * (z + star z))
  rw [star_star]
  congr 1
  ring

theorem breveE_star (z : Complex) :
    star (ShortDraftTrace.breveE z) = ShortDraftTrace.breveE (-z) := by
  change (starRingEnd Complex)
      (Complex.exp (2 * (Real.pi : Complex) * Complex.I * (z + (starRingEnd Complex) z))) =
    Complex.exp (2 * (Real.pi : Complex) * Complex.I * (-z + (starRingEnd Complex) (-z)))
  rw [<- Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    map_add, map_neg]
  have hzz : (starRingEnd Complex) ((starRingEnd Complex) z) = z := star_star z
  rw [hzz]
  ring

theorem anti_reflection_with_phase (I J : Ideal Eis) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (M : Real) (hM : 0 < M) :
    pairedKernel I J W M =
      -((M : Complex) / (pairScale I J : Complex)) *
        (star (gaussTwo I hI.2) * gaussTwo J hJ.2) *
          pairedKernel J I W ((pairScale I J) ^ 2 / M) := by
  have hC := pairScale_pos I J hI hJ
  have hp := cubic_pair_poisson I J hI hJ hcop W M hM
  have hsum :
      (tsum fun z : Eis => CubicSieve.cubicRow I z * star (CubicSieve.cubicRow J z) *
        paperRadialFourier W (M * norm (eisEmbedding z) ^ 2 / (pairScale I J) ^ 2)) =
      -pairedKernel J I W ((pairScale I J) ^ 2 / M) := by
    rw [pairedKernel, <- tsum_neg]
    apply tsum_congr
    intro z
    have ht : 0 <= M * norm (eisEmbedding z) ^ 2 / (pairScale I J) ^ 2 := by positivity
    have he : M * norm (eisEmbedding z) ^ 2 / (pairScale I J) ^ 2 =
        norm (eisEmbedding z) ^ 2 / ((pairScale I J) ^ 2 / M) := by
      field_simp [ne_of_gt hC, ne_of_gt hM]
    rw [hanti _ ht, he]
    ring
  change pairedKernel I J W M =
    (M : Complex) * (star (gaussTwo I hI.2) * gaussTwo J hJ.2) /
      (pairScale I J : Complex) *
        (tsum fun z : Eis => CubicSieve.cubicRow I z * star (CubicSieve.cubicRow J z) *
          paperRadialFourier W (M * norm (eisEmbedding z) ^ 2 / (pairScale I J) ^ 2)) at hp
  rw [hsum] at hp
  calc
    _ = _ := hp
    _ = _ := by ring

theorem selfdual_zero_of_phase_cube (I J : Ideal Eis)
    (hI : Admissible I) (hJ : Admissible J) (hcop : IsCoprime I J)
    (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (hgI : gaussTwo I hI.2 ^ 3 = 1) (hgJ : gaussTwo J hJ.2 ^ 3 = 1)
    (hsym : pairedKernel J I W (pairScale I J) = pairedKernel I J W (pairScale I J)) :
    pairedKernel I J W (pairScale I J) = 0 := by
  let phi : Complex := star (gaussTwo I hI.2) * gaussTwo J hJ.2
  have hphi : phi ^ 3 = 1 := by
    change ((starRingEnd Complex) (gaussTwo I hI.2) * gaussTwo J hJ.2) ^ 3 = 1
    rw [mul_pow, <- map_pow, hgI, map_one, hgJ, one_mul]
  have hnon : Not (1 + phi = 0) := by
    intro h
    have he : phi = -1 := by linear_combination h
    rw [he] at hphi
    norm_num at hphi
  have hC := pairScale_pos I J hI hJ
  have h := anti_reflection_with_phase I J hI hJ hcop W hanti (pairScale I J) hC
  have he : (pairScale I J) ^ 2 / pairScale I J = pairScale I J := by
    field_simp [ne_of_gt hC]
  have hCZ : Not ((pairScale I J : Complex) = 0) := by exact_mod_cast ne_of_gt hC
  change pairedKernel I J W (pairScale I J) =
    -((pairScale I J : Complex) / (pairScale I J : Complex)) * phi *
      pairedKernel J I W ((pairScale I J) ^ 2 / pairScale I J) at h
  rw [he, div_self hCZ, neg_one_mul, hsym] at h
  have hz : (1 + phi) * pairedKernel I J W (pairScale I J) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left hnon

theorem near_selfdual_uniform_of_phase_cube (I J : Ideal Eis)
    (hI : Admissible I) (hJ : Admissible J) (hcop : IsCoprime I J)
    (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (hgI : gaussTwo I hI.2 ^ 3 = 1) (hgJ : gaussTwo J hJ.2 ^ 3 = 1)
    (hsym : pairedKernel J I W (pairScale I J) = pairedKernel I J W (pairScale I J))
    (X H : Real) (hX : 1 <= X) (hH : 0 <= H) (hHX : H <= X)
    (hBand : X ^ 2 <= pairScale I J /\ pairScale I J <= (X + H) ^ 2) :
    norm (pairedKernel I J W (X ^ 2)) <=
      (4 * CubicPairRadius.windowSize1 W *
        (1 + nonzeroLatticeEnvelopeConstant)) * X * H := by
  let R : Real := Real.sqrt (pairScale I J)
  have hC := pairScale_pos I J hI hJ
  have hR : 0 <= R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = pairScale I J := Real.sq_sqrt hC.le
  have hRL : X <= R := by nlinarith [hBand.1]
  have hRU : R <= X + H := by nlinarith [hBand.2]
  have hzero := selfdual_zero_of_phase_cube I J hI hJ hcop W hanti hgI hgJ hsym
  have hb := CubicPairRadius.radiusKernel_difference_bound
    (fun z : Eis => star (CubicSieve.cubicRow I z) * CubicSieve.cubicRow J z)
    (pairedCoefficient_norm_le_one I J) W X X R hX le_rfl (by linarith) hRL (by linarith)
  rw [<- pairedKernel_div_radius, <- pairedKernel_div_radius, hRsq, hzero,
    zero_div, sub_zero] at hb
  have hAbs : abs (X - R) <= H := by
    apply abs_le.mpr
    constructor <;> linarith
  have hL : 0 <= 4 * CubicPairRadius.windowSize1 W *
      (1 + nonzeroLatticeEnvelopeConstant) := by
    have hw := CubicPairRadius.windowSize1_nonneg W
    have hl := nonzeroLatticeEnvelopeConstant_nonneg
    positivity
  have hXpos : 0 < X := by linarith
  have hBound : norm (pairedKernel I J W (X ^ 2)) / X <=
      (4 * CubicPairRadius.windowSize1 W *
        (1 + nonzeroLatticeEnvelopeConstant)) * H := by
    have ht := hb.trans (mul_le_mul_of_nonneg_left hAbs hL)
    simpa only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hXpos] using ht
  calc
    _ = (norm (pairedKernel I J W (X ^ 2)) / X) * X := by field_simp [hXpos.ne']
    _ <= ((4 * CubicPairRadius.windowSize1 W *
        (1 + nonzeroLatticeEnvelopeConstant)) * H) * X :=
      mul_le_mul_of_nonneg_right hBound hXpos.le
    _ = _ := by ring

theorem primary_prime_gaussTwo_cube (a : Eis) (ha : Not (a = 0))
    (hprimary : Dvd.dvd (lambda ^ 2) (a - 1))
    [(Ideal.span {a}).IsMaximal] (hgood : Not (Membership.mem (Ideal.span {a}) lambda))
    (hI : Not (primaryGenerator (Ideal.span {a}) = 0)) :
    gaussTwo (Ideal.span {a}) hI ^ 3 = -eisEmbedding a / (norm (eisEmbedding a) : Complex) := by
  let I : Ideal Eis := Ideal.span {a}
  let g : Eis := primaryGenerator I
  have hspec := primaryGenerator_spec I hI
  have hspan : Ideal.span {g} = I := hspec.1
  letI : (Ideal.span {g}).IsMaximal := by rw [hspan]; infer_instance
  have hgoodg : Not (Membership.mem (Ideal.span {g}) lambda) := by
    simpa only [hspan] using hgood
  have hP0 : Not (I = 0) := NeZero.ne _
  have hprime : Prime I := Ideal.prime_of_isPrime hP0
    (inferInstance : I.IsPrime)
  have hAd : Admissible I := And.intro hprime.squarefree hI
  letI : Finite (HasQuotient.Quotient Eis (Ideal.span {g})) :=
    finite_quotient_span hI
  letI : Fintype (HasQuotient.Quotient Eis (Ideal.span {g})) := Fintype.ofFinite _
  let psi := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates g hI
  have hchi : principalCubicCharacter I hAd =
      (cubicChar (Ideal.span {g}) hgoodg).ringHomComp eisEmbedding := by
    apply DFunLike.ext
    intro x
    have hs := Ideal.Quotient.mk_surjective x
    let z : Eis := Classical.choose hs
    have hz : Ideal.Quotient.mk (Ideal.span {g}) z = x := Classical.choose_spec hs
    rw [<- hz, principalCubicCharacter_mk]
    change eisEmbedding (CubicJacobiGlobal.idealSymbol I z) = _
    have hsval : CubicJacobiGlobal.idealSymbol I z =
        CubicJacobiGlobal.idealSymbol (Ideal.span {g}) z :=
      congrArg (fun K : Ideal Eis => CubicJacobiGlobal.idealSymbol K z) hspan.symm
    rw [hsval, CubicJacobiGlobal.idealSymbol_prime _ hgoodg]
    rfl
  have hg := gaussTwo_eq_gaussSum I hAd
  change gaussTwo I hI =
    gaussSum (principalCubicCharacter I hAd) psi /
      (norm (eisEmbedding g) : Complex) at hg
  rw [hchi] at hg
  rw [hg]
  have hc := cubicGauss_normalized_cube_eis (Ideal.span {g}) hgoodg g rfl
    hspec.2 psi (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive g hI)
  have hgen : g = a := primaryGenerator_span a ha hprimary
  simpa only [hgen] using hc

theorem inert_gaussTwo_cube (p : Nat) (hp : Nat.Prime p) (hmod : p % 3 = 2)
    (hI : Not (primaryGenerator (Ideal.span {(p : Eis)}) = 0)) :
    gaussTwo (Ideal.span {(p : Eis)}) hI ^ 3 = 1 := by
  let a : Eis := -(p : Eis)
  have ha : Not (a = 0) := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  letI : (Ideal.span {a}).IsMaximal := by
    simpa only [a, Ideal.span_singleton_neg] using
      CubicInertArithmetic.rational_prime_isMaximal p hp hmod
  have hgood : Not (Membership.mem (Ideal.span {a}) lambda) := by
    simpa only [a, Ideal.span_singleton_neg] using
      CubicInertArithmetic.rational_prime_avoids_lambda p hp
  have hIa : Not (primaryGenerator (Ideal.span {a}) = 0) := by
    simpa only [a, Ideal.span_singleton_neg] using hI
  have hc := primary_prime_gaussTwo_cube a ha (negative_prime_primary p hmod) hgood hIa
  have hpC : Not ((p : Complex) = 0) := Nat.cast_ne_zero.mpr hp.ne_zero
  have he : -eisEmbedding a / (norm (eisEmbedding a) : Complex) = 1 := by
    dsimp [a]
    simp only [map_neg, map_natCast, norm_neg, Complex.norm_natCast, neg_neg]
    exact div_self hpC
  rw [he] at hc
  simpa only [a, Ideal.span_singleton_neg] using hc

theorem inert_admissible (p : Nat) (hp : Nat.Prime p) (hmod : p % 3 = 2) :
    Admissible (Ideal.span {(p : Eis)}) := by
  let I : Ideal Eis := Ideal.span {(p : Eis)}
  letI : I.IsMaximal := CubicInertArithmetic.rational_prime_isMaximal p hp hmod
  have hprime : Prime I :=
    Ideal.prime_of_isPrime (NeZero.ne _) (inferInstance : I.IsPrime)
  refine And.intro hprime.squarefree ?_
  rw [rational_primaryGenerator p hp hmod]
  exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)

theorem inert_pairScale (p q : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpmod : p % 3 = 2) (hqmod : q % 3 = 2) :
    pairScale (Ideal.span {(p : Eis)}) (Ideal.span {(q : Eis)}) =
      (p : Real) * (q : Real) := by
  unfold pairScale
  rw [rational_primaryGenerator p hp hpmod, rational_primaryGenerator q hq hqmod]
  simp only [map_mul, map_neg, map_natCast, norm_mul, norm_neg, Complex.norm_natCast]

theorem inert_coprime (p q : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpmod : p % 3 = 2) (hqmod : q % 3 = 2) (hpq : Not (p = q)) :
    IsCoprime (Ideal.span {(p : Eis)}) (Ideal.span {(q : Eis)}) := by
  letI := CubicInertArithmetic.rational_prime_isMaximal p hp hpmod
  letI := CubicInertArithmetic.rational_prime_isMaximal q hq hqmod
  apply Ideal.isCoprime_of_isMaximal
  intro he
  have hn := congrArg (fun I : Ideal Eis => Ideal.absNorm I) he
  rw [<- qNat_eq_absNorm_span, <- qNat_eq_absNorm_span,
    rational_qNat p hp.ne_zero,
    rational_qNat q hq.ne_zero] at hn
  apply hpq
  nlinarith

theorem inert_selfdual_zero (p q : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpmod : p % 3 = 2) (hqmod : q % 3 = 2) (hpq : Not (p = q))
    (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t) :
    pairedKernel (Ideal.span {(p : Eis)}) (Ideal.span {(q : Eis)}) W
      ((p : Real) * (q : Real)) = 0 := by
  have hI := inert_admissible p hp hpmod
  have hJ := inert_admissible q hq hqmod
  have hz := selfdual_zero_of_phase_cube _ _ hI hJ
    (inert_coprime p q hp hq hpmod hqmod hpq) W hanti
    (inert_gaussTwo_cube p hp hpmod hI.2)
    (inert_gaussTwo_cube q hq hqmod hJ.2)
    (CubicInertArithmetic.rational_kernel_symmetric p q hp hq hpmod hqmod W _)
  rwa [inert_pairScale p q hp hq hpmod hqmod] at hz

theorem inert_near_selfdual_uniform (p q : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpmod : p % 3 = 2) (hqmod : q % 3 = 2) (hpq : Not (p = q))
    (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (X H : Real) (hX : 1 <= X) (hH : 0 <= H) (hHX : H <= X)
    (hpX : X <= (p : Real)) (hpH : (p : Real) <= X + H)
    (hqX : X <= (q : Real)) (hqH : (q : Real) <= X + H) :
    norm (pairedKernel (Ideal.span {(p : Eis)}) (Ideal.span {(q : Eis)}) W (X ^ 2)) <=
      (4 * CubicPairRadius.windowSize1 W *
        (1 + nonzeroLatticeEnvelopeConstant)) * X * H := by
  have hI := inert_admissible p hp hpmod
  have hJ := inert_admissible q hq hqmod
  apply near_selfdual_uniform_of_phase_cube _ _ hI hJ
    (inert_coprime p q hp hq hpmod hqmod hpq) W hanti
    (inert_gaussTwo_cube p hp hpmod hI.2)
    (inert_gaussTwo_cube q hq hqmod hJ.2)
    (CubicInertArithmetic.rational_kernel_symmetric p q hp hq hpmod hqmod W _)
    X H hX hH hHX
  rw [inert_pairScale p q hp hq hpmod hqmod]
  have hp0 : 0 <= (p : Real) := Nat.cast_nonneg _
  have hq0 : 0 <= (q : Real) := Nat.cast_nonneg _
  constructor
  . nlinarith [mul_nonneg (sub_nonneg.mpr hpX) (sub_nonneg.mpr hqX)]
  . nlinarith [mul_nonneg (sub_nonneg.mpr hpH) (sub_nonneg.mpr hqH)]

theorem twin_near_selfdual_uniform (p q : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpnext : Nat.Prime (p + 2)) (hqnext : Nat.Prime (q + 2))
    (hp3 : Not (p = 3)) (hq3 : Not (q = 3)) (hpq : Not (p = q))
    (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (X H : Real) (hX : 1 <= X) (hH : 0 <= H) (hHX : H <= X)
    (hpX : X <= (p : Real)) (hpH : (p : Real) <= X + H)
    (hqX : X <= (q : Real)) (hqH : (q : Real) <= X + H) :
    norm (pairedKernel (Ideal.span {(p : Eis)}) (Ideal.span {(q : Eis)}) W (X ^ 2)) <=
      (4 * CubicPairRadius.windowSize1 W *
        (1 + nonzeroLatticeEnvelopeConstant)) * X * H :=
  inert_near_selfdual_uniform p q hp hq
    (CubicInertArithmetic.twin_start_mod_three p hp hpnext hp3)
    (CubicInertArithmetic.twin_start_mod_three q hq hqnext hq3)
    hpq W hanti X H hX hH hHX hpX hpH hqX hqH

end PrimeFactorOscillations.CubicInertPhase
