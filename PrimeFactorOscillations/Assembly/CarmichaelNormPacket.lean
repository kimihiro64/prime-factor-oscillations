/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPhaseKernel
import PrimeFactorOscillations.Assembly.CarmichaelWeightedSignal
import PrimeFactorOscillations.Helpers.CubicNormFourier

/-!
# Actual norm Gauss phases in the Carmichael packet

The physical norm transform contributes G=chi(3)*tau^2/q on cubic
characters. Its probability filter uses star(G), with every character and
the principal coefficient retained. No signed arithmetic estimate is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CarmichaelNormPacket
open CarmichaelCorrelation CarmichaelCorrelationSpectrum CarmichaelPhaseKernel

def normPhase (q : Nat) [NeZero q] (psi : AddChar (ZMod q) Complex)
    (chi : DirichletCharacter Complex q) : Complex :=
  chi 3 * DirichletEvenGaussPhase.phase q psi chi ^ 2

def filterPhase (q : Nat) [NeZero q] (psi : AddChar (ZMod q) Complex)
    (chi : DirichletCharacter Complex q) : Complex :=
  star (normPhase q psi chi)

theorem normPhase_principal (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (psi : AddChar (ZMod q) Complex) (h3 : Not ((3 : ZMod q) = 0)) :
    normPhase q psi 1 = 1 := by
  unfold normPhase
  rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr h3),
    DirichletEvenGaussPhase.phase_principal]
  norm_num

theorem normPhase_norm (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (psi : AddChar (ZMod q) Complex) (hpsi : psi.IsPrimitive)
    (h3 : Not ((3 : ZMod q) = 0)) (chi : DirichletCharacter Complex q) :
    norm (normPhase q psi chi) = 1 := by
  have hVal : norm (chi 3) = 1 := by
    change norm (unitCharacter chi (Units.mk0 (3 : ZMod q) h3)) = 1
    exact character_norm_one _ _
  unfold normPhase
  rw [norm_mul, norm_pow, hVal, DirichletEvenGaussPhase.phase_norm q psi hpsi]
  norm_num

theorem normPhase_inverse (q : Nat) [NeZero q]
    (psi : AddChar (ZMod q) Complex) (chi : DirichletCharacter Complex q) :
    normPhase q psi (Inv.inv chi) = star (normPhase q psi chi) := by
  unfold normPhase
  rw [<- MulChar.star_apply', DirichletEvenGaussPhase.phase_inverse]
  change (starRingEnd Complex) (chi 3) *
    (starRingEnd Complex) (DirichletEvenGaussPhase.phase q psi chi) ^ 2 =
      (starRingEnd Complex) (chi 3 * DirichletEvenGaussPhase.phase q psi chi ^ 2)
  rw [map_mul, map_pow]

theorem normPhase_cubic (q : Nat) [NeZero q]
    (psi : AddChar (ZMod q) Complex) (chi : DirichletCharacter Complex q)
    (hChi : Not (chi = 1)) (hCube : chi ^ 3 = 1) :
    normPhase q psi chi =
      chi 3 * gaussSum chi psi ^ 2 / (Fintype.card (ZMod q) : Complex) := by
  have hCard : 0 < (Fintype.card (ZMod q) : Real) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ZMod q))
  have hSquare :
      ((Real.sqrt (Fintype.card (ZMod q)) : Real) : Complex) ^ 2 =
        (Fintype.card (ZMod q) : Complex) := by
    exact_mod_cast (Real.sq_sqrt hCard.le)
  unfold normPhase
  rw [DirichletEvenGaussPhase.phase_cubic q psi chi hChi hCube,
    Complex.ofReal_inv, mul_pow, inv_pow, hSquare]
  ring

theorem cubic_norm_fourier (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (r s : ZMod q) (hrs : Not (r = s)) (hSum : r + s = -1) (hProd : r * s = 1)
    (psi : AddChar (ZMod q) Complex) (chi : DirichletCharacter Complex q)
    (hChi : Not (chi = 1)) (hCube : chi ^ 3 = 1) (c d : ZMod q) :
    CubicNormFourier.normTransform chi psi c d =
      (Fintype.card (ZMod q) : Complex) * normPhase q psi chi *
        (Inv.inv chi) (CubicNormFourier.normForm c d) := by
  have hCard : Not ((Fintype.card (ZMod q) : Complex) = 0) :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [CubicNormFourier.norm_nonprincipal r s hrs hSum hProd chi psi hChi,
    normPhase_cubic q psi chi hChi hCube]
  field_simp [hCard]

theorem filterPhase_principal (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (psi : AddChar (ZMod q) Complex) (h3 : Not ((3 : ZMod q) = 0)) :
    filterPhase q psi 1 = 1 := by
  rw [filterPhase, normPhase_principal q psi h3, star_one]

theorem filterPhase_norm (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (psi : AddChar (ZMod q) Complex) (hpsi : psi.IsPrimitive)
    (h3 : Not ((3 : ZMod q) = 0)) (chi : DirichletCharacter Complex q) :
    norm (filterPhase q psi chi) = 1 := by
  rw [filterPhase, norm_star, normPhase_norm q psi hpsi h3]

theorem filterPhase_inverse (q : Nat) [NeZero q]
    (psi : AddChar (ZMod q) Complex) (chi : DirichletCharacter Complex q) :
    filterPhase q psi (Inv.inv chi) = star (filterPhase q psi chi) := by
  simp only [filterPhase, normPhase_inverse, star_star]

theorem native_coefficient_balance (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (psi : AddChar (ZMod q) Complex) (hpsi : psi.IsPrimitive)
    (h3 : Not ((3 : ZMod q) = 0)) (chi : DirichletCharacter Complex q) :
    phaseCoefficient q l (filterPhase q psi) chi * normPhase q psi chi =
      star (phaseCoefficient q l (filterPhase q psi) chi) := by
  have h := coefficient_phase_balance q l (filterPhase q psi)
    (filterPhase_inverse q psi) (filterPhase_principal q psi h3) chi
    (filterPhase_norm q psi hpsi h3 chi)
  simpa only [filterPhase, star_star] using h

theorem native_coefficient_re_nonneg (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (psi : AddChar (ZMod q) Complex) (hpsi : psi.IsPrimitive)
    (h3 : Not ((3 : ZMod q) = 0)) (chi : DirichletCharacter Complex q) :
    0 <= (phaseCoefficient q l (filterPhase q psi) chi).re :=
  coefficient_re_nonneg q l hDiv (filterPhase q psi)
    (filterPhase_inverse q psi) (filterPhase_principal q psi h3) chi
    (filterPhase_norm q psi hpsi h3 chi).le

theorem native_kernel_ge_half (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hThree : 3 <= CarmichaelPrimePacket.index q l)
    (psi : AddChar (ZMod q) Complex) (hpsi : psi.IsPrimitive)
    (h3 : Not ((3 : ZMod q) = 0)) (u : Units (ZMod q)) :
    (1 / 2 : Real) <= phaseKernel q l (filterPhase q psi) u :=
  kernel_ge_half q l hDiv hThree (filterPhase q psi)
    (filterPhase_inverse q psi) (filterPhase_principal q psi h3)
    (fun chi => (filterPhase_norm q psi hpsi h3 chi).le) u

theorem coefficient_cubic_support (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (chi : DirichletCharacter Complex q)
    (hNonzero : Not (coefficient (CarmichaelPrimePacket.weight q l) chi = 0)) :
    chi ^ 3 = 1 := by
  apply DFunLike.ext
  intro x
  by_cases hx : x = 0
  . subst x
    simp only [MulChar.map_zero]
  . let u : Units (ZMod q) := Units.mk0 x hx
    have h := CarmichaelPrimePacketSpectrum.nonzero_coefficient_prime_power
      q l hDiv chi hNonzero u
    rw [hLabel] at h
    rw [MulChar.pow_apply' _ (by decide : Not ((3 : Nat) = 0)),
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
    exact h

theorem native_coefficient_inverse (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (psi : AddChar (ZMod q) Complex)
    (h3 : Not ((3 : ZMod q) = 0)) (chi : DirichletCharacter Complex q) :
    phaseCoefficient q l (filterPhase q psi) (Inv.inv chi) =
      star (phaseCoefficient q l (filterPhase q psi) chi) := by
  rw [coefficient_amplitude q l (filterPhase q psi)
      (filterPhase_inverse q psi) (filterPhase_principal q psi h3) (Inv.inv chi),
    coefficient_amplitude q l (filterPhase q psi)
      (filterPhase_inverse q psi) (filterPhase_principal q psi h3) chi,
    CarmichaelFilteredSpectrum.amplitude_inverse,
    CarmichaelFilteredSpectrum.filteredAmplitude_inverse q l (filterPhase q psi)
      (filterPhase_inverse q psi)]
  change _ = (starRingEnd Complex) _
  rw [map_mul, Complex.conj_ofReal]
  rfl

def nativeProfile (q : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (psi : AddChar (ZMod q) Complex) (c d : ZMod q) : Complex :=
  Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
    phaseCoefficient q l (filterPhase q psi) chi * chi (CubicNormFourier.normForm c d))

theorem native_profile_real (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (psi : AddChar (ZMod q) Complex)
    (h3 : Not ((3 : ZMod q) = 0)) (c d : ZMod q) :
    star (nativeProfile q l psi c d) = nativeProfile q l psi c d := by
  by_cases hN : CubicNormFourier.normForm c d = 0
  . simp [nativeProfile, hN, MulChar.map_zero]
  . let u : Units (ZMod q) := Units.mk0 (CubicNormFourier.normForm c d) hN
    change star (Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        phaseCoefficient q l (filterPhase q psi) chi * unitCharacter chi u)) =
      Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        phaseCoefficient q l (filterPhase q psi) chi * unitCharacter chi u)
    simpa only [inv_inv] using CarmichaelFilteredSpectrum.hermitian_series q
      (phaseCoefficient q l (filterPhase q psi))
      (native_coefficient_inverse q l psi h3) (Inv.inv u)

def nativeProfileTransform (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (psi : AddChar (ZMod q) Complex) (c d : ZMod q) : Complex :=
  Finset.univ.sum (fun z : Prod (ZMod q) (ZMod q) =>
    nativeProfile q l psi z.1 z.2 * psi (CubicNormFourier.traceForm z.1 z.2 c d))

theorem native_profile_transform_sum (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (psi : AddChar (ZMod q) Complex) (c d : ZMod q) :
    nativeProfileTransform q l psi c d =
      Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        phaseCoefficient q l (filterPhase q psi) chi *
          CubicNormFourier.normTransform chi psi c d) := by
  unfold nativeProfileTransform nativeProfile CubicNormFourier.normTransform
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem native_nonprincipal_transform (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (r s : ZMod q) (hrs : Not (r = s)) (hSum : r + s = -1) (hProd : r * s = 1)
    (psi : AddChar (ZMod q) Complex) (hpsi : psi.IsPrimitive)
    (chi : DirichletCharacter Complex q) (hChi : Not (chi = 1)) (c d : ZMod q) :
    phaseCoefficient q l (filterPhase q psi) chi *
        CubicNormFourier.normTransform chi psi c d =
      (Fintype.card (ZMod q) : Complex) *
        star (phaseCoefficient q l (filterPhase q psi) chi) *
          (Inv.inv chi) (CubicNormFourier.normForm c d) := by
  have h3 := CubicNormFourier.three_ne_zero r s hrs hSum hProd
  by_cases hc : coefficient (CarmichaelPrimePacket.weight q l) chi = 0
  . have hk : phaseCoefficient q l (filterPhase q psi) chi = 0 := by
      rw [coefficient_formula q l hDiv (filterPhase q psi)
        (filterPhase_inverse q psi) (filterPhase_principal q psi h3) chi, hc]
      norm_num
    rw [hk, star_zero]
    ring
  . have hCube := coefficient_cubic_support q l hLabel hDiv chi hc
    rw [cubic_norm_fourier q r s hrs hSum hProd psi chi hChi hCube]
    calc
      _ = (Fintype.card (ZMod q) : Complex) *
          (phaseCoefficient q l (filterPhase q psi) chi * normPhase q psi chi) *
            (Inv.inv chi) (CubicNormFourier.normForm c d) := by ring
      _ = _ := by rw [native_coefficient_balance q l psi hpsi h3 chi]

theorem native_profile_transform (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (r s : ZMod q) (hrs : Not (r = s)) (hSum : r + s = -1) (hProd : r * s = 1)
    (psi : AddChar (ZMod q) Complex) (hpsi : psi.IsPrimitive) (c d : ZMod q) :
    nativeProfileTransform q l psi c d =
      (Fintype.card (ZMod q) : Complex) * nativeProfile q l psi c d +
        ((Fintype.card (ZMod q) : Complex) - 1) *
          ((Fintype.card (ZMod q) : Complex) *
            (if And (c = 0) (d = 0) then 1 else 0) - 1) := by
  classical
  let Q : Complex := (Fintype.card (ZMod q) : Complex)
  let N := CubicNormFourier.normForm c d
  let k := phaseCoefficient q l (filterPhase q psi)
  let f : DirichletCharacter Complex q -> Complex :=
    fun chi => k chi * CubicNormFourier.normTransform chi psi c d
  let a : DirichletCharacter Complex q -> Complex :=
    fun chi => star (k chi) * (Inv.inv chi) N
  have h3 := CubicNormFourier.three_ne_zero r s hrs hSum hProd
  have hK1 : k 1 = 1 := principal q l (filterPhase q psi)
  have hSplit (b : DirichletCharacter Complex q -> Complex) :
      Finset.univ.sum b = b 1 +
        (Finset.univ.erase (1 : DirichletCharacter Complex q)).sum b := by
    exact (Finset.sum_erase_add Finset.univ b (Finset.mem_univ _)).symm.trans (add_comm _ _)
  have hPrincipal : f 1 =
      1 - Q * (if N = 0 then 1 else 0) +
        Q * (Q - 1) * (if And (c = 0) (d = 0) then 1 else 0) := by
    change k 1 * CubicNormFourier.normTransform (1 : DirichletCharacter Complex q) psi c d = _
    rw [hK1, one_mul]
    exact CubicNormFourier.norm_principal r s hrs hSum hProd psi hpsi c d
  have hLow :
      (Finset.univ.erase (1 : DirichletCharacter Complex q)).sum f =
        Q * (Finset.univ.erase (1 : DirichletCharacter Complex q)).sum a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hchi
    have h := native_nonprincipal_transform q l hLabel hDiv r s hrs hSum hProd
      psi hpsi chi (Finset.mem_erase.mp hchi).1 c d
    simpa only [mul_assoc] using h
  have hAll : Finset.univ.sum a = star (nativeProfile q l psi c d) := by
    change Finset.univ.sum a =
      (starRingEnd Complex) (Finset.univ.sum
        (fun chi : DirichletCharacter Complex q => k chi * chi N))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro chi _
    change star (k chi) * (Inv.inv chi) N =
      (starRingEnd Complex) (k chi * chi N)
    rw [map_mul, <- MulChar.star_apply']
    all_goals rfl
  have hUnit : a 1 = (1 : DirichletCharacter Complex q) N := by
    change star (k 1) * (Inv.inv (1 : DirichletCharacter Complex q)) N = _
    rw [hK1, star_one, inv_one, one_mul]
  have hRest :
      (Finset.univ.erase (1 : DirichletCharacter Complex q)).sum a =
        nativeProfile q l psi c d - (1 : DirichletCharacter Complex q) N := by
    have h := hSplit a
    rw [hAll, hUnit, native_profile_real q l psi h3 c d] at h
    linear_combination -h
  rw [native_profile_transform_sum]
  change Finset.univ.sum f = Q * nativeProfile q l psi c d +
    (Q - 1) * (Q * (if And (c = 0) (d = 0) then 1 else 0) - 1)
  rw [hSplit f, hPrincipal, hLow, hRest]
  by_cases hN : N = 0
  . simp only [hN, ite_true, MulChar.map_zero]
    all_goals ring
  . rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hN)]
    simp only [ite_eq_right hN]
    all_goals ring

theorem constant_trace_transform (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (psi : AddChar (ZMod q) Complex) (hpsi : psi.IsPrimitive) (c d : ZMod q) :
    Finset.univ.sum (fun z : Prod (ZMod q) (ZMod q) =>
      psi (CubicNormFourier.traceForm z.1 z.2 c d)) =
      (Fintype.card (ZMod q) : Complex) ^ 2 *
        (if And (c = 0) (d = 0) then 1 else 0) := by
  have he (a b : ZMod q) :
      psi (CubicNormFourier.traceForm a b c d) = psi (a * d) * psi (b * (c - d)) := by
    have ht : CubicNormFourier.traceForm a b c d = a * d + b * (c - d) := by
      dsimp [CubicNormFourier.traceForm]
      ring
    rw [ht, AddChar.map_add_eq_mul]
  rw [Fintype.sum_prod_type]
  simp_rw [he]
  rw [<- Finset.sum_mul_sum, AddChar.sum_mulShift d hpsi,
    AddChar.sum_mulShift (c - d) hpsi]
  by_cases hc : c = 0 <;> by_cases hd : d = 0 <;> simp [hc, hd, pow_two]

def centeredProfile (q : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (psi : AddChar (ZMod q) Complex) (c d : ZMod q) : Complex :=
  nativeProfile q l psi c d -
    ((Fintype.card (ZMod q) : Complex) - 1) / (Fintype.card (ZMod q) : Complex)

def centeredProfileTransform (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (psi : AddChar (ZMod q) Complex) (c d : ZMod q) : Complex :=
  Finset.univ.sum (fun z : Prod (ZMod q) (ZMod q) =>
    centeredProfile q l psi z.1 z.2 * psi (CubicNormFourier.traceForm z.1 z.2 c d))

theorem centered_profile_transform_split (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (psi : AddChar (ZMod q) Complex) (c d : ZMod q) :
    centeredProfileTransform q l psi c d =
      nativeProfileTransform q l psi c d -
        (((Fintype.card (ZMod q) : Complex) - 1) / (Fintype.card (ZMod q) : Complex)) *
          Finset.univ.sum (fun z : Prod (ZMod q) (ZMod q) =>
            psi (CubicNormFourier.traceForm z.1 z.2 c d)) := by
  unfold centeredProfileTransform centeredProfile nativeProfileTransform
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, <- Finset.mul_sum]

theorem centered_profile_transform (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (hLabel : (l : Nat) = 3)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (r s : ZMod q) (hrs : Not (r = s)) (hSum : r + s = -1) (hProd : r * s = 1)
    (psi : AddChar (ZMod q) Complex) (hpsi : psi.IsPrimitive) (c d : ZMod q) :
    centeredProfileTransform q l psi c d =
      (Fintype.card (ZMod q) : Complex) * centeredProfile q l psi c d := by
  rw [centered_profile_transform_split,
    native_profile_transform q l hLabel hDiv r s hrs hSum hProd psi hpsi,
    constant_trace_transform q psi hpsi]
  unfold centeredProfile
  have hCard : Not ((Fintype.card (ZMod q) : Complex) = 0) :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hCard]
  all_goals ring


def centeredCoefficient (q : Nat) [NeZero q] (l : Nat.Primes)
    (psi : AddChar (ZMod q) Complex) (chi : DirichletCharacter Complex q) : Complex := by
  classical
  exact if chi = 1 then 1 else
    (Fintype.card (ZMod q) : Complex) * phaseCoefficient q l (filterPhase q psi) chi

theorem centered_coefficient_principal (q : Nat) [NeZero q] (l : Nat.Primes)
    (psi : AddChar (ZMod q) Complex) :
    centeredCoefficient q l psi 1 = 1 := by
  classical
  simp only [centeredCoefficient, ite_true]

theorem centered_coefficient_re_nonneg (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (psi : AddChar (ZMod q) Complex) (hpsi : psi.IsPrimitive)
    (h3 : Not ((3 : ZMod q) = 0)) (chi : DirichletCharacter Complex q) :
    0 <= (centeredCoefficient q l psi chi).re := by
  classical
  unfold centeredCoefficient
  split_ifs
  . norm_num
  . have h := native_coefficient_re_nonneg q l hDiv psi hpsi h3 chi
    have hCard : (Fintype.card (ZMod q) : Complex) =
        ((Fintype.card (ZMod q) : Real) : Complex) := by simp
    rw [hCard, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_nonneg (Nat.cast_nonneg _) h

theorem centered_coefficient_formula (q : Nat) [NeZero q] (l : Nat.Primes)
    (psi : AddChar (ZMod q) Complex) (chi : DirichletCharacter Complex q) :
    centeredCoefficient q l psi chi =
      (Fintype.card (ZMod q) : Complex) * phaseCoefficient q l (filterPhase q psi) chi -
        ((Fintype.card (ZMod q) : Complex) - 1) *
          (@ite Complex (chi = 1) (Classical.propDecidable _) 1 0) := by
  classical
  by_cases h : chi = 1
  . subst chi
    rw [centered_coefficient_principal, principal]
    simp only [ite_true]
    ring
  . simp only [centeredCoefficient, h, ite_false, mul_zero, sub_zero]

def normalizedProfile (q : Nat) [NeZero q] (l : Nat.Primes)
    (psi : AddChar (ZMod q) Complex) (n : ZMod q) : Complex :=
  Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
    centeredCoefficient q l psi chi * chi n)

theorem normalized_profile_split (q : Nat) [NeZero q] (l : Nat.Primes)
    (psi : AddChar (ZMod q) Complex) (n : ZMod q) :
    normalizedProfile q l psi n =
      (Fintype.card (ZMod q) : Complex) *
        Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
          phaseCoefficient q l (filterPhase q psi) chi * chi n) -
      ((Fintype.card (ZMod q) : Complex) - 1) *
        (1 : DirichletCharacter Complex q) n := by
  classical
  unfold normalizedProfile
  have hTerm (chi : DirichletCharacter Complex q) :
      centeredCoefficient q l psi chi * chi n =
        (Fintype.card (ZMod q) : Complex) *
          (phaseCoefficient q l (filterPhase q psi) chi * chi n) -
        ((Fintype.card (ZMod q) : Complex) - 1) *
          (if chi = 1 then chi n else 0) := by
    rw [centered_coefficient_formula]
    by_cases h : chi = 1
    . simp only [h, ite_true]
      ring
    . simp only [h, ite_false, mul_zero, sub_zero]
      ring
  simp_rw [hTerm]
  rw [Finset.sum_sub_distrib, <- Finset.mul_sum, <- Finset.mul_sum]
  simp

theorem centered_profile_normalization (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (l : Nat.Primes) (psi : AddChar (ZMod q) Complex) (c d : ZMod q) :
    (Fintype.card (ZMod q) : Complex) * centeredProfile q l psi c d =
      normalizedProfile q l psi (CubicNormFourier.normForm c d) -
        ((Fintype.card (ZMod q) : Complex) - 1) *
          (if CubicNormFourier.normForm c d = 0 then 1 else 0) := by
  rw [normalized_profile_split]
  change (Fintype.card (ZMod q) : Complex) * centeredProfile q l psi c d =
    (Fintype.card (ZMod q) : Complex) * nativeProfile q l psi c d -
      ((Fintype.card (ZMod q) : Complex) - 1) *
        (1 : DirichletCharacter Complex q) (CubicNormFourier.normForm c d) -
      ((Fintype.card (ZMod q) : Complex) - 1) *
        (if CubicNormFourier.normForm c d = 0 then 1 else 0)
  unfold centeredProfile
  have hCard : Not ((Fintype.card (ZMod q) : Complex) = 0) :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases hN : CubicNormFourier.normForm c d = 0
  . simp only [hN, ite_true, MulChar.map_zero, mul_zero, sub_zero]
    field_simp [hCard]
  . rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hN)]
    simp only [ite_eq_right hN, mul_zero, sub_zero]
    field_simp [hCard]

theorem centered_principal_zero_not_analytic
    (q : Nat) [NeZero q] [Fact (Nat.Prime q)] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (psi : AddChar (ZMod q) Complex) (hpsi : psi.IsPrimitive)
    (h3 : Not ((3 : ZMod q) = 0)) (rho : Complex) (hOne : Not (rho = 1))
    (hZero : DirichletCharacter.LFunction (1 : DirichletCharacter Complex q) rho = 0)
    (E : Complex -> Complex) (hE : AnalyticAt Complex E rho) :
    Not (AnalyticAt Complex
      (CarmichaelWeightedSignal.readout (fun chi => DirichletCharacter.LFunction chi)
        (centeredCoefficient q l psi) E) rho) :=
  CarmichaelWeightedSignal.principal_zero_not_analytic (centeredCoefficient q l psi)
    (centered_coefficient_re_nonneg q l hDiv psi hpsi h3)
    (centered_coefficient_principal q l psi) rho hOne hZero E hE

end PrimeFactorOscillations.CarmichaelNormPacket
