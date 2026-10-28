/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelFilteredSpectrum
import PrimeFactorOscillations.Assembly.CarmichaelWeightedSignal
import PrimeFactorOscillations.Helpers.DirichletEvenGaussPhase

/-!
# Actual phase-balanced Carmichael cross kernels

The full finite Fourier coefficients are computed from the two actual
profiles. Their principal coefficient is one, their real parts are
nonnegative, and phase balance holds without deleting compensation terms.
The coefficient mass supplies a uniform positive kernel floor. No signed
prime-sampled exponent improvement is asserted by these finite identities.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelPhaseKernel
open CarmichaelCorrelation CarmichaelCorrelationSpectrum CarmichaelPhaseFilter
open CarmichaelFilteredSpectrum CarmichaelCrossCorrelation

def phaseKernel (q : Nat) [NeZero q] (l : Nat.Primes)
    (g : DirichletCharacter Complex q -> Complex) (u : Units (ZMod q)) : Real :=
  crossKernel (filteredProfile q l (fun _ => 1)) (filteredProfile q l g) u

def phaseCoefficient (q : Nat) [NeZero q] (l : Nat.Primes)
    (g : DirichletCharacter Complex q -> Complex)
    (chi : DirichletCharacter Complex q) : Complex :=
  crossCoefficient (filteredProfile q l (fun _ => 1)) (filteredProfile q l g)
    (unitCharacter chi)

theorem principal (q : Nat) [NeZero q] (l : Nat.Primes)
    (g : DirichletCharacter Complex q -> Complex) :
    phaseCoefficient q l g 1 = 1 := by
  have hPos (v : DirichletCharacter Complex q -> Complex) :
      0 < weightSum (filteredProfile q l v) := by
    rw [filteredProfile_weightSum]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Units (ZMod q)))
  unfold phaseCoefficient
  rw [unitCharacter_one]
  exact crossCoefficient_principal _ _ (hPos _) (hPos _)

theorem expansion (q : Nat) [NeZero q] (l : Nat.Primes)
    (g : DirichletCharacter Complex q -> Complex) (u : Units (ZMod q)) :
    (phaseKernel q l g u : Complex) =
      Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        phaseCoefficient q l g chi * unitCharacter chi (Inv.inv u)) :=
  crossKernel_expansion (filteredProfile q l (fun _ => 1)) (filteredProfile q l g) u

theorem coefficient_amplitude (q : Nat) [NeZero q] (l : Nat.Primes)
    (g : DirichletCharacter Complex q -> Complex)
    (hg : forall chi, g (Inv.inv chi) = star (g chi)) (hOne : g 1 = 1)
    (chi : DirichletCharacter Complex q) :
    phaseCoefficient q l g chi =
      (amplitude q l chi : Complex) * filteredAmplitude q l g chi := by
  have hOld := filteredProfile_characterSum q l (fun _ => (1 : Complex))
    (by intro psi; simp only [star_one]) rfl chi
  have hFlat : filteredAmplitude q l (fun _ => (1 : Complex)) chi =
      (amplitude q l chi : Complex) := by
    rw [filteredAmplitude_formula]
    push_cast
    ring
  have hNew := filteredProfile_characterSum q l g hg hOne chi
  have hn : Not ((Fintype.card (Units (ZMod q)) : Complex) = 0) := by
    exact_mod_cast Fintype.card_ne_zero
  unfold phaseCoefficient crossCoefficient
  rw [hOld, hFlat, hNew, filteredProfile_weightSum, filteredProfile_weightSum]
  simp only [Complex.ofReal_natCast, map_mul, map_natCast, Complex.conj_ofReal]
  field_simp [hn] <;> ring

theorem coefficient_formula (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (g : DirichletCharacter Complex q -> Complex)
    (hg : forall chi, g (Inv.inv chi) = star (g chi)) (hOne : g 1 = 1)
    (chi : DirichletCharacter Complex q) :
    phaseCoefficient q l g chi =
      ((coefficient (CarmichaelPrimePacket.weight q l) chi / 2 : Real) : Complex) *
        (1 + g chi) := by
  rw [coefficient_amplitude q l g hg hOne chi, filteredAmplitude_formula]
  calc
    _ = ((amplitude q l chi ^ 2 / 2 : Real) : Complex) * (1 + g chi) := by
      push_cast
      ring
    _ = _ := by rw [amplitude_sq_eq_coefficient q l hDiv chi]

theorem coefficient_re_nonneg (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (g : DirichletCharacter Complex q -> Complex)
    (hg : forall chi, g (Inv.inv chi) = star (g chi)) (hOne : g 1 = 1)
    (chi : DirichletCharacter Complex q) (hNorm : norm (g chi) <= 1) :
    0 <= (phaseCoefficient q l g chi).re := by
  rw [coefficient_formula q l hDiv g hg hOne chi]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_re, Complex.one_re]
  apply mul_nonneg
  . exact div_nonneg (coefficient_nonneg _ chi) (by norm_num)
  . have h := Complex.re_le_norm (-(g chi))
    rw [Complex.neg_re, norm_neg] at h
    linarith

theorem coefficient_phase_balance (q : Nat) [NeZero q] (l : Nat.Primes)
    (g : DirichletCharacter Complex q -> Complex)
    (hg : forall chi, g (Inv.inv chi) = star (g chi)) (hOne : g 1 = 1)
    (chi : DirichletCharacter Complex q) (hNorm : norm (g chi) = 1) :
    phaseCoefficient q l g chi * star (g chi) =
      star (phaseCoefficient q l g chi) := by
  rw [coefficient_amplitude q l g hg hOne chi, star_mul]
  have hr : star (amplitude q l chi : Complex) = (amplitude q l chi : Complex) := by
    change (starRingEnd Complex) (amplitude q l chi : Complex) = _
    exact Complex.conj_ofReal _
  rw [hr, mul_assoc, filtered_amplitude_balance q l g chi hNorm]
  ring

theorem coefficient_norm_le (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (g : DirichletCharacter Complex q -> Complex)
    (hg : forall chi, g (Inv.inv chi) = star (g chi)) (hOne : g 1 = 1)
    (chi : DirichletCharacter Complex q) (hNorm : norm (g chi) <= 1) :
    norm (phaseCoefficient q l g chi) <= coefficient (CarmichaelPrimePacket.weight q l) chi := by
  rw [coefficient_amplitude q l g hg hOne chi, norm_mul]
  have hB := filteredAmplitude_norm_le q l g chi hNorm
  calc
    _ <= norm (amplitude q l chi : Complex) * norm (amplitude q l chi : Complex) :=
      mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    _ = _ := by
      rw [<- pow_two, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        amplitude_sq_eq_coefficient q l hDiv chi]

theorem real_expansion (q : Nat) [NeZero q] (l : Nat.Primes)
    (g : DirichletCharacter Complex q -> Complex) (u : Units (ZMod q)) :
    phaseKernel q l g u = 1 + (nonprincipal q).sum (fun chi =>
      (phaseCoefficient q l g chi * unitCharacter chi (Inv.inv u)).re) := by
  classical
  let f (chi : DirichletCharacter Complex q) : Complex :=
    phaseCoefficient q l g chi * unitCharacter chi (Inv.inv u)
  have hf : f 1 = 1 := by
    dsimp [f]
    rw [principal, unitCharacter_one, MonoidHom.one_apply, mul_one]
  have hs : Finset.univ.sum f = (nonprincipal q).sum f + 1 := by
    calc
      _ = (Finset.univ.erase (1 : DirichletCharacter Complex q)).sum f + f 1 :=
        (Finset.sum_erase_add Finset.univ f (Finset.mem_univ 1)).symm
      _ = _ := by
        rw [hf]
        rfl
  have h := congrArg Complex.re (expansion q l g u)
  change phaseKernel q l g u = (Finset.univ.sum f).re at h
  rw [hs, Complex.add_re, Complex.one_re] at h
  have hRe : ((nonprincipal q).sum f).re =
      (nonprincipal q).sum (fun chi => (f chi).re) :=
    map_sum Complex.reCLM f (nonprincipal q)
  rw [hRe] at h
  change phaseKernel q l g u = 1 + (nonprincipal q).sum (fun chi => (f chi).re)
  linarith

theorem kernel_ge_mass (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (g : DirichletCharacter Complex q -> Complex)
    (hg : forall chi, g (Inv.inv chi) = star (g chi)) (hOne : g 1 = 1)
    (hNorm : forall chi, norm (g chi) <= 1) (u : Units (ZMod q)) :
    1 - 1 / ((CarmichaelPrimePacket.index q l : Real) - 1) <= phaseKernel q l g u := by
  have hTerm (chi : DirichletCharacter Complex q) :
      -(coefficient (CarmichaelPrimePacket.weight q l) chi) <=
        (phaseCoefficient q l g chi * unitCharacter chi (Inv.inv u)).re := by
    have h := Complex.re_le_norm
      (-(phaseCoefficient q l g chi * unitCharacter chi (Inv.inv u)))
    rw [Complex.neg_re, norm_neg, norm_mul, character_norm_one, mul_one] at h
    have hc := coefficient_norm_le q l hDiv g hg hOne chi (hNorm chi)
    linarith
  have hs := Finset.sum_le_sum (s := nonprincipal q) (fun chi _ => hTerm chi)
  rw [Finset.sum_neg_distrib] at hs
  have hm : (nonprincipal q).sum (coefficient (CarmichaelPrimePacket.weight q l)) =
      1 / ((CarmichaelPrimePacket.index q l : Real) - 1) :=
    CarmichaelPrimePacket.nonprincipal_coefficient_mass q l hDiv
  rw [hm] at hs
  rw [real_expansion]
  linarith

theorem kernel_ge_half (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hThree : 3 <= CarmichaelPrimePacket.index q l)
    (g : DirichletCharacter Complex q -> Complex)
    (hg : forall chi, g (Inv.inv chi) = star (g chi)) (hOne : g 1 = 1)
    (hNorm : forall chi, norm (g chi) <= 1) (u : Units (ZMod q)) :
    (1 / 2 : Real) <= phaseKernel q l g u := by
  have hd : (2 : Real) <= (CarmichaelPrimePacket.index q l : Real) - 1 := by
    have h : (3 : Real) <= CarmichaelPrimePacket.index q l := by exact_mod_cast hThree
    linarith
  have hFrac : 1 / ((CarmichaelPrimePacket.index q l : Real) - 1) <= (1 / 2 : Real) :=
    one_div_le_one_div_of_le (by norm_num) hd
  have h := kernel_ge_mass q l hDiv g hg hOne hNorm u
  linarith

theorem actual_gauss_kernel_ge_half (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (psi : AddChar (ZMod q) Complex) (hPsi : psi.IsPrimitive)
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hThree : 3 <= CarmichaelPrimePacket.index q l) (u : Units (ZMod q)) :
    (1 / 2 : Real) <=
      phaseKernel q l (DirichletEvenGaussPhase.phase q psi) u :=
  kernel_ge_half q l hDiv hThree (DirichletEvenGaussPhase.phase q psi)
    (DirichletEvenGaussPhase.phase_inverse q psi)
    (DirichletEvenGaussPhase.phase_principal q psi)
    (fun chi => le_of_eq (DirichletEvenGaussPhase.phase_norm q psi hPsi chi)) u

theorem actual_gauss_principal_signal (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (psi : AddChar (ZMod q) Complex) (hPsi : psi.IsPrimitive)
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (rho : Complex) (hRhoOne : Not (rho = 1))
    (hZero : DirichletCharacter.LFunction (1 : DirichletCharacter Complex q) rho = 0)
    (E : Complex -> Complex) (hE : AnalyticAt Complex E rho) :
    Not (AnalyticAt Complex
      (CarmichaelWeightedSignal.readout (fun chi => DirichletCharacter.LFunction chi)
        (phaseCoefficient q l (DirichletEvenGaussPhase.phase q psi)) E) rho) := by
  let g := DirichletEvenGaussPhase.phase q psi
  have hg : forall chi : DirichletCharacter Complex q,
      g (Inv.inv chi) = star (g chi) := DirichletEvenGaussPhase.phase_inverse q psi
  have hOne : g 1 = 1 := DirichletEvenGaussPhase.phase_principal q psi
  have hNonneg : forall chi : DirichletCharacter Complex q,
      0 <= (phaseCoefficient q l g chi).re := by
    intro chi
    exact coefficient_re_nonneg q l hDiv g hg hOne chi
      (le_of_eq (DirichletEvenGaussPhase.phase_norm q psi hPsi chi))
  exact CarmichaelWeightedSignal.principal_zero_not_analytic
    (phaseCoefficient q l g) hNonneg (principal q l g)
    rho hRhoOne hZero E hE

end PrimeFactorOscillations.CarmichaelPhaseKernel
