/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelCrossCorrelation
import PrimeFactorOscillations.Assembly.CarmichaelPhaseFilter

/-!
# Exact Fourier matching for Carmichael phase-filter profiles

The actual finite unit-group character sums retain character inversion.
Hermitian coefficients reconstruct real profiles with their exact full
Fourier amplitudes. This module supplies the matching needed to apply
the preserved principal-zero signal; it is not an arithmetic exponent bound.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelFilteredSpectrum
open CarmichaelCorrelation CarmichaelCorrelationSpectrum CarmichaelPhaseFilter

local instance (q : Nat) : DecidableEq (DirichletCharacter Complex q) :=
  Classical.typeDecidableEq _

theorem unit_inverse_value (q : Nat) [NeZero q]
    (chi : DirichletCharacter Complex q) (u : Units (ZMod q)) :
    unitCharacter (Inv.inv chi) u = star (unitCharacter chi u) := by
  have hne : Not (unitCharacter chi u = 0) := by
    intro hz
    have h := character_norm_one (unitCharacter chi) u
    rw [hz, norm_zero] at h
    norm_num at h
  have hc := character_mul_conj_one (unitCharacter chi) u
  have hh : (starRingEnd Complex) (unitCharacter chi u) =
      1 / unitCharacter chi u := by
    apply (eq_div_iff hne).mpr
    simpa only [mul_comm] using hc
  simp only [one_div] at hh
  change (Inv.inv chi) (u : ZMod q) = (starRingEnd Complex) (unitCharacter chi u)
  rw [MulChar.inv_apply_eq_inv']
  exact hh.symm

theorem unit_inverse_input (q : Nat) [NeZero q]
    (chi : DirichletCharacter Complex q) (u : Units (ZMod q)) :
    unitCharacter chi (Inv.inv u) = star (unitCharacter chi u) := by
  have hne : Not (unitCharacter chi u = 0) := by
    intro hz
    have h := character_norm_one (unitCharacter chi) u
    rw [hz, norm_zero] at h
    norm_num at h
  have hc := character_mul_conj_one (unitCharacter chi) u
  have hh : (starRingEnd Complex) (unitCharacter chi u) =
      1 / unitCharacter chi u := by
    apply (eq_div_iff hne).mpr
    simpa only [mul_comm] using hc
  have hm : unitCharacter chi u * unitCharacter chi (Inv.inv u) = 1 := by
    rw [<- map_mul, mul_inv_cancel, map_one]
  calc
    _ = 1 / unitCharacter chi u := by
      apply (eq_div_iff hne).mpr
      simpa only [mul_comm] using hm
    _ = _ := hh.symm

theorem unit_mixed_sum (q : Nat) [NeZero q]
    (chi psi : DirichletCharacter Complex q) :
    Finset.univ.sum (fun u : Units (ZMod q) =>
      unitCharacter chi (Inv.inv u) * unitCharacter psi u) =
        if chi = psi then (Fintype.card (Units (ZMod q)) : Complex) else 0 := by
  classical
  by_cases he : chi = psi
  . subst psi
    rw [if_pos rfl]
    have hTerm (u : Units (ZMod q)) :
        unitCharacter chi (Inv.inv u) * unitCharacter chi u = 1 := by
      rw [<- map_mul, inv_mul_cancel, map_one]
    simp only [hTerm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  . rw [if_neg he]
    let theta : DirichletCharacter Complex q := chi * Inv.inv psi
    have hn : Not (theta = 1) := by
      intro hz
      exact he (mul_inv_eq_one.mp hz)
    have hs := unit_character_inverse_sum_zero q theta hn
    calc
      _ = Finset.univ.sum (fun u : Units (ZMod q) =>
          unitCharacter theta (Inv.inv u)) := by
        apply Finset.sum_congr rfl
        intro u _
        change _ = unitCharacter chi (Inv.inv u) *
          unitCharacter (Inv.inv psi) (Inv.inv u)
        rw [unit_inverse_value q psi (Inv.inv u), unit_inverse_input q psi u,
          star_star]
      _ = 0 := hs

theorem characterSum_inverse (q : Nat) [NeZero q]
    (w : Units (ZMod q) -> Real) (chi : DirichletCharacter Complex q) :
    characterSum w (unitCharacter (Inv.inv chi)) =
      star (characterSum w (unitCharacter chi)) := by
  change Finset.univ.sum (fun u => (w u : Complex) * unitCharacter (Inv.inv chi) u) =
    (starRingEnd Complex) (Finset.univ.sum (fun u =>
      (w u : Complex) * unitCharacter chi u))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [unit_inverse_value]
  change _ = (starRingEnd Complex) _
  rw [map_mul, Complex.conj_ofReal]
  rfl

theorem hermitian_series (q : Nat) [NeZero q]
    (a : DirichletCharacter Complex q -> Complex)
    (hSym : forall chi, a (Inv.inv chi) = star (a chi))
    (u : Units (ZMod q)) :
    star (Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
      a chi * unitCharacter chi (Inv.inv u))) =
        Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
          a chi * unitCharacter chi (Inv.inv u)) := by
  classical
  change (starRingEnd Complex) (Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
    a chi * unitCharacter chi (Inv.inv u))) = _
  rw [map_sum]
  have hTerm (chi : DirichletCharacter Complex q) :
      (starRingEnd Complex) (a chi * unitCharacter chi (Inv.inv u)) =
        a (Inv.inv chi) * unitCharacter (Inv.inv chi) (Inv.inv u) := by
    have hA := hSym chi
    change a (Inv.inv chi) = (starRingEnd Complex) (a chi) at hA
    have hB := unit_inverse_value q chi (Inv.inv u)
    change unitCharacter (Inv.inv chi) (Inv.inv u) =
      (starRingEnd Complex) (unitCharacter chi (Inv.inv u)) at hB
    rw [map_mul, <- hA, <- hB]
  calc
    _ = Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        a (Inv.inv chi) * unitCharacter (Inv.inv chi) (Inv.inv u)) :=
      Finset.sum_congr rfl (fun chi _ => hTerm chi)
    _ = _ := Equiv.sum_comp (Equiv.inv (DirichletCharacter Complex q))
      (fun chi => a chi * unitCharacter chi (Inv.inv u))

theorem real_series_cast (q : Nat) [NeZero q]
    (a : DirichletCharacter Complex q -> Complex)
    (hSym : forall chi, a (Inv.inv chi) = star (a chi))
    (u : Units (ZMod q)) :
    ((Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
      a chi * unitCharacter chi (Inv.inv u))).re : Complex) =
        Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
          a chi * unitCharacter chi (Inv.inv u)) := by
  let z : Complex := Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
    a chi * unitCharacter chi (Inv.inv u))
  have h := hermitian_series q a hSym u
  change (starRingEnd Complex) z = z at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  change (z.re : Complex) = z
  apply Complex.ext
  . rfl
  . change 0 = z.im
    linarith

theorem real_series_characterSum (q : Nat) [NeZero q]
    (a : DirichletCharacter Complex q -> Complex)
    (hSym : forall chi, a (Inv.inv chi) = star (a chi))
    (psi : DirichletCharacter Complex q) :
    characterSum (fun u : Units (ZMod q) =>
      (Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        a chi * unitCharacter chi (Inv.inv u))).re) (unitCharacter psi) =
      (Fintype.card (Units (ZMod q)) : Complex) * a psi := by
  classical
  calc
    _ = Finset.univ.sum (fun u : Units (ZMod q) =>
        Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
          a chi * (unitCharacter chi (Inv.inv u) * unitCharacter psi u))) := by
      unfold characterSum
      apply Finset.sum_congr rfl
      intro u _
      rw [real_series_cast q a hSym u, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro chi _
      ring
    _ = Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        a chi * Finset.univ.sum (fun u : Units (ZMod q) =>
          unitCharacter chi (Inv.inv u) * unitCharacter psi u)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro chi _
      rw [Finset.mul_sum]
    _ = _ := by
      simp_rw [unit_mixed_sum]
      simp [mul_ite, mul_comm]

theorem coefficient_inverse (q : Nat) [NeZero q]
    (w : Units (ZMod q) -> Real) (chi : DirichletCharacter Complex q) :
    coefficient w (Inv.inv chi) = coefficient w chi := by
  unfold coefficient
  rw [characterSum_inverse]
  simp only [Complex.normSq_eq_norm_sq, norm_star]

theorem amplitude_inverse (q : Nat) [NeZero q] (l : Nat.Primes)
    (chi : DirichletCharacter Complex q) :
    amplitude q l (Inv.inv chi) = amplitude q l chi := by
  classical
  by_cases hc : chi = 1
  . subst chi
    simp only [inv_one]
  . have hi : Not (Inv.inv chi = 1) := inv_ne_one.mpr hc
    simp only [amplitude, if_neg hi, if_neg hc, coefficient_inverse]

theorem filteredAmplitude_formula (q : Nat) [NeZero q] (l : Nat.Primes)
    (g : DirichletCharacter Complex q -> Complex)
    (chi : DirichletCharacter Complex q) :
    filteredAmplitude q l g chi =
      ((amplitude q l chi / 2 : Real) : Complex) * (1 + g chi) := by
  have hr : star (amplitude q l chi : Complex) = (amplitude q l chi : Complex) := by
    change (starRingEnd Complex) (amplitude q l chi : Complex) = _
    exact Complex.conj_ofReal _
  unfold filteredAmplitude CubicCoupledPhase.project
  rw [hr]
  push_cast
  ring

theorem filteredAmplitude_inverse (q : Nat) [NeZero q] (l : Nat.Primes)
    (g : DirichletCharacter Complex q -> Complex)
    (hg : forall chi, g (Inv.inv chi) = star (g chi))
    (chi : DirichletCharacter Complex q) :
    filteredAmplitude q l g (Inv.inv chi) =
      star (filteredAmplitude q l g chi) := by
  rw [filteredAmplitude_formula, filteredAmplitude_formula, amplitude_inverse, hg]
  change _ = (starRingEnd Complex) _
  rw [map_mul, Complex.conj_ofReal, map_add, map_one]
  rfl

theorem filteredProfile_realSeries (q : Nat) [NeZero q] (l : Nat.Primes)
    (g : DirichletCharacter Complex q -> Complex) (hOne : g 1 = 1)
    (u : Units (ZMod q)) :
    filteredProfile q l g u =
      (Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        filteredAmplitude q l g chi * unitCharacter chi (Inv.inv u))).re := by
  classical
  let f (chi : DirichletCharacter Complex q) : Complex :=
    filteredAmplitude q l g chi * unitCharacter chi (Inv.inv u)
  have hp := filtered_principal q l g hOne
  have hu : unitCharacter (1 : DirichletCharacter Complex q) (Inv.inv u) = 1 := by
    rw [unitCharacter_one, MonoidHom.one_apply]
  have hf : f 1 = 1 := by
    dsimp [f]
    rw [hp, hu, mul_one]
  have hs : Finset.univ.sum f = (nonprincipal q).sum f + 1 := by
    calc
      _ = (Finset.univ.erase (1 : DirichletCharacter Complex q)).sum f + f 1 :=
        (Finset.sum_erase_add Finset.univ f (Finset.mem_univ 1)).symm
      _ = _ := by
        rw [hf]
        rfl
  change filteredProfile q l g u = (Finset.univ.sum f).re
  rw [hs, Complex.add_re, Complex.one_re]
  have hRe : ((nonprincipal q).sum f).re =
      (nonprincipal q).sum (fun chi => (f chi).re) :=
    map_sum Complex.reCLM f (nonprincipal q)
  change 1 + (nonprincipal q).sum (fun chi => (f chi).re) =
    ((nonprincipal q).sum f).re + 1
  rw [hRe]
  ring

theorem filteredProfile_characterSum (q : Nat) [NeZero q] (l : Nat.Primes)
    (g : DirichletCharacter Complex q -> Complex)
    (hg : forall chi, g (Inv.inv chi) = star (g chi)) (hOne : g 1 = 1)
    (psi : DirichletCharacter Complex q) :
    characterSum (filteredProfile q l g) (unitCharacter psi) =
      (Fintype.card (Units (ZMod q)) : Complex) * filteredAmplitude q l g psi := by
  have hFun : filteredProfile q l g = fun u : Units (ZMod q) =>
      (Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        filteredAmplitude q l g chi * unitCharacter chi (Inv.inv u))).re := by
    funext u
    exact filteredProfile_realSeries q l g hOne u
  rw [hFun]
  exact real_series_characterSum q (filteredAmplitude q l g)
    (filteredAmplitude_inverse q l g hg) psi

end PrimeFactorOscillations.CarmichaelFilteredSpectrum
