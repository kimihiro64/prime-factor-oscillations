/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelKernelCoset
import PrimeFactorOscillations.Assembly.CarmichaelPrimePacketSpectrum
import PrimeFactorOscillations.Helpers.CubicCoupledPhase

/-!
# Probability profiles compatible with cubic phase projection

The actual single-return spectrum supplies an exact unit l1 amplitude
budget. Every contractive phase filter gives a real profile between zero
and two of mean one; dividing by two gives a probability weight of mean
one half and retains its actual principal correlation coefficient one.
Prescribed unit-phase amplitudes are balanced. Identifying them with the
new profile's full Fourier amplitudes still requires conjugate compatibility.
No prime-sampled bound or zero-free exponent improvement is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelPhaseFilter
open CarmichaelCorrelation CarmichaelCorrelationSpectrum CarmichaelPrimePacket

variable (q : Nat) [NeZero q] (l : Nat.Primes)

def nonprincipal : Finset (DirichletCharacter Complex q) := by
  classical
  exact Finset.univ.erase 1

def amplitude (chi : DirichletCharacter Complex q) : Real := by
  classical
  exact if chi = 1 then 1 else
    -((index q l : Real) - 1) * coefficient (weight q l) chi

def filteredAmplitude (g : DirichletCharacter Complex q -> Complex)
    (chi : DirichletCharacter Complex q) : Complex :=
  (1 / 2 : Complex) * CubicCoupledPhase.project (g chi) (amplitude q l chi : Complex)

def filteredProfile (g : DirichletCharacter Complex q -> Complex)
    (u : Units (ZMod q)) : Real :=
  1 + (nonprincipal q).sum (fun chi =>
    (filteredAmplitude q l g chi * unitCharacter chi (Inv.inv u)).re)

theorem amplitude_nonprincipal_norm
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (chi : DirichletCharacter Complex q) (hChi : Not (chi = 1)) :
    norm (amplitude q l chi : Complex) =
      ((index q l : Real) - 1) * coefficient (weight q l) chi := by
  have hdNat := index_ge_two q l hDiv
  have hd : (0 : Real) <= (index q l : Real) - 1 := by
    have h : (2 : Real) <= index q l := by exact_mod_cast hdNat
    linarith
  have hc := coefficient_nonneg (weight q l) chi
  rw [amplitude, if_neg hChi, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_neg, abs_of_nonneg hd, abs_of_nonneg hc]

theorem amplitude_norm_sum
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q)))) :
    (nonprincipal q).sum (fun chi => norm (amplitude q l chi : Complex)) = 1 := by
  classical
  have hdNat := index_ge_two q l hDiv
  have hd : Not ((index q l : Real) - 1 = 0) := by
    have h : (2 : Real) <= index q l := by exact_mod_cast hdNat
    linarith
  have he : (nonprincipal q).sum (fun chi => norm (amplitude q l chi : Complex)) =
      ((index q l : Real) - 1) *
        (nonprincipal q).sum (coefficient (weight q l)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hChi
    exact amplitude_nonprincipal_norm q l hDiv chi (Finset.mem_erase.mp hChi).1
  rw [he]
  have hMass : (nonprincipal q).sum (coefficient (weight q l)) =
      1 / ((index q l : Real) - 1) := by
    exact nonprincipal_coefficient_mass q l hDiv
  rw [hMass]
  field_simp [hd]

theorem filteredAmplitude_norm_le
    (g : DirichletCharacter Complex q -> Complex)
    (chi : DirichletCharacter Complex q) (hg : norm (g chi) <= 1) :
    norm (filteredAmplitude q l g chi) <= norm (amplitude q l chi : Complex) := by
  have hh := norm_add_le (amplitude q l chi : Complex)
    (g chi * star (amplitude q l chi : Complex))
  simp only [norm_mul, norm_star] at hh
  have ha := norm_nonneg (amplitude q l chi : Complex)
  have hm := mul_le_mul_of_nonneg_right hg ha
  have hx : star (amplitude q l chi : Complex) = (amplitude q l chi : Complex) := by
    change (starRingEnd Complex) (amplitude q l chi : Complex) = (amplitude q l chi : Complex)
    exact Complex.conj_ofReal _
  rw [hx] at hh
  simp only [Complex.norm_real, Real.norm_eq_abs] at hh hm
  unfold filteredAmplitude CubicCoupledPhase.project
  rw [norm_mul]
  norm_num
  nlinarith

theorem filteredAmplitude_norm_sum_le
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (g : DirichletCharacter Complex q -> Complex)
    (hg : forall chi : DirichletCharacter Complex q, norm (g chi) <= 1) :
    (nonprincipal q).sum (fun chi => norm (filteredAmplitude q l g chi)) <= 1 := by
  rw [<- amplitude_norm_sum q l hDiv]
  apply Finset.sum_le_sum
  intro chi _
  exact filteredAmplitude_norm_le q l g chi (hg chi)

theorem filteredProfile_nonneg
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (g : DirichletCharacter Complex q -> Complex)
    (hg : forall chi : DirichletCharacter Complex q, norm (g chi) <= 1)
    (u : Units (ZMod q)) :
    0 <= filteredProfile q l g u := by
  have hTerm (chi : DirichletCharacter Complex q) :
      -norm (filteredAmplitude q l g chi) <=
        (filteredAmplitude q l g chi * unitCharacter chi (Inv.inv u)).re := by
    have h := Complex.re_le_norm
      (-(filteredAmplitude q l g chi * unitCharacter chi (Inv.inv u)))
    rw [Complex.neg_re, norm_neg, norm_mul, character_norm_one, mul_one] at h
    linarith
  have hSum := Finset.sum_le_sum
    (s := nonprincipal q) (fun chi _ => hTerm chi)
  rw [Finset.sum_neg_distrib] at hSum
  have hMass := filteredAmplitude_norm_sum_le q l hDiv g hg
  unfold filteredProfile
  linarith

theorem filtered_principal
    (g : DirichletCharacter Complex q -> Complex)
    (hg : g 1 = 1) :
    filteredAmplitude q l g 1 = 1 := by
  classical
  simp only [filteredAmplitude, amplitude, if_pos rfl, hg]
  rw [CubicCoupledPhase.project_one_real]
  norm_num

theorem filtered_amplitude_balance
    (g : DirichletCharacter Complex q -> Complex)
    (chi : DirichletCharacter Complex q) (hg : norm (g chi) = 1) :
    filteredAmplitude q l g chi * star (g chi) =
      star (filteredAmplitude q l g chi) := by
  have hh := CubicCoupledPhase.project_balance (g chi)
    (amplitude q l chi : Complex) (CubicCoupledPhase.phase_unit_of_norm _ hg)
  have hr : star (1 / 2 : Complex) = (1 / 2 : Complex) := by
    change (starRingEnd Complex) (1 / 2 : Complex) = (1 / 2 : Complex)
    have h := Complex.conj_ofReal (1 / 2 : Real)
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h
  unfold filteredAmplitude
  rw [star_mul, hr, mul_assoc, hh]
  ring

theorem amplitude_sq_eq_coefficient
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (chi : DirichletCharacter Complex q) :
    amplitude q l chi ^ 2 = coefficient (weight q l) chi := by
  classical
  by_cases hChi : chi = 1
  . subst chi
    rw [amplitude, if_pos rfl, coefficient_principal _ (weightSum_pos q l hDiv)]
    norm_num
  . have hdNat := index_ge_two q l hDiv
    have hd : Not ((index q l : Real) - 1 = 0) := by
      have h : (2 : Real) <= index q l := by exact_mod_cast hdNat
      linarith
    by_cases hT : forall u : Units (ZMod q),
        u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1 ->
          chi (u : ZMod q) = 1
    . have hc := CarmichaelPrimePacketSpectrum.coefficient_of_trivial_return
        q l hDiv chi hChi hT
      rw [amplitude, if_neg hChi, hc]
      field_simp [hd]
    . have hc := CarmichaelPrimePacketSpectrum.coefficient_zero_of_not_trivial_return
        q l chi hT
      rw [amplitude, if_neg hChi, hc]
      ring


theorem unit_character_inverse_sum_zero
    (chi : DirichletCharacter Complex q) (hChi : Not (chi = 1)) :
    Finset.univ.sum (fun u : Units (ZMod q) => unitCharacter chi (Inv.inv u)) = 0 := by
  classical
  let H : Subgroup (Units (ZMod q)) := Top.top
  letI : Fintype H := Fintype.ofFinite _
  have hNot : Not (forall h : H, unitCharacter chi h.val = 1) := by
    intro h
    apply unitCharacter_ne_one chi hChi
    ext u
    change unitCharacter chi u = 1
    exact h (Subtype.mk u (by trivial))
  have hh := CarmichaelKernelCoset.inverse_restriction_sum_zero H chi hNot
  let e : Equiv H (Units (ZMod q)) :=
    Equiv.mk Subtype.val (fun u => Subtype.mk u (by trivial))
      (by intro h; cases h; rfl) (by intro u; rfl)
  have he := Equiv.sum_comp e
    (fun u : Units (ZMod q) => unitCharacter chi (Inv.inv u))
  exact he.symm.trans hh

theorem filteredProfile_weightSum
    (g : DirichletCharacter Complex q -> Complex) :
    weightSum (filteredProfile q l g) = Fintype.card (Units (ZMod q)) := by
  classical
  have hInner (chi : DirichletCharacter Complex q)
      (hChi : Membership.mem (nonprincipal q) chi) :
      Finset.univ.sum (fun u : Units (ZMod q) =>
        (filteredAmplitude q l g chi * unitCharacter chi (Inv.inv u)).re) = 0 := by
    have hc := unit_character_inverse_sum_zero q chi (Finset.mem_erase.mp hChi).1
    change Finset.univ.sum (fun u : Units (ZMod q) =>
      Complex.reCLM (filteredAmplitude q l g chi * unitCharacter chi (Inv.inv u))) = 0
    rw [<- map_sum]
    have hz : Finset.univ.sum (fun u : Units (ZMod q) =>
        filteredAmplitude q l g chi * unitCharacter chi (Inv.inv u)) = 0 := by
      rw [<- Finset.mul_sum, hc, mul_zero]
    rw [hz]
    rfl
  unfold weightSum filteredProfile
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Finset.sum_comm]
  have hz : (nonprincipal q).sum (fun chi =>
      Finset.univ.sum (fun u : Units (ZMod q) =>
        (filteredAmplitude q l g chi * unitCharacter chi (Inv.inv u)).re)) = 0 :=
    Finset.sum_eq_zero hInner
  rw [hz, add_zero]

theorem filteredProfile_mean
    (g : DirichletCharacter Complex q -> Complex) :
    weightMean (filteredProfile q l g) = 1 := by
  unfold weightMean
  rw [filteredProfile_weightSum]
  apply div_self
  exact_mod_cast Fintype.card_ne_zero

theorem filteredProfile_le_two
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (g : DirichletCharacter Complex q -> Complex)
    (hg : forall chi : DirichletCharacter Complex q, norm (g chi) <= 1)
    (u : Units (ZMod q)) :
    filteredProfile q l g u <= 2 := by
  have hTerm (chi : DirichletCharacter Complex q) :
      (filteredAmplitude q l g chi * unitCharacter chi (Inv.inv u)).re <=
        norm (filteredAmplitude q l g chi) := by
    have h := Complex.re_le_norm
      (filteredAmplitude q l g chi * unitCharacter chi (Inv.inv u))
    rw [norm_mul, character_norm_one, mul_one] at h
    exact h
  have hSum := Finset.sum_le_sum (s := nonprincipal q) (fun chi _ => hTerm chi)
  have hMass := filteredAmplitude_norm_sum_le q l hDiv g hg
  unfold filteredProfile
  linarith


def probabilityWeight (g : DirichletCharacter Complex q -> Complex)
    (u : Units (ZMod q)) : Real := filteredProfile q l g u / 2

theorem probabilityWeight_bounds
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (g : DirichletCharacter Complex q -> Complex)
    (hg : forall chi : DirichletCharacter Complex q, norm (g chi) <= 1)
    (u : Units (ZMod q)) :
    0 <= probabilityWeight q l g u /\ probabilityWeight q l g u <= 1 := by
  have hLow := filteredProfile_nonneg q l hDiv g hg u
  have hHigh := filteredProfile_le_two q l hDiv g hg u
  unfold probabilityWeight
  constructor <;> linarith

theorem probabilityWeight_mean
    (g : DirichletCharacter Complex q -> Complex) :
    weightMean (probabilityWeight q l g) = 1 / 2 := by
  have hSum := filteredProfile_weightSum q l g
  unfold weightSum at hSum
  change (Finset.univ.sum (fun u : Units (ZMod q) => filteredProfile q l g u / 2)) /
    (Fintype.card (Units (ZMod q)) : Real) = 1 / 2
  rw [<- Finset.sum_div, hSum]
  have hn : Not ((Fintype.card (Units (ZMod q)) : Real) = 0) := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hn]

theorem probabilityWeight_sum_pos
    (g : DirichletCharacter Complex q -> Complex) :
    0 < weightSum (probabilityWeight q l g) := by
  have hh := probabilityWeight_mean q l g
  unfold weightMean at hh
  have hn : (0 : Real) < Fintype.card (Units (ZMod q)) := by
    exact_mod_cast Fintype.card_pos
  have he := (div_eq_iff (ne_of_gt hn)).mp hh
  rw [he]
  positivity

theorem probabilityWeight_principal
    (g : DirichletCharacter Complex q -> Complex) :
    coefficient (probabilityWeight q l g) 1 = 1 :=
  coefficient_principal _ (probabilityWeight_sum_pos q l g)

end PrimeFactorOscillations.CarmichaelPhaseFilter
