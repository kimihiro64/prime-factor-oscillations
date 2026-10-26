/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPrimePacket

/-!
# Flat nonprincipal spectrum of a single prime return packet

A nonprincipal character survives exactly when it is trivial on the actual
return subgroup. Every survivor has the same positive coefficient. The
principal coefficient remains one and the full complex phases are retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelPrimePacketSpectrum

open CarmichaelPrimePacket CarmichaelCorrelation CarmichaelCorrelationSpectrum
open PrimeOrderReturnLaw

theorem characterSum_of_trivial_return
    (q : Nat) [NeZero q] (l : Nat.Primes)
    (chi : DirichletCharacter Complex q) (hChi : Not (chi = 1))
    (hTrivial : forall u : Units (ZMod q),
      u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1 ->
        chi (u : ZMod q) = 1) :
    characterSum (weight q l) (unitCharacter chi) =
      ((weightSum (weight q l) - (Fintype.card (Units (ZMod q)) : Real) : Real) : Complex) := by
  classical
  have hPower : Not (forall u : Units (ZMod q), (unitCharacter chi u) ^ 1 = 1) := by
    intro h
    apply unitCharacter_ne_one chi hChi
    ext u
    change unitCharacter chi u = 1
    simpa only [pow_one] using h u
  have hEmpty (p : (Finset.empty : Finset Nat.Primes)) : False :=
    Finset.notMem_empty p.val p.property
  have hSumZero : Finset.univ.sum (fun u : Units (ZMod q) => unitCharacter chi u) = 0 := by
    simpa only [one_mul] using
      ReturnPacketPowerSupport.packet_sum_eq_zero_of_not_power
        (Monoid.exponent (Units (ZMod q))) 1 Finset.empty
        (fun p => (hEmpty p).elim) (fun p => (hEmpty p).elim)
        (fun g => Monoid.pow_exponent_eq_one g) (unitCharacter chi) hPower (fun _ => 1)
  have hPoint (u : Units (ZMod q)) :
      (weight q l u : Complex) * unitCharacter chi u =
        unitCharacter chi u - (1 - (weight q l u : Complex)) := by
    by_cases hReturn : u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1
    . have hw : weight q l u = 0 := by
        simp [weight, vacancyWeight, vacancy_iff_not_return, hReturn]
      simp only [hw, Complex.ofReal_zero, zero_mul, sub_zero]
      change 0 = chi (u : ZMod q) - 1
      rw [hTrivial u hReturn, sub_self]
    . have hw : weight q l u = 1 := by
        simp [weight, vacancyWeight, vacancy_iff_not_return, hReturn]
      simp only [hw, Complex.ofReal_one, one_mul, sub_self, sub_zero]
  have hWeightSum :
      Finset.univ.sum (fun u : Units (ZMod q) => (weight q l u : Complex)) =
        (weightSum (weight q l) : Complex) := by
    rw [<- Complex.ofReal_sum]
    rfl
  have hOneSum : Finset.univ.sum (fun _ : Units (ZMod q) => (1 : Complex)) =
      ((Fintype.card (Units (ZMod q)) : Real) : Complex) := by
    simp
  calc
    _ = Finset.univ.sum (fun u : Units (ZMod q) => unitCharacter chi u) -
        Finset.univ.sum (fun u : Units (ZMod q) => 1 - (weight q l u : Complex)) := by
      unfold characterSum
      simp_rw [hPoint]
      rw [Finset.sum_sub_distrib]
    _ = _ := by
      rw [hSumZero, Finset.sum_sub_distrib, hOneSum, hWeightSum]
      push_cast
      ring

theorem coefficient_of_trivial_return
    (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (chi : DirichletCharacter Complex q) (hChi : Not (chi = 1))
    (hTrivial : forall u : Units (ZMod q),
      u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1 ->
        chi (u : ZMod q) = 1) :
    coefficient (weight q l) chi = 1 / ((index q l : Real) - 1) ^ 2 := by
  have hdNat := index_ge_two q l hDiv
  have hd : (1 : Real) < index q l := by exact_mod_cast (show 1 < index q l by omega)
  have h0 : Not ((index q l : Real) = 0) := ne_of_gt (zero_lt_one.trans hd)
  have h1 : Not ((index q l : Real) - 1 = 0) := sub_ne_zero.mpr (ne_of_gt hd)
  have hn : Not ((Fintype.card (Units (ZMod q)) : Real) = 0) := by
    exact_mod_cast Fintype.card_ne_zero
  have hWeight : weightSum (weight q l) =
      (((index q l : Real) - 1) / (index q l : Real)) *
        (Fintype.card (Units (ZMod q)) : Real) := by
    calc
      _ = weightMean (weight q l) * (Fintype.card (Units (ZMod q)) : Real) := by
        unfold weightMean
        field_simp [hn]
      _ = (1 - 1 / (index q l : Real)) * (Fintype.card (Units (ZMod q)) : Real) := by
        rw [weight_mean q l hDiv]
      _ = _ := by field_simp [h0]
  unfold coefficient
  rw [characterSum_of_trivial_return q l chi hChi hTrivial, Complex.normSq_ofReal, hWeight]
  field_simp [hn, h0, h1]
  ring

theorem coefficient_zero_of_not_trivial_return
    (q : Nat) [NeZero q] (l : Nat.Primes)
    (chi : DirichletCharacter Complex q)
    (hNot : Not (forall u : Units (ZMod q),
      u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1 ->
        chi (u : ZMod q) = 1)) :
    coefficient (weight q l) chi = 0 := by
  classical
  choose a hA using (not_forall.mp hNot)
  choose hReturn hCharacter using (not_forall.mp hA)
  exact CarmichaelPacketSpectrum.coefficient_zero_of_kernel_witness q {l} chi
    (Exists.intro a (And.intro
      ((projection_eq_one_iff_return q l a).mpr hReturn) hCharacter))

theorem coefficient_nonzero_iff_trivial_return
    (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (chi : DirichletCharacter Complex q) :
    Not (coefficient (weight q l) chi = 0) <->
      forall u : Units (ZMod q),
        u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1 ->
          chi (u : ZMod q) = 1 := by
  classical
  constructor
  . intro hNonzero u hReturn
    exact CarmichaelPacketSpectrum.nonzero_coefficient_trivial_on_kernel q {l} chi hNonzero u
      ((projection_eq_one_iff_return q l u).mpr hReturn)
  . intro hTrivial
    by_cases hChi : chi = 1
    . subst chi
      rw [coefficient_principal (weight q l) (weightSum_pos q l hDiv)]
      norm_num
    . rw [coefficient_of_trivial_return q l hDiv chi hChi hTrivial]
      have hdNat := index_ge_two q l hDiv
      have hd : 0 < (index q l : Real) - 1 := by
        have h : (1 : Real) < index q l := by exact_mod_cast (show 1 < index q l by omega)
        linarith
      exact ne_of_gt (div_pos zero_lt_one (sq_pos_of_pos hd))

theorem nonzero_coefficient_prime_power
    (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (chi : DirichletCharacter Complex q)
    (hNonzero : Not (coefficient (weight q l) chi = 0)) :
    forall u : Units (ZMod q), (chi (u : ZMod q)) ^ (l : Nat) = 1 := by
  have hDiv' : forall p : ({l} : Finset Nat.Primes),
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))) := by
    intro p
    have hp : p.val = l := Finset.mem_singleton.mp p.property
    simpa only [hp] using hDiv
  have h := CarmichaelPacketSpectrum.nonzero_coefficient_label_power q {l} hDiv' chi hNonzero
  simpa only [Finset.prod_singleton] using h

theorem kernel_expansion_prime_order
    (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (u : Units (ZMod q)) :
    (kernel (weight q l) u : Complex) =
      (CarmichaelPacketSpectrum.powerCharacters q (l : Nat)).sum
        (fun chi => (coefficient (weight q l) chi : Complex) *
          unitCharacter chi (Inv.inv u)) := by
  have hDiv' : forall p : ({l} : Finset Nat.Primes),
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))) := by
    intro p
    have hp : p.val = l := Finset.mem_singleton.mp p.property
    simpa only [hp] using hDiv
  simpa only [weight, Finset.prod_singleton] using
    CarmichaelPacketSpectrum.kernel_expansion_label_power q {l} hDiv' u

theorem exists_nonprincipal_prime_character
    (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q)))) :
    exists chi : DirichletCharacter Complex q, Not (chi = 1) /\
      (forall u : Units (ZMod q), (chi (u : ZMod q)) ^ (l : Nat) = 1) /\
        coefficient (weight q l) chi = 1 / ((index q l : Real) - 1) ^ 2 := by
  classical
  let : DecidableEq (DirichletCharacter Complex q) :=
    CarmichaelPrimePacket.characterDecidableEq q
  have hdNat := index_ge_two q l hDiv
  have hd : 0 < (index q l : Real) - 1 := by
    have h : (1 : Real) < index q l := by exact_mod_cast (show 1 < index q l by omega)
    linarith
  have hMassPos :
      0 < (Finset.univ.erase (1 : DirichletCharacter Complex q)).sum
        (coefficient (weight q l)) := by
    rw [nonprincipal_coefficient_mass q l hDiv]
    exact div_pos zero_lt_one hd
  have hExists : exists chi : DirichletCharacter Complex q,
      Not (chi = 1) /\ 0 < coefficient (weight q l) chi := by
    by_contra hNo
    have hNonpos :
        (Finset.univ.erase (1 : DirichletCharacter Complex q)).sum
          (coefficient (weight q l)) <= 0 := by
      apply Finset.sum_nonpos
      intro chi hMem
      by_contra hn
      exact hNo (Exists.intro chi (And.intro (Finset.mem_erase.mp hMem).1 (lt_of_not_ge hn)))
    exact (not_le_of_gt hMassPos) hNonpos
  choose chi hChi hPositive using hExists
  have hNonzero := ne_of_gt hPositive
  refine Exists.intro chi (And.intro hChi
    (And.intro (nonzero_coefficient_prime_power q l hDiv chi hNonzero) ?_))
  exact coefficient_of_trivial_return q l hDiv chi hChi
    ((coefficient_nonzero_iff_trivial_return q l hDiv chi).mp hNonzero)

end PrimeFactorOscillations.CarmichaelPrimePacketSpectrum
