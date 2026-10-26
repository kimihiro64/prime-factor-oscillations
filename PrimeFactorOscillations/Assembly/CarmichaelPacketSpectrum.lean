/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelCorrelationSpectrum
import PrimeFactorOscillations.Helpers.ReturnPacketPowerSupport

/-!
# Exact Dirichlet filters for native prime-return kernels

The full kernel inversion can be restricted to characters trivial on the
actual packet kernel. In particular every surviving character has power one
at the squarefree label product. Principal mass is unchanged.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelPacketSpectrum

open CarmichaelCorrelation CarmichaelCorrelationSpectrum PrimeOrderReturnLaw

def powerCharacters (q P : Nat) : Finset (DirichletCharacter Complex q) := by
  classical
  exact Finset.univ.filter (fun chi =>
    forall u : Units (ZMod q), (chi (u : ZMod q)) ^ P = 1)

def kernelCharacters (q : Nat) (S : Finset Nat.Primes) :
    Finset (DirichletCharacter Complex q) := by
  classical
  exact Finset.univ.filter (fun chi =>
    forall u : Units (ZMod q),
      packetProjection (Monoid.exponent (Units (ZMod q))) S u = 1 ->
        chi (u : ZMod q) = 1)

theorem vacancy_characterSum_zero_of_not_power
    (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (P : Nat) (hP : forall p : S, Dvd.dvd (p.val : Nat) P)
    (chi : DirichletCharacter Complex q)
    (hPower : Not (forall u : Units (ZMod q), (chi (u : ZMod q)) ^ P = 1)) :
    characterSum
      (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S)
      (unitCharacter chi) = 0 := by
  classical
  let L := Monoid.exponent (Units (ZMod q))
  have h := ReturnPacketPowerSupport.vacancy_sum_eq_zero_of_not_power L P S hDiv hP
    (fun g => Monoid.pow_exponent_eq_one g) (unitCharacter chi) hPower
  have hWeight (g : Units (ZMod q)) : (vacancyWeight L S g : Complex) =
      if OddReturnCharacterSupport.vacancy L S g then (1 : Complex) else 0 := by
    unfold vacancyWeight
    split_ifs <;> norm_num
  change characterSum (vacancyWeight L S) (unitCharacter chi) = 0
  unfold characterSum
  simp_rw [hWeight]
  exact h

theorem coefficient_zero_of_not_power
    (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (P : Nat) (hP : forall p : S, Dvd.dvd (p.val : Nat) P)
    (chi : DirichletCharacter Complex q)
    (hPower : Not (forall u : Units (ZMod q), (chi (u : ZMod q)) ^ P = 1)) :
    coefficient
      (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S) chi = 0 := by
  unfold coefficient
  rw [vacancy_characterSum_zero_of_not_power q S hDiv P hP chi hPower]
  simp

theorem coefficient_zero_outside_label_product
    (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (chi : DirichletCharacter Complex q)
    (hPower : Not (forall u : Units (ZMod q),
      (chi (u : ZMod q)) ^ S.prod (fun p => (p : Nat)) = 1)) :
    coefficient
      (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S) chi = 0 := by
  exact coefficient_zero_of_not_power q S hDiv (S.prod (fun p => (p : Nat)))
    (fun p => Finset.dvd_prod_of_mem (fun r : Nat.Primes => (r : Nat))
      (a := p.val) (s := S) p.property) chi hPower

theorem nonzero_coefficient_label_power
    (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (chi : DirichletCharacter Complex q)
    (hNonzero : Not (coefficient
      (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S) chi = 0)) :
    forall u : Units (ZMod q),
      (chi (u : ZMod q)) ^ S.prod (fun p => (p : Nat)) = 1 := by
  by_contra hPower
  exact hNonzero (coefficient_zero_outside_label_product q S hDiv chi hPower)

theorem coefficient_zero_of_kernel_witness
    (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (chi : DirichletCharacter Complex q)
    (hWitness : exists a : Units (ZMod q),
      packetProjection (Monoid.exponent (Units (ZMod q))) S a = 1 /\
        Not (chi (a : ZMod q) = 1)) :
    coefficient
      (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S) chi = 0 := by
  classical
  let L := Monoid.exponent (Units (ZMod q))
  have h := ReturnPacketPowerSupport.vacancy_sum_eq_zero_of_kernel_witness L S
    (unitCharacter chi) hWitness
  have hWeight (g : Units (ZMod q)) : (vacancyWeight L S g : Complex) =
      if OddReturnCharacterSupport.vacancy L S g then (1 : Complex) else 0 := by
    unfold vacancyWeight
    split_ifs <;> norm_num
  have hZero : characterSum (vacancyWeight L S) (unitCharacter chi) = 0 := by
    unfold characterSum
    simp_rw [hWeight]
    exact h
  unfold coefficient
  rw [hZero]
  simp

theorem nonzero_coefficient_trivial_on_kernel
    (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (chi : DirichletCharacter Complex q)
    (hNonzero : Not (coefficient
      (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S) chi = 0)) :
    forall u : Units (ZMod q),
      packetProjection (Monoid.exponent (Units (ZMod q))) S u = 1 ->
        chi (u : ZMod q) = 1 := by
  classical
  by_contra hNot
  have hWitness : exists a : Units (ZMod q),
      packetProjection (Monoid.exponent (Units (ZMod q))) S a = 1 /\
        Not (chi (a : ZMod q) = 1) := by
    choose a hA using (not_forall.mp hNot)
    choose hKernel hCharacter using (not_forall.mp hA)
    exact Exists.intro a (And.intro hKernel hCharacter)
  exact hNonzero (coefficient_zero_of_kernel_witness q S chi hWitness)

theorem kernel_expansion_label_power
    (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (u : Units (ZMod q)) :
    (kernel (vacancyWeight (G := Units (ZMod q))
      (Monoid.exponent (Units (ZMod q))) S) u : Complex) =
      (powerCharacters q (S.prod (fun p => (p : Nat)))).sum
        (fun chi => (coefficient (vacancyWeight (G := Units (ZMod q))
          (Monoid.exponent (Units (ZMod q))) S) chi : Complex) *
            unitCharacter chi (Inv.inv u)) := by
  classical
  rw [kernel_expansion, powerCharacters, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro chi _
  by_cases hPower : forall v : Units (ZMod q),
      (chi (v : ZMod q)) ^ S.prod (fun p => (p : Nat)) = 1
  . rw [ite_eq_left hPower]
  . rw [ite_eq_right hPower, coefficient_zero_outside_label_product q S hDiv chi hPower]
    simp

theorem kernel_expansion_actual_kernel
    (q : Nat) [NeZero q] (S : Finset Nat.Primes) (u : Units (ZMod q)) :
    (kernel (vacancyWeight (G := Units (ZMod q))
      (Monoid.exponent (Units (ZMod q))) S) u : Complex) =
      (kernelCharacters q S).sum
        (fun chi => (coefficient (vacancyWeight (G := Units (ZMod q))
          (Monoid.exponent (Units (ZMod q))) S) chi : Complex) *
            unitCharacter chi (Inv.inv u)) := by
  classical
  rw [kernel_expansion, kernelCharacters, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro chi _
  by_cases hKernel : forall v : Units (ZMod q),
      packetProjection (Monoid.exponent (Units (ZMod q))) S v = 1 ->
        chi (v : ZMod q) = 1
  . rw [ite_eq_left hKernel]
  . have hZero : coefficient
        (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S) chi = 0 := by
      by_contra hNot
      exact hKernel (nonzero_coefficient_trivial_on_kernel q S chi hNot)
    rw [ite_eq_right hKernel, hZero]
    simp

end PrimeFactorOscillations.CarmichaelPacketSpectrum
