/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.GCDMonoid.Finset
import PrimeFactorOscillations.Assembly.CarmichaelDualCarrier
import PrimeFactorOscillations.Assembly.CarmichaelPrimePacketSpectrum

/-!
# The exact conductor of the original native probability kernel

For every positive modulus, descent of the full native kernel is
equivalent to simultaneous descent of every actual surviving character.
Their conductor lcm is the attained least actual unit reduction modulus.
For squarefree levels it equals the intrinsic probability carrier product,
and therefore the first positive zero frequency of the signed additive
spectrum. The principal coefficient, phases and zero masks remain intact.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelSpectralConductor

open CarmichaelPrimePacket CarmichaelCorrelation CarmichaelCorrelationSpectrum
open CarmichaelPrimePacketSpectrum CarmichaelDualCarrier

theorem kernel_reduction_iff_survivors_factor
    (q d : Nat) [NeZero q] [NeZero d] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hd : Dvd.dvd d q) :
    (forall u v : Units (ZMod q), ZMod.unitsMap hd u = ZMod.unitsMap hd v ->
      kernel (weight q l) u = kernel (weight q l) v) <->
        forall chi : DirichletCharacter Complex q,
          Not (coefficient (weight q l) chi = 0) -> chi.FactorsThrough d := by
  constructor
  . intro hFiber chi hNonzero
    apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
    intro u hu
    have hReduce : ZMod.unitsMap hd u = ZMod.unitsMap hd 1 := by
      change ZMod.unitsMap hd u = 1 at hu
      simpa only [map_one] using hu
    have hReturn := (kernel_peak_iff_return q l hDiv u).mp (hFiber u 1 hReduce)
    apply Units.ext
    change chi (u : ZMod q) = 1
    exact (coefficient_nonzero_iff_trivial_return q l hDiv chi).mp hNonzero u hReturn
  . intro hFactor u v hReduce
    classical
    apply Complex.ofReal_injective
    rw [kernel_expansion, kernel_expansion]
    apply Finset.sum_congr rfl
    intro chi _
    by_cases hZero : coefficient (weight q l) chi = 0
    . simp only [hZero, Complex.ofReal_zero, zero_mul]
    . apply congrArg (fun z : Complex => (coefficient (weight q l) chi : Complex) * z)
      change chi (Units.val (Inv.inv u)) = chi (Units.val (Inv.inv v))
      choose hd' psi hChi using hFactor chi hZero
      have hUnits : chi.toUnitHom (Inv.inv u) = chi.toUnitHom (Inv.inv v) := by
        rw [hChi, DirichletCharacter.changeLevel_toUnitHom]
        apply congrArg psi.toUnitHom
        simpa only [map_inv] using
          congrArg (fun z : Units (ZMod d) => Inv.inv z) hReduce
      have hValues := congrArg (fun z : Units Complex => (z : Complex)) hUnits
      simpa only [MulChar.coe_toUnitHom] using hValues

theorem kernel_reduction_iff_survivor_conductors
    (q d : Nat) [NeZero q] [NeZero d] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hd : Dvd.dvd d q) :
    (forall u v : Units (ZMod q), ZMod.unitsMap hd u = ZMod.unitsMap hd v ->
      kernel (weight q l) u = kernel (weight q l) v) <->
        forall chi : DirichletCharacter Complex q,
          Not (coefficient (weight q l) chi = 0) -> Dvd.dvd chi.conductor d := by
  rw [kernel_reduction_iff_survivors_factor q d l hDiv hd]
  apply forall_congr'
  intro chi
  apply imp_congr_right
  intro _
  exact DirichletCharacter.mem_conductorSet_iff_conductor_dvd chi hd

def spectralConductor (q : Nat) [NeZero q] (l : Nat.Primes) : Nat := by
  classical
  exact ((Finset.univ : Finset (DirichletCharacter Complex q)).filter
    (fun chi => Not (coefficient (weight q l) chi = 0))).lcm
      (fun chi => chi.conductor)

theorem spectralConductor_dvd_iff
    (q : Nat) [NeZero q] (l : Nat.Primes) (d : Nat) :
    Dvd.dvd (spectralConductor q l) d <->
      forall chi : DirichletCharacter Complex q,
        Not (coefficient (weight q l) chi = 0) -> Dvd.dvd chi.conductor d := by
  classical
  simp only [spectralConductor, Finset.lcm_dvd_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem spectralConductor_dvd_level
    (q : Nat) [NeZero q] (l : Nat.Primes) :
    Dvd.dvd (spectralConductor q l) q := by
  apply (spectralConductor_dvd_iff q l q).mpr
  intro chi _
  exact chi.conductor_dvd_level

theorem spectralConductor_pos (q : Nat) [NeZero q] (l : Nat.Primes) :
    0 < spectralConductor q l := by
  apply Nat.pos_of_ne_zero
  intro hZero
  have hDiv := spectralConductor_dvd_level q l
  rw [hZero] at hDiv
  exact NeZero.ne q (Nat.eq_zero_of_zero_dvd hDiv)

local instance spectralConductorNeZero (q : Nat) [NeZero q] (l : Nat.Primes) :
    NeZero (spectralConductor q l) :=
  NeZero.mk (ne_of_gt (spectralConductor_pos q l))

theorem kernel_reduction_iff_spectralConductor_dvd
    (q d : Nat) [NeZero q] [NeZero d] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hd : Dvd.dvd d q) :
    (forall u v : Units (ZMod q), ZMod.unitsMap hd u = ZMod.unitsMap hd v ->
      kernel (weight q l) u = kernel (weight q l) v) <->
        Dvd.dvd (spectralConductor q l) d :=
  (kernel_reduction_iff_survivor_conductors q d l hDiv hd).trans
    (spectralConductor_dvd_iff q l d).symm

theorem spectralConductor_attained (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q)))) :
    forall u v : Units (ZMod q),
      ZMod.unitsMap (spectralConductor_dvd_level q l) u =
        ZMod.unitsMap (spectralConductor_dvd_level q l) v ->
          kernel (weight q l) u = kernel (weight q l) v :=
  (kernel_reduction_iff_spectralConductor_dvd q (spectralConductor q l) l hDiv
    (spectralConductor_dvd_level q l)).mpr (dvd_refl _)

theorem exists_reduced_kernel_iff
    (q d : Nat) [NeZero q] [NeZero d] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hd : Dvd.dvd d q) :
    (exists f : Units (ZMod d) -> Real,
      forall u : Units (ZMod q), kernel (weight q l) u = f (ZMod.unitsMap hd u)) <->
        Dvd.dvd (spectralConductor q l) d := by
  constructor
  . intro h
    choose f hf using h
    apply (kernel_reduction_iff_spectralConductor_dvd q d l hDiv hd).mp
    intro u v hReduce
    rw [hf u, hf v, hReduce]
  . intro hDivisor
    have hFiber := (kernel_reduction_iff_spectralConductor_dvd q d l hDiv hd).mpr hDivisor
    let lift : Units (ZMod d) -> Units (ZMod q) :=
      fun v => Classical.choose (ZMod.unitsMap_surjective hd v)
    have hLift (v : Units (ZMod d)) : ZMod.unitsMap hd (lift v) = v :=
      Classical.choose_spec (ZMod.unitsMap_surjective hd v)
    refine Exists.intro (fun v => kernel (weight q l) (lift v)) ?_
    intro u
    exact hFiber u (lift (ZMod.unitsMap hd u)) (hLift (ZMod.unitsMap hd u)).symm

theorem spectralConductor_eq_kernelCarrierProduct
    (B : Nat) [NeZero B] (hSq : Squarefree B) (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B)))) :
    spectralConductor B l = kernelCarrierProduct B hSq l := by
  let R := kernelCarrierProduct B hSq l
  have hRPos : 0 < R := kernelCarrierProduct_pos B hSq l hDiv
  let : NeZero R := NeZero.mk (ne_of_gt hRPos)
  have hRDiv : Dvd.dvd R B := kernelCarrierProduct_dvd_level B hSq l hDiv
  apply Nat.dvd_antisymm
  . exact (kernel_reduction_iff_spectralConductor_dvd B R l hDiv hRDiv).mp
      (kernelCarrierProduct_minimal B hSq l hDiv).left
  . have hC := spectralConductor_dvd_level B l
    have hSqC : Squarefree (spectralConductor B l) :=
      fun x hx => hSq x (dvd_trans hx hC)
    exact (kernel_reduction_iff B (spectralConductor B l) hSq hSqC l hDiv hC).mp
      (spectralConductor_attained B l hDiv)

theorem spectralConductor_eq_active_product
    (B : Nat) [NeZero B] (hSq : Squarefree B) (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B)))) :
    spectralConductor B l =
      CarmichaelAllCarrierReadout.carrierProduct B
        (Monoid.exponent (Units (ZMod B)) / (l : Nat)) := by
  rw [spectralConductor_eq_kernelCarrierProduct B hSq l hDiv,
    kernelCarrierProduct_eq B hSq l hDiv]

theorem additive_zero_iff_spectralConductor_dvd
    (B : Nat) [NeZero B] (hSq : Squarefree B) (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B)))) (h : Nat) :
    ModularReturnFourier.residueFourier B
      (CarmichaelCarrierReadout.centeredPower B
        (Monoid.exponent (Units (ZMod B)) / (l : Nat))) h = 0 <->
          Dvd.dvd (spectralConductor B l) h := by
  rw [spectralConductor_eq_kernelCarrierProduct B hSq l hDiv]
  exact additive_zero_iff_kernelCarrier_dvd B hSq l hDiv h

end PrimeFactorOscillations.CarmichaelSpectralConductor
