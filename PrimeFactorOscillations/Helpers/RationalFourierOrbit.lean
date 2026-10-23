/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ModularReturnFourier

/-!
# Rational Fourier zero orbits under coprime frequency dilation

The actual rational coefficient polynomial is divisible by the same
cyclotomic polynomial at every coprime power of a primitive root.
This keeps a complete signed Fourier equation intact while changing one
CRT frequency coordinate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.RationalFourierOrbit

open scoped BigOperators
open ModularReturnFourier

theorem standard_character_root (B : Nat) [NeZero B] :
    IsPrimitiveRoot (ZMod.stdAddChar (1 : ZMod B)) B := by
  have hpw : ZMod.stdAddChar (1 : ZMod B) ^ B = 1 := by
    simpa [nsmul_eq_mul] using
      (AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := B)) B (1 : ZMod B)).symm
  refine IsPrimitiveRoot.mk_of_lt _ (NeZero.pos B) hpw ?_
  intro n hn hlt hpow
  have hval : ZMod.stdAddChar (n : ZMod B) = 1 := by
    have he := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := B)) n (1 : ZMod B)
    simpa [nsmul_eq_mul] using he.trans hpow
  have hz : (n : ZMod B) = 0 := by
    apply ZMod.injective_stdAddChar
    simpa only [AddChar.map_zero_eq_one] using hval
  have hd : Dvd.dvd B n := (CharP.cast_eq_zero_iff (ZMod B) B n).mp hz
  exact (Nat.not_le.mpr hlt) (Nat.le_of_dvd hn hd)

theorem polynomial_zero_of_coprime_power (n : Nat) (hn : 0 < n)
    (zeta : Complex) (hzeta : IsPrimitiveRoot zeta n)
    (P : Polynomial Rat) (t : Nat) (ht : Nat.Coprime t n)
    (hz : Polynomial.aeval zeta P = 0) :
    Polynomial.aeval (zeta ^ t) P = 0 := by
  have hzt := hzeta.pow_of_coprime t ht
  rw [<- minpoly.dvd_iff, <- Polynomial.cyclotomic_eq_minpoly_rat hzt hn]
  rw [<- minpoly.dvd_iff, <- Polynomial.cyclotomic_eq_minpoly_rat hzeta hn] at hz
  exact hz

theorem standard_character_nat_mul (B : Nat) [NeZero B] (h : Nat) (x : ZMod B) :
    ZMod.stdAddChar ((h : ZMod B) * x) =
      ZMod.stdAddChar (1 : ZMod B) ^ (h * x.val) := by
  have he := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := B))
    (h * x.val) (1 : ZMod B)
  simpa [nsmul_eq_mul] using he

theorem zero_of_coprime_frequency_dilation (B : Nat) [NeZero B]
    (f : ZMod B -> Rat) (h t : Nat) (ht : Nat.Coprime t B)
    (hz : residueFourier B f h = 0) :
    residueFourier B f (t * h) = 0 := by
  classical
  let zeta := ZMod.stdAddChar (1 : ZMod B)
  let P : Polynomial Rat := Finset.univ.sum (fun x : ZMod B =>
    Polynomial.C (f x) * Polynomial.X ^ (h * x.val))
  have heval (z : Complex) : Polynomial.aeval z P =
      Finset.univ.sum (fun x : ZMod B => (f x : Complex) * z ^ (h * x.val)) := by
    simp [P]
  have hzP : Polynomial.aeval zeta P = 0 := by
    rw [heval]
    simpa only [residueFourier, standard_character_nat_mul] using hz
  have htP := polynomial_zero_of_coprime_power B (NeZero.pos B)
    zeta (standard_character_root B) P t ht hzP
  have htarget : residueFourier B f (t * h) = Polynomial.aeval (zeta ^ t) P := by
    rw [heval]
    unfold residueFourier
    apply Finset.sum_congr rfl
    intro x _
    rw [standard_character_nat_mul]
    simp only [<- pow_mul, Nat.mul_assoc, zeta]
  rw [htarget]
  exact htP

end PrimeFactorOscillations.RationalFourierOrbit
