/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.ZMod.UnitsCyclic
import PrimeFactorOscillations.Helpers.LPFRamanujanGeneral
import PrimeFactorOscillations.Helpers.RationalFourierOrbit

/-!
# Native power returns at prime-power conductors

The return sum uses the actual power kernel in the full modular unit group.
At a primitive prime-power frequency, a zero would force the return mass to
be divisible by the conductor prime. This is incompatible with a power
exponent prime to that prime. The complete centered consumer follows below.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimePowerReturnSpectrum

open scoped BigOperators
open RationalFourierOrbit

def powerKernel (n k : Nat) : Subgroup (Units (ZMod n)) :=
  (powMonoidHom k).ker

instance powerKernelFintype (n : Nat) [NeZero n] (k : Nat) :
    Fintype (powerKernel n k) := Fintype.ofFinite _

def returnTransform (n : Nat) [NeZero n] (k h : Nat) : Complex :=
  Finset.univ.sum (fun u : powerKernel n k =>
    ZMod.stdAddChar ((h : ZMod n) * (u.val : ZMod n)))

def centeredTransform (n : Nat) [NeZero n] (k h : Nat) : Complex :=
  (Fintype.card (Units (ZMod n)) : Complex) * returnTransform n k h -
    (Fintype.card (powerKernel n k) : Complex) * LPF.lpfRamanujanSum (q := n) h

/-- The integral prime-power weight obstruction; signs in the polynomial
are preserved, although this application uses a positive root count. -/
theorem prime_dvd_card_of_root_sum_zero {I : Type*} [Fintype I]
    (p a : Nat) (hp : Nat.Prime p) (zeta : Complex)
    (hzeta : IsPrimitiveRoot zeta (p ^ (a + 1))) (e : I -> Nat)
    (hz : Finset.univ.sum (fun i : I => zeta ^ e i) = 0) :
    Dvd.dvd p (Fintype.card I) := by
  classical
  letI : Fact (Nat.Prime p) := Fact.mk hp
  have hpos : 0 < p ^ (a + 1) := pow_pos hp.pos _
  let P : Polynomial Int := Finset.univ.sum (fun i : I => Polynomial.X ^ e i)
  have hP : Polynomial.aeval zeta P = 0 := by
    simpa [P] using hz
  have hd : Dvd.dvd (Polynomial.cyclotomic (p ^ (a + 1)) Int) P := by
    rw [Polynomial.cyclotomic_eq_minpoly hzeta hpos]
    exact minpoly.isIntegrallyClosed_dvd (hzeta.isIntegral hpos) hP
  have heval := Polynomial.eval_dvd (x := (1 : Int)) hd
  rw [Polynomial.eval_one_cyclotomic_prime_pow] at heval
  have hmass : Polynomial.eval (1 : Int) P = (Fintype.card I : Int) := by
    rw [Polynomial.eval_finset_sum]
    simp [P]
  rw [hmass] at heval
  exact Int.natCast_dvd_natCast.mp heval

theorem power_kernel_card (n : Nat) [NeZero n]
    [IsCyclic (Units (ZMod n))] (k : Nat) :
    Fintype.card (powerKernel n k) = Nat.gcd n.totient k := by
  calc
    Fintype.card (powerKernel n k) = Nat.card (powerKernel n k) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.gcd (Nat.card (Units (ZMod n))) k :=
      IsCyclic.card_powMonoidHom_ker (G := Units (ZMod n)) k
    _ = Nat.gcd n.totient k := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- All primitive frequencies of an odd prime-power return law survive
when the power exponent is prime to the conductor prime. -/
theorem primitive_return_nonzero (p a k h : Nat) [NeZero p] (hp : Nat.Prime p)
    (hp2 : Not (p = 2)) (hpk : Not (Dvd.dvd p k))
    (hh : Nat.Coprime h (p ^ (a + 1))) :
    Not (returnTransform (p ^ (a + 1)) k h = 0) := by
  classical
  letI : NeZero (p ^ (a + 1)) := NeZero.mk (pow_ne_zero _ hp.ne_zero)
  letI : IsCyclic (Units (ZMod (p ^ (a + 1)))) :=
    ZMod.isCyclic_units_of_prime_pow p hp hp2 (a + 1)
  intro hz
  have hroot := (standard_character_root (p ^ (a + 1))).pow_of_coprime h hh
  have hsum : Finset.univ.sum (fun u : powerKernel (p ^ (a + 1)) k =>
      (ZMod.stdAddChar (1 : ZMod (p ^ (a + 1))) ^ h) ^
        (u.val : ZMod (p ^ (a + 1))).val) = 0 := by
    simpa only [returnTransform, standard_character_nat_mul, pow_mul] using hz
  have hd := prime_dvd_card_of_root_sum_zero p a hp _ hroot
    (fun u : powerKernel (p ^ (a + 1)) k =>
      (u.val : ZMod (p ^ (a + 1))).val) hsum
  rw [power_kernel_card] at hd
  exact hpk (dvd_trans hd (Nat.gcd_dvd_right _ _))

theorem primitive_unit_mask (p a h : Nat) [NeZero p] (hp : Nat.Prime p)
    (hh : Nat.Coprime h (p ^ (a + 2))) :
    LPF.lpfRamanujanSum (q := p ^ (a + 2)) h = 0 := by
  have hsq : Not (Squarefree (p ^ (a + 2))) := by
    intro hs
    apply (Nat.squarefree_iff_prime_squarefree.mp hs) p hp
    simpa only [pow_two] using (pow_dvd_pow p (Nat.le_add_left 2 a))
  rw [LPF.lpfRamanujanSum_divisors, hh.symm.gcd_eq_one]
  simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

/-- The full centered return signal, including the unit-mask subtraction,
is nonzero on every primitive frequency of a proper odd prime power. -/
theorem primitive_centered_nonzero (p a k h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2)) (hpk : Not (Dvd.dvd p k))
    (hh : Nat.Coprime h (p ^ (a + 2))) :
    Not (centeredTransform (p ^ (a + 2)) k h = 0) := by
  rw [centeredTransform, primitive_unit_mask p a h hp hh, mul_zero, sub_zero]
  apply mul_ne_zero
  { have hcard : 0 < Fintype.card (Units (ZMod (p ^ (a + 2)))) := Fintype.card_pos
    exact_mod_cast hcard.ne' }
  { exact primitive_return_nonzero p (a + 1) k h hp hp2 hpk hh }

theorem centered_zero_frequency (n : Nat) [NeZero n] (k : Nat) :
    centeredTransform n k 0 = 0 := by
  simp [centeredTransform, returnTransform, LPF.lpfRamanujanSum, mul_comm]

end PrimeFactorOscillations.PrimePowerReturnSpectrum
