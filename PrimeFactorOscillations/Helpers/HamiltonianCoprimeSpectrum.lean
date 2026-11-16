/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeConductor

/-! # Every physical coprime frequency and its exact conductor

The primitive reduction is lifted to every residue frequency. The
constant and possible parity conductors are isolated before estimating
any of the remaining modes.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

variable {n : Nat} [NeZero n]

def hamiltonianCoprimeConductor (k : ZMod n) : Nat :=
  n / Nat.gcd n k.val

theorem hamiltonian_coprime_frequency_factorization (k : ZMod n) :
    0 < Nat.gcd n k.val /\
      0 < hamiltonianCoprimeConductor k /\
      Nat.gcd n k.val * hamiltonianCoprimeConductor k = n /\
      Nat.gcd n k.val * (k.val / Nat.gcd n k.val) = k.val /\
      Nat.Coprime (k.val / Nat.gcd n k.val) (hamiltonianCoprimeConductor k) := by
  have hGcd : 0 < Nat.gcd n k.val := by
    apply Nat.pos_of_ne_zero
    intro h
    exact (NeZero.ne n) (Nat.gcd_eq_zero_iff.mp h).1
  have hSize : Nat.gcd n k.val <= n :=
    Nat.le_of_dvd (NeZero.pos n) (Nat.gcd_dvd_left n k.val)
  refine And.intro hGcd (And.intro (Nat.div_pos hSize hGcd)
    (And.intro ?_ (And.intro ?_ ?_)))
  case refine_1 =>
    unfold hamiltonianCoprimeConductor
    rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left n k.val)]
  case refine_2 =>
    rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right n k.val)]
  case refine_3 =>
    exact (Nat.coprime_div_gcd_div_gcd hGcd).symm

theorem hamiltonian_coprime_conductor_order (k : ZMod n) :
    addOrderOf k = hamiltonianCoprimeConductor k := by
  have h := ZMod.addOrderOf_coe k.val (NeZero.ne n)
  simpa only [ZMod.natCast_zmod_val, hamiltonianCoprimeConductor] using h

theorem hamiltonian_coprime_full_frequency_ratio (k : ZMod n) :
    LPF.lpfRamanujanSum (q := n) k.val / (n.totient : Complex) =
      (ArithmeticFunction.moebius (hamiltonianCoprimeConductor k) : Complex) /
        ((hamiltonianCoprimeConductor k).totient : Complex) := by
  have hF := hamiltonian_coprime_frequency_factorization k
  let g := Nat.gcd n k.val
  let t := hamiltonianCoprimeConductor k
  let b := k.val / Nat.gcd n k.val
  letI : NeZero g := { out := ne_of_gt hF.1 }
  letI : NeZero t := { out := ne_of_gt hF.2.1 }
  have hN : g * t = n := hF.2.2.1
  have hK : g * b = k.val := hF.2.2.2.1
  have h := hamiltonian_coprime_conductor_ratio g t b hF.2.2.2.2
  simpa only [hN, hK] using h

theorem hamiltonian_coprime_full_frequency_gap (k : ZMod n)
    (hHigh : 3 <= hamiltonianCoprimeConductor k) :
    norm (LPF.lpfRamanujanSum (q := n) k.val / (n.totient : Complex)) <= (1 / 2 : Real) := by
  have hF := hamiltonian_coprime_frequency_factorization k
  let g := Nat.gcd n k.val
  let t := hamiltonianCoprimeConductor k
  let b := k.val / Nat.gcd n k.val
  letI : NeZero g := { out := ne_of_gt hF.1 }
  letI : NeZero t := { out := ne_of_gt hF.2.1 }
  have hN : g * t = n := hF.2.2.1
  have hK : g * b = k.val := hF.2.2.2.1
  have h := hamiltonian_coprime_nonprincipal_conductor_gap g t b hF.2.2.2.2 hHigh
  simpa only [hN, hK] using h

theorem hamiltonian_coprime_conductor_one_iff (k : ZMod n) :
    hamiltonianCoprimeConductor k = 1 <-> k = 0 := by
  constructor
  case mp =>
    intro hOne
    have hF := hamiltonian_coprime_frequency_factorization k
    have hGcd : Nat.gcd n k.val = n := by simpa only [hOne, mul_one] using hF.2.2.1
    have hDiv : Dvd.dvd n k.val :=
      Eq.mp (congrArg (fun d : Nat => Dvd.dvd d k.val) hGcd)
        (Nat.gcd_dvd_right n k.val)
    have hCast : (k.val : ZMod n) = 0 := (CharP.cast_eq_zero_iff (ZMod n) n k.val).mpr hDiv
    simpa only [ZMod.natCast_zmod_val] using hCast
  case mpr =>
    intro hZero
    subst k
    simp only [hamiltonianCoprimeConductor, ZMod.val_zero, Nat.gcd_zero_right]
    exact Nat.div_self (NeZero.pos n)

theorem hamiltonian_coprime_conductor_two_even (k : ZMod n)
    (hTwo : hamiltonianCoprimeConductor k = 2) : Even n := by
  have hF := (hamiltonian_coprime_frequency_factorization k).2.2.1
  rw [hTwo] at hF
  exact Exists.intro (Nat.gcd n k.val) (by omega)

theorem hamiltonian_coprime_zero_frequency :
    LPF.lpfRamanujanSum (q := n) 0 / (n.totient : Complex) = 1 := by
  have h := hamiltonian_coprime_full_frequency_ratio (0 : ZMod n)
  have hOne := (hamiltonian_coprime_conductor_one_iff (0 : ZMod n)).mpr rfl
  simpa only [ZMod.val_zero, hOne, ArithmeticFunction.moebius_apply_one, Nat.totient_one,
    Int.cast_one, Nat.cast_one, div_one] using h

theorem hamiltonian_coprime_parity_frequency (k : ZMod n)
    (hTwo : hamiltonianCoprimeConductor k = 2) :
    LPF.lpfRamanujanSum (q := n) k.val / (n.totient : Complex) = -1 := by
  rw [hamiltonian_coprime_full_frequency_ratio, hTwo]
  norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two]

theorem hamiltonian_coprime_odd_frequency_gap (hOdd : Odd n) (k : ZMod n)
    (hNonzero : Not (k = 0)) :
    norm (LPF.lpfRamanujanSum (q := n) k.val / (n.totient : Complex)) <= (1 / 2 : Real) := by
  have hPos := (hamiltonian_coprime_frequency_factorization k).2.1
  have hNotOne : Not (hamiltonianCoprimeConductor k = 1) := by
    intro h
    exact hNonzero ((hamiltonian_coprime_conductor_one_iff k).mp h)
  have hNotTwo : Not (hamiltonianCoprimeConductor k = 2) := by
    intro h
    have hEven := hamiltonian_coprime_conductor_two_even k h
    exact (Nat.not_even_iff_odd.mpr hOdd) hEven
  exact hamiltonian_coprime_full_frequency_gap k (by omega)

theorem hamiltonian_coprime_conductor_multiplicity (t : Nat) (hDiv : Dvd.dvd t n) :
    (Finset.univ.filter (fun k : ZMod n => hamiltonianCoprimeConductor k = t)).card =
      t.totient := by
  have h : (Finset.univ.filter (fun k : ZMod n => addOrderOf k = t)).card = t.totient :=
    IsAddCyclic.card_addOrderOf_eq_totient
      (by simpa only [ZMod.card] using hDiv)
  simpa only [hamiltonian_coprime_conductor_order] using h

theorem hamiltonian_coprime_low_conductor_iff (k : ZMod n) :
    hamiltonianCoprimeConductor k <= 2 <-> SMul.smul (2 : Nat) k = 0 := by
  constructor
  case mp =>
    intro hLow
    have hPos := (hamiltonian_coprime_frequency_factorization k).2.1
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    rw [hamiltonian_coprime_conductor_order]
    have hCases : hamiltonianCoprimeConductor k = 1 \/
        hamiltonianCoprimeConductor k = 2 := by omega
    rcases hCases with hOne | hTwo
    case inl =>
      simpa only [hOne] using one_dvd 2
    case inr =>
      simpa only [hTwo] using dvd_refl 2
  case mpr =>
    intro hZero
    have h := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hZero
    rw [hamiltonian_coprime_conductor_order] at h
    exact Nat.le_of_dvd (by decide : 0 < 2) h

theorem hamiltonian_coprime_full_high_frequency_gap (k : ZMod n)
    (hHigh : Not (SMul.smul (2 : Nat) k = 0)) :
    norm (LPF.lpfRamanujanSum (q := n) k.val / (n.totient : Complex)) <= (1 / 2 : Real) := by
  apply hamiltonian_coprime_full_frequency_gap k
  have hNot : Not (hamiltonianCoprimeConductor k <= 2) := by
    intro h
    exact hHigh ((hamiltonian_coprime_low_conductor_iff k).mp h)
  omega

end PrimeFactorOscillations
