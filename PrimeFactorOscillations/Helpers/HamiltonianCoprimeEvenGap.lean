/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeGap
import PrimeFactorOscillations.Helpers.HamiltonianRationalLowModes

/-! # Exact constant/parity compensation for every even coprime modulus

The two exceptional physical frequencies are identified before the full
signed Ramanujan symbol is bounded. The Fourier transfer preserves the
actual normalization and every remaining mode.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {n : Nat} [NeZero n]

theorem hamiltonian_coprime_half_frequency_data (hEven : Dvd.dvd 2 n) :
    Not (((n / 2 : Nat) : ZMod n) = 0) /\
      hamiltonianCoprimeConductor ((n / 2 : Nat) : ZMod n) = 2 := by
  have hn : 0 < n := NeZero.pos n
  have hn2 : 2 <= n := Nat.le_of_dvd hn hEven
  have hPos : 0 < n / 2 := Nat.div_pos hn2 (by decide)
  have hLt : n / 2 < n := Nat.div_lt_self hn (by decide)
  have hVal : (((n / 2 : Nat) : ZMod n)).val = n / 2 := ZMod.val_natCast_of_lt hLt
  have hMul : n / 2 * 2 = n := Nat.div_mul_cancel hEven
  constructor
  case left =>
    intro h
    have hZ := congrArg (fun k : ZMod n => k.val) h
    rw [hVal, ZMod.val_zero] at hZ
    omega
  case right =>
    rw [hamiltonianCoprimeConductor, hVal,
      Nat.gcd_eq_right_iff_dvd.mpr (Nat.div_dvd_of_dvd hEven)]
    calc
      n / (n / 2) = ((n / 2) * 2) / (n / 2) := by rw [hMul]
      _ = 2 := Nat.mul_div_cancel_left 2 hPos

theorem hamiltonian_coprime_conductor_two_iff_half (hEven : Dvd.dvd 2 n) (k : ZMod n) :
    hamiltonianCoprimeConductor k = 2 <-> k = ((n / 2 : Nat) : ZMod n) := by
  constructor
  case mp =>
    intro hTwo
    have hF := hamiltonian_coprime_frequency_factorization k
    let g := Nat.gcd n k.val
    let b := k.val / Nat.gcd n k.val
    have hg : 0 < g := hF.1
    have hN : g * 2 = n := by simpa only [hTwo] using hF.2.2.1
    have hK : g * b = k.val := hF.2.2.2.1
    have hCoprime : Nat.Coprime b 2 := by simpa only [hTwo] using hF.2.2.2.2
    have hB0 : Not (b = 0) := by
      intro h
      rw [h] at hCoprime
      norm_num at hCoprime
    have hB2 : b < 2 := (Nat.mul_lt_mul_left hg).mp (by
      rw [hK, hN]
      exact ZMod.val_lt k)
    have hB1 : b = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hB2)
      (Nat.one_le_iff_ne_zero.mpr hB0)
    have hG : g = n / 2 := by omega
    have hVal : k.val = n / 2 := by simpa only [hB1, mul_one, hG] using hK.symm
    have hLt : n / 2 < n := Nat.div_lt_self (NeZero.pos n) (by decide)
    apply ZMod.val_injective
    rw [hVal, ZMod.val_natCast_of_lt hLt]
  case mpr =>
    intro h
    rw [h]
    exact (hamiltonian_coprime_half_frequency_data hEven).2

def hamiltonianCoprimeEvenLowSymbol (k : ZMod n) : Complex :=
  (if k = 0 then 1 else 0) - (if k = ((n / 2 : Nat) : ZMod n) then 1 else 0)

def hamiltonianCoprimeEvenHighSymbol (k : ZMod n) : Complex :=
  hamiltonianCoprimeFourierSymbol k / (n.totient : Complex) -
    hamiltonianCoprimeEvenLowSymbol k

def hamiltonianCoprimeConstantParityKernel : Matrix (ZMod n) (ZMod n) Real :=
  fun x y => (1 - (-1 : Real) ^ (x - y).val) / (n : Real)

theorem hamiltonian_coprime_even_high_symbol_bound (hEven : Dvd.dvd 2 n) (k : ZMod n) :
    norm (hamiltonianCoprimeEvenHighSymbol k) <= (1 / 2 : Real) := by
  have hHalf := hamiltonian_coprime_half_frequency_data hEven
  by_cases hZero : k = 0
  case pos =>
    subst k
    have hFreq := hamiltonian_coprime_zero_frequency (n := n)
    have hNot : Not ((0 : ZMod n) = ((n / 2 : Nat) : ZMod n)) := Ne.symm hHalf.1
    simp only [hamiltonianCoprimeEvenHighSymbol, hamiltonianCoprimeEvenLowSymbol,
      hamiltonianCoprimeFourierSymbol, ZMod.val_zero, hFreq, ite_true, hNot, ite_false,
      sub_zero, sub_self, norm_zero]
    norm_num
  case neg =>
    by_cases hParity : k = ((n / 2 : Nat) : ZMod n)
    case pos =>
      have hTwo := (hamiltonian_coprime_conductor_two_iff_half hEven k).mpr hParity
      have hFreq := hamiltonian_coprime_parity_frequency k hTwo
      unfold hamiltonianCoprimeEvenHighSymbol hamiltonianCoprimeEvenLowSymbol
      rw [if_neg hZero, if_pos hParity]
      change norm (LPF.lpfRamanujanSum (q := n) k.val / (n.totient : Complex) -
        ((0 : Complex) - 1)) <= (1 / 2 : Real)
      rw [hFreq]
      norm_num
    case neg =>
      have hNotOne : Not (hamiltonianCoprimeConductor k = 1) := by
        intro h
        exact hZero ((hamiltonian_coprime_conductor_one_iff k).mp h)
      have hNotTwo : Not (hamiltonianCoprimeConductor k = 2) := by
        intro h
        exact hParity ((hamiltonian_coprime_conductor_two_iff_half hEven k).mp h)
      have hPos := (hamiltonian_coprime_frequency_factorization k).2.1
      have hHigh : 3 <= hamiltonianCoprimeConductor k := by omega
      simpa only [hamiltonianCoprimeEvenHighSymbol, hamiltonianCoprimeEvenLowSymbol,
        hZero, hParity, ite_false, sub_zero, hamiltonianCoprimeFourierSymbol] using
          hamiltonian_coprime_full_frequency_gap k hHigh

theorem hamiltonian_cyclic_inverse_half (hEven : Dvd.dvd 2 n) (t : ZMod n) :
    LPF.lpfCyclicInverse
      (fun k : ZMod n => if k = ((n / 2 : Nat) : ZMod n) then (1 : Complex) else 0) t =
        (-1 : Complex) ^ t.val / (n : Complex) := by
  have hChar := LPF.hamiltonian_half_grid_power (R := n) hEven t.val
  rw [ZMod.natCast_zmod_val] at hChar
  have hChar' : ZMod.stdAddChar (t * -((n / 2 : Nat) : ZMod n)) =
      (-1 : Complex) ^ t.val := by simpa only [mul_comm] using hChar
  simp only [LPF.lpfCyclicInverse, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, hChar', zpow_neg_one]
  ring

theorem hamiltonian_coprime_even_low_kernel (hEven : Dvd.dvd 2 n) :
    LPF.hamiltonianFourierHankel (hamiltonianCoprimeEvenLowSymbol (n := n))
      (fun x : ZMod n => x) (fun y : ZMod n => -y) =
      LPF.hamiltonianComplexMatrix (hamiltonianCoprimeConstantParityKernel (n := n)) := by
  unfold hamiltonianCoprimeEvenLowSymbol
  rw [LPF.hamiltonian_fourier_hankel_sub]
  ext x y
  change LPF.lpfCyclicInverse (fun k : ZMod n => if k = 0 then (1 : Complex) else 0)
      (x + -y) -
    LPF.lpfCyclicInverse
      (fun k : ZMod n => if k = ((n / 2 : Nat) : ZMod n) then (1 : Complex) else 0)
      (x + -y) =
    Complex.ofReal ((1 - (-1 : Real) ^ (x - y).val) / (n : Real))
  rw [hamiltonian_cyclic_inverse_principal, hamiltonian_cyclic_inverse_half hEven]
  push_cast
  rw [show x + -y = x - y by ring]
  ring

theorem hamiltonian_coprime_even_high_kernel (hEven : Dvd.dvd 2 n) :
    LPF.hamiltonianFourierHankel (hamiltonianCoprimeEvenHighSymbol (n := n))
      (fun x : ZMod n => x) (fun y : ZMod n => -y) =
      LPF.hamiltonianComplexMatrix
        (hamiltonianCoprimeKernel (n := n) - hamiltonianCoprimeConstantParityKernel) := by
  unfold hamiltonianCoprimeEvenHighSymbol
  rw [LPF.hamiltonian_fourier_hankel_sub, hamiltonian_coprime_kernel_hankel,
    hamiltonian_coprime_even_low_kernel hEven]
  ext x y
  simp only [LPF.hamiltonianComplexMatrix, Matrix.map_apply, Matrix.sub_apply,
    Complex.ofReal_sub]
  rfl

theorem hamiltonian_coprime_even_physical_gap (hEven : Dvd.dvd 2 n) :
    norm (hamiltonianCoprimeKernel (n := n) - hamiltonianCoprimeConstantParityKernel) <=
      (1 / 2 : Real) := by
  have h := LPF.hamiltonian_fourier_hankel_norm_bound
    (hamiltonianCoprimeEvenHighSymbol (n := n))
    (fun x : ZMod n => x) (fun y : ZMod n => -y)
    Function.injective_id neg_injective (1 / 2 : Real) (by norm_num)
    (hamiltonian_coprime_even_high_symbol_bound hEven)
  rw [hamiltonian_coprime_even_high_kernel hEven] at h
  exact (LPF.hamiltonian_real_complex_l2_norm_le
    (hamiltonianCoprimeKernel (n := n) - hamiltonianCoprimeConstantParityKernel)).trans h

end PrimeFactorOscillations
