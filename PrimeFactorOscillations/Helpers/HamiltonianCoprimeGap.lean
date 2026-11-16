/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeSpectrum
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeSymbol
import PrimeFactorOscillations.Helpers.HamiltonianPrimeRealMatrix
import PrimeFactorOscillations.Helpers.HamiltonianStochasticEnergy

/-! # The exact physical half-gap for every odd coprime modulus

The constant Fourier mode is subtracted exactly. All other signed
Ramanujan modes are retained, and cyclic inversion transfers their
half-bound to the actual real centered adjacency operator.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {n : Nat} [NeZero n]

theorem hamiltonian_cyclic_inverse_principal (t : ZMod n) :
    LPF.lpfCyclicInverse (fun k : ZMod n => if k = 0 then (1 : Complex) else 0) t =
      1 / (n : Complex) := by
  simp [LPF.lpfCyclicInverse, zpow_neg_one, one_div]

theorem hamiltonian_coprime_odd_centered_symbol_bound (hOdd : Odd n) (k : ZMod n) :
    norm (hamiltonianCoprimeFourierSymbol k / (n.totient : Complex) -
      (if k = 0 then (1 : Complex) else 0)) <= (1 / 2 : Real) := by
  by_cases hZero : k = 0
  case pos =>
    subst k
    have h := hamiltonian_coprime_zero_frequency (n := n)
    simp only [hamiltonianCoprimeFourierSymbol, ZMod.val_zero, h, ite_true, sub_self, norm_zero]
    norm_num
  case neg =>
    simp only [hZero, ite_false, sub_zero, hamiltonianCoprimeFourierSymbol]
    exact hamiltonian_coprime_odd_frequency_gap hOdd k hZero

theorem hamiltonian_coprime_centered_kernel_hankel :
    LPF.hamiltonianFourierHankel
      (fun k : ZMod n => hamiltonianCoprimeFourierSymbol k / (n.totient : Complex) -
        (if k = 0 then (1 : Complex) else 0))
      (fun x : ZMod n => x) (fun y : ZMod n => -y) =
      LPF.hamiltonianComplexMatrix
        (centeredKernel (hamiltonianCoprimeKernel (n := n)) (1 / (n : Real))) := by
  rw [LPF.hamiltonian_fourier_hankel_sub, hamiltonian_coprime_kernel_hankel]
  ext x y
  change Complex.ofReal (hamiltonianCoprimeKernel x y) -
      LPF.lpfCyclicInverse (fun k : ZMod n => if k = 0 then (1 : Complex) else 0) (x + -y) =
        Complex.ofReal (hamiltonianCoprimeKernel x y - 1 / (n : Real))
  rw [hamiltonian_cyclic_inverse_principal]
  push_cast
  rfl

theorem hamiltonian_coprime_odd_physical_gap (hOdd : Odd n) :
    norm (centeredKernel (hamiltonianCoprimeKernel (n := n)) (1 / (n : Real))) <=
      (1 / 2 : Real) := by
  have h := LPF.hamiltonian_fourier_hankel_norm_bound
    (fun k : ZMod n => hamiltonianCoprimeFourierSymbol k / (n.totient : Complex) -
      (if k = 0 then (1 : Complex) else 0))
    (fun x : ZMod n => x) (fun y : ZMod n => -y)
    Function.injective_id neg_injective (1 / 2 : Real) (by norm_num)
    (hamiltonian_coprime_odd_centered_symbol_bound hOdd)
  rw [hamiltonian_coprime_centered_kernel_hankel] at h
  exact (LPF.hamiltonian_real_complex_l2_norm_le
    (centeredKernel (hamiltonianCoprimeKernel (n := n)) (1 / (n : Real)))).trans h

end PrimeFactorOscillations
