/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeFourier

/-! # Exact Fourier inversion for the actual coprime graph operator

The complete signed Ramanujan symbol is transferred to the physical
adjacency kernel, with the original normalization and no dimension loss.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {n : Nat} [NeZero n]

def hamiltonianCoprimeFourierSymbol (k : ZMod n) : Complex :=
  LPF.lpfRamanujanSum (q := n) k.val

theorem hamiltonian_cyclic_fourier_inversion (f : ZMod n -> Complex) (t : ZMod n) :
    LPF.lpfCyclicInverse (LPF.lpfCyclicTransform f) t = f t := by
  have h := LPF.lpfCyclicInverse_finite_product
    (Finset.univ : Finset (ZMod n)) ({0} : Finset (ZMod n))
    (fun z : ZMod n => z) (fun _ : ZMod n => (0 : ZMod n))
    f (fun _ : ZMod n => (1 : Complex)) t
  change LPF.lpfCyclicInverse (fun x : ZMod n =>
    Finset.univ.sum (fun z : ZMod n => f z * ZMod.stdAddChar (x * z))) t = f t
  simpa [LPF.lpfFiniteTransform] using h

theorem hamiltonian_coprime_symbol_transform (k : ZMod n) :
    LPF.lpfCyclicTransform (fun z : ZMod n => if IsUnit z then (1 : Complex) else 0) k =
      hamiltonianCoprimeFourierSymbol k := by
  unfold LPF.lpfCyclicTransform hamiltonianCoprimeFourierSymbol LPF.lpfRamanujanSum
  calc
    _ = Finset.univ.sum (fun z : ZMod n =>
        if IsUnit z then ZMod.stdAddChar (k * z) else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases h : IsUnit z <;> simp [h]
    _ = Finset.univ.sum (fun a : Units (ZMod n) =>
        ZMod.stdAddChar (k * (a : ZMod n))) := hamiltonian_coprime_unit_sum _
    _ = _ := by
      simp only [ZMod.natCast_zmod_val]
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      ring

theorem hamiltonian_coprime_symbol_inverse (t : ZMod n) :
    LPF.lpfCyclicInverse (hamiltonianCoprimeFourierSymbol (n := n)) t =
      if IsUnit t then (1 : Complex) else 0 := by
  have hF : hamiltonianCoprimeFourierSymbol (n := n) =
      LPF.lpfCyclicTransform (fun z : ZMod n => if IsUnit z then (1 : Complex) else 0) := by
    funext k
    exact (hamiltonian_coprime_symbol_transform k).symm
  rw [hF, hamiltonian_cyclic_fourier_inversion]

theorem hamiltonian_coprime_adjacency_hankel :
    LPF.hamiltonianFourierHankel (hamiltonianCoprimeFourierSymbol (n := n))
      (fun x : ZMod n => x) (fun y : ZMod n => -y) =
        (hamiltonianCoprimeAdjacency (n := n)).map Complex.ofRealHom := by
  ext x y
  change LPF.lpfCyclicInverse (hamiltonianCoprimeFourierSymbol (n := n)) (x + -y) =
    Complex.ofReal (if IsUnit (x - y) then (1 : Real) else 0)
  rw [show x + -y = x - y by ring, hamiltonian_coprime_symbol_inverse]
  split_ifs <;> rfl

theorem hamiltonian_cyclic_inverse_div (F : ZMod n -> Complex) (c : Complex) (t : ZMod n) :
    LPF.lpfCyclicInverse (fun k => F k / c) t = LPF.lpfCyclicInverse F t / c := by
  unfold LPF.lpfCyclicInverse
  have hSum : Finset.univ.sum (fun k : ZMod n =>
      F k / c * ZMod.stdAddChar (t * -k)) =
        (Finset.univ.sum (fun k : ZMod n => F k * ZMod.stdAddChar (t * -k))) / c := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hSum]
  ring

theorem hamiltonian_coprime_kernel_hankel :
    LPF.hamiltonianFourierHankel
      (fun k : ZMod n => hamiltonianCoprimeFourierSymbol k / (n.totient : Complex))
      (fun x : ZMod n => x) (fun y : ZMod n => -y) =
        (hamiltonianCoprimeKernel (n := n)).map Complex.ofRealHom := by
  ext x y
  change LPF.lpfCyclicInverse
      (fun k : ZMod n => hamiltonianCoprimeFourierSymbol k / (n.totient : Complex))
      (x + -y) = Complex.ofReal
        ((if IsUnit (x - y) then (1 : Real) else 0) / (n.totient : Real))
  rw [hamiltonian_cyclic_inverse_div, show x + -y = x - y by ring,
    hamiltonian_coprime_symbol_inverse]
  split_ifs <;> simp

end PrimeFactorOscillations
