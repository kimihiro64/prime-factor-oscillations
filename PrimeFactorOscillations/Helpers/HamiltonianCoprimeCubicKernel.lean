/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeSymbol

/-! # Exact cubic Fourier readout for the native coprime transition kernel

The cyclic normalization and every character phase survive both
convolutions. The final matrix is the actual normalized adjacency
cubed, before any conductor grouping or arithmetic lower estimate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {n : Nat} [NeZero n]

def hamiltonianCyclicKernel (F : ZMod n -> Complex) :
    Matrix (ZMod n) (ZMod n) Complex :=
  LPF.hamiltonianFourierHankel F (fun x => x) (fun y => -y)

theorem hamiltonian_cyclic_transform_inverse (F : ZMod n -> Complex) (x : ZMod n) :
    LPF.lpfCyclicTransform (fun t => LPF.lpfCyclicInverse F t) x = F x := by
  have hN : Not ((n : Complex) = 0) := by exact_mod_cast NeZero.ne n
  have hPhase (t k : ZMod n) :
      ZMod.stdAddChar (t * -k) * ZMod.stdAddChar (x * t) =
        ZMod.stdAddChar (t * x) *
          (starRingEnd Complex) (ZMod.stdAddChar (t * k)) := by
    rw [show t * -k = -(t * k) by ring, AddChar.map_neg_eq_conj,
      show x * t = t * x by ring]
    ring
  calc
    _ = Finset.univ.sum (fun k : ZMod n => (Inv.inv (n : Complex) * F k) *
        Finset.univ.sum (fun t : ZMod n =>
          ZMod.stdAddChar (t * x) *
            (starRingEnd Complex) (ZMod.stdAddChar (t * k)))) := by
      simp only [LPF.lpfCyclicTransform, LPF.lpfCyclicInverse, zpow_neg_one,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro t ht
      calc
        _ = (Inv.inv (n : Complex) * F k) *
            (ZMod.stdAddChar (t * -k) * ZMod.stdAddChar (x * t)) := by ring
        _ = _ := by rw [hPhase]
    _ = _ := by
      simp_rw [AddChar.sum_crossPhase (ZMod.stdAddChar (N := n))
        (ZMod.isPrimitive_stdAddChar n)]
      simp only [ZMod.card] at *
      simp [mul_ite]
      field_simp [hN]

theorem hamiltonian_cyclic_kernel_mul (F G : ZMod n -> Complex) :
    hamiltonianCyclicKernel F * hamiltonianCyclicKernel G =
      hamiltonianCyclicKernel (fun k => F k * G k) := by
  ext x y
  have hProduct := LPF.lpfCyclicInverse_product
    (fun u => LPF.lpfCyclicInverse F u) (fun u => LPF.lpfCyclicInverse G u) (x - y)
  simp_rw [hamiltonian_cyclic_transform_inverse] at hProduct
  change Finset.univ.sum (fun z : ZMod n =>
      LPF.lpfCyclicInverse F (x + -z) * LPF.lpfCyclicInverse G (z + -y)) =
    LPF.lpfCyclicInverse (fun k => F k * G k) (x + -y)
  rw [show x + -y = x - y by ring, hProduct]
  apply Fintype.sum_equiv (Equiv.subLeft x)
  intro z
  congr 1
  next =>
    congr 1
    change x + -z = x - z
    ring
  next =>
    congr 1
    change z + -y = x - y - (x - z)
    ring

theorem hamiltonian_cyclic_kernel_cube (F : ZMod n -> Complex) :
    (hamiltonianCyclicKernel F * hamiltonianCyclicKernel F) * hamiltonianCyclicKernel F =
      hamiltonianCyclicKernel (fun k => F k ^ 3) := by
  rw [hamiltonian_cyclic_kernel_mul, hamiltonian_cyclic_kernel_mul]
  congr 1
  funext k
  ring

def hamiltonianCoprimeThreeStepKernel : Matrix (ZMod n) (ZMod n) Real :=
  (hamiltonianCoprimeKernel (n := n) * hamiltonianCoprimeKernel (n := n)) *
    hamiltonianCoprimeKernel (n := n)

theorem hamiltonian_coprime_cubic_inverse (a b : ZMod n) :
    LPF.lpfCyclicInverse
        (fun k : ZMod n => (hamiltonianCoprimeFourierSymbol k / (n.totient : Complex)) ^ 3)
        (a - b) =
      Complex.ofReal (hamiltonianCoprimeThreeStepKernel a b) := by
  let P : Matrix (ZMod n) (ZMod n) Real := hamiltonianCoprimeKernel
  let F := fun k : ZMod n => hamiltonianCoprimeFourierSymbol k / (n.totient : Complex)
  have hP : hamiltonianCyclicKernel F = P.map Complex.ofRealHom :=
    hamiltonian_coprime_kernel_hankel
  have hMap (A B : Matrix (ZMod n) (ZMod n) Real) :
      (A * B).map Complex.ofRealHom =
        A.map Complex.ofRealHom * B.map Complex.ofRealHom := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
  have hCube := hamiltonian_cyclic_kernel_cube F
  rw [hP, <- hMap P P, <- hMap (P * P) P] at hCube
  have hEntry := congrArg (fun M : Matrix (ZMod n) (ZMod n) Complex => M a b) hCube
  change Complex.ofReal (((P * P) * P) a b) =
    LPF.lpfCyclicInverse (fun k => F k ^ 3) (a + -b) at hEntry
  simpa only [sub_eq_add_neg, F, P, hamiltonianCoprimeThreeStepKernel] using hEntry.symm

end PrimeFactorOscillations
