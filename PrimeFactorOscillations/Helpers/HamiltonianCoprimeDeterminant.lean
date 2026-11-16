/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeGap
import PrimeFactorOscillations.Helpers.HamiltonianFourierDeterminant

/-! # The exact signed coprime characteristic determinant

The principal mode is compensated before taking determinants. The full
frequency product is regrouped on the actual divisor support using the
proved totient multiplicities. No modulus or squarefree restriction is used.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

variable {n : Nat} [NeZero n]

def hamiltonianCoprimeCenteredEigenvalue (k : ZMod n) : Real :=
  if hamiltonianCoprimeConductor k = 1 then 0 else
    (ArithmeticFunction.moebius (hamiltonianCoprimeConductor k) : Real) /
      ((hamiltonianCoprimeConductor k).totient : Real)

def hamiltonianCoprimeDeterminantFactor (z : Real) (t : Nat) : Real :=
  if t = 1 then 1 else
    1 - z * ((ArithmeticFunction.moebius t : Real) / (t.totient : Real))

theorem hamiltonian_coprime_centered_eigenvalue_cast (k : ZMod n) :
    (hamiltonianCoprimeCenteredEigenvalue k : Complex) =
      hamiltonianCoprimeFourierSymbol k / (n.totient : Complex) -
        (if k = 0 then (1 : Complex) else 0) := by
  by_cases h : k = 0
  case pos =>
    subst k
    have hOne := (hamiltonian_coprime_conductor_one_iff (0 : ZMod n)).mpr rfl
    simp only [hamiltonianCoprimeCenteredEigenvalue, hOne, ite_true, Complex.ofReal_zero,
      hamiltonianCoprimeFourierSymbol, ZMod.val_zero, hamiltonian_coprime_zero_frequency,
      sub_self]
  case neg =>
    have hNotOne : Not (hamiltonianCoprimeConductor k = 1) := by
      intro hOne
      exact h ((hamiltonian_coprime_conductor_one_iff k).mp hOne)
    rw [hamiltonianCoprimeCenteredEigenvalue, if_neg hNotOne, if_neg h,
      sub_zero, hamiltonianCoprimeFourierSymbol, hamiltonian_coprime_full_frequency_ratio]
    push_cast
    rfl

theorem hamiltonian_coprime_shifted_hankel (z : Real) :
    LPF.hamiltonianFourierHankel
      (fun k : ZMod n => 1 - (z : Complex) * (hamiltonianCoprimeCenteredEigenvalue k : Complex))
      (fun x : ZMod n => x) (fun y : ZMod n => -y) =
        LPF.hamiltonianComplexMatrix
          ((1 : Matrix (ZMod n) (ZMod n) Real) -
            HSMul.hSMul z (centeredKernel (hamiltonianCoprimeKernel (n := n)) (1 / (n : Real)))) := by
  rw [LPF.hamiltonian_fourier_hankel_sub, LPF.hamiltonian_fourier_difference_identity,
    LPF.hamiltonian_fourier_hankel_scalar]
  have hSymbol :
      (fun k : ZMod n => (hamiltonianCoprimeCenteredEigenvalue k : Complex)) =
        (fun k : ZMod n => hamiltonianCoprimeFourierSymbol k / (n.totient : Complex) -
          (if k = 0 then (1 : Complex) else 0)) :=
    funext hamiltonian_coprime_centered_eigenvalue_cast
  rw [hSymbol, hamiltonian_coprime_centered_kernel_hankel]
  ext x y
  simp only [LPF.hamiltonianComplexMatrix, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_mul]
  congr 1
  by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy]

theorem hamiltonian_coprime_determinant_frequency_product (z : Real) :
    Matrix.det ((1 : Matrix (ZMod n) (ZMod n) Real) -
        HSMul.hSMul z (centeredKernel (hamiltonianCoprimeKernel (n := n)) (1 / (n : Real)))) =
      Finset.univ.prod (fun k : ZMod n => 1 - z * hamiltonianCoprimeCenteredEigenvalue k) := by
  apply Complex.ofReal_injective
  have hCast :
      ((Matrix.det ((1 : Matrix (ZMod n) (ZMod n) Real) -
        HSMul.hSMul z (centeredKernel (hamiltonianCoprimeKernel (n := n))
          (1 / (n : Real)))) : Real) : Complex) =
      Matrix.det (LPF.hamiltonianComplexMatrix ((1 : Matrix (ZMod n) (ZMod n) Real) -
        HSMul.hSMul z (centeredKernel (hamiltonianCoprimeKernel (n := n))
          (1 / (n : Real))))) :=
    Complex.ofRealHom.map_det _
  rw [hCast, <- hamiltonian_coprime_shifted_hankel,
    LPF.hamiltonian_fourier_difference_determinant]
  push_cast
  rfl

theorem hamiltonian_coprime_conductor_mem_divisors (k : ZMod n) :
    Membership.mem n.divisors (hamiltonianCoprimeConductor k) := by
  have hFactor := (hamiltonian_coprime_frequency_factorization k).2.2.1
  have hDiv : Dvd.dvd (hamiltonianCoprimeConductor k) n :=
    Exists.intro (Nat.gcd n k.val) (by simpa only [Nat.mul_comm] using hFactor.symm)
  exact Nat.mem_divisors.mpr (And.intro hDiv (NeZero.ne n))

theorem hamiltonian_coprime_conductor_product (f : Nat -> Real) :
    Finset.univ.prod (fun k : ZMod n => f (hamiltonianCoprimeConductor k)) =
      n.divisors.prod (fun t => f t ^ t.totient) := by
  have hMaps : forall k, Membership.mem (Finset.univ : Finset (ZMod n)) k ->
      Membership.mem n.divisors (hamiltonianCoprimeConductor k) := by
    intro k hk
    exact hamiltonian_coprime_conductor_mem_divisors k
  calc
    _ = n.divisors.prod (fun t =>
        (Finset.univ.filter (fun k : ZMod n => hamiltonianCoprimeConductor k = t)).prod
          (fun k => f (hamiltonianCoprimeConductor k))) :=
      (Finset.prod_fiberwise_of_maps_to hMaps
        (fun k : ZMod n => f (hamiltonianCoprimeConductor k))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro t ht
      have hDiv := (Nat.mem_divisors.mp ht).1
      calc
        _ = (Finset.univ.filter (fun k : ZMod n => hamiltonianCoprimeConductor k = t)).prod
            (fun _ => f t) := by
          apply Finset.prod_congr rfl
          intro k hk
          rw [(Finset.mem_filter.mp hk).2]
        _ = _ := by
          rw [Finset.prod_const, hamiltonian_coprime_conductor_multiplicity t hDiv]

theorem hamiltonian_coprime_determinant_divisor_product (z : Real) :
    Matrix.det ((1 : Matrix (ZMod n) (ZMod n) Real) -
        HSMul.hSMul z (centeredKernel (hamiltonianCoprimeKernel (n := n)) (1 / (n : Real)))) =
      n.divisors.prod (fun t => hamiltonianCoprimeDeterminantFactor z t ^ t.totient) := by
  rw [hamiltonian_coprime_determinant_frequency_product]
  have hFactor (k : ZMod n) :
      1 - z * hamiltonianCoprimeCenteredEigenvalue k =
        hamiltonianCoprimeDeterminantFactor z (hamiltonianCoprimeConductor k) := by
    unfold hamiltonianCoprimeCenteredEigenvalue hamiltonianCoprimeDeterminantFactor
    split_ifs <;> ring
  simp_rw [hFactor]
  exact hamiltonian_coprime_conductor_product _

end PrimeFactorOscillations
