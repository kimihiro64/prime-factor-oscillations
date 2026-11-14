/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import PrimeFactorOscillations.Helpers.HamiltonianGaussianTensorTilt

/-! # The actual Gaussian polynomial functional and Stein identity

The finite polynomial functional is identified with an integrable
multivariable complex Gaussian integral. Its integration-by-parts identity
is proved for every polynomial, retaining every monomial and coefficient.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def gaussianMonomialState (z : Iota -> Complex) (d : Iota -> Nat) : Complex :=
  Finset.prod Finset.univ (fun i => gaussianWickMonomial (z i) (d i))

def gaussianPolynomialState (z : Iota -> Complex) (p : MvPolynomial Iota Complex) : Complex :=
  p.coeff.sum (fun d a => a * gaussianMonomialState z (fun i => d i))

theorem gaussianPolynomialState_monomial (z : Iota -> Complex)
    (d : Finsupp Iota Nat) (a : Complex) :
    gaussianPolynomialState z (MvPolynomial.monomial d a) =
      a * gaussianMonomialState z (fun i => d i) := by
  unfold gaussianPolynomialState
  exact MvPolynomial.sum_monomial_eq (by simp)

theorem gaussianPolynomialState_zero (z : Iota -> Complex) :
    gaussianPolynomialState z 0 = 0 := by
  simpa only [MvPolynomial.monomial_zero, zero_mul] using
    gaussianPolynomialState_monomial z (0 : Finsupp Iota Nat) 0

theorem gaussianPolynomialState_add (z : Iota -> Complex)
    (p q : MvPolynomial Iota Complex) :
    gaussianPolynomialState z (p + q) =
      gaussianPolynomialState z p + gaussianPolynomialState z q := by
  unfold gaussianPolynomialState
  rw [AddMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index (by intro d; simp) (by intro d hd a b; ring)

theorem gaussianPolynomialState_C_mul (z : Iota -> Complex) (a : Complex)
    (p : MvPolynomial Iota Complex) :
    gaussianPolynomialState z (MvPolynomial.C a * p) =
      a * gaussianPolynomialState z p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    rw [mul_add, gaussianPolynomialState_add, gaussianPolynomialState_add, hp, hq]
    ring
  | monomial d b =>
    rw [MvPolynomial.C_mul_monomial, gaussianPolynomialState_monomial,
      gaussianPolynomialState_monomial]
    ring

theorem gaussianWickMonomial_successor (z : Complex) (n : Nat) :
    gaussianWickMonomial z (n + 1) =
      (n : Complex) * z * gaussianWickMonomial z (n - 1) := by
  cases n with
  | zero => simp [gaussianWickMonomial]
  | succ n => simp only [gaussianWickMonomial, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one]

theorem gaussianMonomialState_shift (z : Iota -> Complex)
    (d : Finsupp Iota Nat) (i : Iota) :
    gaussianMonomialState z (fun j => (d + (Finsupp.single i (1 : Nat) : Finsupp Iota Nat)) j) =
      z i * (d i : Complex) *
        gaussianMonomialState z (fun j => (d - (Finsupp.single i (1 : Nat) : Finsupp Iota Nat)) j) := by
  have hAddRest :
      Finset.prod (Finset.univ.erase i) (fun j =>
        gaussianWickMonomial (z j) ((d + (Finsupp.single i (1 : Nat) : Finsupp Iota Nat)) j)) =
      Finset.prod (Finset.univ.erase i) (fun j => gaussianWickMonomial (z j) (d j)) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hji), add_zero]
  have hSubRest :
      Finset.prod (Finset.univ.erase i) (fun j =>
        gaussianWickMonomial (z j) ((d - (Finsupp.single i (1 : Nat) : Finsupp Iota Nat)) j)) =
      Finset.prod (Finset.univ.erase i) (fun j => gaussianWickMonomial (z j) (d j)) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hji), Nat.sub_zero]
  unfold gaussianMonomialState
  rw [<- Finset.mul_prod_erase Finset.univ
    (fun j => gaussianWickMonomial (z j) ((d + (Finsupp.single i (1 : Nat) : Finsupp Iota Nat)) j))
    (Finset.mem_univ i)]
  rw [<- Finset.mul_prod_erase Finset.univ
    (fun j => gaussianWickMonomial (z j) ((d - (Finsupp.single i (1 : Nat) : Finsupp Iota Nat)) j))
    (Finset.mem_univ i)]
  rw [hAddRest, hSubRest]
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
  rw [gaussianWickMonomial_successor]
  ring

theorem gaussianPolynomialState_stein (z : Iota -> Complex)
    (i : Iota) (p : MvPolynomial Iota Complex) :
    gaussianPolynomialState z (MvPolynomial.X i * p) =
      z i * gaussianPolynomialState z (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    rw [mul_add, gaussianPolynomialState_add, map_add,
      gaussianPolynomialState_add, hp, hq]
    ring
  | monomial d a =>
    rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul,
      gaussianPolynomialState_monomial, MvPolynomial.pderiv_monomial,
      gaussianPolynomialState_monomial, add_comm ((Finsupp.single i (1 : Nat) : Finsupp Iota Nat)) d,
      gaussianMonomialState_shift]
    ring

def gaussianMvTiltKernel (z w : Iota -> Complex)
    (p : MvPolynomial Iota Complex) (x : Iota -> Real) : Complex :=
  MvPolynomial.eval (fun i => w i * (x i : Complex)) p *
    Finset.prod Finset.univ (fun i =>
      Complex.exp (-gaussianTiltPrecision (z i) * (x i : Complex) ^ 2))

theorem gaussianMvTiltKernel_expansion (z w : Iota -> Complex)
    (p : MvPolynomial Iota Complex) :
    gaussianMvTiltKernel z w p =
      gaussianTensorPolynomialTiltKernel z w p.support (fun d => p.coeff d)
        (fun d i => d i) := by
  funext x
  unfold gaussianMvTiltKernel gaussianTensorPolynomialTiltKernel gaussianTensorTiltKernel
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [mul_assoc, <- Finset.prod_mul_distrib]

theorem gaussianMvTiltKernel_integrable (z w : Iota -> Complex)
    (hz : forall i, norm (z i) < 1) (p : MvPolynomial Iota Complex) :
    MeasureTheory.Integrable (gaussianMvTiltKernel z w p) gaussianTensorMeasure := by
  rw [gaussianMvTiltKernel_expansion]
  exact gaussianTensorPolynomialTiltKernel_integrable z w hz p.support
    (fun d => p.coeff d) (fun d i => d i)

theorem gaussianMvTiltKernel_normalized (z w : Iota -> Complex)
    (hz : forall i, norm (z i) < 1)
    (hw : forall i, w i ^ 2 = z i / (1 + z i))
    (p : MvPolynomial Iota Complex) :
    MeasureTheory.integral gaussianTensorMeasure (gaussianMvTiltKernel z w p) /
        gaussianTensorTiltNormalizer z =
      gaussianPolynomialState z p := by
  rw [gaussianMvTiltKernel_expansion]
  exact gaussianTensorPolynomialTilt_normalized z w hz hw p.support
    (fun d => p.coeff d) (fun d i => d i)

end PrimeFactorOscillations
