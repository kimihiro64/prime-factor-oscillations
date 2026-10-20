/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import PrimeFactorOscillations.Helpers.UniformCarrierCoefficients

/-!
# QuadraticPairDiagonal

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Exact square diagonal of the quadratic inverse/plain pair

All sums retain their finite annular support. The final decomposition leaves
the full signed remainder intact; it proves no cancellation estimate.
-/


noncomputable section
namespace PrimeFactorOscillations.QuadraticPairDiagonal

def annulus (N : Nat) : Finset Nat := Finset.Ico N (2 * N)

def mu (n : Nat) : Complex := ((ArithmeticFunction.moebius n : Int) : Complex)

def squareKernel (n : Nat) : Complex :=
  @ite Complex (IsSquare n) (Classical.propDecidable _) 1 0

theorem square_annulus_eq (N a b : Nat) (hN : 1 <= N)
    (ha : Membership.mem (annulus N) a)
    (hb : Membership.mem (annulus N) b)
    (hsf : Squarefree a) (hsq : IsSquare (a * b)) : a = b := by
  have haN : N <= a := (Finset.mem_Ico.mp ha).1
  have hbN : N <= b := (Finset.mem_Ico.mp hb).1
  have hbUpper : b < 2 * N := (Finset.mem_Ico.mp hb).2
  have hbPos : 0 < b :=
    _root_.lt_of_lt_of_le (by decide : 0 < (1 : Nat)) (hN.trans hbN)
  choose c hc using hsf.dvd_of_isSquare_mul hsq
  by_cases hc0 : c = 0
  . have hb0 : b = 0 := by simpa [hc0] using hc
    omega
  by_cases hc1 : c = 1
  . simpa [hc1] using hc.symm
  have hcTwo : 2 <= c := by omega
  have hbad : 2 * N <= b := by
    calc
      2 * N <= 2 * a := Nat.mul_le_mul_left 2 haN
      _ = a * 2 := Nat.mul_comm _ _
      _ <= a * c := Nat.mul_le_mul_left a hcTwo
      _ = b := hc.symm
  omega

theorem squareKernel_annulus (N a b : Nat) (hN : 1 <= N)
    (ha : Membership.mem (annulus N) a)
    (hb : Membership.mem (annulus N) b)
    (hsf : Squarefree a) :
    squareKernel (a * b) = if b = a then 1 else 0 := by
  classical
  by_cases hba : b = a
  . subst b
    have hsq : IsSquare (a * a) := Exists.intro a rfl
    simp [squareKernel, hsq]
  . have hsq : Not (IsSquare (a * b)) := by
      intro h
      exact hba (square_annulus_eq N a b hN ha hb hsf h).symm
    simp [squareKernel, hsq, hba]

theorem moebius_square_diagonal (N : Nat) (hN : 1 <= N)
    (h : Nat -> Nat -> Complex) :
    (annulus N).sum (fun a => (annulus N).sum
      (fun b => mu a * h a b * squareKernel (a * b))) =
    (annulus N).sum (fun a => mu a * h a a) := by
  classical
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hsf : Squarefree a
  . calc
      (annulus N).sum (fun b => mu a * h a b * squareKernel (a * b)) =
          (annulus N).sum (fun b => if b = a then mu a * h a a else 0) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [squareKernel_annulus N a b hN ha hb hsf]
        by_cases hba : b = a
        . subst b
          simp
        . simp [hba]
      _ = mu a * h a a := by simp [ha]
  . have hm : ArithmeticFunction.moebius a = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
    simp [mu, hm]

def kernelSum (N : Nat) (chi K : Nat -> Complex) : Complex :=
  (annulus N).sum (fun a => (annulus N).sum
    (fun b => mu a * chi b * K (a * b))) / (N : Complex)

def diagonalSum (N : Nat) (chi w : Nat -> Complex) : Complex :=
  (annulus N).sum (fun a => mu a * chi a * w a) / (N : Complex)

theorem kernel_eq_diagonal_add_remainder (N : Nat) (hN : 1 <= N)
    (chi K w : Nat -> Complex)
    (hw : forall a : Nat, w (a * a) = w a) :
    kernelSum N chi K =
      diagonalSum N chi w +
      kernelSum N chi (fun n => K n - squareKernel n * w n) := by
  have hdiag :
      (annulus N).sum (fun a => (annulus N).sum
        (fun b => mu a * chi b * (squareKernel (a * b) * w (a * b)))) =
      (annulus N).sum (fun a => mu a * chi a * w a) := by
    calc
      (annulus N).sum (fun a => (annulus N).sum
          (fun b => mu a * chi b * (squareKernel (a * b) * w (a * b)))) =
          (annulus N).sum (fun a => (annulus N).sum
            (fun b => mu a * (chi b * w (a * b)) * squareKernel (a * b))) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = (annulus N).sum (fun a => mu a * (chi a * w (a * a))) :=
        moebius_square_diagonal N hN (fun a b => chi b * w (a * b))
      _ = (annulus N).sum (fun a => mu a * chi a * w a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hw a]
        ring
  unfold kernelSum diagonalSum
  rw [<- add_div]
  apply congrArg (fun z : Complex => z / (N : Complex))
  rw [<- hdiag, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  ring

end PrimeFactorOscillations.QuadraticPairDiagonal
