/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Full l1 estimates for Dirichlet convolution

The signed mass identity is obtained by regrouping the full product series
by its multiplication fibers. The absolute convolution controls the norm
and gives the full Young inequality for summable arithmetic functions.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.ArithmeticFunctionL1

noncomputable def absolute (f : ArithmeticFunction Real) : ArithmeticFunction Real where
  toFun n := norm (f n)
  map_zero' := by simp

private theorem fiber_tsum (f g : ArithmeticFunction Real) (n : Nat) :
    tsum (fun x : {x : Prod Nat Nat // x.1 * x.2 = n} => f x.val.1 * g x.val.2) =
      (f * g) n := by
  by_cases hn : n = 0
  . subst n
    have hz : forall x : {x : Prod Nat Nat // x.1 * x.2 = 0},
        f x.val.1 * g x.val.2 = 0 := by
      intro x
      rcases mul_eq_zero.mp x.property with ha | hb
      . simp [ha]
      . simp [hb]
    have heq : (fun x : {x : Prod Nat Nat // x.1 * x.2 = 0} =>
        f x.val.1 * g x.val.2) = (fun _ => (0 : Real)) := funext hz
    rw [heq]
    simp
  . have hset : {x : Prod Nat Nat | x.1 * x.2 = n} =
        (n.divisorsAntidiagonal : Set (Prod Nat Nat)) := by
      ext x
      constructor
      . intro hx
        exact Nat.mem_divisorsAntidiagonal.mpr (And.intro hx hn)
      . intro hx
        exact (Nat.mem_divisorsAntidiagonal.mp hx).1
    change tsum (fun x : ({x : Prod Nat Nat | x.1 * x.2 = n} : Set (Prod Nat Nat)) =>
      f x.val.1 * g x.val.2) = (f * g) n
    rw [hset, tsum_fintype, ArithmeticFunction.mul_apply]
    exact Finset.sum_coe_sort n.divisorsAntidiagonal (fun x : Prod Nat Nat => f x.1 * g x.2)

theorem convolution_hasSum (f g : ArithmeticFunction Real)
    (hf : Summable (fun n : Nat => norm (f n)))
    (hg : Summable (fun n : Nat => norm (g n))) :
    HasSum (fun n : Nat => (f * g) n) (tsum (fun n : Nat => f n) * tsum (fun n : Nat => g n)) := by
  have hpairs : Summable (fun x : Prod Nat Nat => f x.1 * g x.2) :=
    summable_mul_of_summable_norm hf hg
  have hprod := hf.of_norm.hasSum.mul hg.of_norm.hasSum hpairs
  have hpush := hprod.tsum_fiberwise (fun x : Prod Nat Nat => x.1 * x.2)
  have heq : (fun n : Nat => tsum
      (fun x : Set.preimage (fun y : Prod Nat Nat => y.1 * y.2) {n} =>
        f x.val.1 * g x.val.2)) = (fun n : Nat => (f * g) n) := by
    funext n
    exact fiber_tsum f g n
  rw [heq] at hpush
  exact hpush

theorem absolute_convolution_hasSum (f g : ArithmeticFunction Real)
    (hf : Summable (fun n : Nat => norm (f n)))
    (hg : Summable (fun n : Nat => norm (g n))) :
    HasSum (fun n : Nat => (absolute f * absolute g) n)
      (tsum (fun n : Nat => norm (f n)) * tsum (fun n : Nat => norm (g n))) := by
  have hf' : Summable (fun n : Nat => norm (absolute f n)) := by
    change Summable (fun n : Nat => norm (norm (f n)))
    simpa only [norm_norm] using hf
  have hg' : Summable (fun n : Nat => norm (absolute g n)) := by
    change Summable (fun n : Nat => norm (norm (g n)))
    simpa only [norm_norm] using hg
  exact convolution_hasSum (absolute f) (absolute g) hf' hg'

theorem norm_convolution_le_absolute (f g : ArithmeticFunction Real) (n : Nat) :
    norm ((f * g) n) <= (absolute f * absolute g) n := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  calc
    norm (n.divisorsAntidiagonal.sum (fun x => f x.1 * g x.2)) <=
        n.divisorsAntidiagonal.sum (fun x => norm (f x.1 * g x.2)) := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      exact norm_mul (f x.1) (g x.2)

theorem norm_convolution_summable (f g : ArithmeticFunction Real)
    (hf : Summable (fun n : Nat => norm (f n)))
    (hg : Summable (fun n : Nat => norm (g n))) :
    Summable (fun n : Nat => norm ((f * g) n)) :=
  (absolute_convolution_hasSum f g hf hg).summable.of_nonneg_of_le
    (fun _n => norm_nonneg _) (norm_convolution_le_absolute f g)

theorem tsum_norm_convolution_le (f g : ArithmeticFunction Real)
    (hf : Summable (fun n : Nat => norm (f n)))
    (hg : Summable (fun n : Nat => norm (g n))) :
    tsum (fun n : Nat => norm ((f * g) n)) <=
      tsum (fun n : Nat => norm (f n)) * tsum (fun n : Nat => norm (g n)) := by
  have hmajor := absolute_convolution_hasSum f g hf hg
  exact (Summable.tsum_le_tsum (norm_convolution_le_absolute f g)
    (norm_convolution_summable f g hf hg) hmajor.summable).trans_eq hmajor.tsum_eq

end PrimeFactorOscillations.ArithmeticFunctionL1
