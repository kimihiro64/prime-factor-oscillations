/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PositiveDirichletContinuation

/-!
# Positive series at a bounded boundary limit

A uniform upper bound on convergent nonnegative series passes to a
pointwise boundary limit and forces summability there. The explicit
Dirichlet specialization is the boundary consumer for the ordinary
endpoint Euler-quotient argument, not a zeta zero theorem in Lean.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter
open scoped Topology

noncomputable section

theorem summable_nonneg_of_bounded_tsum_limit {I : Type*}
    (f : Nat -> I -> Real) (g : I -> Real) (M : Real)
    (hg : forall i, 0 <= g i)
    (hf : forall n i, 0 <= f n i)
    (hSum : forall n, Summable (f n))
    (hLimit : forall i, Tendsto (fun n => f n i) atTop (nhds (g i)))
    (hBound : forall n, tsum (f n) <= M) :
    Summable g := by
  apply summable_of_sum_le hg
  intro S
  have hFinite : Tendsto (fun n => S.sum (fun i => f n i)) atTop
      (nhds (S.sum g)) :=
    tendsto_finsetSum S (fun i _ => hLimit i)
  apply le_of_tendsto hFinite
  apply Filter.Eventually.of_forall
  intro n
  exact ((hSum n).sum_le_tsum S (fun i _ => hf n i)).trans (hBound n)

theorem summable_positiveDirichlet_of_bounded_boundary
    (a : Nat -> Real) (ha : forall n, 0 <= a n)
    (sigma : Nat -> Real) (alpha M : Real)
    (hSigma : Tendsto sigma atTop (nhds alpha))
    (hSum : forall j, Summable (positiveDirichletTerm a (sigma j)))
    (hBound : forall j, tsum (positiveDirichletTerm a (sigma j)) <= M) :
    Summable (positiveDirichletTerm a alpha) := by
  apply summable_nonneg_of_bounded_tsum_limit
    (fun j => positiveDirichletTerm a (sigma j))
    (positiveDirichletTerm a alpha) M
  case hg =>
    intro n
    exact mul_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  case hf =>
    intro j n
    exact mul_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  case hSum => exact hSum
  case hLimit =>
    intro n
    have hp : 0 < ((n + 1 : Nat) : Real) :=
      Nat.cast_pos.mpr (Nat.zero_lt_succ n)
    have hInner : Tendsto
        (fun j => Real.log ((n + 1 : Nat) : Real) * -(sigma j)) atTop
        (nhds (Real.log ((n + 1 : Nat) : Real) * -alpha)) :=
      tendsto_const_nhds.mul hSigma.neg
    have hExp := Real.continuous_exp.continuousAt.tendsto.comp hInner
    have hTerm : Tendsto
        (fun j => a n * Real.exp
          (Real.log ((n + 1 : Nat) : Real) * -(sigma j))) atTop
        (nhds (a n * Real.exp
          (Real.log ((n + 1 : Nat) : Real) * -alpha))) :=
      tendsto_const_nhds.mul hExp
    simpa only [positiveDirichletTerm, Real.rpow_def_of_pos hp] using hTerm
  case hBound => exact hBound

end

end PrimeFactorOscillations.PrimeClassDeletion
