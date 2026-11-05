/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Exact finite observations from a dense linear subspace

A dense subspace can match every finite-dimensional continuous linear
observation exactly. This is the algebraic-topological input for matching
finitely many Laurent coefficients by K-finite sections. The representation
and meromorphic-distribution interfaces are not asserted by this theorem.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Metaplectic.DenseObservation

variable {K E V : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [AddCommGroup E] [Module K E]
  [TopologicalSpace E] [NormedAddCommGroup V] [NormedSpace K V]
  [FiniteDimensional K V]

theorem exists_same_observation (S : Submodule K E)
    (hS : Dense (S : Set E)) (F : ContinuousLinearMap (RingHom.id K) E V) (x : E) :
    exists y : E, And (Membership.mem S y) (F y = F x) := by
  let R : Submodule K V := Submodule.map F.toLinearMap S
  have hclosed : IsClosed (R : Set V) := R.closed_of_finiteDimensional
  have hsub : Set.Subset (S : Set E) (Set.preimage F (R : Set V)) := by
    intro y hy
    exact Submodule.mem_map.mpr (Exists.intro y (And.intro hy rfl))
  have hall : Set.Subset (closure (S : Set E))
      (Set.preimage F (R : Set V)) :=
    closure_minimal hsub (hclosed.preimage F.continuous)
  exact Submodule.mem_map.mp (hall (hS x))

end Metaplectic.DenseObservation
