/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Topology.MetricSpace.Contracting
import PrimeFactorOscillations.Helpers.HamiltonianFiniteRowInverse

/-! # The quantitative nonlinear repair on the actual finite vector space

The full signed nonlinear map is retained. Explicit row-sum, source and
radius budgets give a fixed point and a quadratic displacement bound.
The matrix norm used internally is the absolute row operator norm; every
matrix hypothesis and the conclusion are stated without an implicit norm.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianRepairNonlinear (P : Matrix Iota Iota Real)
    (ell z : Iota -> Real) : Iota -> Real :=
  ell * z - z * P.mulVec z

def hamiltonianNonlinearRepairMap (P G : Matrix Iota Iota Real)
    (ell z : Iota -> Real) : Iota -> Real :=
  G.mulVec (ell + hamiltonianRepairNonlinear P ell z)

theorem hamiltonianRepairNonlinear_norm
    (P : Matrix Iota Iota Real) (ell : Iota -> Real) (eta radius : Real)
    (hEta : 0 <= eta) (hRadius : 0 <= radius)
    (hP : forall i, Finset.sum Finset.univ (fun j => abs (P i j)) <= 1)
    (hEll : norm ell <= eta) (z : Iota -> Real) (hz : norm z <= radius) :
    norm (hamiltonianRepairNonlinear P ell z) <= eta * radius + radius ^ 2 := by
  have hPNorm : norm P <= 1 := matrix_row_operator_norm_le P 1 (by norm_num) hP
  have hPz : norm (P.mulVec z) <= radius := by
    calc
      _ <= norm P * norm z := Matrix.linfty_opNorm_mulVec P z
      _ <= 1 * radius := mul_le_mul hPNorm hz (norm_nonneg _) (by norm_num)
      _ = radius := one_mul _
  calc
    _ <= norm (ell * z) + norm (z * P.mulVec z) := norm_sub_le _ _
    _ <= norm ell * norm z + norm z * norm (P.mulVec z) :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ <= eta * radius + radius * radius :=
      add_le_add (mul_le_mul hEll hz (norm_nonneg _) hEta)
        (mul_le_mul hz hPz (norm_nonneg _) hRadius)
    _ = _ := by ring

theorem hamiltonianRepairNonlinear_sub_norm
    (P : Matrix Iota Iota Real) (ell : Iota -> Real) (eta radius : Real)
    (hEta : 0 <= eta) (hRadius : 0 <= radius)
    (hP : forall i, Finset.sum Finset.univ (fun j => abs (P i j)) <= 1)
    (hEll : norm ell <= eta) (x y : Iota -> Real)
    (hx : norm x <= radius) (hy : norm y <= radius) :
    norm (hamiltonianRepairNonlinear P ell x - hamiltonianRepairNonlinear P ell y) <=
      (eta + 2 * radius) * norm (x - y) := by
  have hPNorm : norm P <= 1 := matrix_row_operator_norm_le P 1 (by norm_num) hP
  have hPv (v : Iota -> Real) : norm (P.mulVec v) <= norm v := by
    calc
      _ <= norm P * norm v := Matrix.linfty_opNorm_mulVec P v
      _ <= 1 * norm v := mul_le_mul_of_nonneg_right hPNorm (norm_nonneg _)
      _ = _ := one_mul _
  have hIdentity :
      hamiltonianRepairNonlinear P ell x - hamiltonianRepairNonlinear P ell y =
        ell * (x - y) - (x - y) * P.mulVec x - y * P.mulVec (x - y) := by
    apply funext
    intro i
    simp only [hamiltonianRepairNonlinear, Matrix.mulVec_sub,
      Pi.sub_apply, Pi.mul_apply]
    ring
  rw [hIdentity]
  calc
    _ <= norm (ell * (x - y) - (x - y) * P.mulVec x) +
        norm (y * P.mulVec (x - y)) := norm_sub_le _ _
    _ <= norm (ell * (x - y)) + norm ((x - y) * P.mulVec x) +
        norm (y * P.mulVec (x - y)) :=
      add_le_add (norm_sub_le _ _) (le_refl _)
    _ <= norm ell * norm (x - y) + norm (x - y) * norm (P.mulVec x) +
        norm y * norm (P.mulVec (x - y)) :=
      add_le_add (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)) (norm_mul_le _ _)
    _ <= eta * norm (x - y) + norm (x - y) * radius + radius * norm (x - y) := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_right hEll (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (le_trans (hPv x) hx) (norm_nonneg _)))
        (mul_le_mul hy (hPv (x - y)) (norm_nonneg _) hRadius)
    _ = _ := by ring

theorem hamiltonian_nonlinear_repair_fixed_point
    (P G : Matrix Iota Iota Real) (ell : Iota -> Real)
    (g eta radius e : Real)
    (hg : 0 <= g) (hEta : 0 <= eta) (hRadius : 0 <= radius)
    (hP : forall i, Finset.sum Finset.univ (fun j => abs (P i j)) <= 1)
    (hG : forall i, Finset.sum Finset.univ (fun j => abs (G i j)) <= g)
    (hEll : norm ell <= eta) (hSource : norm (G.mulVec ell) <= e)
    (hBall : e + g * (eta * radius + radius ^ 2) <= radius)
    (hLip : g * (eta + 2 * radius) <= 1 / 2) :
    exists z : Iota -> Real, norm z <= radius /\
      hamiltonianNonlinearRepairMap P G ell z = z /\
      norm (z - G.mulVec ell) <= g * (eta * radius + radius ^ 2) := by
  let F := hamiltonianNonlinearRepairMap P G ell
  let s : Set (Iota -> Real) := fun z => norm z <= radius
  have hGNorm : norm G <= g := matrix_row_operator_norm_le G g hg hG
  have hGv (v : Iota -> Real) : norm (G.mulVec v) <= g * norm v :=
    le_trans (Matrix.linfty_opNorm_mulVec G v)
      (mul_le_mul_of_nonneg_right hGNorm (norm_nonneg _))
  have hBound (z : Iota -> Real) (hz : norm z <= radius) : norm (F z) <= radius := by
    have hN := hamiltonianRepairNonlinear_norm P ell eta radius hEta hRadius hP hEll z hz
    calc
      _ = norm (G.mulVec ell + G.mulVec (hamiltonianRepairNonlinear P ell z)) := by
        change norm (G.mulVec (ell + hamiltonianRepairNonlinear P ell z)) = _
        rw [Matrix.mulVec_add]
      _ <= norm (G.mulVec ell) + norm (G.mulVec (hamiltonianRepairNonlinear P ell z)) :=
        norm_add_le _ _
      _ <= e + g * (eta * radius + radius ^ 2) :=
        add_le_add hSource (le_trans (hGv _) (mul_le_mul_of_nonneg_left hN hg))
      _ <= radius := hBall
  have hMaps : Set.MapsTo F s s := fun z hz => hBound z hz
  have hDist (x y : Iota -> Real) (hx : norm x <= radius) (hy : norm y <= radius) :
      norm (F x - F y) <= (1 / 2) * norm (x - y) := by
    have hDiff : F x - F y =
        G.mulVec (hamiltonianRepairNonlinear P ell x -
          hamiltonianRepairNonlinear P ell y) := by
      dsimp only [F, hamiltonianNonlinearRepairMap]
      rw [<- Matrix.mulVec_sub]
      congr 1
      abel
    rw [hDiff]
    calc
      _ <= g * norm (hamiltonianRepairNonlinear P ell x -
          hamiltonianRepairNonlinear P ell y) := hGv _
      _ <= g * ((eta + 2 * radius) * norm (x - y)) :=
        mul_le_mul_of_nonneg_left
          (hamiltonianRepairNonlinear_sub_norm P ell eta radius hEta hRadius
            hP hEll x y hx hy) hg
      _ = (g * (eta + 2 * radius)) * norm (x - y) := by ring
      _ <= (1 / 2) * norm (x - y) :=
        mul_le_mul_of_nonneg_right hLip (norm_nonneg _)
  have hClosed : IsClosed s := isClosed_le continuous_norm continuous_const
  have hComplete : IsComplete s := hClosed.isComplete
  have hZero : Membership.mem s (0 : Iota -> Real) := by
    change norm (0 : Iota -> Real) <= radius
    simpa only [norm_zero] using hRadius
  let Fsub := hMaps.restrict F s s
  have hContract : ContractingWith (1 / 2 : NNReal) Fsub := by
    refine And.intro (by norm_num) ?_
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (F x.val) (F y.val) <=
      ((1 / 2 : NNReal) : Real) * dist x.val y.val
    simpa only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
      hDist x.val y.val x.property y.property
  have hExists := ContractingWith.exists_fixedPoint' hComplete hMaps hContract hZero
    (edist_ne_top (0 : Iota -> Real) (F 0))
  let z := Classical.choose hExists
  have hz := Classical.choose_spec hExists
  have hEq : F z = z := hz.2.1
  refine Exists.intro z (And.intro hz.1 (And.intro hEq ?_))
  have hDiff : z - G.mulVec ell = G.mulVec (hamiltonianRepairNonlinear P ell z) := by
    calc
      _ = F z - G.mulVec ell := congrArg (fun v => v - G.mulVec ell) hEq.symm
      _ = _ := by
        change G.mulVec (ell + hamiltonianRepairNonlinear P ell z) -
          G.mulVec ell = _
        rw [Matrix.mulVec_add, add_sub_cancel_left]
  rw [hDiff]
  exact le_trans (hGv _)
    (mul_le_mul_of_nonneg_left
      (hamiltonianRepairNonlinear_norm P ell eta radius hEta hRadius hP hEll z hz.1) hg)

end PrimeFactorOscillations
