/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianNonlinearRepair

/-! # The full quadratic fixed point for the degree Jacobian

The inverse acts on the degree Jacobian, so the only nonlinear term is
the full signed product -z*(Qz). All of its cross terms are retained.
The hypotheses and conclusions use explicit row budgets.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianDegreeNonlinear (P : Matrix Iota Iota Real) (z : Iota -> Real) : Iota -> Real :=
  -z * P.mulVec z

def hamiltonianDegreeRepairMap (P G : Matrix Iota Iota Real)
    (ell z : Iota -> Real) : Iota -> Real :=
  G.mulVec (ell + hamiltonianDegreeNonlinear P z)

theorem hamiltonian_degree_nonlinear_norm
    (P : Matrix Iota Iota Real) (b radius : Real)
    (hb : 0 <= b) (hRadius : 0 <= radius)
    (hP : forall i, Finset.univ.sum (fun j => abs (P i j)) <= b)
    (z : Iota -> Real) (hz : norm z <= radius) :
    norm (hamiltonianDegreeNonlinear P z) <= b * radius ^ 2 := by
  have hPNorm := matrix_row_operator_norm_le P b hb hP
  have hPz : norm (P.mulVec z) <= b * radius :=
    (Matrix.linfty_opNorm_mulVec P z).trans
      (mul_le_mul hPNorm hz (norm_nonneg _) hb)
  calc
    _ <= norm (-z) * norm (P.mulVec z) := norm_mul_le _ _
    _ = norm z * norm (P.mulVec z) := by rw [norm_neg]
    _ <= radius * (b * radius) :=
      mul_le_mul hz hPz (norm_nonneg _) hRadius
    _ = _ := by ring

theorem hamiltonian_degree_nonlinear_sub_norm
    (P : Matrix Iota Iota Real) (b radius : Real)
    (hb : 0 <= b) (hRadius : 0 <= radius)
    (hP : forall i, Finset.univ.sum (fun j => abs (P i j)) <= b)
    (x y : Iota -> Real) (hx : norm x <= radius) (hy : norm y <= radius) :
    norm (hamiltonianDegreeNonlinear P x - hamiltonianDegreeNonlinear P y) <=
      (2 * b * radius) * norm (x - y) := by
  have hPNorm := matrix_row_operator_norm_le P b hb hP
  have hPv (v : Iota -> Real) : norm (P.mulVec v) <= b * norm v :=
    (Matrix.linfty_opNorm_mulVec P v).trans
      (mul_le_mul_of_nonneg_right hPNorm (norm_nonneg _))
  have hIdentity : hamiltonianDegreeNonlinear P x - hamiltonianDegreeNonlinear P y =
      -(x - y) * P.mulVec x - y * P.mulVec (x - y) := by
    funext i
    simp only [hamiltonianDegreeNonlinear, Matrix.mulVec_sub,
      Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]
    ring
  rw [hIdentity]
  calc
    _ <= norm (-(x - y) * P.mulVec x) + norm (y * P.mulVec (x - y)) := norm_sub_le _ _
    _ <= norm (-(x - y)) * norm (P.mulVec x) + norm y * norm (P.mulVec (x - y)) :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = norm (x - y) * norm (P.mulVec x) + norm y * norm (P.mulVec (x - y)) := by rw [norm_neg]
    _ <= norm (x - y) * (b * radius) + radius * (b * norm (x - y)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left ((hPv x).trans (mul_le_mul_of_nonneg_left hx hb)) (norm_nonneg _))
        (mul_le_mul hy (hPv (x - y)) (norm_nonneg _) hRadius)
    _ = _ := by ring

theorem hamiltonian_degree_repair_fixed_point
    (P G : Matrix Iota Iota Real) (ell : Iota -> Real)
    (b g eta radius : Real)
    (hb : 0 <= b) (hg : 0 <= g) (hEta : 0 <= eta) (hRadius : 0 <= radius)
    (hP : forall i, Finset.univ.sum (fun j => abs (P i j)) <= b)
    (hG : forall i, Finset.univ.sum (fun j => abs (G i j)) <= g)
    (hEll : norm ell <= eta)
    (hBall : g * eta + g * b * radius ^ 2 <= radius)
    (hLip : 2 * g * b * radius <= 1 / 2) :
    exists z : Iota -> Real, norm z <= radius /\
      hamiltonianDegreeRepairMap P G ell z = z /\
      norm (z - G.mulVec ell) <= g * b * radius ^ 2 := by
  let F := hamiltonianDegreeRepairMap P G ell
  let s : Set (Iota -> Real) := fun z => norm z <= radius
  have hGNorm : norm G <= g := matrix_row_operator_norm_le G g hg hG
  have hGv (v : Iota -> Real) : norm (G.mulVec v) <= g * norm v :=
    (Matrix.linfty_opNorm_mulVec G v).trans
      (mul_le_mul_of_nonneg_right hGNorm (norm_nonneg _))
  have hBound (z : Iota -> Real) (hz : norm z <= radius) : norm (F z) <= radius := by
    have hN := hamiltonian_degree_nonlinear_norm P b radius hb hRadius hP z hz
    calc
      _ = norm (G.mulVec ell + G.mulVec (hamiltonianDegreeNonlinear P z)) := by
        change norm (G.mulVec (ell + hamiltonianDegreeNonlinear P z)) = _
        rw [Matrix.mulVec_add]
      _ <= norm (G.mulVec ell) + norm (G.mulVec (hamiltonianDegreeNonlinear P z)) := norm_add_le _ _
      _ <= g * eta + g * (b * radius ^ 2) :=
        add_le_add ((hGv _).trans (mul_le_mul_of_nonneg_left hEll hg))
          ((hGv _).trans (mul_le_mul_of_nonneg_left hN hg))
      _ <= radius := by nlinarith only [hBall]
  have hMaps : Set.MapsTo F s s := fun z hz => hBound z hz
  have hDist (x y : Iota -> Real) (hx : norm x <= radius) (hy : norm y <= radius) :
      norm (F x - F y) <= (1 / 2) * norm (x - y) := by
    have hDiff : F x - F y =
        G.mulVec (hamiltonianDegreeNonlinear P x - hamiltonianDegreeNonlinear P y) := by
      dsimp only [F, hamiltonianDegreeRepairMap]
      rw [<- Matrix.mulVec_sub]
      congr 1
      abel
    rw [hDiff]
    calc
      _ <= g * norm (hamiltonianDegreeNonlinear P x - hamiltonianDegreeNonlinear P y) := hGv _
      _ <= g * ((2 * b * radius) * norm (x - y)) :=
        mul_le_mul_of_nonneg_left
          (hamiltonian_degree_nonlinear_sub_norm P b radius hb hRadius hP x y hx hy) hg
      _ = (2 * g * b * radius) * norm (x - y) := by ring
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
  have hDiff : z - G.mulVec ell = G.mulVec (hamiltonianDegreeNonlinear P z) := by
    calc
      _ = F z - G.mulVec ell := congrArg (fun v => v - G.mulVec ell) hEq.symm
      _ = _ := by
        change G.mulVec (ell + hamiltonianDegreeNonlinear P z) - G.mulVec ell = _
        rw [Matrix.mulVec_add, add_sub_cancel_left]
  rw [hDiff]
  exact (hGv _).trans
    (by simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left
        (hamiltonian_degree_nonlinear_norm P b radius hb hRadius hP z hz.1) hg))

end PrimeFactorOscillations
