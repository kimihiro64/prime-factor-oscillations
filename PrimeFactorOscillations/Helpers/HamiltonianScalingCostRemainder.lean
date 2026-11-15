/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBoundaryBudgets
import PrimeFactorOscillations.Helpers.HamiltonianScalingCostIdentity
import PrimeFactorOscillations.Helpers.HamiltonianScalingLogRemainder

/-! # Two-power scaling-cost remainder before signed main-term reduction

The exact quadratic cost is the starting point. Bounds apply only to
the nonlinear residual, cubic Taylor error and removed-coordinate
substitution error; the leading bilinear form remains signed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_scaling_cost_remainder
    (P : Matrix Iota Iota Real) (hSym : forall i j, P i j = P j i)
    (ell z : Iota -> Real)
    (hDegree : forall i, P.mulVec 1 i = 1 - ell i)
    (hScaling : forall i, (1 + z i) * P.mulVec (1 + z) i = 1)
    (radius mass : Real) (hRadius : 0 <= radius) (hSmall : radius <= 1 / 2)
    (hz : forall i, abs (z i) <= radius)
    (hP : forall i, Finset.sum Finset.univ (fun j => abs (P i j)) <= 1)
    (hMass : Finset.sum Finset.univ (fun i => abs (ell i)) <= mass) :
    abs (Finset.sum Finset.univ (fun i => Real.log (1 + z i)) -
      Finset.sum Finset.univ ell / 2 -
        Finset.sum Finset.univ (fun i => ell i * z i) / 2) <=
      mass * radius ^ 2 / 2 + 5 * (Fintype.card Iota : Real) * radius ^ 3 / 2 := by
  have hPz (i : Iota) : abs (P.mulVec z i) <= radius := by
    change abs (Finset.sum Finset.univ (fun j => P i j * z j)) <= radius
    calc
      _ <= Finset.sum Finset.univ (fun j => abs (P i j * z j)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ = Finset.sum Finset.univ (fun j => abs (P i j) * abs (z j)) := by
        simp only [abs_mul]
      _ <= Finset.sum Finset.univ (fun j => abs (P i j) * radius) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hz j) (abs_nonneg _))
      _ = Finset.sum Finset.univ (fun j => abs (P i j)) * radius := by rw [Finset.sum_mul]
      _ <= 1 * radius := mul_le_mul_of_nonneg_right (hP i) hRadius
      _ = _ := one_mul _
  have hSq (i : Iota) : z i ^ 2 <= radius ^ 2 := by
    have h := mul_le_mul (hz i) (hz i) (abs_nonneg _) hRadius
    simpa only [<- pow_two, sq_abs] using h
  have hPoint (i : Iota) :
      abs (z i * hamiltonianRepairNonlinear P ell z i) <=
        abs (ell i) * radius ^ 2 + radius ^ 3 := by
    have hId : z i * hamiltonianRepairNonlinear P ell z i =
        ell i * z i ^ 2 - z i ^ 2 * P.mulVec z i := by
      change z i * (ell i * z i - z i * P.mulVec z i) = _
      ring
    rw [hId]
    calc
      _ <= abs (ell i * z i ^ 2) + abs (z i ^ 2 * P.mulVec z i) := by
        simpa only [Real.norm_eq_abs] using
          norm_sub_le (ell i * z i ^ 2) (z i ^ 2 * P.mulVec z i)
      _ = abs (ell i) * z i ^ 2 + z i ^ 2 * abs (P.mulVec z i) := by
        simp only [abs_mul, abs_pow, sq_abs]
      _ <= abs (ell i) * radius ^ 2 + radius ^ 2 * radius :=
        add_le_add (mul_le_mul_of_nonneg_left (hSq i) (abs_nonneg _))
          (mul_le_mul (hSq i) (hPz i) (abs_nonneg _) (sq_nonneg radius))
      _ = _ := by ring
  have hNonlinear : abs (Finset.sum Finset.univ
      (fun i => z i * hamiltonianRepairNonlinear P ell z i)) <=
        mass * radius ^ 2 + (Fintype.card Iota : Real) * radius ^ 3 := by
    calc
      _ <= Finset.sum Finset.univ (fun i => abs (z i * hamiltonianRepairNonlinear P ell z i)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum Finset.univ (fun i => abs (ell i) * radius ^ 2 + radius ^ 3) :=
        Finset.sum_le_sum (fun i _ => hPoint i)
      _ = Finset.sum Finset.univ (fun i => abs (ell i)) * radius ^ 2 +
          (Fintype.card Iota : Real) * radius ^ 3 := by
        rw [Finset.sum_add_distrib, <- Finset.sum_mul]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ <= _ := add_le_add (mul_le_mul_of_nonneg_right hMass (sq_nonneg radius)) (le_refl _)
  have hQuadratic := hamiltonian_scaling_quadratic_cost_identity P hSym ell z hDegree hScaling
  have hTaylor := hamiltonian_scaling_log_sum_remainder z radius hRadius hSmall hz
  have hExact :
      Finset.sum Finset.univ (fun i => Real.log (1 + z i)) -
        Finset.sum Finset.univ ell / 2 - Finset.sum Finset.univ (fun i => ell i * z i) / 2 =
      (Finset.sum Finset.univ (fun i => Real.log (1 + z i)) -
        Finset.sum Finset.univ z + Finset.sum Finset.univ (fun i => z i ^ 2) / 2) -
          Finset.sum Finset.univ (fun i => z i * hamiltonianRepairNonlinear P ell z i) / 2 := by
    linarith only [hQuadratic]
  have hDiv : abs (Finset.sum Finset.univ
      (fun i => z i * hamiltonianRepairNonlinear P ell z i) / 2) =
      abs (Finset.sum Finset.univ
        (fun i => z i * hamiltonianRepairNonlinear P ell z i)) / 2 := by
    rw [abs_div]
    norm_num
  rw [hExact]
  have hTriangle := norm_sub_le
    (Finset.sum Finset.univ (fun i => Real.log (1 + z i)) -
      Finset.sum Finset.univ z + Finset.sum Finset.univ (fun i => z i ^ 2) / 2)
    (Finset.sum Finset.univ (fun i => z i * hamiltonianRepairNonlinear P ell z i) / 2)
  simp only [Real.norm_eq_abs, hDiv] at hTriangle
  linarith only [hTriangle, hTaylor, hNonlinear]

theorem hamiltonian_retained_linear_cost_error
    (D : Finset Iota) (ell k : Iota -> Real)
    (z : forall _i : (Compl.compl D : Finset Iota), Real)
    (err bound mass deletedMass : Real) (hErr : 0 <= err) (hBound : 0 <= bound)
    (hClose : forall i : (Compl.compl D : Finset Iota), abs (z i - k i.val) <= err)
    (hRemoved : forall d : D, abs (k d.val) <= bound)
    (hMass : Finset.sum Finset.univ (fun i => abs (ell i)) <= mass)
    (hDeleted : Finset.sum Finset.univ (fun d : D => abs (ell d.val)) <= deletedMass) :
    abs (Finset.sum Finset.univ
      (fun i : (Compl.compl D : Finset Iota) => ell i.val * z i) -
        Finset.sum Finset.univ (fun i => ell i * k i)) <=
      mass * err + deletedMass * bound := by
  let R : Finset Iota := Compl.compl D
  have hWeighted (W : Finset Iota) (w v : W -> Real) (b : Real)
      (hv : forall j, abs (v j) <= b) :
      abs (Finset.sum Finset.univ (fun j => w j * v j)) <=
        Finset.sum Finset.univ (fun j => abs (w j)) * b := by
    calc
      _ <= Finset.sum Finset.univ (fun j => abs (w j * v j)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ = Finset.sum Finset.univ (fun j => abs (w j) * abs (v j)) := by simp only [abs_mul]
      _ <= Finset.sum Finset.univ (fun j => abs (w j) * b) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _))
      _ = _ := by rw [Finset.sum_mul]
  have hPart := hamiltonian_sum_support_partition (fun i => ell i * k i) D
  have hExact :
      Finset.sum Finset.univ (fun i : R => ell i.val * z i) -
        Finset.sum Finset.univ (fun i => ell i * k i) =
      Finset.sum Finset.univ (fun i : R => ell i.val * (z i - k i.val)) -
        Finset.sum Finset.univ (fun d : D => ell d.val * k d.val) := by
    rw [hPart]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hRet : abs (Finset.sum Finset.univ (fun i : R => ell i.val * (z i - k i.val))) <=
      mass * err :=
    le_trans (hWeighted R (fun i : R => ell i.val) (fun i : R => z i - k i.val) err hClose)
      (mul_le_mul_of_nonneg_right
        (le_trans (hamiltonian_retained_sum_le (fun i => abs (ell i)) D
          (fun _ => abs_nonneg _)) hMass) hErr)
  have hDel : abs (Finset.sum Finset.univ (fun d : D => ell d.val * k d.val)) <=
      deletedMass * bound :=
    le_trans (hWeighted D (fun d : D => ell d.val) (fun d : D => k d.val) bound hRemoved)
      (mul_le_mul_of_nonneg_right hDeleted hBound)
  rw [hExact]
  have hTriangle := norm_sub_le
    (Finset.sum Finset.univ (fun i : R => ell i.val * (z i - k i.val)))
    (Finset.sum Finset.univ (fun d : D => ell d.val * k d.val))
  simpa only [Real.norm_eq_abs] using le_trans hTriangle (add_le_add hRet hDel)

end PrimeFactorOscillations
