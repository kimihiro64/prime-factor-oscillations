/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianLogMomentChoice
import PrimeFactorOscillations.Helpers.HamiltonianRoundingConstruction

/-! # Actual supported binary rounding with an explicit logarithmic error -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_joint_logarithmic_rounding
    (P : Matrix Iota Iota Real) (S1 S2 : Finset (Sum Iota Iota))
    (delta alpha : Real) (d : Nat) (hd : 1 <= d)
    (hd0 : 0 < delta) (hd1 : delta < 1) (ha : 0 <= alpha)
    (hP : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hPRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hPCols : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (hGap : norm (centeredKernel P (1 / (Fintype.card Iota : Real))) <= 1 - delta)
    (hSmall : ((d : Real) * alpha) * Real.log (4 * (Fintype.card Iota : Real)) ^ 2 <=
      hamiltonianForbiddenRepairSmall delta) :
    exists H : Matrix Iota Iota Real,
      (forall i j, H i j = 0 \/ H i j = 1) /\
      (forall i, Finset.univ.sum (fun j => H i j) = (d : Real)) /\
      (forall j, Finset.univ.sum (fun i => H i j) = (d : Real)) /\
      (forall i j, P i j = 0 -> H i j = 0) /\
      norm (hamiltonianBipartiteJointLift S1 S2 (H - HSMul.hSMul (d : Real) P)) <=
        16 * Real.sqrt ((d : Real) * Real.log (4 * (Fintype.card Iota : Real))) +
        hamiltonianRoundingDriftCost Iota delta alpha * (d : Real) ^ 2 := by
  have hmNat : 1 <= Fintype.card Iota := Fintype.card_pos
  have hm : (1 : Real) <= (Fintype.card Iota : Real) := by exact_mod_cast hmNat
  have hdReal : (1 : Real) <= (d : Real) := by exact_mod_cast hd
  let p := hamiltonianLogMoment (6 * (Fintype.card Iota : Real))
  have hChoice := hamiltonian_even_logarithmic_moment
    (6 * (Fintype.card Iota : Real)) (by linarith only [hm])
  cases hamiltonian_joint_rounding_with_moment_order P S1 S2 delta alpha p d
      hd0 hd1 ha hP hCap hPRows hPCols hGap hSmall hChoice.1 hChoice.2.1 with
  | intro H hH =>
    have hSqrt := hamiltonian_logarithmic_rounding_sqrt_bound
      (Fintype.card Iota : Real) (d : Real) hm hdReal
    exact Exists.intro H (And.intro hH.1
      (And.intro hH.2.1 (And.intro hH.2.2.1 (And.intro hH.2.2.2.1
        (hH.2.2.2.2.trans (add_le_add hSqrt le_rfl))))))

end PrimeFactorOscillations
