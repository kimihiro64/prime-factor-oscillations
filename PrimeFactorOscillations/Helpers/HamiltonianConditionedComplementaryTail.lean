/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianComplementaryPolynomialTail
import PrimeFactorOscillations.Helpers.HamiltonianFiniteConditioning
import PrimeFactorOscillations.Helpers.HamiltonianPrescribedCutCounts

/-! # Balanced and prescribed-coordinate complementary-cut tails

Exact full-cube cardinalities discharge both conditioning costs.
The actual covariance and actual coordinate quarter estimate
therefore retain polynomial failure bounds uniformly in endpoints.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem hamiltonian_balanced_tail_conditioning
    (B : Finset (I -> Bool)) (A : Real) (m : Nat) (hm : 1 <= m)
    (hSize : Fintype.card I = 2 * m)
    (hTail : (B.card : Real) / (Fintype.card (I -> Bool) : Real) <=
      (Fintype.card I : Real) ^ (-(A + 3))) :
    ((Inter.inter B (hamiltonianBalancedSigns (I := I) m)).card : Real) /
      ((hamiltonianBalancedSigns (I := I) m).card : Real) <=
        (Fintype.card I : Real) ^ (-A) := by
  let n : Real := Fintype.card I
  have hDim : 2 <= Fintype.card I := by omega
  have hn : 2 <= n := by dsimp only [n]; exact_mod_cast hDim
  have hEvent : (Fintype.card (I -> Bool) : Real) <=
      (n + 1) * ((hamiltonianBalancedSigns (I := I) m).card : Real) := by
    dsimp only [n]
    exact_mod_cast hamiltonian_balanced_sign_mass (I := I) m hSize
  have hP : 0 <= n ^ (-(A + 3)) := Real.rpow_nonneg (by linarith only [hn]) _
  have h := hamiltonian_finite_conditioned_count B (hamiltonianBalancedSigns m)
    (n ^ (-(A + 3))) (n + 1) hP hTail hEvent
  exact h.trans (hamiltonian_conditioning_power_budget n A (n + 1) hn
    (hamiltonian_polynomial_conditioning_budgets n hn).1)

theorem hamiltonian_prescribed_tail_conditioning
    (B : Finset (I -> Bool)) (A : Real) (a b : I) (hab : Not (a = b))
    (m : Nat) (hm : 1 <= m) (hSize : Fintype.card I = 2 * m)
    (hTail : (B.card : Real) / (Fintype.card (I -> Bool) : Real) <=
      (Fintype.card I : Real) ^ (-(A + 3))) :
    ((Inter.inter B (hamiltonianPrescribedBalancedSigns m a b)).card : Real) /
      ((hamiltonianPrescribedBalancedSigns m a b).card : Real) <=
        (Fintype.card I : Real) ^ (-A) := by
  let n : Real := Fintype.card I
  have hDim : 2 <= Fintype.card I := by omega
  have hn : 2 <= n := by dsimp only [n]; exact_mod_cast hDim
  have hMass := hamiltonian_prescribed_balanced_sign_mass a b hab m hm hSize
  have hStepNat : Fintype.card I - 1 + 1 = Fintype.card I :=
    Nat.sub_add_cancel (by omega)
  have hStep : ((Fintype.card I - 1 : Nat) : Real) + 1 = n := by
    dsimp only [n]
    exact_mod_cast hStepNat
  have hPred : ((Fintype.card I - 1 : Nat) : Real) = n - 1 := by linarith only [hStep]
  have hEvent : (Fintype.card (I -> Bool) : Real) <=
      (4 * (n - 1)) * ((hamiltonianPrescribedBalancedSigns m a b).card : Real) := by
    have h : (Fintype.card (I -> Bool) : Real) <=
        (4 : Real) * ((Fintype.card I - 1 : Nat) : Real) *
          ((hamiltonianPrescribedBalancedSigns m a b).card : Real) := by
      exact_mod_cast hMass
    rw [hPred] at h
    exact h
  have hP : 0 <= n ^ (-(A + 3)) := Real.rpow_nonneg (by linarith only [hn]) _
  have h := hamiltonian_finite_conditioned_count B (hamiltonianPrescribedBalancedSigns m a b)
    (n ^ (-(A + 3))) (4 * (n - 1)) hP hTail hEvent
  exact h.trans (hamiltonian_conditioning_power_budget n A (4 * (n - 1)) hn
    (hamiltonian_polynomial_conditioning_budgets n hn).2)

def hamiltonianComplementaryCovarianceBadSigns
    (E : Matrix I I Real) (alpha A : Real) : Finset (I -> Bool) :=
  Finset.univ.filter (fun e =>
    Real.sqrt (2 * (A + 5) * alpha * Real.log (2 * (Fintype.card I : Real))) <
      norm (hamiltonianComplementaryCovariance E
        (hamiltonianCutProjection (hamiltonianSignCut e))))

def hamiltonianComplementaryQuarterBadSigns
    (E : Matrix I I Real) (alpha A : Real) : Finset (I -> Bool) :=
  Finset.univ.filter (fun e =>
    norm E ^ 2 / 4 + (3 / 2 : Real) *
        Real.sqrt (2 * (A + 5) * alpha * Real.log (2 * (Fintype.card I : Real))) <
      norm (E.submatrix (fun i : hamiltonianSignCut e => i.val)
        (fun j : (Compl.compl (hamiltonianSignCut e) : Finset I) => j.val)) ^ 2)

theorem hamiltonian_balanced_covariance_polynomial_tail
    (E : Matrix I I Real) (hE : E.IsHermitian)
    (alpha A : Real) (hAlpha : 0 <= alpha) (hA : 0 < A)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha) (hNorm : norm E <= 1)
    (m : Nat) (hm : 1 <= m) (hSize : Fintype.card I = 2 * m) :
    ((Inter.inter (hamiltonianComplementaryCovarianceBadSigns E alpha A)
      (hamiltonianBalancedSigns (I := I) m)).card : Real) /
        ((hamiltonianBalancedSigns (I := I) m).card : Real) <=
          (Fintype.card I : Real) ^ (-A) := by
  have hRaw := hamiltonian_actual_covariance_uniform_polynomial_tail
    E hE alpha A hAlpha hA hColumn hNorm (by omega)
  exact hamiltonian_balanced_tail_conditioning
    (hamiltonianComplementaryCovarianceBadSigns E alpha A) A m hm hSize hRaw

theorem hamiltonian_prescribed_covariance_polynomial_tail
    (E : Matrix I I Real) (hE : E.IsHermitian)
    (alpha A : Real) (hAlpha : 0 <= alpha) (hA : 0 < A)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha) (hNorm : norm E <= 1)
    (a b : I) (hab : Not (a = b)) (m : Nat) (hm : 1 <= m)
    (hSize : Fintype.card I = 2 * m) :
    ((Inter.inter (hamiltonianComplementaryCovarianceBadSigns E alpha A)
      (hamiltonianPrescribedBalancedSigns m a b)).card : Real) /
        ((hamiltonianPrescribedBalancedSigns m a b).card : Real) <=
          (Fintype.card I : Real) ^ (-A) := by
  have hRaw := hamiltonian_actual_covariance_uniform_polynomial_tail
    E hE alpha A hAlpha hA hColumn hNorm (by omega)
  exact hamiltonian_prescribed_tail_conditioning
    (hamiltonianComplementaryCovarianceBadSigns E alpha A) A a b hab m hm hSize hRaw

theorem hamiltonian_balanced_complementary_quarter_polynomial_tail
    (E : Matrix I I Real) (hE : E.IsHermitian)
    (alpha A : Real) (hAlpha : 0 <= alpha) (hA : 0 < A)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha) (hNorm : norm E <= 1)
    (m : Nat) (hm : 1 <= m) (hSize : Fintype.card I = 2 * m) :
    ((Inter.inter (hamiltonianComplementaryQuarterBadSigns E alpha A)
      (hamiltonianBalancedSigns (I := I) m)).card : Real) /
        ((hamiltonianBalancedSigns (I := I) m).card : Real) <=
          (Fintype.card I : Real) ^ (-A) := by
  have hRaw := hamiltonian_actual_complementary_quarter_polynomial_tail
    E hE alpha A hAlpha hA hColumn hNorm (by omega)
  exact hamiltonian_balanced_tail_conditioning
    (hamiltonianComplementaryQuarterBadSigns E alpha A) A m hm hSize hRaw

theorem hamiltonian_prescribed_complementary_quarter_polynomial_tail
    (E : Matrix I I Real) (hE : E.IsHermitian)
    (alpha A : Real) (hAlpha : 0 <= alpha) (hA : 0 < A)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha) (hNorm : norm E <= 1)
    (a b : I) (hab : Not (a = b)) (m : Nat) (hm : 1 <= m)
    (hSize : Fintype.card I = 2 * m) :
    ((Inter.inter (hamiltonianComplementaryQuarterBadSigns E alpha A)
      (hamiltonianPrescribedBalancedSigns m a b)).card : Real) /
        ((hamiltonianPrescribedBalancedSigns m a b).card : Real) <=
          (Fintype.card I : Real) ^ (-A) := by
  have hRaw := hamiltonian_actual_complementary_quarter_polynomial_tail
    E hE alpha A hAlpha hA hColumn hNorm (by omega)
  exact hamiltonian_prescribed_tail_conditioning
    (hamiltonianComplementaryQuarterBadSigns E alpha A) A a b hab m hm hSize hRaw

end PrimeFactorOscillations
