/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeFactorHeadline
import PrimeFactorOscillations.Helpers.HamiltonianQuarterRoundingLimits

/-! # Actual simple prime-supported rounding at the prescribed degree -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianQuarterPrimeRoundingError (B : Real) (m : Nat) : Real :=
  16 * Real.sqrt (Real.log (4 * (m : Real)) /
      (hamiltonianQuarterPrimeDegree m : Real)) +
    hamiltonianForbiddenObservableCost (1 / 4) *
      ((hamiltonianQuarterPrimeDegree m : Real) *
        (1 / (hamiltonianPrimeFactorRank B m : Real)) * Real.log (4 * (m : Real)))

theorem hamiltonian_prime_factor_inverse_entry_mass
    (B : Real) (m : Nat) (hm : 1 <= m)
    (F : Finset (Prod (Fin m) (Fin m))) (h : HamiltonianPrimeFactorPacket B m F) :
    0 < (hamiltonianPrimeFactorRank B m : Real) /\
      (m : Real) * (1 / (hamiltonianPrimeFactorRank B m : Real)) <=
        Real.log (2 * (m : Real)) := by
  let r := (hamiltonianPrimeFactorRank B m : Real)
  let ell := Real.log (2 * (m : Real))
  have hr : 0 < r := by
    change (0 : Real) < (hamiltonianPrimeFactorRank B m : Real)
    exact_mod_cast (show 0 < hamiltonianPrimeFactorRank B m by have hh := h.rank_positive; omega)
  have hEll : 0 < ell := Real.log_pos (by
    have hM : (1 : Real) <= (m : Real) := by exact_mod_cast hm
    linarith only [hM])
  have hD : (hamiltonianPrimeFactorDegree m / 2) * ell = (m : Real) := by
    simp only [hamiltonianPrimeFactorDegree, Nat.cast_mul, Nat.cast_ofNat]
    change ((2 * (m : Real) / ell) / 2) * ell = (m : Real)
    field_simp [ne_of_gt hEll]
    <;> ring
  have hCross : (m : Real) <= r * ell := by
    have hHalf := mul_le_mul_of_nonneg_right h.rank_half hEll.le
    rw [hD] at hHalf
    exact hHalf
  refine And.intro hr ?_
  calc
    _ = (m : Real) / r := by ring
    _ <= (r * ell) / r := div_le_div_of_nonneg_right hCross hr.le
    _ = ell := by field_simp [ne_of_gt hr]

theorem hamiltonian_quarter_prime_rounding_step
    (B : Real) (m : Nat) (hm : 256 <= m)
    (F : Finset (Prod (Fin m) (Fin m))) (h : HamiltonianPrimeFactorPacket B m F)
    (hGap : norm (hamiltonianPrimeNormalizedFactor B m F -
      hamiltonianRealConstantParityMatrix (2 * m)) <= (3 / 4 : Real))
    (hSmall : ((hamiltonianQuarterPrimeDegree m : Real) *
        (1 / (hamiltonianPrimeFactorRank B m : Real))) *
          Real.log (4 * (m : Real)) ^ 2 <= hamiltonianForbiddenRepairSmall (1 / 4)) :
    exists E : Finset (Prod (Fin m) (Fin m)),
      E <= F /\
      (forall i, (E.filter (fun e => e.1 = i)).card = hamiltonianQuarterPrimeDegree m) /\
      (forall j, (E.filter (fun e => e.2 = j)).card = hamiltonianQuarterPrimeDegree m) /\
      norm (SMul.smul (1 / (hamiltonianQuarterPrimeDegree m : Real))
        (hamiltonianFactorAdjacency E) -
          bipartiteLift (hamiltonianPrimeRegularCross B m F)) <=
            hamiltonianQuarterPrimeRoundingError B m := by
  classical
  have hm1 : 1 <= m := by omega
  letI : NeZero m := NeZero.mk (by omega)
  let alpha : Real := 1 / (hamiltonianPrimeFactorRank B m : Real)
  have hr := (hamiltonian_prime_factor_inverse_entry_mass B m hm1 F h).1
  have ha : 0 <= alpha := one_div_nonneg.mpr hr.le
  have hP (i j : Fin m) : 0 <= hamiltonianPrimeRegularCross B m F i j := by
    change 0 <= alpha * (if Membership.mem F (i, j) then 1 else 0)
    split_ifs <;> simp only [mul_one, mul_zero] <;> first | exact ha | exact le_refl _
  have hCap (i j : Fin m) : hamiltonianPrimeRegularCross B m F i j <= alpha := by
    change alpha * (if Membership.mem F (i, j) then 1 else 0) <= alpha
    split_ifs <;> simp only [mul_one, mul_zero] <;> first | exact le_refl _ | exact ha
  have hStoch := hamiltonian_prime_regular_cross_stochastic B m F h
  have hCentered :
      norm (centeredKernel (hamiltonianPrimeRegularCross B m F)
        (1 / (Fintype.card (Fin m) : Real))) <= 1 - (1 / 4 : Real) := by
    rw [Fintype.card_fin, hamiltonian_prime_regular_cross_centered_norm B m hm1 F]
    linarith only [hGap]
  have hSmall' : ((hamiltonianQuarterPrimeDegree m : Real) * alpha) *
      Real.log (4 * (Fintype.card (Fin m) : Real)) ^ 2 <=
        hamiltonianForbiddenRepairSmall (1 / 4) := by
    simpa only [Fintype.card_fin] using hSmall
  cases hamiltonian_supported_simple_rounding (hamiltonianPrimeRegularCross B m F) {} {}
      (1 / 4) alpha (hamiltonianQuarterPrimeDegree m)
      (hamiltonian_quarter_prime_degree_bounds m hm).1
      (by norm_num) (by norm_num) ha hP hCap hStoch.1 hStoch.2 hCentered hSmall' with
  | intro E hE =>
    refine Exists.intro E (And.intro ?_ (And.intro hE.2.1 (And.intro hE.2.2.1 ?_)))
    . intro e he
      by_contra hNot
      have hPositive := hE.1 e he
      simp [hamiltonianPrimeRegularCross, hNot] at hPositive
    . have hNorm := hE.2.2.2.1
      simpa only [hamiltonianQuarterPrimeRoundingError, hamiltonianRoundingDriftCost,
        Fintype.card_fin, alpha, mul_assoc, mul_left_comm, mul_comm] using hNorm

end PrimeFactorOscillations.LPF
