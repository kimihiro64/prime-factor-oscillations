/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeFactorNormalization

/-! # Complete density and spectral budgets through every fixed packing margin -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianPackingModePrecision (kappa : Real) : Real :=
  min (1 / 100) ((1 / 2 - 4 * kappa) / 2)

def hamiltonianPackingCenteredRho (kappa : Real) : Real :=
  (1 / 2 + hamiltonianPackingModePrecision kappa + 2 * kappa) / (1 - 2 * kappa)

theorem hamiltonian_centered_deletion_ratio_monotone
    (gamma alpha beta : Real) (hg : 0 <= gamma) (ha : 0 <= alpha)
    (hab : alpha <= beta) (hb : beta < 1) :
    (gamma + alpha) / (1 - alpha) <= (gamma + beta) / (1 - beta) := by
  have hA : 0 < 1 - alpha := by linarith only [hab, hb]
  have hB : 0 < 1 - beta := sub_pos.mpr hb
  calc
    _ <= (gamma + beta) / (1 - alpha) :=
      div_le_div_of_nonneg_right (add_le_add (le_refl gamma) hab) (le_of_lt hA)
    _ <= _ := div_le_div_of_nonneg_left (by linarith only [hg, ha, hab]) hB
      (sub_le_sub_left hab 1)

theorem hamiltonian_packing_margin_budget
    (kappa : Real) (hk0 : 0 <= kappa) (hk1 : kappa < (1 / 8 : Real)) :
    0 < hamiltonianPackingModePrecision kappa /\
      hamiltonianPackingModePrecision kappa <= (1 / 100 : Real) /\
      0 <= hamiltonianPackingCenteredRho kappa /\
      hamiltonianPackingCenteredRho kappa < 1 /\
      forall alpha : Real, 0 <= alpha -> alpha <= 2 * kappa ->
        alpha <= (1 / 4 : Real) /\
          ((1 / 2 : Real) + hamiltonianPackingModePrecision kappa + alpha) / (1 - alpha) <=
            hamiltonianPackingCenteredRho kappa := by
  have he : 0 < (1 / 2 - 4 * kappa) / 2 := by linarith only [hk1]
  have hEps : 0 < hamiltonianPackingModePrecision kappa :=
    lt_min (by norm_num) he
  have hEpsUpper := min_le_left (1 / 100 : Real) ((1 / 2 - 4 * kappa) / 2)
  have hEpsMargin := min_le_right (1 / 100 : Real) ((1 / 2 - 4 * kappa) / 2)
  have hGap : 0 < 1 - 2 * kappa := by linarith only [hk1]
  have hTop : 0 <= 1 / 2 + hamiltonianPackingModePrecision kappa + 2 * kappa := by
    linarith only [hEps, hk0]
  have hRho0 : 0 <= hamiltonianPackingCenteredRho kappa := div_nonneg hTop hGap.le
  have hNumerator : 1 / 2 + hamiltonianPackingModePrecision kappa + 2 * kappa <
      1 - 2 * kappa := by
    change hamiltonianPackingModePrecision kappa <= (1 / 2 - 4 * kappa) / 2 at hEpsMargin
    linarith only [hEpsMargin, hk1]
  have hRho1 : hamiltonianPackingCenteredRho kappa < 1 := by
    calc
      _ < (1 - 2 * kappa) / (1 - 2 * kappa) := div_lt_div_of_pos_right hNumerator hGap
      _ = 1 := by field_simp
  refine And.intro hEps (And.intro hEpsUpper (And.intro hRho0 (And.intro hRho1 ?_)))
  intro alpha ha hab
  refine And.intro (by linarith only [hab, hk1]) ?_
  exact hamiltonian_centered_deletion_ratio_monotone
    (1 / 2 + hamiltonianPackingModePrecision kappa) alpha (2 * kappa)
    (by linarith only [hEps]) ha hab (by linarith only [hk1])

theorem hamiltonian_prime_packing_density_budget
    (m : Nat) (D r d : Real) (hm : 1 <= m) (hD : 0 < D) (hd : 0 < d)
    (hScale : D * Real.log (2 * (m : Real)) = 2 * (m : Real))
    (hr : (99 / 100 : Real) * D <= r) (hRemain : (3 / 4 : Real) * r <= d) :
    (m : Real) / d <= 1 + (7 / 10 : Real) * Real.log (m : Real) := by
  have hmR : (1 : Real) <= (m : Real) := by exact_mod_cast hm
  have hmPos : (0 : Real) < (m : Real) := by linarith only [hmR]
  have hL : 0 <= Real.log (2 * (m : Real)) :=
    Real.log_nonneg (by linarith only [hmR])
  have hLower : (297 / 400 : Real) * D <= d := by linarith only [hr, hRemain]
  have hMul := mul_le_mul_of_nonneg_right hLower
    (mul_nonneg (by norm_num : (0 : Real) <= 200 / 297) hL)
  have hMass : (m : Real) <= d * ((200 / 297 : Real) * Real.log (2 * (m : Real))) := by
    nlinarith only [hMul, hScale]
  have hDensity : (m : Real) / d <= (200 / 297 : Real) * Real.log (2 * (m : Real)) := by
    calc
      _ <= (d * ((200 / 297 : Real) * Real.log (2 * (m : Real)))) / d :=
        div_le_div_of_nonneg_right hMass hd.le
      _ = _ := by field_simp
  have hLog0 : 0 <= Real.log (m : Real) := Real.log_nonneg hmR
  have hLog2 : Real.log (2 : Real) <= 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith only [h]
  have hSplit : Real.log (2 * (m : Real)) = Real.log 2 + Real.log (m : Real) :=
    Real.log_mul (by norm_num) (ne_of_gt hmPos)
  exact hDensity.trans (by linarith only [hLog0, hLog2, hSplit])

end PrimeFactorOscillations
