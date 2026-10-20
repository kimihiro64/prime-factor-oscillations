/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.DetectorPackets.IndependentMomentInput

/-!
# FlexibleHighBudget

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-!
Actual fine HighData can be chosen with a tight auxiliary-epsilon cost.
The fixed central saving below is independent of beta-7/8. No improved
global zero-free boundary or perturbed-scale high theorem is asserted.
-/


noncomputable section

open scoped Classical BigOperators
open OAI.SevenEighths

namespace PrimeFactorOscillations.FlexibleHighBudget

open Parameters ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands

def centralCost {Delta : Real} (D : HighData Delta) (saving : Real) : Real :=
  @HighData.rec Delta (fun _ => Real)
    (fun t N _ _ epsilon e _ _ eps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      (13 / 16 : Real) * (159 * epsilon + t + t + 7 * t) + 2 * t +
        (3 / 2) * (2 * t) +
        (26 * e + ((N : Real) + 8) * eps + t + t / 6) +
        (t + t + t) + saving) D

theorem exists_tight_data (Delta : Real) (hDelta : 0 < Delta)
    (mesh : Real -> Real) (hmesh : forall t : Real, 0 < t -> 0 < mesh t) :
    exists D : HighData Delta,
      (forall j, D.ell j <= mesh D.t / 200) /\
      ((D.N : Real) + 8) * D.eps <= D.t /\
      centralCost D (1 / 20000) <= (49 / 440640 : Real) := by
  refine Exists.elim (exists_high_data_fine Delta hDelta mesh hmesh) ?_
  intro D0 hfine
  cases D0 with
  | mk t N ell rmin epsilon e kappa cost eps sigma t_pos t_delta t_small slots_pos slots_injective slots_sum slots_bounds rmin_pos epsilon_pos epsilon_small epsilon_gap e_pos e_small kappa_pos kappa_small cost_pos eps_pos eps_small sigma_pos detector_budget phase_budget count_budget central_budget geometric_budget principal_budget window_budget floor_budget high_saving height_choice =>
    have hb := slots_bounds (Fin.mk 0 slots_pos)
    have hrone : rmin <= 1 := by
      linarith only [hb.2.1, hb.2.2, t_small]
    have hEpsilon : epsilon <= t := by
      have hm := mul_le_mul_of_nonneg_right hrone t_pos.le
      nlinarith only [epsilon_gap, hm]
    have heT : e <= t := by
      linarith only [detector_budget, kappa_pos, cost_pos, hEpsilon, t_pos]
    have hden : 0 < (N : Real) + 8 := by positivity
    let epsNew := min eps (t / ((N : Real) + 8))
    have hNewPos : 0 < epsNew :=
      lt_min eps_pos (div_pos t_pos hden)
    have hNewLe : epsNew <= eps := min_le_left _ _
    have hNewSmall : epsNew <= 1 := hNewLe.trans eps_small
    have hNewCost : ((N : Real) + 8) * epsNew <= t := by
      calc
        ((N : Real) + 8) * epsNew <=
            ((N : Real) + 8) * (t / ((N : Real) + 8)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hden.le
        _ = t := by field_simp [ne_of_gt hden]
    have hMono := mul_le_mul_of_nonneg_left hNewLe hden.le
    have hCentralNew :
        (13 / 16 : Real) * (159 * epsilon + t + t + 7 * t) + 2 * t +
          (3 / 2) * (2 * t) +
          (26 * e + ((N : Real) + 8) * epsNew + t + t / 6) +
          (t + t + t) + t <= 49 / 440640 := by
      linarith only [central_budget, hMono]
    have hFloorNew :
        2 * t + 26 * e + ((N : Real) + 8) * epsNew + t + t / 6 +
          t / 8 + sigma <= 7 / 1200 := by
      linarith only [floor_budget, hMono]
    have hHeightNew :
        forall J : Real, 0 <= J ->
          exists tau : Real, 0 < tau /\ tau < (1 / 200 : Real) / 2 /\
            4 * tau < (1 / 200 : Real) * cost /\ tau < t /\
            2 * tau * (1 + J) <= t /\ tau * (2 + 4 * epsNew) < t := by
      intro J hJ
      have hex := height_choice J hJ
      let tau := Classical.choose hex
      have hTau := Classical.choose_spec hex
      have hTauLe : tau * (2 + 4 * epsNew) <= tau * (2 + 4 * eps) := by
        apply mul_le_mul_of_nonneg_left ?_ (show 0 <= tau from hTau.1.le)
        linarith only [hNewLe]
      exact Exists.intro tau
        (And.intro hTau.1 (And.intro hTau.2.1 (And.intro hTau.2.2.1
          (And.intro hTau.2.2.2.1 (And.intro hTau.2.2.2.2.1
            (lt_of_le_of_lt hTauLe hTau.2.2.2.2.2))))))
    let D : HighData Delta := @HighData.mk Delta t N ell rmin epsilon e kappa cost epsNew sigma t_pos t_delta t_small slots_pos slots_injective slots_sum slots_bounds rmin_pos epsilon_pos epsilon_small epsilon_gap e_pos e_small kappa_pos kappa_small cost_pos hNewPos hNewSmall sigma_pos detector_budget phase_budget count_budget hCentralNew geometric_budget principal_budget window_budget hFloorNew high_saving hHeightNew
    have hBudget : centralCost D (1 / 20000) <= (49 / 440640 : Real) := by
      dsimp only [centralCost, D]
      nlinarith only [hEpsilon, heT, hNewCost, t_small]
    exact Exists.intro D (And.intro hfine (And.intro hNewCost hBudget))

theorem central_exponent_margin (Delta t : Real)
    (hDelta : Delta <= (1 / 100000 : Real))
    (ht : t <= (1 / 100000000 : Real)) :
    (3 / 16 : Real) + Delta - 1 / 20000 + t / 8 + t / 8 <=
      3 / 16 - 1 / 30000 := by
  linarith only [hDelta, ht]

end PrimeFactorOscillations.FlexibleHighBudget
