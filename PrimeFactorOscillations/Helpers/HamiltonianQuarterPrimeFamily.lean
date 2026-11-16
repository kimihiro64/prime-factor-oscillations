/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianQuarterPrimeRounding

/-! # One prime-supported quarter-degree family with a vanishing spectral error -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianQuarterPrimeMatrix (m : Nat)
    (E : Finset (Prod (Fin m) (Fin m))) : Matrix (Fin (2 * m)) (Fin (2 * m)) Real :=
  SMul.smul (1 / (hamiltonianQuarterPrimeDegree m : Real))
    (hamiltonianPrimeFactorAdjacency m E)

theorem hamiltonian_quarter_prime_physical_error
    (B : Real) (m : Nat) (F E : Finset (Prod (Fin m) (Fin m))) :
    norm (hamiltonianQuarterPrimeMatrix m E - hamiltonianPrimeNormalizedFactor B m F) =
      norm (SMul.smul (1 / (hamiltonianQuarterPrimeDegree m : Real))
        (hamiltonianFactorAdjacency E) -
          bipartiteLift (hamiltonianPrimeRegularCross B m F)) := by
  let e := hamiltonianParityEquiv m
  have hPull : (hamiltonianQuarterPrimeMatrix m E -
      hamiltonianPrimeNormalizedFactor B m F).submatrix e e =
        SMul.smul (1 / (hamiltonianQuarterPrimeDegree m : Real))
          (hamiltonianFactorAdjacency E) -
            bipartiteLift (hamiltonianPrimeRegularCross B m F) := by
    change (hamiltonianQuarterPrimeMatrix m E).submatrix e e -
      (hamiltonianPrimeNormalizedFactor B m F).submatrix e e = _
    rw [hamiltonian_prime_regular_cross_reindex]
    congr 1
    ext i j
    change (1 / (hamiltonianQuarterPrimeDegree m : Real)) *
        hamiltonianFactorAdjacency E (e.symm (e i)) (e.symm (e j)) =
      (1 / (hamiltonianQuarterPrimeDegree m : Real)) * hamiltonianFactorAdjacency E i j
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [<- hPull, hamiltonian_reindex_matrix_norm]

theorem hamiltonian_quarter_prime_factor_family :
    exists M0 : Nat, 256 <= M0 /\
      exists E : (m : Nat) -> Finset (Prod (Fin m) (Fin m)),
        (forall m : Nat, M0 <= m ->
          E m <= hamiltonianPrimeFactorEdges m /\
          (forall i, ((E m).filter (fun e => e.1 = i)).card =
            hamiltonianQuarterPrimeDegree m) /\
          (forall j, ((E m).filter (fun e => e.2 = j)).card =
            hamiltonianQuarterPrimeDegree m)) /\
        (forall eta : Real, 0 < eta -> exists M : Nat, M0 <= M /\
          forall m : Nat, M <= m ->
            norm (hamiltonianQuarterPrimeMatrix m (E m) -
              hamiltonianRealConstantParityMatrix (2 * m)) <= (1 / 2 : Real) + eta) := by
  classical
  choose B hB A hA F P hReference hWindows using
    hamiltonian_prime_near_optimal_factor_family
  choose W hW hFixed using hWindows (1 / 4) (by norm_num)
  let c := hamiltonianForbiddenRepairSmall (1 / 4)
  let C := hamiltonianForbiddenObservableCost (1 / 4)
  have hc : 0 < c :=
    (hamiltonian_forbidden_repair_constants_positive (1 / 4) (by norm_num) (by norm_num)).1
  have hC : 0 < C :=
    hamiltonian_forbidden_observable_constant_positive (1 / 4) (by norm_num) (by norm_num)
  choose T hT hBudgets using
    hamiltonian_quarter_rounding_budgets_terminal c C 1 hc hC (by norm_num)
  let M0 := max W T
  have hM0 : 256 <= M0 := hT.trans (le_max_right _ _)
  have hEach (m : Nat) (hm : M0 <= m) :
      exists E : Finset (Prod (Fin m) (Fin m)),
        E <= F m /\
        (forall i, (E.filter (fun e => e.1 = i)).card = hamiltonianQuarterPrimeDegree m) /\
        (forall j, (E.filter (fun e => e.2 = j)).card = hamiltonianQuarterPrimeDegree m) /\
        norm (hamiltonianQuarterPrimeMatrix m E - hamiltonianPrimeNormalizedFactor B m (F m)) <=
          hamiltonianQuarterPrimeRoundingError B m := by
    have hmW : W <= m := (le_max_left _ _).trans hm
    have hmT : T <= m := (le_max_right _ _).trans hm
    have hmA : A <= m := hW.trans hmW
    have hm256 : 256 <= m := hM0.trans hm
    have hf := (hReference m hmA).factor_packet
    have hMass := hamiltonian_prime_factor_inverse_entry_mass B m (by omega) (F m) hf
    have hSmall := (hBudgets m hmT _ (one_div_nonneg.mpr hMass.1.le) hMass.2).1
    have hGap := (hFixed m hmW).factor_gap
    cases hamiltonian_quarter_prime_rounding_step B m hm256 (F m) hf
        (by linarith only [hGap]) hSmall with
    | intro E hE =>
      refine Exists.intro E (And.intro hE.1 (And.intro hE.2.1 (And.intro hE.2.2.1 ?_)))
      rw [hamiltonian_quarter_prime_physical_error]
      exact hE.2.2.2
  choose K hK using hEach
  let E : (m : Nat) -> Finset (Prod (Fin m) (Fin m)) :=
    fun m => if h : M0 <= m then K m h else {}
  have hChosen (m : Nat) (hm : M0 <= m) :
      E m <= F m /\
        (forall i, ((E m).filter (fun e => e.1 = i)).card = hamiltonianQuarterPrimeDegree m) /\
        (forall j, ((E m).filter (fun e => e.2 = j)).card = hamiltonianQuarterPrimeDegree m) /\
        norm (hamiltonianQuarterPrimeMatrix m (E m) - hamiltonianPrimeNormalizedFactor B m (F m)) <=
          hamiltonianQuarterPrimeRoundingError B m := by
    simpa only [E, dif_pos hm] using hK m hm
  refine Exists.intro M0 (And.intro hM0 (Exists.intro E (And.intro ?_ ?_)))
  . intro m hm
    have hmA : A <= m := hW.trans ((le_max_left W T).trans hm)
    have he := hChosen m hm
    exact And.intro (he.1.trans (hReference m hmA).factor_packet.subset_prime)
      (And.intro he.2.1 he.2.2.1)
  . intro eta hEta
    have hHalf : 0 < eta / 2 := div_pos hEta (by norm_num)
    choose U hU hWindow using hWindows (eta / 2) hHalf
    choose V hV hError using hamiltonian_quarter_rounding_budgets_terminal c C
      (eta / 2) hc hC hHalf
    let M := max M0 (max U V)
    refine Exists.intro M (And.intro (le_max_left _ _) ?_)
    intro m hm
    have hm0 : M0 <= m := (le_max_left _ _).trans hm
    have hmU : U <= m := by dsimp [M] at hm; omega
    have hmV : V <= m := by dsimp [M] at hm; omega
    have hmA : A <= m := hU.trans hmU
    have hf := (hReference m hmA).factor_packet
    have hMass := hamiltonian_prime_factor_inverse_entry_mass B m (by omega) (F m) hf
    have hErr : hamiltonianQuarterPrimeRoundingError B m <= eta / 2 :=
      (hError m hmV _ (one_div_nonneg.mpr hMass.1.le) hMass.2).2
    have hNorm := (hChosen m hm0).2.2.2
    have hGap := (hWindow m hmU).factor_gap
    have hTri := norm_add_le
      (hamiltonianQuarterPrimeMatrix m (E m) - hamiltonianPrimeNormalizedFactor B m (F m))
      (hamiltonianPrimeNormalizedFactor B m (F m) -
        hamiltonianRealConstantParityMatrix (2 * m))
    have hId :
        (hamiltonianQuarterPrimeMatrix m (E m) - hamiltonianPrimeNormalizedFactor B m (F m)) +
        (hamiltonianPrimeNormalizedFactor B m (F m) -
          hamiltonianRealConstantParityMatrix (2 * m)) =
        hamiltonianQuarterPrimeMatrix m (E m) -
          hamiltonianRealConstantParityMatrix (2 * m) := by abel
    rw [hId] at hTri
    linarith only [hTri, hNorm, hErr, hGap]

end PrimeFactorOscillations.LPF
