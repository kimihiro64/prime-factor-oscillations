/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFactorDeletion
import PrimeFactorOscillations.Helpers.HamiltonianPrimeFactorLimits
import PrimeFactorOscillations.Helpers.HamiltonianRegularFactorKernels
import PrimeFactorOscillations.Helpers.HamiltonianResilientNormalization

/-! # Actual locally resilient prime factors in the signed counting domain -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimeResilientRank (m : Nat) : Nat :=
  Nat.floor ((39 / 40 : Real) * hamiltonianPrimeFactorDegree m)

theorem hamiltonian_prime_resilient_factor
    (B : Real) (m : Nat) (hm : 1 <= m)
    (F0 : Finset (Prod (Fin m) (Fin m))) (hBase : HamiltonianPrimeFactorPacket B m F0)
    (hDefect : hamiltonianPrimeFactorDefect B m <= (1 / 1000 : Real))
    (hLarge : 1000 <= hamiltonianPrimeFactorDegree m)
    (hGap : norm (hamiltonianUnweightedPrimeMatrix (2 * m) -
      hamiltonianRealConstantParityMatrix (2 * m)) <= (501 / 1000 : Real))
    (hCut : forall S T : Finset (Fin m),
      (1 / 5 : Real) * hamiltonianPrimeFactorDegree m *
        min ((S.card : Real) + (T.card : Real))
          (((Compl.compl S).card : Real) + ((Compl.compl T).card : Real)) <=
      ((hamiltonianFactorCross (hamiltonianPrimeFactorEdges m) S T).card : Real) +
        ((hamiltonianFactorCross (hamiltonianPrimeFactorEdges m)
          (Compl.compl S) (Compl.compl T)).card : Real))
    (Q : Finset (Prod (Fin m) (Fin m))) (hQE : Q <= hamiltonianPrimeFactorEdges m)
    (hQL : forall a, ((Q.filter (fun e => e.1 = a)).card : Real) <=
      (1 / 1000 : Real) * hamiltonianPrimeFactorDegree m)
    (hQR : forall b, ((Q.filter (fun e => e.2 = b)).card : Real) <=
      (1 / 1000 : Real) * hamiltonianPrimeFactorDegree m) :
    Exists (fun F : Finset (Prod (Fin m) (Fin m)) =>
      F <= hamiltonianPrimeFactorEdges m \ Q /\
      (forall a, (F.filter (fun e => e.1 = a)).card = hamiltonianPrimeResilientRank m) /\
      (forall b, (F.filter (fun e => e.2 = b)).card = hamiltonianPrimeResilientRank m) /\
      norm (centeredKernel (hamiltonianRegularFactorCross (hamiltonianPrimeResilientRank m) F)
        (1 / (m : Real))) <= (3 / 5 : Real)) := by
  have hD := (hamiltonian_prime_factor_scalars m hm).2.1
  have hDefectD := mul_le_mul_of_nonneg_right hDefect hD.le
  have hleft : forall a,
      (1 - (1 / 1000 : Real)) * hamiltonianPrimeFactorDegree m <=
        (((hamiltonianPrimeFactorEdges m).filter (fun e => e.1 = a)).card : Real) /\
      (((hamiltonianPrimeFactorEdges m).filter (fun e => e.1 = a)).card : Real) <=
        (1 + (1 / 1000 : Real)) * hamiltonianPrimeFactorDegree m := by
    intro a
    have hd := hBase.original_left_degree a
    constructor <;> nlinarith only [hd.1, hd.2, hDefectD]
  have hright : forall b,
      (1 - (1 / 1000 : Real)) * hamiltonianPrimeFactorDegree m <=
        (((hamiltonianPrimeFactorEdges m).filter (fun e => e.2 = b)).card : Real) /\
      (((hamiltonianPrimeFactorEdges m).filter (fun e => e.2 = b)).card : Real) <=
        (1 + (1 / 1000 : Real)) * hamiltonianPrimeFactorDegree m := by
    intro b
    have hd := hBase.original_right_degree b
    constructor <;> nlinarith only [hd.1, hd.2, hDefectD]
  have hf := hamiltonian_resilient_factor_floor (hamiltonianPrimeFactorDegree m) hLarge
  change And (1 <= hamiltonianPrimeResilientRank m)
    (And ((97 / 100 : Real) * hamiltonianPrimeFactorDegree m <=
      (hamiltonianPrimeResilientRank m : Real))
    (And ((hamiltonianPrimeResilientRank m : Real) <= hamiltonianPrimeFactorDegree m)
      ((hamiltonianPrimeResilientRank m : Real) <=
        (195 / 199 : Real) * hamiltonianPrimeFactorDegree m))) at hf
  have hRank : (hamiltonianPrimeResilientRank m : Real) <=
      (1 - 2 * ((1 / 1000 : Real) + 1 / 1000) / (1 / 5 - 1 / 1000)) *
        hamiltonianPrimeFactorDegree m := by
    convert hf.2.2.2 using 1 <;> norm_num
  choose F hF hFL hFR hLoss using hamiltonian_regular_factor_after_local_deletion
    (hamiltonianPrimeFactorEdges m) Q hQE (hamiltonianPrimeResilientRank m) rfl
    (hamiltonianPrimeFactorDegree m) (1 / 5) (1 / 1000) (1 / 1000)
    hD (by norm_num) (by norm_num) (by norm_num) (by norm_num) hRank
    hleft hright hQL hQR hCut
  have hPhysicalLoss :
      norm (SMul.smul (hamiltonianPrimeFactorDegree m)
          (hamiltonianUnweightedPrimeMatrix (2 * m)) -
        hamiltonianPrimeFactorAdjacency m F) <=
      (1001 / 1000 : Real) * hamiltonianPrimeFactorDegree m -
        (hamiltonianPrimeResilientRank m : Real) := by
    rw [hamiltonian_prime_factor_full_adjacency m hm,
      hamiltonian_prime_factor_physical_loss]
    convert hLoss using 1 <;> norm_num
  have hU : norm (hamiltonianUnweightedPrimeMatrix (2 * m)) <= (1001 / 1000 : Real) := by
    have hn := hamiltonian_prime_factor_original_norm B m hm F0 hBase
    linarith only [hn, hDefect]
  have hr : 0 < (hamiltonianPrimeResilientRank m : Real) :=
    Nat.cast_pos.mpr (by omega)
  have hNorm := hamiltonian_resilient_normalization
    (hamiltonianUnweightedPrimeMatrix (2 * m)) (hamiltonianPrimeFactorAdjacency m F)
    (hamiltonianPrimeFactorDegree m) (hamiltonianPrimeResilientRank m : Real)
    hD hr hf.2.1 hf.2.2.1 hU hPhysicalLoss
  have hFull : norm (hamiltonianRegularNormalizedAdjacency m (hamiltonianPrimeResilientRank m) F -
      hamiltonianRealConstantParityMatrix (2 * m)) <= (3 / 5 : Real) := by
    have ht := norm_add_le
      (hamiltonianRegularNormalizedAdjacency m (hamiltonianPrimeResilientRank m) F -
        hamiltonianUnweightedPrimeMatrix (2 * m))
      (hamiltonianUnweightedPrimeMatrix (2 * m) - hamiltonianRealConstantParityMatrix (2 * m))
    have heq :
        (hamiltonianRegularNormalizedAdjacency m (hamiltonianPrimeResilientRank m) F -
          hamiltonianUnweightedPrimeMatrix (2 * m)) +
        (hamiltonianUnweightedPrimeMatrix (2 * m) - hamiltonianRealConstantParityMatrix (2 * m)) =
        hamiltonianRegularNormalizedAdjacency m (hamiltonianPrimeResilientRank m) F -
          hamiltonianRealConstantParityMatrix (2 * m) := by abel
    rw [heq] at ht
    change norm (hamiltonianRegularNormalizedAdjacency m (hamiltonianPrimeResilientRank m) F -
      hamiltonianUnweightedPrimeMatrix (2 * m)) <= _ at hNorm
    linarith only [ht, hNorm, hGap]
  refine Exists.intro F (And.intro hF (And.intro hFL (And.intro hFR ?_)))
  rw [hamiltonian_regular_factor_centered_norm m (hamiltonianPrimeResilientRank m) hm F]
  exact hFull

theorem hamiltonian_prime_resilient_entry_cap
    (m : Nat) (hm : 1 <= m) (hLarge : 1000 <= hamiltonianPrimeFactorDegree m)
    (F : Finset (Prod (Fin m) (Fin m))) (i j : Fin m) :
    hamiltonianRegularFactorCross (hamiltonianPrimeResilientRank m) F i j <=
      ((3 / 5 : Real) * Real.log (2 * m : Nat)) * (1 / (m : Real)) := by
  have hf := hamiltonian_resilient_factor_floor (hamiltonianPrimeFactorDegree m) hLarge
  have hr : 0 < (hamiltonianPrimeResilientRank m : Real) := Nat.cast_pos.mpr (by
    have hOne : 1 <= hamiltonianPrimeResilientRank m := hf.1
    omega)
  have hmR : 0 < (m : Real) := Nat.cast_pos.mpr (by omega)
  have hL : 0 < Real.log (2 * m : Nat) := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * m))
  have hDL : hamiltonianPrimeFactorDegree m * Real.log (2 * m : Nat) = (2 : Real) * m := by
    unfold hamiltonianPrimeFactorDegree
    field_simp [ne_of_gt hL]
    push_cast
    ring
  have hLow : (97 / 100 : Real) * hamiltonianPrimeFactorDegree m <=
      (hamiltonianPrimeResilientRank m : Real) := hf.2.1
  have hMult := mul_le_mul_of_nonneg_right hLow hL.le
  have hSignal : (m : Real) <=
      ((3 / 5 : Real) * Real.log (2 * m : Nat)) * (hamiltonianPrimeResilientRank m : Real) := by
    nlinarith only [hMult, hDL, hmR]
  have hInv : 1 / (hamiltonianPrimeResilientRank m : Real) <=
      ((3 / 5 : Real) * Real.log (2 * m : Nat)) * (1 / (m : Real)) := by
    by_contra h
    have ht := mul_lt_mul_of_pos_right (lt_of_not_ge h)
      (mul_pos hmR hr)
    have hOne : (1 / (hamiltonianPrimeResilientRank m : Real)) *
        ((m : Real) * (hamiltonianPrimeResilientRank m : Real)) = (m : Real) := by
      field_simp [ne_of_gt hr]
    have hOther :
        (((3 / 5 : Real) * Real.log (2 * m : Nat)) * (1 / (m : Real))) *
          ((m : Real) * (hamiltonianPrimeResilientRank m : Real)) =
        ((3 / 5 : Real) * Real.log (2 * m : Nat)) * (hamiltonianPrimeResilientRank m : Real) := by
      field_simp [ne_of_gt hmR]
    rw [hOne, hOther] at ht
    exact (not_lt_of_ge hSignal) ht
  unfold hamiltonianRegularFactorCross
  split_ifs <;> simp only [mul_one, mul_zero]
  . exact hInv
  . positivity

theorem hamiltonian_prime_local_resilience_uniform :
    Exists (fun M0 : Nat => And (256 <= M0)
      (forall m : Nat, M0 <= m ->
        forall Q : Finset (Prod (Fin m) (Fin m)),
          Q <= hamiltonianPrimeFactorEdges m ->
          (forall a, ((Q.filter (fun e => e.1 = a)).card : Real) <=
            (1 / 1000 : Real) * hamiltonianPrimeFactorDegree m) ->
          (forall b, ((Q.filter (fun e => e.2 = b)).card : Real) <=
            (1 / 1000 : Real) * hamiltonianPrimeFactorDegree m) ->
          Exists (fun F : Finset (Prod (Fin m) (Fin m)) =>
            F <= hamiltonianPrimeFactorEdges m \ Q /\
            Exists (fun f : Equiv.Perm (Sum (Fin m) (Fin m)) =>
              (hamiltonianPermutationOrbits f).card = 1 /\
              (forall s, Not (hamiltonianFactorAdjacency F (f s) s = 0)) /\
              (forall s, hamiltonianFactorAdjacency Q (f s) s = 0) /\
              (forall s,
                Not ((hamiltonianParityEquiv m) (f s) = (hamiltonianParityEquiv m) s) /\
                Nat.Prime ((((hamiltonianParityEquiv m) (f s)).val + 1) +
                  (((hamiltonianParityEquiv m) s).val + 1))))))) := by
  classical
  choose B hB Mf hMf base hBase using hamiltonian_prime_factor_single_family
  choose Me hMe hError using hamiltonian_prime_factor_error_terminal B (1 / 1000) hB (by norm_num)
  choose Mg hMg hGap using hamiltonian_unweighted_prime_operator_gap (1 / 1000) (by norm_num)
  choose Mk hMk hCut using hamiltonian_prime_factor_cut_uniform
  choose Mc hMc hCount using stochastic_three_fifths_cycle_power_uniform.{0}
  choose Ml hMl hLog using hamiltonian_log_terminal_lower 4000
  let M0 := max Mf (max Me (max Mg (max Mk (max Mc Ml))))
  refine Exists.intro M0 (And.intro (by dsimp only [M0]; omega) ?_)
  intro m hm Q hQE hQL hQR
  have hmf : Mf <= m := by dsimp only [M0] at hm; omega
  have hme : Me <= m := by dsimp only [M0] at hm; omega
  have hmg : Mg <= 2 * m := by dsimp only [M0] at hm; omega
  have hmk : Mk <= m := by dsimp only [M0] at hm; omega
  have hmc : Mc <= m := by dsimp only [M0] at hm; omega
  have hml : Ml <= 2 * m := by dsimp only [M0] at hm; omega
  have hm256 : 256 <= m := by omega
  have hm1 : 1 <= m := by omega
  have hmR : 0 < (m : Real) := Nat.cast_pos.mpr (by omega)
  haveI : NeZero m := { out := by omega }
  have hPacket := hBase m hmf
  have hLpos : 0 < Real.log (2 * m : Nat) := by linarith only [hPacket.log_large]
  have hErr := hError m hme
  have hTail : 0 <= (24 : Real) / Real.log (2 * m : Nat) :=
    div_nonneg (by norm_num) hLpos.le
  have hDefect : hamiltonianPrimeFactorDefect B m <= (1 / 1000 : Real) := by
    linarith only [hErr, hTail, hPacket.defect_positive]
  have hDL : Real.log (2 * m : Nat) / 4 <= hamiltonianPrimeFactorDegree m :=
    hamiltonian_logarithmic_degree_lower (2 * m : Nat) (by exact_mod_cast (by omega : 1 < 2 * m))
  have hLarge : 1000 <= hamiltonianPrimeFactorDegree m := by
    linarith only [hDL, hLog (2 * m) hml]
  have hG : norm (hamiltonianUnweightedPrimeMatrix (2 * m) -
      hamiltonianRealConstantParityMatrix (2 * m)) <= (501 / 1000 : Real) := by
    convert hGap (2 * m) hmg using 1 <;> norm_num
  choose F hF hFL hFR hNorm using hamiltonian_prime_resilient_factor B m hm1 (base m)
    hPacket hDefect hLarge hG (hCut m hmk) Q hQE hQL hQR
  have hf := hamiltonian_resilient_factor_floor (hamiltonianPrimeFactorDegree m) hLarge
  have hr : 0 < hamiltonianPrimeResilientRank m := by
    have hp : 1 <= hamiltonianPrimeResilientRank m := hf.1
    omega
  have hStoch := hamiltonian_regular_factor_cross_stochastic m
    (hamiltonianPrimeResilientRank m) hr F hFL hFR
  let T := hamiltonianRegularFactorCross (hamiltonianPrimeResilientRank m) F
  let a := (3 / 5 : Real) * Real.log (2 * m : Nat)
  have hq : (Fintype.card (Fin m) : Real) * (1 / (m : Real)) = 1 := by
    simp only [Fintype.card_fin]
    field_simp [ne_of_gt hmR]
  have ha : 1 <= a := by dsimp only [a]; linarith only [hPacket.log_large]
  have hNonnegative : forall i j, 0 <= T i j := by
    intro i j
    dsimp only [T, hamiltonianRegularFactorCross]
    positivity
  have hCap : forall i j, T i j <= a * (1 / (m : Real)) :=
    hamiltonian_prime_resilient_entry_cap m hm1 hLarge F
  have hSplit : Real.log (2 * m : Nat) = Real.log 2 + Real.log (m : Real) := by
    push_cast
    exact Real.log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt hmR)
  have hTwo : Real.log (2 : Real) <= 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith only [h]
  have hDensity : a - 1 <= (3 / 5 : Real) * Real.log (Fintype.card (Fin m) : Real) := by
    simp only [Fintype.card_fin]
    dsimp only [a]
    linarith only [hSplit, hTwo]
  have hResult := hCount (Fin m) (by simpa only [Fintype.card_fin] using hmc)
    T (1 / (m : Real)) a hq ha hStoch.1 hStoch.2 hNonnegative hCap hNorm hDensity
  simp only [Fintype.card_fin] at hResult
  have hPow : (m : Real) ^ (-3 / 5 : Real) < 1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt
      (by exact_mod_cast (by omega : 1 < m) : (1 : Real) < (m : Real))
      (by norm_num : (-3 / 5 : Real) < 0)
    simpa only [Real.rpow_zero] using h
  have hLower := (abs_le.mp hResult).1
  have hPositive : 0 < hamiltonianBipartiteCountRatio T := by
    linarith only [hLower, hPow]
  choose f hOne hEdges using hamiltonian_regular_factor_cycle_witness m
    (hamiltonianPrimeResilientRank m) F hPositive
  have hMask : forall s t : Sum (Fin m) (Fin m),
      Not (hamiltonianFactorAdjacency F s t = 0) ->
        hamiltonianFactorAdjacency Q s t = 0 := by
    intro s t hn
    cases s with
    | inl u =>
      cases t with
      | inl v => simp [hamiltonianFactorAdjacency] at hn
      | inr v =>
        have hmem : Membership.mem F (u, v) := by
          by_contra h
          simp [hamiltonianFactorAdjacency, h] at hn
        have hNot := (Finset.mem_sdiff.mp (hF hmem)).2
        simp [hamiltonianFactorAdjacency, hNot]
    | inr v =>
      cases t with
      | inl u =>
        have hmem : Membership.mem F (u, v) := by
          by_contra h
          simp [hamiltonianFactorAdjacency, h] at hn
        have hNot := (Finset.mem_sdiff.mp (hF hmem)).2
        simp [hamiltonianFactorAdjacency, hNot]
      | inr u => simp [hamiltonianFactorAdjacency] at hn
  refine Exists.intro F (And.intro hF (Exists.intro f
    (And.intro hOne (And.intro hEdges (And.intro (fun s => hMask (f s) s (hEdges s)) ?_)))))
  intro s
  have hFE : F <= hamiltonianPrimeFactorEdges m :=
    fun e he => (Finset.mem_sdiff.mp (hF he)).1
  have hPhysical : Not (hamiltonianPrimeFactorAdjacency m F
      ((hamiltonianParityEquiv m) (f s)) ((hamiltonianParityEquiv m) s) = 0) := by
    simpa only [hamiltonianPrimeFactorAdjacency, Matrix.submatrix_apply,
      Equiv.symm_apply_apply] using hEdges s
  exact hamiltonian_prime_factor_physical_support m hm1 F hFE
    ((hamiltonianParityEquiv m) (f s)) ((hamiltonianParityEquiv m) s) hPhysical

end PrimeFactorOscillations.LPF
