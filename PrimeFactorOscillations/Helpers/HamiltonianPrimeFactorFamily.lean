/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFactorFloor
import PrimeFactorOscillations.Helpers.HamiltonianPrimeStochasticScaling

/-!
# One integral prime-factor family with a simultaneous shrinking defect

The degree rate has one fixed terminal threshold. No moving parameter is
substituted into the eventual threshold of a fixed-parameter theorem.
-/

set_option autoImplicit false
set_option Elab.async false

open Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimeFactorDefect (B : Real) (m : Nat) : Real :=
  B / Real.sqrt (Real.log (2 * m : Nat))

def hamiltonianPrimeFactorRank (B : Real) (m : Nat) : Nat :=
  Nat.floor ((1 - 10 * hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m)

structure HamiltonianPrimeFactorPacket (B : Real) (m : Nat)
    (F : Finset (Prod (Fin m) (Fin m))) : Prop where
  log_large : 64 <= Real.log (2 * m : Nat)
  defect_positive : 0 < hamiltonianPrimeFactorDefect B m
  defect_small : hamiltonianPrimeFactorDefect B m <= (1 / 100 : Real)
  degree_lower : 16 <= hamiltonianPrimeFactorDegree m
  original_left_degree : forall a : Fin m,
    (1 - hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m <=
      (((hamiltonianPrimeFactorEdges m).filter (fun e => e.1 = a)).card : Real) /\
    (((hamiltonianPrimeFactorEdges m).filter (fun e => e.1 = a)).card : Real) <=
      (1 + hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m
  original_right_degree : forall b : Fin m,
    (1 - hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m <=
      (((hamiltonianPrimeFactorEdges m).filter (fun e => e.2 = b)).card : Real) /\
    (((hamiltonianPrimeFactorEdges m).filter (fun e => e.2 = b)).card : Real) <=
      (1 + hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m
  rank_positive : 1 <= hamiltonianPrimeFactorRank B m
  subset_prime : F <= hamiltonianPrimeFactorEdges m
  left_regular : forall a, (F.filter (fun e => e.1 = a)).card = hamiltonianPrimeFactorRank B m
  right_regular : forall b, (F.filter (fun e => e.2 = b)).card = hamiltonianPrimeFactorRank B m
  adjacency_loss :
    norm (hamiltonianPrimeFactorAdjacency m (hamiltonianPrimeFactorEdges m) -
      hamiltonianPrimeFactorAdjacency m F) <=
      (1 + hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m -
        (hamiltonianPrimeFactorRank B m : Real)
  rank_half : hamiltonianPrimeFactorDegree m / 2 <= (hamiltonianPrimeFactorRank B m : Real)
  rank_upper : (hamiltonianPrimeFactorRank B m : Real) <= hamiltonianPrimeFactorDegree m
  relative_rank :
    abs ((hamiltonianPrimeFactorRank B m : Real) / hamiltonianPrimeFactorDegree m - 1) <=
      10 * hamiltonianPrimeFactorDefect B m + 4 / Real.log (2 * m : Nat)

theorem hamiltonian_prime_factor_simultaneous_packets :
    Exists (fun B : Real => And (0 < B)
      (Exists (fun M0 : Nat => And (256 <= M0)
        (forall m : Nat, M0 <= m ->
          Exists (fun F : Finset (Prod (Fin m) (Fin m)) =>
            HamiltonianPrimeFactorPacket B m F))))) := by
  choose B hB Md hMd hdegree using hamiltonian_prime_cross_degree_sqrt
  choose Mc hMc hcut using hamiltonian_prime_factor_cut_uniform
  choose Ml hMl hlog using hamiltonian_log_terminal_lower (max 64 ((100 * B) ^ 2))
  let M0 := max Md (max Mc Ml)
  refine Exists.intro B (And.intro hB (Exists.intro M0 (And.intro ?_ ?_)))
  . dsimp only [M0]
    omega
  . intro m hm
    have hmd : Md <= m := by dsimp only [M0] at hm; omega
    have hmc : Mc <= m := by dsimp only [M0] at hm; omega
    have hml : Ml <= 2 * m := by dsimp only [M0] at hm; omega
    have hm1 : 1 <= m := by omega
    have hd := hdegree m hmd
    have hL : 64 <= Real.log (2 * m : Nat) := hd.1
    have hLpos : 0 < Real.log (2 * m : Nat) := by linarith only [hL]
    have hroot : 0 < Real.sqrt (Real.log (2 * m : Nat)) := Real.sqrt_pos.mpr hLpos
    have hSquare : (100 * B) ^ 2 <= Real.log (2 * m : Nat) :=
      (le_max_right _ _).trans (hlog (2 * m) hml)
    have hRootLower : 100 * B <= Real.sqrt (Real.log (2 * m : Nat)) := by
      nlinarith only [hSquare, Real.sq_sqrt (le_of_lt hLpos),
        Real.sqrt_nonneg (Real.log (2 * m : Nat)), hB]
    have heps : 0 < hamiltonianPrimeFactorDefect B m := div_pos hB hroot
    have hepsSmall : hamiltonianPrimeFactorDefect B m <= (1 / 100 : Real) := by
      have hden : 0 < 100 * B := mul_pos (by norm_num) hB
      have h := div_le_div_of_nonneg_left (le_of_lt hB) hden hRootLower
      have heq : B / (100 * B) = (1 / 100 : Real) := by field_simp [ne_of_gt hB]
      exact h.trans_eq heq
    have hs := hamiltonian_prime_factor_scalars m hm1
    have hDL : Real.log (2 * m : Nat) / 4 <= hamiltonianPrimeFactorDegree m := by
      exact hamiltonian_logarithmic_degree_lower ((2 * m : Nat) : Real)
        (by exact_mod_cast (by omega : 1 < 2 * m))
    have hD : 16 <= hamiltonianPrimeFactorDegree m := by linarith only [hDL, hL]
    have hconvert (v : Real)
        (hv : abs (hamiltonianPrimeFactorScale m * v - 1) <= hamiltonianPrimeFactorDefect B m) :
        (1 - hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m <= v /\
          v <= (1 + hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m := by
      have hlo : 1 - hamiltonianPrimeFactorDefect B m <= hamiltonianPrimeFactorScale m * v := by
        linarith only [(abs_le.mp hv).1]
      have hhi : hamiltonianPrimeFactorScale m * v <= 1 + hamiltonianPrimeFactorDefect B m := by
        linarith only [(abs_le.mp hv).2]
      have hc : (hamiltonianPrimeFactorScale m * v) * hamiltonianPrimeFactorDegree m = v := by
        calc
          _ = (hamiltonianPrimeFactorScale m * hamiltonianPrimeFactorDegree m) * v := by ring
          _ = v := by rw [hs.2.2, one_mul]
      have hLo := mul_le_mul_of_nonneg_right hlo (le_of_lt hs.2.1)
      have hHi := mul_le_mul_of_nonneg_right hhi (le_of_lt hs.2.1)
      rw [hc] at hLo hHi
      exact And.intro hLo hHi
    have hleft : forall a : Fin m,
        (1 - hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m <=
          (((hamiltonianPrimeFactorEdges m).filter (fun e => e.1 = a)).card : Real) /\
        (((hamiltonianPrimeFactorEdges m).filter (fun e => e.1 = a)).card : Real) <=
          (1 + hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m := by
      intro a
      apply hconvert
      simpa only [hamiltonian_prime_factor_left_degree, hamiltonianPrimeFactorDefect] using hd.2.1 a
    have hright : forall b : Fin m,
        (1 - hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m <=
          (((hamiltonianPrimeFactorEdges m).filter (fun e => e.2 = b)).card : Real) /\
        (((hamiltonianPrimeFactorEdges m).filter (fun e => e.2 = b)).card : Real) <=
          (1 + hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m := by
      intro b
      apply hconvert
      simpa only [hamiltonian_prime_factor_right_degree, hamiltonianPrimeFactorDefect] using hd.2.2 b
    have hnonneg : 0 <= (1 - 10 * hamiltonianPrimeFactorDefect B m) *
        hamiltonianPrimeFactorDegree m :=
      mul_nonneg (by linarith only [hepsSmall]) (le_of_lt hs.2.1)
    have hr : (hamiltonianPrimeFactorRank B m : Real) <=
        (1 - 2 * hamiltonianPrimeFactorDefect B m / (1 / 5 : Real)) *
          hamiltonianPrimeFactorDegree m := by
      have heq : (1 - 2 * hamiltonianPrimeFactorDefect B m / (1 / 5 : Real)) *
          hamiltonianPrimeFactorDegree m =
          (1 - 10 * hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m := by ring
      rw [heq]
      exact Nat.floor_le hnonneg
    have hepsg : hamiltonianPrimeFactorDefect B m < (1 / 5 : Real) / 2 := by
      linarith only [hepsSmall]
    choose F hF using hamiltonian_regular_factor_and_operator
      (hamiltonianPrimeFactorEdges m) (hamiltonianPrimeFactorRank B m) rfl
      (hamiltonianPrimeFactorDegree m) (1 / 5 : Real) (hamiltonianPrimeFactorDefect B m)
      hs.2.1 (by norm_num) (le_of_lt heps) hepsg hr hleft hright (hcut m hmc)
    have hf := hamiltonian_factor_floor_bounds (hamiltonianPrimeFactorDegree m)
      (hamiltonianPrimeFactorDefect B m) hD (le_of_lt heps) hepsSmall
    have hrel := hamiltonian_factor_floor_relative (hamiltonianPrimeFactorDegree m)
      (hamiltonianPrimeFactorDefect B m) hD (le_of_lt heps) hepsSmall
    have hinv := hamiltonian_factor_reciprocal_degree (Real.log (2 * m : Nat))
      (hamiltonianPrimeFactorDegree m) hLpos hDL
    refine Exists.intro F {
      log_large := hL
      defect_positive := heps
      defect_small := hepsSmall
      degree_lower := hD
      original_left_degree := hleft
      original_right_degree := hright
      rank_positive := hf.1
      subset_prime := hF.1
      left_regular := hF.2.1
      right_regular := hF.2.2.1
      adjacency_loss := ?_
      rank_half := hf.2.2.2
      rank_upper := hf.2.1
      relative_rank := ?_ }
    . rw [hamiltonian_prime_factor_physical_loss]
      exact hF.2.2.2
    . exact hrel.trans (by linarith only [hinv])

theorem hamiltonian_prime_factor_single_family :
    Exists (fun B : Real => And (0 < B)
      (Exists (fun M0 : Nat => And (256 <= M0)
        (Exists (fun F : (m : Nat) -> Finset (Prod (Fin m) (Fin m)) =>
          forall m : Nat, M0 <= m -> HamiltonianPrimeFactorPacket B m (F m)))))) := by
  choose B hB M0 hM0 hex using hamiltonian_prime_factor_simultaneous_packets
  choose F hF using hex
  let family : (m : Nat) -> Finset (Prod (Fin m) (Fin m)) :=
    fun m => if h : M0 <= m then F m h else {}
  refine Exists.intro B (And.intro hB (Exists.intro M0 (And.intro hM0
    (Exists.intro family ?_))))
  intro m hm
  simpa only [family, dif_pos hm] using hF m hm

end PrimeFactorOscillations.LPF
