/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeFactorReference

/-! # Whole-terminal error windows for the same prime-factor family -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

theorem hamiltonian_factor_log_error_window (B eta : Real) (hB : 0 < B) (hEta : 0 < eta) :
    Exists (fun L0 : Real => And (64 <= L0)
      (forall L : Real, L0 <= L -> 62 * (B / Real.sqrt L) + 24 / L <= eta)) := by
  let a := 124 * B / eta
  let b := 48 / eta
  let L0 := max 64 (max (a ^ 2) b)
  refine Exists.intro L0 (And.intro (le_max_left _ _) ?_)
  intro L hLarge
  have hL : 64 <= L := (le_max_left _ _).trans hLarge
  have hLpos : 0 < L := by linarith only [hL]
  have ha : 0 < a := div_pos (mul_pos (by norm_num) hB) hEta
  have hb : 0 < b := div_pos (by norm_num) hEta
  have haSq : a ^ 2 <= L := (le_max_left _ _).trans ((le_max_right _ _).trans hLarge)
  have hbL : b <= L := (le_max_right _ _).trans ((le_max_right _ _).trans hLarge)
  have hRoot : a <= Real.sqrt L := by
    nlinarith only [haSq, Real.sq_sqrt (le_of_lt hLpos), Real.sqrt_nonneg L, ha]
  have hFirst : 62 * (B / Real.sqrt L) <= eta / 2 := by
    have h := div_le_div_of_nonneg_left (by positivity : (0 : Real) <= 62 * B) ha hRoot
    have heq : (62 * B) / a = eta / 2 := by
      dsimp only [a]
      field_simp [ne_of_gt hB, ne_of_gt hEta]
      <;> ring
    calc
      _ = (62 * B) / Real.sqrt L := by ring
      _ <= (62 * B) / a := h
      _ = eta / 2 := heq
  have hSecond : 24 / L <= eta / 2 := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 24) hb hbL
    have heq : (24 : Real) / b = eta / 2 := by
      dsimp only [b]
      field_simp [ne_of_gt hEta]
      <;> norm_num
    exact h.trans_eq heq
  linarith only [hFirst, hSecond]

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_factor_error_terminal (B eta : Real)
    (hB : 0 < B) (hEta : 0 < eta) :
    Exists (fun M0 : Nat => And (256 <= M0)
      (forall m : Nat, M0 <= m ->
        62 * hamiltonianPrimeFactorDefect B m + 24 / Real.log (2 * m : Nat) <= eta)) := by
  choose L0 hL0 hWindow using hamiltonian_factor_log_error_window B eta hB hEta
  choose N0 hN0 hLog using hamiltonian_log_terminal_lower L0
  refine Exists.intro (max 256 N0) (And.intro (le_max_left _ _) ?_)
  intro m hm
  have hn : N0 <= 2 * m := by omega
  simpa only [hamiltonianPrimeFactorDefect] using
    hWindow (Real.log (2 * m : Nat)) (hLog (2 * m) hn)

theorem hamiltonian_prime_factor_mixture_terminal (eta : Real) (hEta : 0 < eta) :
    Exists (fun M0 : Nat => And (256 <= M0)
      (forall m : Nat, M0 <= m -> 2 / ((m : Real) + 1) <= eta)) := by
  choose N hN using exists_nat_gt ((2 : Real) / eta)
  refine Exists.intro (max 256 N) (And.intro (le_max_left _ _) ?_)
  intro m hm
  have hNm : N <= m := by omega
  have hNmR : (N : Real) <= (m : Real) := Nat.cast_le.mpr hNm
  have hLower : 2 / eta <= (m : Real) + 1 := by linarith only [hN, hNmR]
  have h := div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 2)
    (div_pos (by norm_num : (0 : Real) < 2) hEta) hLower
  have heq : (2 : Real) / (2 / eta) = eta := by field_simp [ne_of_gt hEta]
  exact h.trans_eq heq

theorem hamiltonian_prime_factor_packet_deviations_terminal (B eta : Real)
    (hB : 0 < B) (hEta : 0 < eta) :
    Exists (fun M0 : Nat => And (256 <= M0)
      (forall m : Nat, M0 <= m ->
        forall (F : Finset (Prod (Fin m) (Fin m)))
          (P : Matrix (Fin (2 * m)) (Fin (2 * m)) Real),
        HamiltonianPrimeFactorReferencePacket B m F P ->
        And (abs ((hamiltonianPrimeFactorRank B m : Real) /
          hamiltonianPrimeFactorDegree m - 1) <= eta)
        (And (norm (hamiltonianPrimeNormalizedFactor B m F - P) <= eta)
        (And (norm (P - hamiltonianUnweightedPrimeMatrix (2 * m)) <= eta)
          (norm (hamiltonianPrimeNormalizedFactor B m F -
            hamiltonianUnweightedPrimeMatrix (2 * m)) <= eta))))) := by
  have hHalf : 0 < eta / 2 := div_pos hEta (by norm_num)
  choose Me hMe hError using hamiltonian_prime_factor_error_terminal B (eta / 2) hB hHalf
  choose Md hMd hMix using hamiltonian_prime_factor_mixture_terminal (eta / 2) hHalf
  refine Exists.intro (max Me Md) (And.intro (hMe.trans (le_max_left _ _)) ?_)
  intro m hm F P h
  have he := hError m (by omega : Me <= m)
  have hd := hMix m (by omega : Md <= m)
  have hL : 0 < Real.log (2 * m : Nat) := by linarith only [h.factor_packet.log_large]
  have hSmall : 10 * hamiltonianPrimeFactorDefect B m + 4 / Real.log (2 * m : Nat) <=
      62 * hamiltonianPrimeFactorDefect B m + 24 / Real.log (2 * m : Nat) :=
    add_le_add
      (mul_le_mul_of_nonneg_right (by norm_num : (10 : Real) <= 62)
        (le_of_lt h.factor_packet.defect_positive))
      (div_le_div_of_nonneg_right (by norm_num : (4 : Real) <= 24) (le_of_lt hL))
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  . exact h.factor_packet.relative_rank.trans (hSmall.trans (by linarith only [he, hEta]))
  . exact h.close_factor.trans (by linarith only [hd, hEta])
  . linarith only [h.close_original, he, hd]
  . exact h.factor_error.trans (by linarith only [he, hEta])

end PrimeFactorOscillations.LPF
