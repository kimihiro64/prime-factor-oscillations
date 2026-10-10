/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import BombieriVinogradov.Assembly.PrimeCountingConversion.Main
import PrimeFactorOscillations.Helpers.NicolasPrimePowerAsymptotic

/-!
# Fixed-progression Mangoldt asymptotics from cached analytic inputs

Weighted Bombieri-Vinogradov and the ordinary prime number theorem give
the fixed reduced-residue Mangoldt limit. The endpoint conversion proves
the exact strict-prefix convention needed by the upstream QRH argument.
All moduli are fixed before the limit; no zero-free region is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations
open Filter BombieriVinogradov.WeightedBombieriVinogradov
open BombieriVinogradov.PrimeCountingConversion

theorem fixed_progression_mangoldt_error (q : Nat) (hq : 1 <= q)
    (a : Units (ZMod q)) :
    exists C : Real, 0 < C /\ Filter.Eventually (fun N : Nat =>
      abs (psiProgression N q a - psiGlobal N / (q.totient : Real)) <=
        C * ((N : Real) / Real.log N)) atTop := by
  classical
  choose C hC hCX using weighted_bombieri_vinogradov
    ((1 : Real) / 4) (by norm_num) 1 (by norm_num)
  refine Exists.intro C (And.intro hC ?_)
  have hscale : Filter.Eventually (fun N : Nat =>
      (q : Real) <= (N : Real) ^ ((1 : Real) / 4)) atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (q : Real))
  filter_upwards [hscale, eventually_ge_atTop (3 : Nat)] with N hScale hN
  have hqmem : Membership.mem (Finset.Icc 1
      (Nat.floor ((N : Real) ^ ((1 : Real) / 4)))) q :=
    Finset.mem_Icc.mpr (And.intro hq (Nat.le_floor hScale))
  have hPoint := abs_sum_centeredPsiCoefficient_le_maximal
    (X := (N : Real)) (k := N) a (by simp)
  rw [sum_centeredPsiCoefficient] at hPoint
  have hSum : maximalWeightedDiscrepancy (N : Real) q <=
      averageWeightedDiscrepancy (N : Real)
        (Nat.floor ((N : Real) ^ ((1 : Real) / 4))) := by
    apply Finset.single_le_sum
    . intro r hr
      exact maximalWeightedDiscrepancy_nonneg (N : Real) r
    . exact hqmem
  have hBound := hCX (X := (N : Real)) (by exact_mod_cast hN)
  simpa only [Real.rpow_one] using hPoint.trans (hSum.trans hBound)

theorem tendsto_fixed_progression_mangoldt_ratio (q : Nat) (hq : 1 <= q)
    (a : Units (ZMod q)) :
    Tendsto (fun N : Nat => psiProgression N q a / (N : Real))
      atTop (nhds ((q.totient : Real) ^ (-1 : Int))) := by
  choose C hC hError using fixed_progression_mangoldt_error q hq a
  have hInv : Tendsto (fun N : Nat => Inv.inv (Real.log (N : Real)))
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hDiff : Tendsto (fun N : Nat =>
      (psiProgression N q a - psiGlobal N / (q.totient : Real)) / (N : Real))
      atTop (nhds 0) := by
    apply squeeze_zero_norm' ?_ (by simpa using hInv.const_mul C)
    filter_upwards [hError, eventually_ge_atTop (1 : Nat)] with N hE hN
    have hNp : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hNp]
    have h := div_le_div_of_nonneg_right hE hNp.le
    have hCancel : C * ((N : Real) / Real.log N) / (N : Real) =
        C * Inv.inv (Real.log (N : Real)) := by
      field_simp
    simpa only [hCancel] using h
  have hGlobal := (tendsto_nicolasPsi_ratio.comp tendsto_natCast_atTop_atTop).div_const
    (q.totient : Real)
  have hG : Tendsto (fun N : Nat => psiGlobal N / (q.totient : Real) / (N : Real))
      atTop (nhds (1 / (q.totient : Real))) := by
    simpa only [Function.comp_def, psiGlobal_eq_chebyshevPsi, div_right_comm] using hGlobal
  have hTotal := hDiff.add hG
  convert hTotal using 1
  . funext N
    ring
  . simp

theorem mangoldt_residue_range_succ (q N : Nat) (a : ZMod q) :
    (Finset.range (N + 1)).sum (ArithmeticFunction.vonMangoldt.residueClass a) =
      psiProgression N q a := by
  classical
  have hSubset : forall n : Nat, Membership.mem (Finset.Icc 1 N) n ->
      Membership.mem (Finset.range (N + 1)) n := by
    intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  have hSum := Finset.sum_subset (f := ArithmeticFunction.vonMangoldt.residueClass a)
    hSubset (fun n hn hnNot => by
    have hnZero : n = 0 := by
      simp only [Finset.mem_Icc, Finset.mem_range] at *
      omega
    subst n
    simp [ArithmeticFunction.vonMangoldt.residueClass])
  rw [<- hSum, psiProgression]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply,
    Set.mem_setOf_eq]
  by_cases h : (n : ZMod q) = a
  . simp [h]
  . simp [h, Ne.symm h]

theorem tendsto_mangoldt_residue_range_ratio (q : Nat) (hq : 1 <= q)
    (a : Units (ZMod q)) :
    Tendsto (fun N : Nat =>
      (Finset.range N).sum (ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q)) /
        (N : Real)) atTop (nhds ((q.totient : Real) ^ (-1 : Int))) := by
  have hInv : Tendsto (fun N : Nat => Inv.inv (N : Real)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hInvSucc := (tendsto_add_atTop_iff_nat 1).mpr hInv
  have hRatio : Tendsto (fun N : Nat => (N : Real) / ((N + 1 : Nat) : Real))
      atTop (nhds (1 : Real)) := by
    have hConst : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) :=
      tendsto_const_nhds
    convert hConst.sub hInvSucc using 1
    . funext N
      have hN : Not (((N + 1 : Nat) : Real) = 0) := by positivity
      field_simp
      push_cast
      ring
    . simp
  apply (tendsto_add_atTop_iff_nat 1).mp
  have h := (tendsto_fixed_progression_mangoldt_ratio q hq a).mul hRatio
  convert h using 1
  . funext N
    rw [mangoldt_residue_range_succ]
    by_cases hN : N = 0
    . simp [hN, psiProgression_zero]
    . have hNR : Not ((N : Real) = 0) := by exact_mod_cast hN
      field_simp
  . simp

end PrimeFactorOscillations
