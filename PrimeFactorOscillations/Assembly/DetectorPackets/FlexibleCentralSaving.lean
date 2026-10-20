/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.FlexibleHighBudget

/-!
# FlexibleCentralSaving

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-!
A fixed central-row saving for actual source data. The existing coupled
source moment theorem is used in full. This result concerns the central
nonfloor rows at the original physical scales, not the complete high probe.
-/


noncomputable section

open scoped Classical BigOperators ContDiff
open Filter
open OAI.SevenEighths

namespace PrimeFactorOscillations.FlexibleCentralSaving

open HeckeFamily Parameters ProbePhysical ProbeHighRowFamily ProbeFinalAssembly
open ProbeFinalAssemblyCertifiedBands PrincipalSignalComparison
open HeckeInverseAmplification HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition
open ProbeMellinBoundary PrincipalMellinResidues ProbePrincipalResidueActual
open ProbeRaySlots
open PrimeFactorOscillations.FlexibleMomentInput
open PrimeFactorOscillations.FlexibleHighBudget

def RowConclusion {Delta : Real} (D : HighData Delta) (F : SourceData D)
    (tau : Real) (n m : Nat) (eta : Character) (Z C : Real) : Prop :=
  forall rows : Finset FreeRow,
    (forall u, Membership.mem rows u ->
      Not (u.val = 1) /\ Z ^ (1 / 100 : Real) <= rowNorm u /\
      Not ((calibrationForSet F.S F.maximal).residueMonoid u.val = 0) /\
      rowNorm u <= Z ^ (13 / 16 + D.t)) ->
    forall idx grid : FreeRow -> Nat,
      (forall u, Membership.mem rows u ->
        idx u <= n /\ grid u <= m /\ Not (grid u = 0) /\
        (51 / 100 : Real) + D.e * grid u <= 1) ->
      (forall u, Membership.mem rows u ->
        detectorMaximum
          (sourceDetectorFamily F.S F.exclusions.prime eta u
            (rayCubeFamily F.modulus Top.top le_top u))
          (3 * ((idx u + 1 : Nat) : Real) * Z ^ tau) <
            (51 / 100 : Real) + D.e * grid u + 2 * D.e) ->
      (forall u, Membership.mem rows u ->
        (51 / 100 : Real) + D.e * grid u <=
          detectorMaximum
            (sourceDetectorFamily F.S F.exclusions.prime eta u
              (rayCubeFamily F.modulus Top.top le_top u))
            (((3 * idx u : Nat) : Real) * Z ^ tau)) ->
      let Y : Fin D.N -> Real := fun j => Z ^ (D.ell j)
      let T := fun j =>
        pool (RayQuotient.identityClass F.modulus Top.top) F.S 1 2 (Y j)
      let normer :=
        sourceResidueConstant F.W F.W F.modulus *
          (Probe.principalScalar Finset.univ Z (1 / 6)
            (slotMass T (residueWeights (fun _ => F.w) Y)) : Complex)
      Not (normer = 0) /\
        norm (finiteCentralCubeRows F.S F.exclusions F.maximal eta rows T
          (nonfloorPoolOutside F.modulus Top.top F.S D.N 1 2 Y)
          (fun _ y => (F.w y : Complex)) Y F.W F.W
          (Z ^ (17 / 48 : Real)) (Z ^ (23 / 48 : Real)) Z D.e
          (fun u => (51 / 100 : Real) + D.e * grid u)
          (fun u => ((3 * idx u + 1 : Nat) : Real) * Z ^ tau) / normer) <=
            C * Z ^ (3 / 16 - 1 / 30000 : Real)

theorem fixed_central_bound {Delta : Real} (D : HighData Delta)
    (hDelta : 0 < Delta) (hDeltaSmall : Delta <= (1 / 100000 : Real))
    (hBudget : centralCost D (1 / 20000) <= (49 / 440640 : Real))
    (F : SourceData D) (counts : CountParameters F.modulus Top.top D.t)
    (tau : Real) (htau : 0 < tau) (htaud : tau < (1 / 200 : Real) / 2)
    (htaucost : 4 * tau < (1 / 200 : Real) * D.cost)
    (htau2 : 2 * tau <= D.t) (htaueps : tau * (2 + 4 * D.eps) < D.t)
    (n m : Nat) :
    exists C : Real, 0 < C /\
      forall eta : Character, Filter.Eventually
        (fun Z : Real => forall C0 : Real, 0 <= C0 ->
          SourceMomentBound F counts eta Z tau (C0 * Z ^ D.t) (Z ^ (2 * tau)) ->
          RowConclusion D F tau n m eta Z
            (C * C0 * (eta.modulus.absNorm : Real) ^ (2 * D.eps)))
        Filter.atTop := by
  cases D with
  | mk t N ell rmin epsilon e kappa cost eps sigma t_pos t_delta t_small slots_pos slots_injective slots_sum slots_bounds rmin_pos epsilon_pos epsilon_small epsilon_gap e_pos e_small kappa_pos kappa_small cost_pos eps_pos eps_small sigma_pos detector_budget phase_budget count_budget central_budget geometric_budget principal_budget window_budget floor_budget high_saving height_choice =>
    let D : HighData Delta := @HighData.mk Delta t N ell rmin epsilon e kappa cost eps sigma t_pos t_delta t_small slots_pos slots_injective slots_sum slots_bounds rmin_pos epsilon_pos epsilon_small epsilon_gap e_pos e_small kappa_pos kappa_small cost_pos eps_pos eps_small sigma_pos detector_budget phase_budget count_budget central_budget geometric_budget principal_budget window_budget floor_budget high_saving height_choice
    have hconductor : (13 / 16 : Real) + t + 2 * t <= 7 / 8 := by
      linarith only [t_small]
    have hfinal :
        (13 / 16 : Real) * (159 * epsilon + t + t + 7 * t) + 2 * t +
          (3 / 2) * (2 * t) +
          (26 * e + ((N : Real) + 8) * eps + t + t / 6) +
          (t + 2 * tau + t) + 1 / 20000 <= 49 / 440640 := by
      dsimp only [centralCost] at hBudget
      linarith only [hBudget, htau2]
    have hex := ProbeFinalAssembly.actual_nonfloor_rows_saving
      F.modulus Top.top le_top N n e eps 1 2 1 t (1 / 200) (7 / 8) rmin
      tau epsilon kappa cost t t t
      e_pos e_small eps_pos (by norm_num) (by norm_num) (by norm_num)
      t_pos.le (by norm_num) (by norm_num) (by norm_num) rmin_pos
      htau epsilon_pos kappa_pos cost_pos.le t_pos
      phase_budget epsilon_gap t_pos (by linarith only [htaucost, htau]) htaueps
      F.S F.exclusions F.first F.maximal ell slots_injective
      (fun j => (slots_bounds j).2.1) (fun j => (slots_bounds j).2.2)
      (fun _ => F.w) (fun _ => F.support) (fun _ => F.smooth)
      (fun _ => F.bounded) (fun _ => F.compact) (fun _ => F.nonzero) slots_sum
      (by norm_num) epsilon_small kappa_small htaud htaucost
      (by nlinarith only [detector_budget])
      F.w F.smooth F.compact F.positive_support
      (fun y => (F.bounded y).1) F.nonzero
      1 2 1 (by norm_num) (by norm_num) (by norm_num)
      F.support (fun y => (F.bounded y).2)
      t Delta t t (2 * tau) t t_pos hDelta.le
      (by linarith only [hDeltaSmall]) t_pos t_pos (by linarith only [htau])
      t (2 * t) (1 / 20000) t_pos.le
      (by linarith only [t_small]) (by positivity) count_budget hfinal
      F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
      F.complex_support F.complex_support F.real F.real
      F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
      (t / 8) (by positivity) m (t / 8) (by positivity)
      (by norm_num) hconductor (by linarith) counts
    let C := Classical.choose hex
    have hC := (Classical.choose_spec hex).1
    have hbound := (Classical.choose_spec hex).2
    refine Exists.intro C (And.intro hC ?_)
    intro eta
    filter_upwards [hbound eta,
      sourceDyad_geometry_eventually (1 / 200) (7 / 8) t (13 / 16 + t)
        (by norm_num) (by norm_num) t_pos hconductor,
      HeckeDyadic.constant_absorbed_eventually (3 * (n : Real) + 1) tau htau,
      eventually_gt_atTop (1 : Real)] with Z hb hgeo hnheight hZ
    intro C0 hC0 hmom
    unfold RowConclusion
    intro rows hrows idx grid hlabels hnext hcurrent
    have hest := hb C0 hC0 rows hrows idx grid hlabels hnext hcurrent (by
      intro k hk i hi j hj
      dsimp only
      intro hne vheight htheight
      let rows' := cubeBinRows (Inter.inter rows (dyadicRows 1 k)) idx grid i j
      have hsub : forall u, Membership.mem rows' u ->
          Membership.mem (Inter.inter rows (dyadicRows 1 k)) u :=
        Finset.filter_subset _ _
      have hsubr : forall u, Membership.mem rows' u -> Membership.mem rows u :=
        fun u hu => (Finset.mem_inter.mp (hsub u hu)).1
      have hrowsBasic : forall u, Membership.mem rows u ->
          Not (u.val = 1) /\ Z ^ (1 / 100 : Real) <= rowNorm u /\
            rowNorm u <= Z ^ (13 / 16 + t) :=
        fun u hu => And.intro (hrows u hu).1
          (And.intro (hrows u hu).2.1 (hrows u hu).2.2.2)
      have hg := hgeo rows hrowsBasic k (hne.mono hsub)
      let u := Classical.choose hne
      have hu := Classical.choose_spec hne
      have huj : grid u = j := ((mem_cubeBinRows _ idx grid i j u).mp hu).2.2
      have hjne : Not (j = 0) := by
        intro hjzero
        exact (hlabels u (hsubr u hu)).2.2.1 (huj.trans hjzero)
      have ha : (51 / 100 : Real) < 51 / 100 + e * j := by
        have hjp : (0 : Real) < j := by exact_mod_cast Nat.pos_of_ne_zero hjne
        nlinarith only [e_pos, hjp]
      have ha' : (51 / 100 : Real) + e * j <= 1 := by
        simpa only [huj] using (hlabels u (hsubr u hu)).2.2.2
      have hrow' : forall v, Membership.mem rows' v ->
          Not (v.val = 1) /\ Z ^ (1 / 100 : Real) <= rowNorm v /\
            Not ((calibrationForSet F.S F.maximal).residueMonoid v.val = 0) /\
            rowNorm v <= Z ^ (sourceDyadConductor Z t k - t) := by
        intro v hv
        exact And.intro (hrows v (hsubr v hv)).1
          (And.intro (hrows v (hsubr v hv)).2.1
            (And.intro (hrows v (hsubr v hv)).2.2.1
              (hg.2.2.2.2.2 v (hsub v hv))))
      have hi' : (i : Real) <= n := by
        exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hheight : ((3 * i + 1 : Nat) : Real) * Z ^ tau <= Z ^ (2 * tau) := by
        have hZp : 0 < Z := zero_lt_one.trans hZ
        calc
          _ <= (3 * (n : Real) + 1) * Z ^ tau := by push_cast; gcongr
          _ <= Z ^ tau * Z ^ tau :=
            mul_le_mul_of_nonneg_right hnheight (by positivity)
          _ = Z ^ (2 * tau) := by
            rw [<- Real.rpow_add hZp]
            congr 1
            ring
      exact hmom rows' (sourceDyadConductor Z t k) (51 / 100 + e * j)
        hg.2.2.1 hg.2.2.2.1 ha ha' hrow' i
        ((17 / 50 : Complex) + (vheight.1.2 : Complex) * Complex.I)
        (by simp) (by simpa using htheight.2.trans hheight))
    have hMargin := central_exponent_margin Delta t hDeltaSmall t_small
    have hPower :
        Z ^ ((3 / 16 : Real) + Delta - 1 / 20000 + t / 8 + t / 8) <=
          Z ^ (3 / 16 - 1 / 30000 : Real) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le hMargin
    have hCoeff : 0 <= C * C0 * (eta.modulus.absNorm : Real) ^ (2 * eps) := by
      positivity
    exact And.intro hest.1
      (hest.2.trans (mul_le_mul_of_nonneg_left hPower hCoeff))

theorem exists_central_saving (hbad : (3 / 4 : Real) < HeckeZeroSupremum.beta) :
    exists D : HighData (1 / 100000), exists F : SourceData D,
      exists tau : Real, 0 < tau /\
        forall n m : Nat, forall eta : Character,
          exists C : Real, 0 < C /\
            Filter.Eventually
              (fun Z : Real => RowConclusion D F tau n m eta Z C) Filter.atTop := by
  have hd := exists_tight_data (1 / 100000) (by norm_num)
    (detectorMesh (1 / 100000))
    (fun t ht => detectorMesh_pos (by norm_num) ht)
  let D := Classical.choose hd
  have hD := Classical.choose_spec hd
  let F := Classical.choice (exists_source_data D)
  let counts := Classical.choice (source_count_parameters F)
  have hm := source_moments_flexible D F counts hbad hD.1
  let J := Classical.choose hm
  have hJ := (Classical.choose_spec hm).1
  have hMom := (Classical.choose_spec hm).2
  have hh := chosen_data_height D F counts J hJ hMom
  let tau := Classical.choose hh
  have ht := Classical.choose_spec hh
  refine Exists.intro D (Exists.intro F (Exists.intro tau (And.intro ht.1 ?_)))
  intro n m eta
  have hc := fixed_central_bound D (by norm_num) (by norm_num) hD.2.2 F counts
    tau ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2.1 n m
  let C := Classical.choose hc
  have hC := (Classical.choose_spec hc).1
  have hBound := (Classical.choose_spec hc).2 eta
  have hsrc := ht.2.2.2.2.2.2 eta
  let C0 := Classical.choose hsrc
  have hC0 := (Classical.choose_spec hsrc).1
  have hSource := (Classical.choose_spec hsrc).2
  have hCoeffNonneg :
      0 <= C * C0 * (eta.modulus.absNorm : Real) ^ (2 * D.eps) :=
    mul_nonneg (mul_nonneg hC.le hC0.le)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine Exists.intro (1 + C * C0 * (eta.modulus.absNorm : Real) ^ (2 * D.eps))
    (And.intro (by linarith only [hCoeffNonneg]) ?_)
  filter_upwards [hBound, hSource, eventually_ge_atTop (1 : Real)] with Z hb hs hZ
  have hp := hb C0 hC0.le hs
  intro rows hrows idx grid hlabels hnext hcurrent
  have hr := hp rows hrows idx grid hlabels hnext hcurrent
  exact And.intro hr.1 (hr.2.trans
    (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)))

end PrimeFactorOscillations.FlexibleCentralSaving
