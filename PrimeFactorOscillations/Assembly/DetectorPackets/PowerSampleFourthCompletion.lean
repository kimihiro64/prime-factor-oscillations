/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.SpectralCoefficient
import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleFourthCRT

/-!
# PowerSampleFourthCompletion

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

set_option maxHeartbeats 2200000

noncomputable section
namespace OAI.SevenEighths.ProbePowerGauss
open scoped Classical BigOperators
open ActualEisensteinCubic ActualEisensteinCoordinates ConcretePrimeRowBridge
open CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein ProbePhysical ProbePhase
open CompletedGauss ProbeCompleted ProbeRow RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem fourth_conductor_phase_cancel (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s})) :
    G (A * s) * star (G A) * reciprocitySign A s = G s := by
  have hoA := supported_residue_odd A hA
  have hos := supported_residue_odd s hs
  have hg := G_conjugate_cancel A hoA (cubicTwo_isUnit_of_odd A hoA)
  have hr := reciprocitySign_sq A s hoA hos
  rw [G_mul A s hoA hos]
  calc
    _ = (star (G A) * G A) * G s * reciprocitySign A s ^ 2 := by ring
    _ = _ := by rw [hg, hr, one_mul, mul_one]

theorem spectralSummand_fourth_completed
    (S : Finset (Ideal O)) (D I J : Ideal O)
    (eta : HeckeFamily.Character) (C : CalibrationData) (s : O)
    (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime C.generator (completedIndex I J)) (t : Complex) :
    G (completedIndex I J * s) *
        spectralSummand S D (baseRowCoefficient eta C.Xi s hs) t I J =
      completedMask S D I J *
        (gaussTwo I (supported_primaryGenerator_ne_zero I hI) *
          star (FiniteGaussPhase.angularFactor (completedIndex I J)) *
          targetMonoid eta (completedIndex I J) * (C.Xi (completedIndex I J)) ^ (-1 : Int) *
          G s) /
        ((Real.sqrt (Ideal.absNorm I) : Complex) * (Ideal.absNorm J : Complex)) *
        (fullIdealWeight t I * fullIdealWeight (3 * t) J) := by
  have hA := supported_completed _ _
    ((supported_span_primaryGenerator_iff I).mpr hI)
    ((supported_span_primaryGenerator_iff J).mpr hJ)
  have hphase := fourth_conductor_phase_cancel (completedIndex I J) s hA hs
  rw [spectralSummand_source_coefficient S D I J eta C s hs hI hJ hsf hcop t]
  simp only [star_mul, zpow_neg_one]
  calc
    _ = (G (completedIndex I J * s) * star (G (completedIndex I J)) *
          reciprocitySign (completedIndex I J) s) *
        (completedMask S D I J *
          (gaussTwo I (supported_primaryGenerator_ne_zero I hI) *
            star (FiniteGaussPhase.angularFactor (completedIndex I J)) *
            targetMonoid eta (completedIndex I J) * (C.Xi (completedIndex I J)) ^ (-1 : Int)) /
          ((Real.sqrt (Ideal.absNorm I) : Complex) * (Ideal.absNorm J : Complex)) *
          (fullIdealWeight t I * fullIdealWeight (3 * t) J)) := by
      simp only [zpow_neg_one]
      ring
    _ = _ := by
      rw [hphase]
      simp only [zpow_neg_one]
      ring

theorem completed_fourth_packet_ray_expansion
    {iota : Type*} [Fintype iota] (A s : iota -> O)
    (hAs : forall i, Supported (Ideal.span {A i * s i})) (z : iota -> Complex) :
    (Finset.univ.sum fun i => G (A i * s i) * z i) =
      Finset.univ.sum (fun chi : RayCharacter => gCoeff chi *
        (Finset.univ.sum fun i => rayCharacter chi (A i) * rayCharacter chi (s i) * z i)) := by
  have he (i : iota) : G (A i * s i) =
      Finset.univ.sum (fun chi : RayCharacter =>
        gCoeff chi * rayCharacter chi (A i) * rayCharacter chi (s i)) := by
    have h : rayMask (A i * s i) * G (A i * s i) =
        Finset.univ.sum (fun chi : RayCharacter =>
          gCoeff chi * rayCharacter chi (A i * s i)) :=
      fixedG_character_expansion (A i * s i)
    rw [rayMask_supported (A i * s i) (hAs i), one_mul] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro chi hchi
    rw [rayCharacter_mul]
    ring
  simp_rw [he, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro chi hchi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem completed_fourth_packet_ray_bound
    {iota : Type*} [Fintype iota] (A s : iota -> O)
    (hAs : forall i, Supported (Ideal.span {A i * s i})) (z : iota -> Complex)
    (B : Real) (hB : 0 <= B)
    (hb : forall chi : RayCharacter,
      norm (Finset.univ.sum fun i =>
        rayCharacter chi (A i) * rayCharacter chi (s i) * z i) <= B) :
    norm (Finset.univ.sum fun i => G (A i * s i) * z i) <= 32 * B := by
  rw [completed_fourth_packet_ray_expansion A s hAs z]
  calc
    _ <= Finset.univ.sum (fun chi : RayCharacter => norm (gCoeff chi *
        (Finset.univ.sum fun i =>
          rayCharacter chi (A i) * rayCharacter chi (s i) * z i))) :=
      norm_sum_le _ _
    _ <= Finset.univ.sum (fun chi : RayCharacter => norm (gCoeff chi) * B) := by
      apply Finset.sum_le_sum
      intro chi hchi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb chi) (norm_nonneg _)
    _ = (Finset.univ.sum fun chi : RayCharacter => norm (gCoeff chi)) * B :=
      (Finset.sum_mul ..).symm
    _ <= _ := mul_le_mul_of_nonneg_right gCoeff_sum_norm_le hB

theorem original_fourth_packet_ray_expansion
    {iota : Type*} [Fintype iota] (A s : iota -> O)
    (hAs : forall i, Supported (Ideal.span {A i * s i})) (z : iota -> Complex) :
    (Finset.univ.sum z) =
      Finset.univ.sum (fun chi : RayCharacter => star (gCoeff chi) *
        (Finset.univ.sum fun i =>
          star (rayCharacter chi (A i)) * star (rayCharacter chi (s i)) *
            G (A i * s i) * z i)) := by
  have he := completed_fourth_packet_ray_expansion A s hAs
    (fun i => star (G (A i * s i) * z i))
  have hstar := congrArg star he
  simp only [star_sum, star_mul, star_star] at hstar
  calc
    _ = Finset.univ.sum (fun i => star (G (A i * s i)) * (G (A i * s i) * z i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have ho := supported_residue_odd (A i * s i) (hAs i)
      have hc := G_conjugate_cancel (A i * s i) ho
        (cubicTwo_isUnit_of_odd (A i * s i) ho)
      rw [<-mul_assoc, hc, one_mul]
    _ = _ := by simpa only [mul_assoc, mul_comm, mul_left_comm] using hstar

theorem original_fourth_packet_ray_bound
    {iota : Type*} [Fintype iota] (A s : iota -> O)
    (hAs : forall i, Supported (Ideal.span {A i * s i})) (z : iota -> Complex)
    (B : Real) (hB : 0 <= B)
    (hb : forall chi : RayCharacter,
      norm (Finset.univ.sum fun i =>
        star (rayCharacter chi (A i)) * star (rayCharacter chi (s i)) *
          G (A i * s i) * z i) <= B) :
    norm (Finset.univ.sum z) <= 32 * B := by
  rw [original_fourth_packet_ray_expansion A s hAs z]
  calc
    _ <= Finset.univ.sum (fun chi : RayCharacter => norm (star (gCoeff chi) *
        (Finset.univ.sum fun i =>
          star (rayCharacter chi (A i)) * star (rayCharacter chi (s i)) *
            G (A i * s i) * z i))) := norm_sum_le _ _
    _ <= Finset.univ.sum (fun chi : RayCharacter => norm (gCoeff chi) * B) := by
      apply Finset.sum_le_sum
      intro chi hchi
      rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (hb chi) (norm_nonneg _)
    _ = (Finset.univ.sum fun chi : RayCharacter => norm (gCoeff chi)) * B :=
      (Finset.sum_mul ..).symm
    _ <= _ := mul_le_mul_of_nonneg_right gCoeff_sum_norm_le hB


theorem completed_fourth_cross_cancel (c n d m : O)
    (hc : Supported (Ideal.span {c})) (hn : Supported (Ideal.span {n}))
    (hd : Supported (Ideal.span {d})) (hm : Supported (Ideal.span {m}))
    (hpc : Dvd.dvd (goodLambda ^ 2) (c - 1))
    (hpn : Dvd.dvd (goodLambda ^ 2) (n - 1))
    (hpd : Dvd.dvd (goodLambda ^ 2) (d - 1))
    (hpm : Dvd.dvd (goodLambda ^ 2) (m - 1))
    (hcd : IsCoprime c d) (hcm : IsCoprime c m)
    (hnd : IsCoprime n d) (hnm : IsCoprime n m) :
    sexticPair (c * n ^ 3) (d * m ^ 3) ^ 4 * sexticPair c d ^ 2 = 1 := by
  have he := completed_cubic_cross_cancel c n d m hc hn hd hm
    hpc hpn hpd hpm hcd hcm hnd hnm
  rw [reciprocitySign_star] at he
  have hQ3 := sexticPair_cube_supported c d hc hd hpc hpd hcd
  have hQ2 := reciprocitySign_sq c d (supported_residue_odd c hc)
    (supported_residue_odd d hd)
  have hQ6 : sexticPair c d ^ 6 = 1 := by
    calc
      _ = (sexticPair c d ^ 3) ^ 2 := by ring
      _ = _ := by rw [hQ3, hQ2]
  have hAs := supported_completed c n hc hn
  have hBs := supported_completed d m hd hm
  have hR2 := reciprocitySign_sq (c * n ^ 3) (d * m ^ 3)
    (supported_residue_odd _ hAs) (supported_residue_odd _ hBs)
  have hR4 : reciprocitySign (c * n ^ 3) (d * m ^ 3) ^ 4 = 1 := by
    calc
      _ = (reciprocitySign (c * n ^ 3) (d * m ^ 3) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hR2, one_pow]
  calc
    _ = sexticPair (c * n ^ 3) (d * m ^ 3) ^ 4 * sexticPair c d ^ 2 *
        sexticPair c d ^ 6 * reciprocitySign (c * n ^ 3) (d * m ^ 3) ^ 4 := by
      rw [hQ6, hR4, mul_one, mul_one]
    _ = (sexticPair (c * n ^ 3) (d * m ^ 3) * sexticPair c d ^ 2 *
        reciprocitySign (c * n ^ 3) (d * m ^ 3)) ^ 4 := by ring
    _ = _ := by rw [he, one_pow]

theorem completed_fourth_coefficient_product (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I * J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryGenerator I}))
    (hd : Supported (Ideal.span {primaryGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : Dvd.dvd (goodLambda ^ 2) (primaryGenerator I - 1))
    (hpd : Dvd.dvd (goodLambda ^ 2) (primaryGenerator J - 1))
    (hpn : Dvd.dvd (goodLambda ^ 2) (n - 1))
    (hpm : Dvd.dvd (goodLambda ^ 2) (m - 1))
    (hps : Dvd.dvd (goodLambda ^ 2) (s - 1))
    (hpr : Dvd.dvd (goodLambda ^ 2) (r - 1))
    (hcop : IsCoprime ((primaryGenerator I * n ^ 3) * s)
      ((primaryGenerator J * m ^ 3) * r)) (H : O) :
    let A := primaryGenerator I * n ^ 3
    let B := primaryGenerator J * m ^ 3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    gaussTwo (I * J) hIJ.2 *
        completedFourthFourier (A * B) (s * r)
          (mul_ne_zero hA hB)
          (mul_ne_zero (supportedElement_ne_zero s hs) (supportedElement_ne_zero r hr)) H =
      (gaussTwo I hI.2 *
        completedFourthFourier A s hA (supportedElement_ne_zero s hs) H) *
      (gaussTwo J hJ.2 *
        completedFourthFourier B r hB (supportedElement_ne_zero r hr) H) := by
  dsimp only
  let c := primaryGenerator I
  let d := primaryGenerator J
  let A := c * n ^ 3
  let B := d * m ^ 3
  have hAs := supported_completed c n hc hn
  have hBs := supported_completed d m hd hm
  have hAB : IsCoprime A B := hcop.of_mul_left_left.of_mul_right_left
  have hnA : Dvd.dvd n A := by
    refine Exists.intro (c * n ^ 2) ?_
    dsimp only [A]
    ring
  have hmB : Dvd.dvd m B := by
    refine Exists.intro (d * m ^ 2) ?_
    dsimp only [B]
    ring
  have hcA : Dvd.dvd c A := dvd_mul_right c (n ^ 3)
  have hdB : Dvd.dvd d B := dvd_mul_right d (m ^ 3)
  have hcd := (hAB.of_isCoprime_of_dvd_left hcA).of_isCoprime_of_dvd_right hdB
  have hcm := (hAB.of_isCoprime_of_dvd_left hcA).of_isCoprime_of_dvd_right hmB
  have hnd := (hAB.of_isCoprime_of_dvd_left hnA).of_isCoprime_of_dvd_right hdB
  have hnm := (hAB.of_isCoprime_of_dvd_left hnA).of_isCoprime_of_dvd_right hmB
  have hphase := completed_fourth_cross_cancel c n d m hc hn hd hm
    hpc hpn hpd hpm hcd hcm hnd hnm
  change sexticPair A B ^ 4 * sexticPair c d ^ 2 = 1 at hphase
  rw [gaussTwo_coprime_product_sextic I J hI hJ hIJ hIJcop,
    completedFourthFourier_product A B s r hAs hBs hs hr
      (primary_completed c n hpc hpn) (primary_completed d m hpd hpm)
      hps hpr hcop H]
  calc
    _ = (sexticPair A B ^ 4 * sexticPair c d ^ 2) *
      ((gaussTwo I hI.2 * completedFourthFourier A s
          (supportedElement_ne_zero A hAs) (supportedElement_ne_zero s hs) H) *
       (gaussTwo J hJ.2 * completedFourthFourier B r
          (supportedElement_ne_zero B hBs) (supportedElement_ne_zero r hr) H)) := by ring
    _ = _ := by rw [hphase, one_mul]

end OAI.SevenEighths.ProbePowerGauss
