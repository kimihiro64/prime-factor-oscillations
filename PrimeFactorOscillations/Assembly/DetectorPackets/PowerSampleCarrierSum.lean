/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleCarrierBudget

/-!
# PowerSampleCarrierSum

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
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein ConcretePrimeRowBridge
open GaussianShiftedPartition ProbeGauss ProbePrimePower ProbePhysical ProbeEuler
local notation "O" => ActualEisensteinCubic.O
local notation "Res" p => HasQuotient.Quotient O (Ideal.span {p})

local instance sumCarrierField (p : O) [(Ideal.span {p} : Ideal O).IsMaximal] :
    Field (Res p) := Ideal.Quotient.field _
local instance sumCarrierFintype (p : O) [(Ideal.span {p} : Ideal O).IsMaximal] :
    Fintype (Res p) := Fintype.ofFinite _

theorem fourthPhysicalCubeBlock_decomposition (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (eta a C X W : Complex) (l : Nat) (H : O) :
    fourthPhysicalCubeBlock p hp hg eta a C X W l H =
      fourthCarrierState p hp hg eta a C X W 0 l 0 H +
      fourthCarrierState p hp hg eta a C X W 1 l 1 H +
      fourthCarrierWaveBlock p hp hg eta a C X W l H := by
  calc
    _ = fourthCarrierCubeBlock p hp.ne_zero
        (CompletedGauss.actualSextic (Ideal.span {p}) hg) eta a
        (primeGauss p hp.ne_zero (CompletedGauss.actualSextic (Ideal.span {p}) hg) 1)
        C (CompletedGauss.actualSextic (Ideal.span {p}) hg (-1)) X W l H := by
      unfold fourthPhysicalCubeBlock fourthCarrierCubeBlock
      dsimp only
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro k hk
      rw [fourthCarrierLocalFourier_physical p hp hg e.val l k.val (by omega) H]
    _ = _ := by
      unfold fourthCarrierCubeBlock fourthCarrierState fourthCarrierWaveBlock
      dsimp only
      simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
      ring

theorem fourthPhysicalCubeBlock_norm (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (hprimary : Dvd.dvd (goodLambda ^ 2) (p - 1))
    (eta a C X W : Complex) (hC : norm C <= 1) (l : Nat) (H : O) :
    norm (fourthPhysicalCubeBlock p hp hg eta a C X W l H) <=
      norm (a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex)) ^ l *
        (1 + norm (eta * X * W) +
          norm (eta * X) / (Ideal.absNorm (Ideal.span {p}) : Real) + norm W) := by
  have h0 := fourthCarrierBase_norm p hp hg hc eta a C X W hC l H
  have h1 := fourthCarrierShared_norm p hp hg hc eta a C X W hC l H
  have hT := fourthCarrierWaveBlock_norm p hp hg hc hprimary eta a C X W hC l H
  have hn0 := norm_add_le
    (fourthCarrierState p hp hg eta a C X W 0 l 0 H)
    (fourthCarrierState p hp hg eta a C X W 1 l 1 H)
  have hn1 := norm_add_le
    (fourthCarrierState p hp hg eta a C X W 0 l 0 H +
      fourthCarrierState p hp hg eta a C X W 1 l 1 H)
    (fourthCarrierWaveBlock p hp hg eta a C X W l H)
  rw [fourthPhysicalCubeBlock_decomposition]
  nlinarith

theorem fourthPhysicalCube_norm_summable (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (hprimary : Dvd.dvd (goodLambda ^ 2) (p - 1))
    (eta a C X W : Complex) (hC : norm C <= 1)
    (hv : norm (a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex)) < 1)
    (H : O) :
    Summable (fun l : Nat => norm (fourthPhysicalCubeBlock p hp hg eta a C X W l H)) := by
  let v := norm (a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex))
  let D := 1 + norm (eta * X * W) +
    norm (eta * X) / (Ideal.absNorm (Ideal.span {p}) : Real) + norm W
  have hs : Summable (fun l : Nat => v ^ l * D) :=
    (summable_geometric_of_lt_one (norm_nonneg _) hv).mul_right D
  exact Summable.of_nonneg_of_le (fun l => norm_nonneg _)
    (fun l => fourthPhysicalCubeBlock_norm p hp hg hc hprimary eta a C X W hC l H) hs

theorem fourthPhysicalCube_norm_tsum_le (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (hprimary : Dvd.dvd (goodLambda ^ 2) (p - 1))
    (eta a C X W : Complex) (hC : norm C <= 1)
    (hv : norm (a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex)) < 1)
    (H : O) :
    (tsum (fun l : Nat => norm (fourthPhysicalCubeBlock p hp hg eta a C X W l H))) <=
      (1 - norm (a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex))) ^ (-1 : Int) *
        (1 + norm (eta * X * W) +
          norm (eta * X) / (Ideal.absNorm (Ideal.span {p}) : Real) + norm W) := by
  let v := norm (a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex))
  let D := 1 + norm (eta * X * W) +
    norm (eta * X) / (Ideal.absNorm (Ideal.span {p}) : Real) + norm W
  have hs : Summable (fun l : Nat => v ^ l * D) :=
    (summable_geometric_of_lt_one (norm_nonneg _) hv).mul_right D
  calc
    _ <= tsum (fun l : Nat => v ^ l * D) :=
      Summable.tsum_le_tsum
        (fun l => fourthPhysicalCubeBlock_norm p hp hg hc hprimary eta a C X W hC l H)
        (fourthPhysicalCube_norm_summable p hp hg hc hprimary eta a C X W hC hv H) hs
    _ = _ := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one (norm_nonneg _) hv]
      simp only [zpow_neg, zpow_one]
      rfl

theorem fourthPhysicalCube_uniform_three (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (hprimary : Dvd.dvd (goodLambda ^ 2) (p - 1))
    (eta a C X W : Complex) (hC : norm C <= 1)
    (hv : norm (a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex)) <= 1 / 2)
    (hu : norm (eta * X * W) <= 1 / 4)
    (ha : norm (eta * X) / (Ideal.absNorm (Ideal.span {p}) : Real) <= 1 / 8)
    (hb : norm W <= 1 / 8) (H : O) :
    Summable (fun l : Nat => fourthPhysicalCubeBlock p hp hg eta a C X W l H) /\
      norm (tsum (fun l : Nat => fourthPhysicalCubeBlock p hp hg eta a C X W l H)) <= 3 := by
  have hv1 : norm (a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex)) < 1 := by
    linarith
  have hn := fourthPhysicalCube_norm_summable p hp hg hc hprimary eta a C X W hC hv1 H
  refine And.intro (summable_norm_iff.mp hn) ?_
  have he := (norm_tsum_le_tsum_norm hn).trans
    (fourthPhysicalCube_norm_tsum_le p hp hg hc hprimary eta a C X W hC hv1 H)
  have hi : (1 - norm (a * X ^ 3 /
      (Ideal.absNorm (Ideal.span {p}) : Complex))) ^ (-1 : Int) <= (2 : Real) := by
    simp only [zpow_neg, zpow_one]
    have hx : 0 < 1 - norm (a * X ^ 3 /
        (Ideal.absNorm (Ideal.span {p}) : Complex)) := by linarith
    have hd := div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 1)
      (by norm_num : (0 : Real) < 1 / 2)
      (by linarith : (1 / 2 : Real) <=
        1 - norm (a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex)))
    simpa only [one_div, inv_inv] using hd
  have hD : 0 <= 1 + norm (eta * X * W) +
      norm (eta * X) / (Ideal.absNorm (Ideal.span {p}) : Real) + norm W := by positivity
  have hm := mul_le_mul_of_nonneg_right hi hD
  nlinarith

end OAI.SevenEighths.ProbePowerGauss
