/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSamplePhysicalCRT

/-!
# PowerSampleZeroMode

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

set_option maxHeartbeats 2200000

namespace OAI.SevenEighths.ProbePowerGauss
noncomputable section
open scoped Classical BigOperators
open ProbeGauss

variable {F : Type*} [Field F] [Fintype F]

theorem sextic_fourth_value (chi : MulChar F Complex) (h6 : chi ^ 6 = 1)
    (l : Nat) (r : F) :
    chi r ^ (4 * (1 + 3 * l)) = chi r ^ 4 := by
  have he : chi ^ (4 * (1 + 3 * l)) = chi ^ 4 := by
    rw [show 4 * (1 + 3 * l) = 4 + 6 * (2 * l) by omega,
      pow_add, pow_mul, h6, one_pow, mul_one]
  calc
    _ = (chi ^ (4 * (1 + 3 * l))) r :=
      (MulChar.pow_apply' chi (by omega) r).symm
    _ = (chi ^ 4) r := by rw [he]
    _ = _ := MulChar.pow_apply' chi (by decide) r

theorem sextic_cube_unit_mask (chi : MulChar F Complex) (h6 : chi ^ 6 = 1)
    {l : Nat} (hl : 0 < l) (r : F) :
    chi r ^ (4 * (3 * l)) = (1 : MulChar F Complex) r := by
  have he : chi ^ (4 * (3 * l)) = 1 := by
    rw [show 4 * (3 * l) = 6 * (2 * l) by omega, pow_mul, h6, one_pow]
  calc
    _ = (chi ^ (4 * (3 * l))) r :=
      (MulChar.pow_apply' chi (by omega) r).symm
    _ = _ := by rw [he]

theorem unmasked_fourth_frequency (chi : MulChar F Complex)
    (hchi : Not (chi = 1)) (psi psiFourier : AddChar F Complex)
    (h : F) :
    (Finset.univ.sum fun r : F =>
      frequencyGauss chi psi (-(r ^ 4)) * psiFourier (h * r)) =
      frequencyGauss chi psi (-1) *
        frequencyGauss ((chi ^ (-1 : Int)) ^ 4) psiFourier h := by
  have he := power_fourier chi 1 psi psiFourier (by decide : 0 < 4) h
  simp only [one_mul] at he
  rw [<-he]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hz : r = 0
  case pos =>
    subst r
    simp only [MulChar.map_zero, zero_pow (by decide : Not (4 = 0)),
      neg_zero, frequencyGauss_zero_nonprincipal chi psi hchi, mul_zero, zero_mul]
  case neg =>
    rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hz), one_pow, one_mul]

def fourthPrimeAverage (chi : MulChar F Complex) (psi : AddChar F Complex)
    (e l k : Nat) : Complex :=
  (Finset.univ.sum fun r : F =>
    chi r ^ (4 * (e + 3 * l)) * frequencyGauss chi psi (-(r ^ 4)) ^ k) /
      (Fintype.card F : Complex)

theorem fourthPrimeAverage_no_source (chi : MulChar F Complex)
    (h6 : chi ^ 6 = 1) (h2 : Not (chi ^ 2 = 1))
    (psi : AddChar F Complex) (e l : Nat) (he : e <= 1) :
    fourthPrimeAverage chi psi e l 0 =
      if e = 0 then
        if l = 0 then 1
        else (Fintype.card (Units F) : Complex) / (Fintype.card F : Complex)
      else 0 := by
  have hq : Not ((Fintype.card F : Complex) = 0) := by
    exact_mod_cast Fintype.card_ne_zero
  have h4 : Not (chi ^ 4 = 1) := by
    intro h
    exact h2 ((sextic_fourth_resonance chi h6).mp h)
  have hecases : e = 0 \/ e = 1 := by omega
  rcases hecases with rfl | rfl
  case inl =>
    by_cases hl : l = 0
    case pos =>
      subst l
      simp only [fourthPrimeAverage, Nat.zero_add, Nat.mul_zero, pow_zero,
        mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        if_pos rfl]
      exact div_self hq
    case neg =>
      simp only [fourthPrimeAverage, Nat.zero_add, pow_zero, mul_one,
        sextic_cube_unit_mask chi h6 (Nat.pos_of_ne_zero hl), if_pos rfl, if_neg hl]
      congr 1
      exact MulChar.sum_one_eq_card_units
  case inr =>
    simp only [fourthPrimeAverage, pow_zero, mul_one, sextic_fourth_value chi h6,
      if_neg (by decide : Not (1 = 0))]
    have hz : (Finset.univ.sum fun r : F => chi r ^ 4) = 0 := by
      simpa only [MulChar.pow_apply' chi (by decide : Not (4 = 0))] using
        MulChar.sum_eq_zero_of_ne_one h4
    rw [hz, zero_div]

theorem fourthPrimeAverage_source (chi : MulChar F Complex)
    (h6 : chi ^ 6 = 1) (h2 : Not (chi ^ 2 = 1))
    (psi : AddChar F Complex) (e l : Nat) (he : e <= 1) :
    fourthPrimeAverage chi psi e l 1 =
      if e = 0 then 0 else
        frequencyGauss chi psi (-1) *
          (Fintype.card (Units F) : Complex) / (Fintype.card F : Complex) := by
  have hc : Not (chi = 1) := by
    intro h
    apply h2
    rw [h, one_pow]
  have hi : (chi ^ (-1 : Int)) ^ 4 = chi ^ 2 := by
    rw [zpow_neg_one, inv_pow]
    apply inv_eq_of_mul_eq_one_right
    rw [<-pow_add]
    exact h6
  have hecases : e = 0 \/ e = 1 := by omega
  rcases hecases with rfl | rfl
  case inl =>
    by_cases hl : l = 0
    case pos =>
      subst l
      simp only [fourthPrimeAverage, Nat.zero_add, Nat.mul_zero, pow_zero, pow_one,
        one_mul, ite_true]
      have hz := unmasked_fourth_frequency chi hc psi (1 : AddChar F Complex) 0
      simp only [AddChar.one_apply, mul_one, hi,
        frequencyGauss_zero_nonprincipal (chi ^ 2) (1 : AddChar F Complex) h2] at hz
      rw [hz, mul_zero, zero_div]
    case neg =>
      simp only [fourthPrimeAverage, Nat.zero_add, pow_one,
        sextic_cube_unit_mask chi h6 (Nat.pos_of_ne_zero hl), ite_true]
      have hz := power_correlation chi (1 : MulChar F Complex) psi (by decide : 0 < 4)
      simp only [one_mul, hi, if_neg h2] at hz
      have hp (r : F) : (1 : MulChar F Complex) r ^ 4 =
          (1 : MulChar F Complex) r := by
        by_cases hr : r = 0
        case pos =>
          subst r
          rw [MulChar.map_zero, zero_pow (by decide : Not (4 = 0))]
        case neg => rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hr), one_pow]
      simp_rw [hp] at hz
      rw [hz, mul_zero, zero_div]
  case inr =>
    simp only [fourthPrimeAverage, pow_one, sextic_fourth_value chi h6,
      if_neg (by decide : Not (1 = 0))]
    rw [diagonal_correlation chi psi (by decide : 0 < 4)]

open ProbeEuler

theorem cubePhase_shared_cancel (C omega : Complex) (ho : omega ^ 2 = 1)
    (l : Nat) :
    localCubePhase C omega 1 l 1 * omega = localCubePhase C omega 0 l 0 := by
  unfold localCubePhase
  simp only [one_mul, mul_one, zero_mul, zero_add, add_zero]
  rw [mul_assoc, <-pow_succ]
  have he : 1 + 3 * l + l + l.choose 2 + 1 = l.choose 2 + 2 * (2 * l + 1) := by omega
  rw [he, pow_add, pow_mul, ho, one_pow, mul_one]
  simp only [mul_zero, zero_add]

theorem cubePhase_odd (C omega : Complex) (hC : C ^ 2 = omega)
    (ho : omega ^ 2 = 1) (e r k : Nat) :
    localCubePhase C omega e (2 * r + 1) k = C * omega ^ (e * k + e + k) := by
  have hs (l : Nat) :
      localCubePhase C omega e (l + 1) k =
        C * omega ^ (3 * k + e + l) * localCubePhase C omega e l k := by
    have he :
        (e + 3 * (l + 1)) * k + e * (l + 1) + (l + 1).choose 2 =
        ((e + 3 * l) * k + e * l + l.choose 2) + (3 * k + e + l) := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      ring
    unfold localCubePhase
    rw [he, pow_add, pow_succ]
    ring
  rw [hs, localCubePhase_even C omega hC ho]
  have he : omega ^ (3 * k + e + 2 * r) = omega ^ (e + k) := by
    rw [show 3 * k + e + 2 * r = e + k + 2 * (k + r) by ring,
      pow_add, pow_mul, ho, one_pow, mul_one]
  rw [he, mul_assoc, <-pow_add]
  congr 2
  omega

def fourthZeroCubeBlock (chi : MulChar F Complex) (psi : AddChar F Complex)
    (eta a G1 C omega X W : Complex) (l : Nat) : Complex :=
  Finset.univ.sum (fun e : Fin 2 =>
    Finset.univ.sum (fun k : Fin 2 =>
      weightedScalar (Fintype.card F : Complex) eta a G1 C omega X W 1
        (fourthPrimeAverage chi psi e.val l k.val) e.val l k.val 0))

theorem fourthZeroCubeBlock_eq (chi : MulChar F Complex)
    (h6 : chi ^ 6 = 1) (h2 : Not (chi ^ 2 = 1))
    (psi : AddChar F Complex) (eta a G1 C omega X W : Complex)
    (hG1 : Not (G1 = 0)) (ho : omega ^ 2 = 1)
    (hminus : frequencyGauss chi psi (-1) = omega * G1) (l : Nat) :
    fourthZeroCubeBlock chi psi eta a G1 C omega X W l =
      (a * X ^ 3 / (Fintype.card F : Complex)) ^ l *
        localCubePhase C omega 0 l 0 *
        ((if l = 0 then 1 else
          (Fintype.card (Units F) : Complex) / (Fintype.card F : Complex)) -
          ((Fintype.card (Units F) : Complex) / (Fintype.card F : Complex)) *
            eta * X * W) := by
  unfold fourthZeroCubeBlock
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  rw [fourthPrimeAverage_no_source chi h6 h2 psi 0 l (by decide),
    fourthPrimeAverage_source chi h6 h2 psi 0 l (by decide),
    fourthPrimeAverage_no_source chi h6 h2 psi 1 l (by decide),
    fourthPrimeAverage_source chi h6 h2 psi 1 l (by decide)]
  simp only [ite_true, ite_false, Nat.one_ne_zero, weightedScalar_zero,
    add_zero, zero_add]
  rw [hminus]
  unfold weightedScalar
  simp only [pow_zero, pow_one, mul_one, one_mul]
  calc
    _ = (a * X ^ 3 / (Fintype.card F : Complex)) ^ l *
        localCubePhase C omega 0 l 0 *
          (if l = 0 then 1 else
            (Fintype.card (Units F) : Complex) / (Fintype.card F : Complex)) -
      (a * X ^ 3 / (Fintype.card F : Complex)) ^ l *
        (localCubePhase C omega 1 l 1 * omega) *
          ((Fintype.card (Units F) : Complex) / (Fintype.card F : Complex)) *
            eta * X * W := by
      field_simp
      <;> ring
    _ = _ := by
      rw [cubePhase_shared_cancel C omega ho]
      ring

theorem fourthZeroCubePair (chi : MulChar F Complex)
    (h6 : chi ^ 6 = 1) (h2 : Not (chi ^ 2 = 1))
    (psi : AddChar F Complex) (eta a G1 C omega X W : Complex)
    (hG1 : Not (G1 = 0)) (hC : C ^ 2 = omega) (ho : omega ^ 2 = 1)
    (hminus : frequencyGauss chi psi (-1) = omega * G1) (r : Nat) :
    let v : Complex := a * X ^ 3 / (Fintype.card F : Complex)
    let c : Complex := (Fintype.card (Units F) : Complex) / (Fintype.card F : Complex)
    fourthZeroCubeBlock chi psi eta a G1 C omega X W (2 * r) +
      fourthZeroCubeBlock chi psi eta a G1 C omega X W (2 * r + 1) =
      (if r = 0 then 1 - c else 0) +
        (v ^ 2) ^ r * (c * (1 - eta * X * W) * (1 + C * v)) := by
  dsimp only
  rw [fourthZeroCubeBlock_eq chi h6 h2 psi eta a G1 C omega X W hG1 ho hminus,
    fourthZeroCubeBlock_eq chi h6 h2 psi eta a G1 C omega X W hG1 ho hminus,
    localCubePhase_even C omega hC ho, cubePhase_odd C omega hC ho]
  have he : 2 * r = 0 <-> r = 0 := by omega
  have hn : Not (2 * r + 1 = 0) := by omega
  simp only [zero_mul, zero_add, pow_zero, mul_one, he, ite_eq_right hn,
    pow_add, pow_mul, pow_one]
  by_cases hr : r = 0
  case pos =>
    subst r
    simp only [ite_true, pow_zero]
    ring
  case neg =>
    simp only [ite_eq_right hr]
    ring

theorem fourthZeroCubePaired_hasSum (chi : MulChar F Complex)
    (h6 : chi ^ 6 = 1) (h2 : Not (chi ^ 2 = 1))
    (psi : AddChar F Complex) (eta a G1 C omega X W : Complex)
    (hG1 : Not (G1 = 0)) (hC : C ^ 2 = omega) (ho : omega ^ 2 = 1)
    (hminus : frequencyGauss chi psi (-1) = omega * G1)
    (hv : norm ((a * X ^ 3 / (Fintype.card F : Complex)) ^ 2) < 1) :
    let v : Complex := a * X ^ 3 / (Fintype.card F : Complex)
    let c : Complex := (Fintype.card (Units F) : Complex) / (Fintype.card F : Complex)
    HasSum (fun r : Nat =>
      fourthZeroCubeBlock chi psi eta a G1 C omega X W (2 * r) +
        fourthZeroCubeBlock chi psi eta a G1 C omega X W (2 * r + 1))
      ((1 - c) + c * (1 - eta * X * W) * (1 + C * v) / (1 - v ^ 2)) := by
  let v : Complex := a * X ^ 3 / (Fintype.card F : Complex)
  let c : Complex := (Fintype.card (Units F) : Complex) / (Fintype.card F : Complex)
  let B : Complex := c * (1 - eta * X * W) * (1 + C * v)
  have hg : HasSum (fun r : Nat => (v ^ 2) ^ r * B) ((1 - v ^ 2) ^ (-1 : Int) * B) := by
    simpa only [zpow_neg_one] using (hasSum_geometric_of_norm_lt_one hv).mul_right B
  have hd : HasSum (fun r : Nat => if r = 0 then 1 - c else 0) (1 - c) :=
    hasSum_ite_eq (0 : Nat) (1 - c)
  have hs := hd.add hg
  convert hs using 1
  next =>
    funext r
    exact fourthZeroCubePair chi h6 h2 psi eta a G1 C omega X W hG1 hC ho hminus r
  next =>
    dsimp only [B]
    simp only [zpow_neg_one, div_eq_mul_inv]
    ring

theorem fourthZeroCube_hasSum (chi : MulChar F Complex)
    (h6 : chi ^ 6 = 1) (h2 : Not (chi ^ 2 = 1))
    (psi : AddChar F Complex) (eta a G1 C omega X W : Complex)
    (hG1 : Not (G1 = 0)) (hC : C ^ 2 = omega) (ho : omega ^ 2 = 1)
    (hminus : frequencyGauss chi psi (-1) = omega * G1)
    (hv : norm ((a * X ^ 3 / (Fintype.card F : Complex)) ^ 2) < 1) :
    let v : Complex := a * X ^ 3 / (Fintype.card F : Complex)
    let c : Complex := (Fintype.card (Units F) : Complex) / (Fintype.card F : Complex)
    HasSum (fourthZeroCubeBlock chi psi eta a G1 C omega X W)
      ((1 - c) + c * (1 - eta * X * W) * (1 + C * v) / (1 - v ^ 2)) := by
  let v : Complex := a * X ^ 3 / (Fintype.card F : Complex)
  let c : Complex := (Fintype.card (Units F) : Complex) / (Fintype.card F : Complex)
  let E : Complex := (1 - c) + c * (1 - eta * X * W) * (1 + C * v) / (1 - v ^ 2)
  let D : Complex := v * C * c * (1 - eta * X * W)
  let S : Complex := (1 - v ^ 2) ^ (-1 : Int) * D
  change HasSum _ E
  have hp := fourthZeroCubePaired_hasSum chi h6 h2 psi eta a G1 C omega X W
    hG1 hC ho hminus hv
  change HasSum _ E at hp
  have hg : HasSum (fun r : Nat => (v ^ 2) ^ r * D) S := by
    simpa only [S, zpow_neg_one] using (hasSum_geometric_of_norm_lt_one hv).mul_right D
  have hodd : HasSum (fun r : Nat =>
      fourthZeroCubeBlock chi psi eta a G1 C omega X W (2 * r + 1)) S := by
    convert hg using 1
    funext r
    rw [fourthZeroCubeBlock_eq chi h6 h2 psi eta a G1 C omega X W hG1 ho hminus,
      cubePhase_odd C omega hC ho]
    have hn : Not (2 * r + 1 = 0) := by omega
    simp only [zero_mul, zero_add, pow_zero, mul_one, ite_eq_right hn,
      pow_add, pow_mul, pow_one]
    dsimp only [v, D, c]
    ring
  have heven : HasSum (fun r : Nat =>
      fourthZeroCubeBlock chi psi eta a G1 C omega X W (2 * r)) (E - S) := by
    simpa only [add_sub_cancel_right] using hp.sub hodd
  simpa only [sub_add_cancel] using heven.even_add_odd hodd

end
end OAI.SevenEighths.ProbePowerGauss
