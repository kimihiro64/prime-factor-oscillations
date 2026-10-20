/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleZeroModeActual

/-!
# PowerSampleWaveKernel

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
open ProbeGauss ProbeEuler

variable {F : Type*} [Field F] [Fintype F]

def fourthPrimeFourier (chi : MulChar F Complex) (psi : AddChar F Complex)
    (e l k : Nat) (h : F) : Complex :=
  (Finset.univ.sum fun r : F =>
    (chi r ^ (4 * (e + 3 * l)) * frequencyGauss chi psi (-(r ^ 4)) ^ k) *
      psi (h * r)) / (Fintype.card F : Complex)

theorem fourthPrimeFourier_no_source (chi : MulChar F Complex)
    (h6 : chi ^ 6 = 1) (psi : AddChar F Complex)
    (e l : Nat) (he : e <= 1) (h : F) :
    fourthPrimeFourier chi psi e l 0 h =
      if e = 0 then
        if l = 0 then
          (Finset.univ.sum fun r : F => psi (h * r)) / (Fintype.card F : Complex)
        else frequencyGauss 1 psi h / (Fintype.card F : Complex)
      else frequencyGauss (chi ^ 4) psi h / (Fintype.card F : Complex) := by
  have hecases : e = 0 \/ e = 1 := by omega
  rcases hecases with rfl | rfl
  case inl =>
    by_cases hl : l = 0
    case pos =>
      subst l
      simp only [fourthPrimeFourier, Nat.zero_add, Nat.mul_zero, pow_zero,
        one_mul, ite_true]
    case neg =>
      simp only [fourthPrimeFourier, Nat.zero_add, pow_zero, mul_one,
        sextic_cube_unit_mask chi h6 (Nat.pos_of_ne_zero hl), ite_true, ite_eq_right hl]
      rfl
  case inr =>
    simp only [fourthPrimeFourier, pow_zero, mul_one, sextic_fourth_value chi h6,
      ite_eq_right (by decide : Not (1 = 0))]
    simp only [frequencyGauss, MulChar.pow_apply' chi (by decide : Not (4 = 0))]

theorem fourthPrimeFourier_source (chi : MulChar F Complex)
    (h6 : chi ^ 6 = 1) (h2 : Not (chi ^ 2 = 1))
    (psi : AddChar F Complex) (e l : Nat) (he : e <= 1) (h : F) :
    fourthPrimeFourier chi psi e l 1 h =
      if e = 0 then
        frequencyGauss chi psi (-1) *
          frequencyGauss (chi ^ 2) psi h / (Fintype.card F : Complex)
      else frequencyGauss chi psi (-1) *
          frequencyGauss 1 psi h / (Fintype.card F : Complex) := by
  have hc : Not (chi = 1) := by
    intro hz
    apply h2
    rw [hz, one_pow]
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
      simp only [fourthPrimeFourier, Nat.zero_add, Nat.mul_zero, pow_zero,
        pow_one, one_mul, ite_true]
      rw [unmasked_fourth_frequency chi hc psi psi h, hi]
    case neg =>
      simp only [fourthPrimeFourier, Nat.zero_add, pow_one,
        sextic_cube_unit_mask chi h6 (Nat.pos_of_ne_zero hl), ite_true]
      have he := power_fourier chi (1 : MulChar F Complex) psi psi
        (by decide : 0 < 4) h
      simp only [one_mul, hi] at he
      have hp (r : F) : (1 : MulChar F Complex) r ^ 4 =
          (1 : MulChar F Complex) r := by
        by_cases hr : r = 0
        case pos =>
          subst r
          rw [MulChar.map_zero, zero_pow (by decide : Not (4 = 0))]
        case neg =>
          rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hr), one_pow]
      simp_rw [hp] at he
      rw [he]
  case inr =>
    simp only [fourthPrimeFourier, pow_one, sextic_fourth_value chi h6,
      ite_eq_right (by decide : Not (1 = 0))]
    rw [power_fourier chi chi psi psi (by decide : 0 < 4) h]
    simp only [zpow_neg_one, mul_inv_cancel, one_pow]

def fourthWaveCubeBlock (chi : MulChar F Complex) (psi : AddChar F Complex)
    (eta a G1 C omega X W : Complex) (l : Nat) (h : F) : Complex :=
  Finset.univ.sum (fun e : Fin 2 =>
    Finset.univ.sum (fun k : Fin 2 =>
      weightedScalar (Fintype.card F : Complex) eta a G1 C omega X W 1
        (fourthPrimeFourier chi psi e.val l k.val h) e.val l k.val 0))

theorem cubePhase_source_cubic (C omega : Complex) (ho : omega ^ 2 = 1)
    (l : Nat) :
    localCubePhase C omega 0 l 1 = localCubePhase C omega 1 l 0 := by
  unfold localCubePhase
  simp only [zero_add, one_mul, mul_one, zero_mul, mul_zero, add_zero]
  rw [show 3 * l + l.choose 2 = l + l.choose 2 + 2 * l by omega,
    pow_add, pow_mul, ho, one_pow, mul_one]

theorem cubePhaseSeries_hasSum (C omega v : Complex) (hC : C ^ 2 = omega)
    (ho : omega ^ 2 = 1) (hv : norm (v ^ 2) < 1) (e : Nat) :
    HasSum (fun l : Nat => v ^ l * localCubePhase C omega e l 0)
      ((1 + C * omega ^ e * v) / (1 - v ^ 2)) := by
  have hg := hasSum_geometric_of_norm_lt_one hv
  have heven : HasSum (fun r : Nat =>
      v ^ (2 * r) * localCubePhase C omega e (2 * r) 0) ((1 - v ^ 2) ^ (-1 : Int)) := by
    simpa only [localCubePhase_even C omega hC ho, mul_zero, pow_zero, mul_one,
      pow_mul, zpow_neg_one] using hg
  have hodd : HasSum (fun r : Nat =>
      v ^ (2 * r + 1) * localCubePhase C omega e (2 * r + 1) 0)
      ((1 - v ^ 2) ^ (-1 : Int) * (v * C * omega ^ e)) := by
    have ht : HasSum (fun r : Nat => (v ^ 2) ^ r * (v * C * omega ^ e))
        ((1 - v ^ 2) ^ (-1 : Int) * (v * C * omega ^ e)) := by
      simpa only [zpow_neg_one] using hg.mul_right (v * C * omega ^ e)
    convert ht using 1
    funext r
    rw [cubePhase_odd C omega hC ho]
    simp only [mul_zero, zero_add, add_zero, pow_add, pow_mul, pow_one]
    ring
  have hs := HasSum.even_add_odd
    (f := fun l : Nat => v ^ l * localCubePhase C omega e l 0) heven hodd
  convert hs using 1
  simp only [div_eq_mul_inv, zpow_neg_one]
  ring

theorem fourthWaveCubeBlock_eq (chi : MulChar F Complex)
    (h6 : chi ^ 6 = 1) (h2 : Not (chi ^ 2 = 1))
    (psi : AddChar F Complex) (eta a G1 C omega X W : Complex)
    (hG1 : Not (G1 = 0)) (ho : omega ^ 2 = 1)
    (hminus : frequencyGauss chi psi (-1) = omega * G1) (l : Nat) (h : F) :
    let q : Complex := Fintype.card F
    let v : Complex := a * X ^ 3 / q
    let R : Complex := frequencyGauss 1 psi h / q
    let D : Complex := (Finset.univ.sum fun r : F => psi (h * r)) / q
    let T : Complex :=
      (-eta * X / G1) * frequencyGauss (chi ^ 4) psi h / q +
        W * frequencyGauss chi psi (-1) * frequencyGauss (chi ^ 2) psi h / q
    fourthWaveCubeBlock chi psi eta a G1 C omega X W l h =
      (if l = 0 then D - R else 0) +
        v ^ l * localCubePhase C omega 0 l 0 * (1 - eta * X * W) * R +
        v ^ l * localCubePhase C omega 1 l 0 * T := by
  dsimp only
  unfold fourthWaveCubeBlock
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  rw [fourthPrimeFourier_no_source chi h6 psi 0 l (by decide),
    fourthPrimeFourier_source chi h6 h2 psi 0 l (by decide),
    fourthPrimeFourier_no_source chi h6 psi 1 l (by decide),
    fourthPrimeFourier_source chi h6 h2 psi 1 l (by decide)]
  simp only [ite_true, ite_false, Nat.one_ne_zero]
  unfold weightedScalar
  simp only [pow_zero, pow_one, mul_one, one_mul]
  rw [cubePhase_source_cubic C omega ho]
  calc
    _ = (a * X ^ 3 / (Fintype.card F : Complex)) ^ l *
          localCubePhase C omega 0 l 0 *
            (if l = 0 then
              (Finset.univ.sum fun r : F => psi (h * r)) / (Fintype.card F : Complex)
            else frequencyGauss 1 psi h / (Fintype.card F : Complex)) -
        (a * X ^ 3 / (Fintype.card F : Complex)) ^ l *
          (localCubePhase C omega 1 l 1 * omega) * eta * X * W *
            (frequencyGauss 1 psi h / (Fintype.card F : Complex)) +
        (a * X ^ 3 / (Fintype.card F : Complex)) ^ l *
          localCubePhase C omega 1 l 0 *
          ((-eta * X / G1) * frequencyGauss (chi ^ 4) psi h / (Fintype.card F : Complex) +
            W * frequencyGauss chi psi (-1) * frequencyGauss (chi ^ 2) psi h /
              (Fintype.card F : Complex)) := by
      rw [hminus]
      field_simp
      <;> ring
    _ = _ := by
      rw [cubePhase_shared_cancel C omega ho]
      by_cases hl : l = 0
      case pos =>
        subst l
        simp only [ite_true, pow_zero, localCubePhase, Nat.choose_zero_right,
          Nat.choose_eq_zero_of_lt (by decide : 0 < 2), mul_zero, zero_add,
          add_zero, pow_zero, mul_one]
        ring
      case neg =>
        simp only [ite_eq_right hl]
        ring

theorem fourthWaveCube_hasSum (chi : MulChar F Complex)
    (h6 : chi ^ 6 = 1) (h2 : Not (chi ^ 2 = 1))
    (psi : AddChar F Complex) (eta a G1 C omega X W : Complex)
    (hG1 : Not (G1 = 0)) (hC : C ^ 2 = omega) (ho : omega ^ 2 = 1)
    (hminus : frequencyGauss chi psi (-1) = omega * G1)
    (hv : norm ((a * X ^ 3 / (Fintype.card F : Complex)) ^ 2) < 1) (h : F) :
    let q : Complex := Fintype.card F
    let v : Complex := a * X ^ 3 / q
    let R : Complex := frequencyGauss 1 psi h / q
    let D : Complex := (Finset.univ.sum fun r : F => psi (h * r)) / q
    let H0 : Complex := (1 + C * v) / (1 - v ^ 2)
    let H1 : Complex := (1 + C * omega * v) / (1 - v ^ 2)
    let T : Complex :=
      (-eta * X / G1) * frequencyGauss (chi ^ 4) psi h / q +
        W * frequencyGauss chi psi (-1) * frequencyGauss (chi ^ 2) psi h / q
    HasSum (fun l : Nat => fourthWaveCubeBlock chi psi eta a G1 C omega X W l h)
      (D + ((1 - eta * X * W) * H0 - 1) * R + H1 * T) := by
  let q : Complex := Fintype.card F
  let v : Complex := a * X ^ 3 / q
  let R : Complex := frequencyGauss 1 psi h / q
  let D : Complex := (Finset.univ.sum fun r : F => psi (h * r)) / q
  let H0 : Complex := (1 + C * v) / (1 - v ^ 2)
  let H1 : Complex := (1 + C * omega * v) / (1 - v ^ 2)
  let T : Complex :=
    (-eta * X / G1) * frequencyGauss (chi ^ 4) psi h / q +
      W * frequencyGauss chi psi (-1) * frequencyGauss (chi ^ 2) psi h / q
  have h0 : HasSum (fun l : Nat => v ^ l * localCubePhase C omega 0 l 0) H0 := by
    simpa only [pow_zero, mul_one] using cubePhaseSeries_hasSum C omega v hC ho hv 0
  have h1 : HasSum (fun l : Nat => v ^ l * localCubePhase C omega 1 l 0) H1 := by
    simpa only [pow_one] using cubePhaseSeries_hasSum C omega v hC ho hv 1
  have hd : HasSum (fun l : Nat => if l = 0 then D - R else 0) (D - R) :=
    hasSum_ite_eq (0 : Nat) (D - R)
  have hs := (hd.add (h0.mul_right ((1 - eta * X * W) * R))).add (h1.mul_right T)
  convert hs using 1
  next =>
    funext l
    simpa only [q, v, R, D, T, mul_assoc] using
      fourthWaveCubeBlock_eq chi h6 h2 psi eta a G1 C omega X W hG1 ho hminus l h
  next =>
    dsimp only [H0, H1]
    ring

end
end OAI.SevenEighths.ProbePowerGauss
