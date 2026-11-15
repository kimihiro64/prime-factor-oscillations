/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGammaAffine
import PrimeFactorOscillations.Helpers.HamiltonianSpectralTaylor

/-! # Signed determinant and covariance product averaging

All three terms of the affine-product remainder are retained. The determinant
estimates come from the actual spectral factor Taylor theorem and central
ratio, and the Gamma consumer cancels only the complete signed linear term.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*}

def spectralAffineRemainderBound (S : Finset Iota) (lam : Iota -> Real)
    (delta eps : Real) : Real :=
  abs (spectralFactorJet2 S lam 1 / 2) +
    abs (spectralFactorJet3 S lam 1 / 6) * eps +
    spectralTaylorRemainderBound S lam delta * eps ^ 2

theorem spectralFactors_affine_remainder (S : Finset Iota) (lam : Iota -> Real)
    (delta eps s : Real) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hEps0 : 0 <= eps) (hEps1 : eps <= delta / 4)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hSmall : 2 * (Finset.sum S lam) * eps <= delta)
    (hs : abs (s - 1) <= eps) :
    abs (spectralFactors S lam s - spectralFactors S lam 1 -
        spectralFactorJet1 S lam 1 * (s - 1)) <=
      spectralAffineRemainderBound S lam delta eps * (s - 1) ^ 2 := by
  let t := s - 1
  let c := spectralFactorJet2 S lam 1 / 2
  let d := spectralFactorJet3 S lam 1 / 6
  let R := spectralTaylorRemainderBound S lam delta
  have hMass : 0 <= Finset.sum S lam := Finset.sum_nonneg (fun i hi => hLam0 i hi)
  have hR : 0 <= R := by
    dsimp only [R, spectralTaylorRemainderBound]
    have hPos : 0 < spectralFactors S lam 1 := Real.exp_pos _
    positivity
  have hT : abs t <= eps := hs
  have hT2 : t ^ 2 <= eps ^ 2 := by
    have h := abs_le.mp hT
    nlinarith only [h.1, h.2, sq_nonneg (eps - t), sq_nonneg (eps + t)]
  have hT4 : t ^ 4 <= eps ^ 2 * t ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hT2 (sq_nonneg t)
    nlinarith only [h]
  have hT3 : abs (t ^ 3) <= eps * t ^ 2 := by
    calc
      _ = abs t * t ^ 2 := by rw [show t ^ 3 = t * t ^ 2 by ring, abs_mul,
        abs_of_nonneg (sq_nonneg t)]
      _ <= _ := mul_le_mul_of_nonneg_right hT (sq_nonneg t)
  have hTaylor := spectralFactors_taylor_remainder S lam delta eps s
    hDelta0 hDelta1 hEps0 hEps1 hLam0 hLam1 hSmall hs
  have hId : spectralFactors S lam s - spectralFactors S lam 1 -
      spectralFactorJet1 S lam 1 * t =
      (spectralFactors S lam s - spectralTaylorCubic S lam s) +
        c * t ^ 2 + d * t ^ 3 := by
    dsimp only [spectralTaylorCubic, gammaCubic, c, d, t]
    ring
  change abs (spectralFactors S lam s - spectralFactors S lam 1 -
    spectralFactorJet1 S lam 1 * t) <= _
  rw [hId]
  have hA := abs_add_le (spectralFactors S lam s - spectralTaylorCubic S lam s) (c * t ^ 2)
  have hB := abs_add_le
    ((spectralFactors S lam s - spectralTaylorCubic S lam s) + c * t ^ 2) (d * t ^ 3)
  rw [abs_mul, abs_of_nonneg (sq_nonneg t)] at hA
  rw [abs_mul] at hB
  have hC := mul_le_mul_of_nonneg_left hT3 (abs_nonneg d)
  have hD := mul_le_mul_of_nonneg_left hT4 hR
  change abs (spectralFactors S lam s - spectralTaylorCubic S lam s) <= R * t ^ 4 at hTaylor
  change _ <= (abs c + abs d * eps + R * eps ^ 2) * t ^ 2
  nlinarith only [hA, hB, hC, hD, hTaylor]

theorem spectralFactors_first_increment (S : Finset Iota) (lam : Iota -> Real)
    (delta eps s : Real) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hEps0 : 0 <= eps) (hEps1 : eps <= delta / 4)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hSmall : 2 * (Finset.sum S lam) * eps <= delta)
    (hs : abs (s - 1) <= eps) :
    abs (spectralFactors S lam s - spectralFactors S lam 1) <=
      (abs (spectralFactorJet1 S lam 1) +
        spectralAffineRemainderBound S lam delta eps * eps) * abs (s - 1) := by
  have hRem := spectralFactors_affine_remainder S lam delta eps s
    hDelta0 hDelta1 hEps0 hEps1 hLam0 hLam1 hSmall hs
  have hR : 0 <= spectralAffineRemainderBound S lam delta eps := by
    unfold spectralAffineRemainderBound spectralTaylorRemainderBound
    have hPos : 0 < spectralFactors S lam 1 := Real.exp_pos _
    have hMass := Finset.sum_nonneg (fun i hi => hLam0 i hi)
    positivity
  have hT : (s - 1) ^ 2 <= eps * abs (s - 1) := by
    have h := mul_le_mul_of_nonneg_right hs (abs_nonneg (s - 1))
    nlinarith only [h, sq_abs (s - 1)]
  have hId : spectralFactors S lam s - spectralFactors S lam 1 =
      (spectralFactors S lam s - spectralFactors S lam 1 -
        spectralFactorJet1 S lam 1 * (s - 1)) +
        spectralFactorJet1 S lam 1 * (s - 1) := by ring
  rw [hId]
  have h := abs_add_le
    (spectralFactors S lam s - spectralFactors S lam 1 -
      spectralFactorJet1 S lam 1 * (s - 1))
    (spectralFactorJet1 S lam 1 * (s - 1))
  rw [abs_mul] at h
  have hMul := mul_le_mul_of_nonneg_left hT hR
  nlinarith only [h, hRem, hMul]

def spectralCorrectionProductRemainderBound (S : Finset Iota) (lam : Iota -> Real)
    (delta eps G0 G1 G2 : Real) : Real :=
  spectralAffineRemainderBound S lam delta eps * G0 +
    (abs (spectralFactorJet1 S lam 1) +
      spectralAffineRemainderBound S lam delta eps * eps) * G1 +
    Real.exp 1 * spectralFactors S lam 1 * G2

theorem spectralFactors_signed_product_remainder
    (S : Finset Iota) (lam : Iota -> Real)
    (delta eps : Real) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hEps0 : 0 <= eps) (hEps1 : eps <= delta / 4)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hSmall : 2 * (Finset.sum S lam) * eps <= delta)
    (g : Real -> Real) (g1 G0 G1 G2 : Real)
    (hG0 : 0 <= G0) (hG1 : 0 <= G1) (hG2 : 0 <= G2)
    (hg0 : abs (g 1) <= G0) (hg1 : abs g1 <= G1)
    (hg2 : forall s, abs (s - 1) <= eps ->
      abs (g s - g 1 - (s - 1) * g1) <= G2 * (s - 1) ^ 2)
    (s : Real) (hs : abs (s - 1) <= eps) :
    abs (spectralFactors S lam s * g s -
      gammaCubic (spectralFactors S lam 1 * g 1)
        (spectralFactors S lam 1 * g1 + spectralFactorJet1 S lam 1 * g 1) 0 0 s) <=
      spectralCorrectionProductRemainderBound S lam delta eps G0 G1 G2 *
        (s - 1) ^ 2 := by
  let D := spectralFactors S lam
  let D1 := spectralFactorJet1 S lam 1
  let R := spectralAffineRemainderBound S lam delta eps
  let t := s - 1
  have hR : 0 <= R := by
    dsimp only [R, spectralAffineRemainderBound, spectralTaylorRemainderBound]
    have hPos : 0 < spectralFactors S lam 1 := Real.exp_pos _
    have hMass := Finset.sum_nonneg (fun i hi => hLam0 i hi)
    positivity
  have hDs : abs (D s) <= Real.exp 1 * D 1 := by
    have hPositive : 0 < D s := Real.exp_pos _
    rw [abs_of_pos hPositive]
    exact spectralFactors_central_ratio S lam delta eps s hDelta0 hDelta1
      hEps0 hEps1 hLam0 hLam1 hSmall hs
  have hD2 := spectralFactors_affine_remainder S lam delta eps s hDelta0 hDelta1
    hEps0 hEps1 hLam0 hLam1 hSmall hs
  have hDInc := spectralFactors_first_increment S lam delta eps s hDelta0 hDelta1
    hEps0 hEps1 hLam0 hLam1 hSmall hs
  have hId : D s * g s - gammaCubic (D 1 * g 1) (D 1 * g1 + D1 * g 1) 0 0 s =
      (D s - D 1 - D1 * t) * g 1 +
        (D s - D 1) * g1 * t +
        D s * (g s - g 1 - t * g1) := by
    dsimp only [gammaCubic, t]
    ring
  change abs (D s * g s - gammaCubic (D 1 * g 1) (D 1 * g1 + D1 * g 1) 0 0 s) <= _
  rw [hId]
  have hFirst := mul_le_mul hD2 hg0 (abs_nonneg _) (mul_nonneg hR (sq_nonneg t))
  have hIncNonneg : 0 <=
      (abs (spectralFactorJet1 S lam 1) +
        spectralAffineRemainderBound S lam delta eps * eps) * abs (s - 1) :=
    mul_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg hR hEps0)) (abs_nonneg _)
  have hSecond := mul_le_mul hDInc hg1 (abs_nonneg _) hIncNonneg
  have hSecond' := mul_le_mul_of_nonneg_right hSecond (abs_nonneg t)
  have hCentral : 0 < D 1 := Real.exp_pos _
  have hThird := mul_le_mul hDs (hg2 s hs) (abs_nonneg _)
    (mul_nonneg (Real.exp_pos 1).le hCentral.le)
  have hA := abs_add_le ((D s - D 1 - D1 * t) * g 1) ((D s - D 1) * g1 * t)
  have hB := abs_add_le
    ((D s - D 1 - D1 * t) * g 1 + (D s - D 1) * g1 * t)
    (D s * (g s - g 1 - t * g1))
  simp only [abs_mul] at hA hB
  change _ <= (R * G0 + (abs D1 + R * eps) * G1 + Real.exp 1 * D 1 * G2) * t ^ 2
  change abs (D s - D 1 - D1 * t) * abs (g 1) <= R * t ^ 2 * G0 at hFirst
  change abs (D s - D 1) * abs g1 * abs t <=
    (abs D1 + R * eps) * abs t * G1 * abs t at hSecond'
  change abs (D s) * abs (g s - g 1 - t * g1) <=
    Real.exp 1 * D 1 * (G2 * t ^ 2) at hThird
  have hSecondFinal : abs (D s - D 1) * abs g1 * abs t <=
      (abs D1 + R * eps) * G1 * t ^ 2 := by
    calc
      _ <= (abs D1 + R * eps) * abs t * G1 * abs t := hSecond'
      _ = (abs D1 + R * eps) * G1 * (abs t) ^ 2 := by ring
      _ = _ := by rw [sq_abs]
  nlinarith only [hA, hB, hFirst, hSecondFinal, hThird]

end PrimeFactorOscillations
