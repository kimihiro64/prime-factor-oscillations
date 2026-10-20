/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import PrimeFactorOscillations.Proof.DetectorPackets.SchwartzQuadraticPullback

/-!
# SchwartzQuadraticSource

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section

namespace PrimeFactorOscillations.SchwartzQuadraticSource

open SchwartzQuadraticPullback

theorem fourier_even (f : Real -> Complex) (hf : forall x : Real, f (-x) = f x)
    (x : Real) :
    FourierTransform.fourier f (-x) = FourierTransform.fourier f x := by
  have heq : (fun y : Real => f (-y)) = f := funext hf
  calc
    _ = FourierTransformInv.fourierInv f x :=
      (Real.fourierInv_eq_fourier_neg f x).symm
    _ = FourierTransform.fourier (fun y : Real => f (-y)) x :=
      congrFun (Real.fourierInv_eq_fourier_comp_neg f) x
    _ = _ := by rw [heq]

def sourcePsi (W : SchwartzMap Real Complex) (a : Real) (ha : Not (a = 0)) :
    SchwartzMap Real Complex :=
  quadraticProfile a ha (FourierTransform.fourier W)

def sourceRho (W : SchwartzMap Real Complex) (a : Real) (ha : Not (a = 0)) :
    SchwartzMap Real Complex :=
  FourierTransform.fourier (sourcePsi W a ha)

theorem sourcePsi_apply (W : SchwartzMap Real Complex) (a : Real) (ha : Not (a = 0))
    (x : Real) : sourcePsi W a ha x = (FourierTransform.fourier W) (a * x ^ 2) :=
  quadraticProfile_apply a ha (FourierTransform.fourier W) x

theorem sourcePsi_even (W : SchwartzMap Real Complex) (a : Real) (ha : Not (a = 0))
    (x : Real) : sourcePsi W a ha (-x) = sourcePsi W a ha x :=
  quadraticProfile_even a ha (FourierTransform.fourier W) x

theorem sourcePsi_zero (W : SchwartzMap Real Complex) (a : Real) (ha : Not (a = 0)) :
    sourcePsi W a ha 0 = (FourierTransform.fourier W) 0 := by
  rw [sourcePsi_apply]
  simp only [zero_pow (by decide : Not (2 = 0)), mul_zero]

theorem sourceRho_even (W : SchwartzMap Real Complex) (a : Real) (ha : Not (a = 0))
    (x : Real) : sourceRho W a ha (-x) = sourceRho W a ha x := by
  have h := fourier_even (sourcePsi W a ha : Real -> Complex)
    (sourcePsi_even W a ha) x
  simpa only [sourceRho, <- SchwartzMap.fourier_coe] using h

theorem sourceRho_negative_argument (W : SchwartzMap Real Complex) (a : Real)
    (ha : Not (a = 0)) (ell d e n m X r : Real) :
    sourceRho W a ha ((-ell) / d * Real.sqrt (e * n * m / (X * r))) =
      sourceRho W a ha (ell / d * Real.sqrt (e * n * m / (X * r))) := by
  have harg : (-ell) / d * Real.sqrt (e * n * m / (X * r)) =
      -(ell / d * Real.sqrt (e * n * m / (X * r))) := by ring
  rw [harg]
  exact sourceRho_even W a ha _

end PrimeFactorOscillations.SchwartzQuadraticSource

