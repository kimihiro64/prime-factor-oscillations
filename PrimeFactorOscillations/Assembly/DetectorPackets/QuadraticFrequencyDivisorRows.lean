/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticFullFrequencyBand
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticFullFrequencyUnit

/-!
# QuadraticFrequencyDivisorRows

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
open scoped BigOperators Classical

namespace PrimeFactorOscillations.QuadraticFrequencyDivisorRows

open QuadraticSmoothBandRows CoprimeSchwartzSplit
open QuadraticFullFrequencyBand QuadraticFullFrequencyUnit

def rowMean (R S T : Finset Nat) (a b : Nat -> Complex)
    (F : SchwartzMap Real Complex) (L : Nat) (e X : Real) (d : Nat) : Real :=
  (1 / (d : Real)) * R.sum (fun r =>
    norm ((S.product T).sum (fun q => coefficient a b d r q.1 q.2 *
      frequencyPacket L F
        (Real.sqrt (e * (q.1 : Real) * (q.2 : Real) / (X * (r : Real))) / (d : Real)))))

def rangeMean (Y Z : Nat) (R S T : Finset Nat) (a b : Nat -> Complex)
    (F : SchwartzMap Real Complex) (L : Nat) (e X : Real) : Real :=
  (Finset.Ioc Y Z).sum (rowMean R S T a b F L e X)

theorem rowMean_nonneg (R S T : Finset Nat) (a b : Nat -> Complex)
    (F : SchwartzMap Real Complex) (L : Nat) (e X : Real) (d : Nat) :
    0 <= rowMean R S T a b F L e X d := by
  unfold rowMean
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun r hr => norm_nonneg _))

theorem rowMean_one (R S T : Finset Nat) (a b : Nat -> Complex)
    (F : SchwartzMap Real Complex) (L : Nat) (e X : Real) :
    rowMean R S T a b F L e X 1 = fullFrequencyUnitMean R S T a b F L e X := by
  simp only [rowMean, fullFrequencyUnitMean, Nat.cast_one, div_one, one_mul]

theorem band_sum (D : Nat) (R S T : Finset Nat) (a b : Nat -> Complex)
    (F : SchwartzMap Real Complex) (L : Nat) (e X : Real) :
    (Finset.Ioc D (2 * D)).sum (rowMean R S T a b F L e X) =
      fullFrequencyBandMean D R S T a b F L e X := by
  unfold rowMean fullFrequencyBandMean bandRows
  calc
    _ = (Finset.Ioc D (2 * D)).sum (fun d => R.sum (fun r =>
        (1 / (d : Real)) *
        norm ((S.product T).sum (fun q => coefficient a b d r q.1 q.2 *
          frequencyPacket L F
            (Real.sqrt (e * (q.1 : Real) * (q.2 : Real) / (X * (r : Real))) / (d : Real)))))) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.mul_sum R _ (1 / (d : Real))
    _ = _ := (Finset.sum_product (Finset.Ioc D (2 * D)) R
      (fun p => (1 / (p.1 : Real)) *
        norm ((S.product T).sum (fun q => coefficient a b p.1 p.2 q.1 q.2 *
          frequencyPacket L F
            (Real.sqrt (e * (q.1 : Real) * (q.2 : Real) / (X * (p.2 : Real))) /
              (p.1 : Real)))))).symm

end PrimeFactorOscillations.QuadraticFrequencyDivisorRows

