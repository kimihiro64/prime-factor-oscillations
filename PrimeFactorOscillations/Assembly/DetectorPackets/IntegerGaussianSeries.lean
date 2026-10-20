/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerGaussianTail

/-!
# IntegerGaussianSeries

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

namespace PrimeFactorOscillations.IntegerGaussianSeries

open IntegerGaussianTail

def fullTerm (a : Real) (phase : Int -> Real) (n : Int) : Complex :=
  (Real.exp (-a * (n : Real) ^ 2) : Complex) *
    Complex.exp (Complex.I * (phase n : Complex))

theorem fullTerm_split (a : Real) (phase : Int -> Real) (n : Int) :
    fullTerm a phase n =
      (if n = 0 then Complex.exp (Complex.I * (phase 0 : Complex)) else 0) +
        offZeroTerm a phase n := by
  by_cases hn : n = 0
  . subst n
    simp [fullTerm, offZeroTerm]
  . simp only [fullTerm, offZeroTerm, ite_eq_right hn, zero_add]

theorem fullGaussian_decompose (a : Real) (ha : 0 < a) (phase : Int -> Real) :
    Summable (fullTerm a phase) /\
      tsum (fullTerm a phase) =
        Complex.exp (Complex.I * (phase 0 : Complex)) + offZeroGaussian a phase := by
  choose C hC hc using offZeroGaussian_bound
  have hTail := (hc a phase ha).1
  have hSingle : Summable (fun n : Int =>
      if n = 0 then Complex.exp (Complex.I * (phase 0 : Complex)) else 0) :=
    (hasSum_ite_eq (0 : Int) (Complex.exp (Complex.I * (phase 0 : Complex)))).summable
  have hPoint : fullTerm a phase = fun n : Int =>
      (if n = 0 then Complex.exp (Complex.I * (phase 0 : Complex)) else 0) +
        offZeroTerm a phase n := funext (fullTerm_split a phase)
  have hSum : Summable (fullTerm a phase) := by
    rw [hPoint]
    exact hSingle.add hTail
  refine And.intro hSum ?_
  calc
    _ = tsum (fun n : Int =>
        (if n = 0 then Complex.exp (Complex.I * (phase 0 : Complex)) else 0) +
          offZeroTerm a phase n) := by rw [hPoint]
    _ = tsum (fun n : Int =>
        if n = 0 then Complex.exp (Complex.I * (phase 0 : Complex)) else 0) +
          tsum (offZeroTerm a phase) := hSingle.tsum_add hTail
    _ = _ := by
      rw [(hasSum_ite_eq (0 : Int)
        (Complex.exp (Complex.I * (phase 0 : Complex)))).tsum_eq]
      rfl

end PrimeFactorOscillations.IntegerGaussianSeries

