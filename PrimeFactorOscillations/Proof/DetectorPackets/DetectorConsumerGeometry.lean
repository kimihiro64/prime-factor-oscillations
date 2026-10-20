/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# DetectorConsumerGeometry

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Same-kernel exponent checks for compensated packets

These are exact scalar certificates. The sextic expressions come from the
audited source Mellin and Gram formulas. The quartic expressions are a proposed
kernel template; this file does not establish that analytic template, a moment
estimate, or any improved zero-free region.
-/


noncomputable section
namespace PrimeFactorOscillations.DetectorConsumerGeometry

def poleShift (r x width : Real) : Real :=
  (1/2-1/r)*x-1+1/r+width/r

def exceptionalGram (r x y : Real) : Real :=
  ((1-1/r)*x+y/r)/2

def fullGram (r x y d : Real) : Real :=
  max ((x-d)/2) (max (exceptionalGram r x y-d/2) ((y-x)/2))

def normalizedBudget (r x y width : Real) : Real :=
  fullGram r x y 0-poleShift r x width

def markedLength (width d : Real) : Real := 1+width-d

theorem quartic_exceptional_boundary (x y width : Real)
    (hxy : x+y=1-width) :
    exceptionalGram 4 x y-poleShift 4 x width=7/8-3*width/8 := by
  unfold exceptionalGram poleShift
  norm_num
  linarith

theorem sextic_exceptional_boundary (x y width : Real)
    (hxy : x+y=1-width) :
    exceptionalGram 6 x y-poleShift 6 x width=11/12-width/4 := by
  unfold exceptionalGram poleShift
  norm_num
  linarith

theorem quartic_candidate_full_budget :
    normalizedBudget 4 (1/5) (7/15) (1/3)=3/4 := by
  norm_num [normalizedBudget, fullGram, exceptionalGram, poleShift]

theorem quartic_candidate_shift :
    poleShift 4 (1/5) (1/3)= -(37/60) := by
  norm_num [poleShift]

theorem sextic_candidate_full_budget :
    normalizedBudget 6 (5/48) (11/48) (2/3)=3/4 := by
  norm_num [normalizedBudget, fullGram, exceptionalGram, poleShift]

theorem sextic_candidate_shift :
    poleShift 6 (5/48) (2/3)= -(11/16) := by
  norm_num [poleShift]

theorem quartic_candidate_length (d : Real) :
    markedLength (1/3) d=4/3-d := by
  unfold markedLength
  linarith

theorem sextic_candidate_length (d : Real) :
    markedLength (2/3) d=5/3-d := by
  unfold markedLength
  linarith

def gaussianBglBudget (d : Real) : Real :=
  max (2/3-2*d) (max (4/3-d) ((2/3)*((2/3-2*d)+(4/3-d))))

theorem gaussian_bgl_low_cone (d : Real) (hd : 0 <= d) :
    gaussianBglBudget d <= 4/3 := by
  unfold gaussianBglBudget
  apply max_le
  . linarith
  . apply max_le <;> linarith

def sourceBoundary (d energy : Real) : Real :=
  fullGram 6 (5/48) (11/48) d+
    (energy-(1/3-2*d))/2-d/2+11/16

theorem sextic_full_gram (d : Real) (hd : 0 <= d) :
    fullGram 6 (5/48) (11/48) d=1/16 := by
  unfold fullGram exceptionalGram
  norm_num
  have hi : max (1/16-d/2) (1/16:Real)=1/16 :=
    max_eq_right (by linarith)
  rw [hi]
  apply max_eq_right
  linarith

theorem source_complete_energy_consumer (d energy : Real) (hd : 0 <= d) :
    sourceBoundary d energy=3/4+(energy-(1/3-d))/2 := by
  unfold sourceBoundary
  rw [sextic_full_gram d hd]
  linarith

theorem source_required_energy (d energy : Real) (hd : 0 <= d) :
    sourceBoundary d energy <= 3/4 <-> energy <= 1/3-d := by
  rw [source_complete_energy_consumer d energy hd]
  constructor <;> intro h <;> linarith

theorem source_generic_length_loss (d : Real) (hd : 0 <= d) :
    sourceBoundary d (markedLength (2/3) d)=17/12 := by
  rw [source_complete_energy_consumer d _ hd, sextic_candidate_length]
  linarith

end PrimeFactorOscillations.DetectorConsumerGeometry
