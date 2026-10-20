/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# FilteredQuarticBudget

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
# Complete conductor budget for a filtered quartic packet

The conductor is K^3 F^2 and the quartic sieve cross term has exponent 3/4.
The scalar certificate checks the resulting candidate estimate on the full
physical cone needed at Lambda=1/3. The analytic packet estimate remains a
separate obligation; these inequalities do not prove that estimate.
-/


noncomputable section
namespace PrimeFactorOscillations.FilteredQuarticBudget

def balanced (m v : Real) : Real :=
  max m (max ((3/2)*m+v) ((15/8)*m+(3/4)*v))

def twoSides (m v u : Real) : Real :=
  max m (max (min u (3*m+2*v-u))
    ((3/4)*(m+min u (3*m+2*v-u))))

theorem min_dual_length (m v u : Real) :
    min u (3*m+2*v-u) <= (3/2)*m+v := by
  have h1 := min_le_left u (3*m+2*v-u)
  have h2 := min_le_right u (3*m+2*v-u)
  linarith

theorem complete_conductor_balance (m v u : Real) :
    twoSides m v u <= balanced m v := by
  unfold twoSides balanced
  apply max_le_max le_rfl
  apply max_le_max
  . exact min_dual_length m v u
  . have h := min_dual_length m v u
    linarith

theorem physical_cone (d : Real) (hd : 0 <= d) :
    balanced (2/3-2*d) d <= 5/4 := by
  unfold balanced
  apply max_le
  . linarith
  . apply max_le
    . linarith
    . linarith

theorem physical_row_nonneg (d : Real) (hd : d <= 1/3) :
    0 <= 2/3-2*d := by
  linarith

theorem full_consumer_margin (d : Real) (hd : 0 <= d) :
    balanced (2/3-2*d) d + 1/12 <= (4/3-d)+d := by
  have h := physical_cone d hd
  linarith

theorem margin_after_loss (d loss : Real) (hd : 0 <= d)
    (hloss : loss < 1/12) :
    balanced (2/3-2*d) d + loss < (4/3-d)+d := by
  have h := full_consumer_margin d hd
  linarith

theorem quartic_terminal_cone (d : Real) (hd : 2/27 <= d) :
    3*(2/3-2*d) <= (4/3-d)+4*d := by
  linarith

theorem quartic_terminal_open_interval (d : Real) (hd : d < 2/27) :
    (4/3-d)+4*d < 3*(2/3-2*d) := by
  linarith

def crudeMarked (m v h : Real) : Real :=
  max (m+h) (max ((3/2)*m+v+2*h) ((15/8)*m+(3/4)*v+(7/4)*h))

def jointMarked (m v h : Real) : Real :=
  max (m+h) (max ((3/2)*m+v+h) ((15/8)*m+(3/4)*v+(1/4)*h))

theorem crude_marked_range (d h : Real) :
    crudeMarked (2/3-2*d) d h <= 4/3 <->
      h <= 2/3+2*d /\ h <= 1/6+d /\ h <= 1/21+(12/7)*d := by
  simp only [crudeMarked, max_le_iff]
  constructor
  . intro hs
    constructor
    . linarith [hs.1]
    . constructor
      . linarith [hs.2.1]
      . linarith [hs.2.2]
  . intro hs
    constructor
    . linarith [hs.1]
    . constructor
      . linarith [hs.2.1]
      . linarith [hs.2.2]

theorem crude_full_slot_loss :
    4/3+1/2 <= crudeMarked (2/3) 0 (1/3) := by
  unfold crudeMarked
  have h := le_trans
    (le_max_right ((3/2)*(2/3:Real)+0+2*(1/3))
      ((15/8)*(2/3)+(3/4)*0+(7/4)*(1/3)))
    (le_max_right ((2/3:Real)+(1/3))
      (max ((3/2)*(2/3)+0+2*(1/3))
        ((15/8)*(2/3)+(3/4)*0+(7/4)*(1/3))))
  linarith

theorem joint_full_slot_cone (d h : Real) (hd : 0 <= d) (hh : h <= 1/3) :
    jointMarked (2/3-2*d) d h <= 4/3 := by
  unfold jointMarked
  apply max_le
  . linarith
  . apply max_le
    . linarith
    . linarith

end PrimeFactorOscillations.FilteredQuarticBudget
