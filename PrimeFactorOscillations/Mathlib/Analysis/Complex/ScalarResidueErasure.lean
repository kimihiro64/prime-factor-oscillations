/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.Complex.AnchoredScalarMultiplicity

/-!
# The multiplicity cost of a vanished real residue

The complete real projection is an integer minus a positive scalar defect.
Erasure therefore costs at least one unit of defect times reference order.
The exact denominator retains the height and real-part dependence.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

def scalarResidueDefect (d : Nat) (z : Complex) : Real :=
  (d : Real) - ((d : Complex) * z / (z + (d : Complex) - 1)).re

theorem scalarResidueDefect_formula (d : Nat) (hd : 2 <= d)
    (z : Complex) (hRe : 0 <= z.re) :
    scalarResidueDefect d z =
      (d : Real) * ((d : Real) - 1) * (z.re + (d : Real) - 1) /
        ((z.re + (d : Real) - 1) ^ 2 + z.im ^ 2) := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hDen : Not (z + (d : Complex) - 1 = 0) := by
    intro he
    have hh := congrArg Complex.re he
    change z.re + (d : Real) - 1 = 0 at hh
    linarith
  have he : (d : Complex) * z / (z + (d : Complex) - 1) =
      (d : Complex) - (d : Complex) * ((d : Complex) - 1) /
        (z + (d : Complex) - 1) := by
    field_simp [hDen] <;> ring
  unfold scalarResidueDefect
  rw [he]
  norm_num [Complex.div_re, Complex.normSq_apply]
  ring

theorem scalarResidueDefect_pos (d : Nat) (hd : 2 <= d)
    (z : Complex) (hRe : 0 <= z.re) : 0 < scalarResidueDefect d z := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hx : 0 < z.re + (d : Real) - 1 := by linarith
  have hDen : 0 < (z.re + (d : Real) - 1) ^ 2 + z.im ^ 2 := by
    nlinarith [sq_nonneg z.im]
  rw [scalarResidueDefect_formula d hd z hRe]
  exact div_pos (mul_pos (mul_pos (by linarith) (by linarith)) hx) hDen

theorem integerResidueCode_real_decomposition (d : Nat) (z : Complex) (a b : Int) :
    (integerResidueCode d z a b).re =
      (d : Real) * (b : Real) - (a : Real) - scalarResidueDefect d z * (b : Real) := by
  rw [integerResidueCode_re_scalar]
  unfold anchoredScalarFirst scalarResidueDefect
  ring

theorem scalar_erasure_cost (d : Nat) (hd : 2 <= d) (z : Complex) (hRe : 0 <= z.re)
    (a b : Nat) (hMass : 0 < a + b)
    (hErase : (integerResidueCode d z (a : Int) (b : Int)).re = 0) :
    And (0 < b) (1 <= scalarResidueDefect d z * (b : Real)) := by
  have hr := integerResidueCode_real_decomposition d z (a : Int) (b : Int)
  rw [hErase] at hr
  simp only [Int.cast_natCast] at hr
  have hb : 0 < b := by
    by_contra hn
    have hb0 : b = 0 := by omega
    have haR : (a : Real) = 0 := by
      norm_num [hb0] at hr
      linarith
    have ha : a = 0 := by exact_mod_cast haR
    omega
  have hbR : 0 < (b : Real) := by exact_mod_cast hb
  have hp := mul_pos (scalarResidueDefect_pos d hd z hRe) hbR
  have haR : (a : Real) < (d : Real) * (b : Real) := by linarith
  have ha : a < d * b := by exact_mod_cast haR
  have hOne : (a : Real) + 1 <= (d : Real) * (b : Real) := by
    exact_mod_cast (Nat.succ_le_of_lt ha)
  exact And.intro hb (by linarith)

theorem scalarResidueDefect_lt_degree (d : Nat) (hd : 2 <= d)
    (z : Complex) (hRe : 0 < z.re) : scalarResidueDefect d z < d := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hx : 0 < z.re + (d : Real) - 1 := by linarith
  have hDen : 0 < (z.re + (d : Real) - 1) ^ 2 + z.im ^ 2 := by
    nlinarith [sq_nonneg z.im]
  have hPos : 0 < (d : Real) *
      (z.re * (z.re + (d : Real) - 1) + z.im ^ 2) := by
    apply mul_pos (by linarith)
    nlinarith [mul_pos hRe hx, sq_nonneg z.im]
  have he : (d : Real) * ((z.re + (d : Real) - 1) ^ 2 + z.im ^ 2) -
      (d : Real) * ((d : Real) - 1) * (z.re + (d : Real) - 1) =
      (d : Real) * (z.re * (z.re + (d : Real) - 1) + z.im ^ 2) := by ring
  have hEq : scalarResidueDefect d z *
      ((z.re + (d : Real) - 1) ^ 2 + z.im ^ 2) =
      (d : Real) * ((d : Real) - 1) * (z.re + (d : Real) - 1) := by
    rw [scalarResidueDefect_formula d hd z hRe.le]
    field_simp [ne_of_gt hDen] <;> ring
  by_contra hn
  have hGe : (d : Real) <= scalarResidueDefect d z := le_of_not_gt hn
  have hm := mul_le_mul_of_nonneg_right hGe hDen.le
  rw [hEq] at hm
  linarith [he, hPos]

theorem integerResidueCode_real_mul_den (d : Nat) (hd : 2 <= d)
    (z : Complex) (hRe : 0 <= z.re) (a b : Int) :
    (integerResidueCode d z a b).re *
        ((z.re + (d : Real) - 1) ^ 2 + z.im ^ 2) =
      ((d : Real) * (b : Real) - (a : Real)) *
        ((z.re + (d : Real) - 1) ^ 2 + z.im ^ 2) -
      (d : Real) * ((d : Real) - 1) * (b : Real) * (z.re + (d : Real) - 1) := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hx : 0 < z.re + (d : Real) - 1 := by linarith
  have hDen : 0 < (z.re + (d : Real) - 1) ^ 2 + z.im ^ 2 := by
    nlinarith [sq_nonneg z.im]
  rw [integerResidueCode_real_decomposition, scalarResidueDefect_formula d hd z hRe]
  field_simp [ne_of_gt hDen] <;> ring

theorem integerResidueCode_re_zero_iff (d : Nat) (hd : 2 <= d)
    (z : Complex) (hRe : 0 <= z.re) (a b : Int) :
    (integerResidueCode d z a b).re = 0 <->
      ((d : Real) * (b : Real) - (a : Real)) *
        ((z.re + (d : Real) - 1) ^ 2 + z.im ^ 2) =
      (d : Real) * ((d : Real) - 1) * (b : Real) * (z.re + (d : Real) - 1) := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hx : 0 < z.re + (d : Real) - 1 := by linarith
  have hDen : 0 < (z.re + (d : Real) - 1) ^ 2 + z.im ^ 2 := by
    nlinarith [sq_nonneg z.im]
  have hm := integerResidueCode_real_mul_den d hd z hRe a b
  constructor
  . intro he
    rw [he, zero_mul] at hm
    linarith
  . intro he
    have hh : (integerResidueCode d z a b).re *
        ((z.re + (d : Real) - 1) ^ 2 + z.im ^ 2) = 0 := by linarith
    exact (mul_eq_zero.mp hh).resolve_right (ne_of_gt hDen)

theorem scalar_erasure_height (d : Nat) (hd : 2 <= d) (z : Complex)
    (hRe : 0 <= z.re) (u : Real) (hUpper : z.re <= u) (a b : Nat)
    (hMass : 0 < a + b) (hErase : (integerResidueCode d z (a : Int) (b : Int)).re = 0)
    (hMono : 2 * (u + (d : Real) - 1) <=
      (d : Real) * ((d : Real) - 1) * (b : Real)) :
    z.im ^ 2 + (u + (d : Real) - 1) ^ 2 <=
      (d : Real) * ((d : Real) - 1) * (b : Real) * (u + (d : Real) - 1) := by
  let x := z.re + (d : Real) - 1
  let U := u + (d : Real) - 1
  let k := (d : Real) * ((d : Real) - 1)
  let D := x ^ 2 + z.im ^ 2
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hx : 0 < x := by dsimp [x]; linarith
  have hDen : 0 < D := by dsimp [D]; nlinarith [sq_nonneg z.im]
  have hCost := scalar_erasure_cost d hd z hRe a b hMass hErase
  have hEq : scalarResidueDefect d z * (b : Real) * D = k * (b : Real) * x := by
    have hF := scalarResidueDefect_formula d hd z hRe
    change scalarResidueDefect d z = k * x / D at hF
    rw [hF]
    field_simp [ne_of_gt hDen] <;> ring
  have hScaled := mul_le_mul_of_nonneg_right hCost.2 hDen.le
  rw [one_mul, hEq] at hScaled
  have hxU : x <= U := by dsimp [x, U]; linarith
  have hOther : 0 <= k * (b : Real) - U - x := by
    change 2 * U <= k * (b : Real) at hMono
    linarith
  have hDiff := mul_nonneg (sub_nonneg.mpr hxU) hOther
  change z.im ^ 2 + U ^ 2 <= k * (b : Real) * U
  dsimp only [D] at hScaled
  nlinarith [hScaled, hDiff]

theorem quadratic_scalar_unit_erasure (z : Complex) (hRe : 0 < z.re) (a : Nat)
    (hErase : (integerResidueCode 2 z (a : Int) 1).re = 0) :
    And (a = 1) (z.re ^ 2 + z.im ^ 2 = 1) := by
  have hr := integerResidueCode_real_decomposition 2 z (a : Int) 1
  rw [hErase] at hr
  norm_num at hr
  have hPos := scalarResidueDefect_pos 2 (by norm_num) z hRe.le
  have hLt := scalarResidueDefect_lt_degree 2 (by norm_num) z hRe
  norm_num only [Nat.cast_ofNat] at hLt
  have hLo : (0 : Real) < a := by linarith
  have hHi : (a : Real) < 2 := by linarith
  have hLoN : 0 < a := by exact_mod_cast hLo
  have hHiN : a < 2 := by exact_mod_cast hHi
  have ha : a = 1 := by omega
  refine And.intro ha ?_
  have hm := integerResidueCode_real_mul_den 2 (by norm_num) z hRe.le (a : Int) 1
  rw [hErase] at hm
  norm_num [ha] at hm
  nlinarith [hm]

theorem scalar_erasure_height_attains (d : Nat) (hd : 2 <= d) (M : Nat) (hM : 1 <= M)
    (u : Real) (hu : 0 <= u)
    (hMono : 2 * (u + (d : Real) - 1) <=
      (d : Real) * ((d : Real) - 1) * (M : Real)) :
    And (0 < (d : Int) * (M : Int) - 1)
      (Exists (fun z : Complex => And (z.re = u)
        (And ((integerResidueCode d z ((d : Int) * (M : Int) - 1) (M : Int)).re = 0)
          (z.im ^ 2 + (u + (d : Real) - 1) ^ 2 =
            (d : Real) * ((d : Real) - 1) * (M : Real) * (u + (d : Real) - 1))))) := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hdI : (2 : Int) <= d := by exact_mod_cast hd
  have hMI : (1 : Int) <= M := by exact_mod_cast hM
  refine And.intro (by nlinarith) ?_
  let U := u + (d : Real) - 1
  let k := (d : Real) * ((d : Real) - 1)
  let S := k * (M : Real) * U - U ^ 2
  have hU : 0 < U := by dsimp [U]; linarith
  have hMul := mul_le_mul_of_nonneg_right hMono hU.le
  have hS : 0 <= S := by
    change 2 * U * U <= k * (M : Real) * U at hMul
    dsimp only [S]
    nlinarith [hMul, sq_nonneg U]
  have hSq := Real.sq_sqrt hS
  let z : Complex := Complex.mk u (Real.sqrt S)
  refine Exists.intro z (And.intro rfl (And.intro ?_ ?_))
  . apply (integerResidueCode_re_zero_iff d hd z (by change 0 <= u; exact hu)
      ((d : Int) * (M : Int) - 1) (M : Int)).mpr
    push_cast
    change ((d : Real) * (M : Real) - ((d : Real) * (M : Real) - 1)) *
        ((u + (d : Real) - 1) ^ 2 + (Real.sqrt S) ^ 2) =
      (d : Real) * ((d : Real) - 1) * (M : Real) * (u + (d : Real) - 1)
    rw [hSq]
    dsimp [S, k, U]
    ring
  . change (Real.sqrt S) ^ 2 + U ^ 2 = k * (M : Real) * U
    rw [hSq]
    dsimp [S]
    ring

theorem quadratic_scalar_unit_circle_iff (z : Complex) (hRe : 0 <= z.re) :
    (integerResidueCode 2 z 1 1).re = 0 <-> z.re ^ 2 + z.im ^ 2 = 1 := by
  rw [integerResidueCode_re_zero_iff 2 (by norm_num) z hRe]
  norm_num
  constructor <;> intro h <;> nlinarith

end Complex

end
