/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairEulerCount


/-!
# Exact moments for conditional quadratic-pair weights

The translated quadratic-character transform retains its full signed
covariance. The actual irreducible quadratic-pair count has an exact
second moment, including both singular constants. Its normalized mean,
second moment and variance are computed without Hasse or RH; the possible
zero normalizer is explicit, and disappears for field cardinal at least 16.
No short-interval integer prime-pair estimate is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped BigOperators

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem quadraticChar_translate_square_sum (hF : Not (ringChar F = 2)) :
    (Finset.univ.sum fun c : F => ((quadraticChar F) c) ^ 2) =
      (Fintype.card F : Int) - 1 := by
  classical
  have hp (c : F) :
      ((quadraticChar F) c) ^ 2 = 1 - (if c = 0 then 1 else 0) := by
    by_cases hc : c = 0
    . simp [hc]
    . simp only [if_neg hc, sub_zero]
      exact quadraticChar_sq_one hc
  simp_rw [hp]
  simp

theorem quadraticChar_translate_correlation (hF : Not (ringChar F = 2))
    (a b : F) :
    (Finset.univ.sum fun c : F =>
      (quadraticChar F) (c + a) * (quadraticChar F) (c + b)) =
        (Fintype.card F : Int) * (if b = a then 1 else 0) - 1 := by
  classical
  by_cases hab : b = a
  . subst b
    let e : Equiv F F :=
      { toFun := fun c => c + a
        invFun := fun c => c - a
        left_inv := by intro c; ring
        right_inv := by intro c; ring }
    have he := Equiv.sum_comp e
      (fun c : F => ((quadraticChar F) c) ^ 2)
    simp only [pow_two] at he
    change (Finset.univ.sum fun c : F =>
      (quadraticChar F) (c + a) * (quadraticChar F) (c + a)) = _ at he
    rw [he]
    simpa only [ite_true, mul_one, pow_two] using quadraticChar_translate_square_sum hF
  . have hn : Not (-a = -b) := by
      intro he
      apply hab
      exact (neg_injective he).symm
    have hh := quadraticChar_sum_mul_sub hF (-a) (-b) hn
    simpa only [sub_neg_eq_add, map_mul, if_neg hab, mul_zero, zero_sub] using hh


theorem quadraticChar_convolution_energy (hF : Not (ringChar F = 2))
    (w : F -> Int) :
    (Finset.univ.sum fun c : F =>
      (Finset.univ.sum fun x : F => w x * (quadraticChar F) (c + x)) ^ 2) =
      (Fintype.card F : Int) * (Finset.univ.sum fun x : F => (w x) ^ 2) -
        (Finset.univ.sum w) ^ 2 := by
  classical
  have hexpand (c : F) :
      (Finset.univ.sum fun x : F => w x * (quadraticChar F) (c + x)) ^ 2 =
        Finset.univ.sum (fun x : F => Finset.univ.sum (fun y : F =>
          w x * w y * ((quadraticChar F) (c + x) *
            (quadraticChar F) (c + y)))) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hinner (x : F) :
      (Finset.univ.sum fun y : F =>
        w x * w y * ((Fintype.card F : Int) *
          (if y = x then 1 else 0) - 1)) =
        (Fintype.card F : Int) * (w x) ^ 2 -
          w x * (Finset.univ.sum w) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    congr 1
    . have hp (y : F) :
          w x * w y * ((Fintype.card F : Int) * (if y = x then 1 else 0)) =
            if y = x then (Fintype.card F : Int) * (w x) ^ 2 else 0 := by
        split_ifs with hy
        . subst y; ring
        . ring
      simp_rw [hp]
      simp
    . exact (Finset.mul_sum Finset.univ (fun y : F => w y) (w x)).symm
  calc
    _ = Finset.univ.sum (fun c : F =>
        Finset.univ.sum (fun x : F => Finset.univ.sum (fun y : F =>
          w x * w y * ((quadraticChar F) (c + x) *
            (quadraticChar F) (c + y))))) := by simp_rw [hexpand]
    _ = Finset.univ.sum (fun x : F => Finset.univ.sum (fun y : F =>
        Finset.univ.sum (fun c : F =>
          w x * w y * ((quadraticChar F) (c + x) *
            (quadraticChar F) (c + y))))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = Finset.univ.sum (fun x : F => Finset.univ.sum (fun y : F =>
        w x * w y * ((Fintype.card F : Int) *
          (if y = x then 1 else 0) - 1))) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [<- Finset.mul_sum, quadraticChar_translate_correlation hF x y]
    _ = _ := by
      simp_rw [hinner]
      rw [Finset.sum_sub_distrib, <- Finset.mul_sum, <- Finset.sum_mul]
      ring


theorem quadraticChar_convolution_pairing (hF : Not (ringChar F = 2))
    (w : F -> Int) (v : F) :
    (Finset.univ.sum fun c : F =>
      (Finset.univ.sum fun x : F => w x * (quadraticChar F) (c + x)) *
        (quadraticChar F) (c + v)) =
      (Fintype.card F : Int) * w v - Finset.univ.sum w := by
  classical
  calc
    _ = Finset.univ.sum (fun x : F => w x *
        (Finset.univ.sum fun c : F =>
          (quadraticChar F) (c + x) * (quadraticChar F) (c + v))) := by
      simp only [Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = Finset.univ.sum (fun x : F => w x *
        ((Fintype.card F : Int) * (if v = x then 1 else 0) - 1)) := by
      simp_rw [quadraticChar_translate_correlation hF]
    _ = _ := by
      have hp (x : F) :
          w x * ((Fintype.card F : Int) * (if v = x then 1 else 0) - 1) =
            (if x = v then (Fintype.card F : Int) * w v else 0) - w x := by
        by_cases hx : x = v
        . subst x; simp only [ite_true, mul_one]; ring
        . have hv : Not (v = x) := Ne.symm hx
          simp only [if_neg hx, if_neg hv]
          ring
      simp_rw [hp]
      simp

theorem splitCubicPointTrace_convolution
    (hF : Not (ringChar F = 2)) (c h : F) :
    splitCubicPointTrace c (c + h) =
      -(Finset.univ.sum fun x : F =>
        (quadraticChar F) (x * (x - h)) * (quadraticChar F) (c + x)) := by
  let e : Equiv F F :=
    { toFun := fun x => x + c
      invFun := fun x => x - c
      left_inv := by intro x; ring
      right_inv := by intro x; ring }
  have he := Equiv.sum_comp e (fun t : F =>
    (quadraticChar F) (t * (t - c) * (t - (c + h))))
  rw [splitCubicPointTrace_eq hF, <- he]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  change (quadraticChar F) ((x + c) * (x + c - c) * (x + c - (c + h))) = _
  have hh :
      (x + c) * (x + c - c) * (x + c - (c + h)) =
        (x * (x - h)) * (c + x) := by ring
  rw [hh, map_mul]

theorem quadraticPairKernel_sum
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0)) :
    (Finset.univ.sum fun x : F => (quadraticChar F) (x * (x - h))) = -1 := by
  simpa only [sub_zero] using
    quadraticChar_sum_mul_sub hF (0 : F) h (Ne.symm hh)

theorem quadraticPairKernel_square_sum
    (h : F) (hh : Not (h = 0)) :
    (Finset.univ.sum fun x : F => ((quadraticChar F) (x * (x - h))) ^ 2) =
      (Fintype.card F : Int) - 2 := by
  classical
  have hp (x : F) :
      ((quadraticChar F) (x * (x - h))) ^ 2 =
        1 - (if x = 0 then 1 else 0) - (if x = h then 1 else 0) := by
    by_cases hx : x = 0
    . subst x
      simp [Ne.symm hh]
    . by_cases hxh : x = h
      . subst x
        simp [hh]
      . have hn : Not (x * (x - h) = 0) :=
          mul_ne_zero hx (sub_ne_zero.mpr hxh)
        rw [quadraticChar_sq_one hn]
        simp only [if_neg hx, if_neg hxh, sub_zero]
  simp_rw [hp]
  simp only [Finset.sum_sub_distrib]
  simp
  ring

theorem sum_splitCubicPointTrace_square
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0)) :
    (Finset.univ.sum fun c : F => (splitCubicPointTrace c (c + h)) ^ 2) =
      (Fintype.card F : Int) ^ 2 - 2 * (Fintype.card F : Int) - 1 := by
  simp_rw [splitCubicPointTrace_convolution hF, neg_sq]
  rw [quadraticChar_convolution_energy hF,
    quadraticPairKernel_square_sum h hh, quadraticPairKernel_sum hF h hh]
  ring


theorem quadraticChar_translate_sum (hF : Not (ringChar F = 2)) (a : F) :
    (Finset.univ.sum fun c : F => (quadraticChar F) (c + a)) = 0 := by
  let e : Equiv F F :=
    { toFun := fun c => c + a
      invFun := fun c => c - a
      left_inv := by intro c; ring
      right_inv := by intro c; ring }
  exact (Equiv.sum_comp e (quadraticChar F)).trans (quadraticChar_sum_zero hF)

theorem quadraticChar_convolution_sum (hF : Not (ringChar F = 2))
    (w : F -> Int) :
    (Finset.univ.sum fun c : F =>
      Finset.univ.sum (fun x : F => w x * (quadraticChar F) (c + x))) = 0 := by
  rw [Finset.sum_comm]
  simp_rw [<- Finset.mul_sum, quadraticChar_translate_sum hF]
  simp

theorem sum_splitCubicPointTrace
    (hF : Not (ringChar F = 2)) (h : F) :
    (Finset.univ.sum fun c : F => splitCubicPointTrace c (c + h)) = 0 := by
  simp_rw [splitCubicPointTrace_convolution hF, Finset.sum_neg_distrib]
  rw [quadraticChar_convolution_sum hF, neg_zero]

theorem sum_splitCubicPointTrace_mul_char
    (hF : Not (ringChar F = 2)) (h v : F) (hh : Not (h = 0)) :
    (Finset.univ.sum fun c : F =>
      splitCubicPointTrace c (c + h) * (quadraticChar F) (c + v)) =
        -(Fintype.card F : Int) * (quadraticChar F) (v * (v - h)) - 1 := by
  calc
    _ = -(Finset.univ.sum fun c : F =>
        (Finset.univ.sum fun x : F =>
          (quadraticChar F) (x * (x - h)) * (quadraticChar F) (c + x)) *
            (quadraticChar F) (c + v)) := by
      simp_rw [splitCubicPointTrace_convolution hF, neg_mul, Finset.sum_neg_distrib]
    _ = _ := by
      rw [quadraticChar_convolution_pairing hF, quadraticPairKernel_sum hF h hh]
      ring

theorem splitCubicPointTrace_zero_left
    (hF : Not (ringChar F = 2)) (b : F) :
    splitCubicPointTrace (0 : F) b = (quadraticChar F) (-b) := by
  classical
  have hp (x : F) :
      (quadraticChar F) (x * (x - 0) * (x - b)) =
        (quadraticChar F) (x - b) -
          (if x = 0 then (quadraticChar F) (-b) else 0) := by
    by_cases hx : x = 0
    . subst x
      simp
    . have he : x * (x - 0) * (x - b) = x ^ 2 * (x - b) := by ring
      rw [he, map_mul, map_pow, quadraticChar_sq_one hx, one_mul]
      simp only [if_neg hx, sub_zero]
  rw [splitCubicPointTrace_eq hF]
  simp_rw [hp]
  rw [Finset.sum_sub_distrib]
  have hs : (Finset.univ.sum fun x : F => (quadraticChar F) (x - b)) = 0 := by
    simpa only [sub_eq_add_neg] using quadraticChar_translate_sum hF (-b)
  rw [hs]
  simp

theorem splitCubicPointTrace_comm
    (hF : Not (ringChar F = 2)) (a b : F) :
    splitCubicPointTrace a b = splitCubicPointTrace b a := by
  rw [splitCubicPointTrace_eq hF, splitCubicPointTrace_eq hF]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  ring


theorem completed_trace_numerator_square_sum
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0))
    (A alpha beta : Int) :
    (Finset.univ.sum fun c : F =>
      (A - splitCubicPointTrace c (c + h) -
        alpha * (quadraticChar F) c - beta * (quadraticChar F) (c + h)) ^ 2) =
      (Fintype.card F : Int) * A ^ 2 +
        ((Fintype.card F : Int) ^ 2 - 2 * (Fintype.card F : Int) - 1) +
        (alpha ^ 2 + beta ^ 2) * ((Fintype.card F : Int) - 1) -
        2 * alpha - 2 * beta - 2 * alpha * beta := by
  have hz : (quadraticChar F) (0 : F) = 0 := by simp
  have hx := quadraticChar_translate_square_sum (F := F) hF
  have hy := quadraticChar_translate_correlation hF h h
  simp only [ite_true, mul_one, <- pow_two] at hy
  have hxy := quadraticChar_translate_correlation hF (0 : F) h
  simp only [add_zero, if_neg hh, mul_zero, zero_sub] at hxy
  have htx := sum_splitCubicPointTrace_mul_char hF h (0 : F) hh
  simp only [add_zero, zero_mul, hz, mul_zero, zero_sub] at htx
  have hty := sum_splitCubicPointTrace_mul_char hF h h hh
  simp only [sub_self, mul_zero, hz, zero_sub] at hty
  have hp (c : F) :
      (A - splitCubicPointTrace c (c + h) -
        alpha * (quadraticChar F) c - beta * (quadraticChar F) (c + h)) ^ 2 =
      A ^ 2 + (splitCubicPointTrace c (c + h)) ^ 2 +
        alpha ^ 2 * ((quadraticChar F) c) ^ 2 +
        beta ^ 2 * ((quadraticChar F) (c + h)) ^ 2 -
        (2 * A) * splitCubicPointTrace c (c + h) -
        (2 * A * alpha) * (quadraticChar F) c -
        (2 * A * beta) * (quadraticChar F) (c + h) +
        (2 * alpha) * (splitCubicPointTrace c (c + h) * (quadraticChar F) c) +
        (2 * beta) * (splitCubicPointTrace c (c + h) * (quadraticChar F) (c + h)) +
        (2 * alpha * beta) * ((quadraticChar F) c * (quadraticChar F) (c + h)) := by
    ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum]
  rw [sum_splitCubicPointTrace_square hF h hh, hx, hy,
    sum_splitCubicPointTrace hF h, quadraticChar_sum_zero hF,
    quadraticChar_translate_sum hF h, htx, hty, hxy]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

noncomputable def completedQuadraticPairNumerator (c h : F) : Int :=
  (Fintype.card F : Int) - 1 + (quadraticChar F) h + (quadraticChar F) (-h) -
    splitCubicPointTrace c (c + h) -
    (1 - (quadraticChar F) (-h)) * (quadraticChar F) c -
    (1 - (quadraticChar F) h) * (quadraticChar F) (c + h)

theorem completedQuadraticPairNumerator_zero
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0)) :
    completedQuadraticPairNumerator (0 : F) h = (Fintype.card F : Int) := by
  have hz : (quadraticChar F) (0 : F) = 0 := by simp
  simp only [completedQuadraticPairNumerator, zero_add,
    splitCubicPointTrace_zero_left hF, hz, mul_zero, sub_zero]
  nlinarith only [quadraticChar_sq_one hh]

theorem completedQuadraticPairNumerator_neg_shift
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0)) :
    completedQuadraticPairNumerator (-h) h = (Fintype.card F : Int) := by
  have hz : (quadraticChar F) (0 : F) = 0 := by simp
  have ht : splitCubicPointTrace (-h) (0 : F) = (quadraticChar F) h := by
    rw [splitCubicPointTrace_comm hF, splitCubicPointTrace_zero_left hF, neg_neg]
  simp only [completedQuadraticPairNumerator, ht, neg_add_cancel, hz,
    mul_zero, sub_zero]
  nlinarith only [quadraticChar_sq_one (neg_ne_zero.mpr hh)]

theorem quadraticPairCount_square_completion
    (hF : Not (ringChar F = 2)) (c h : F) (hh : Not (h = 0)) :
    16 * (monicQuadraticPairCount c h) ^ 2 =
      (completedQuadraticPairNumerator c h) ^ 2 -
        (if c = 0 then (Fintype.card F : Int) ^ 2 else 0) -
        (if c = -h then (Fintype.card F : Int) ^ 2 else 0) := by
  classical
  by_cases hc : c = 0
  . subst c
    rw [monicQuadraticPairCount_zero hF, completedQuadraticPairNumerator_zero hF h hh]
    have hz : Not ((0 : F) = -h) := Ne.symm (neg_ne_zero.mpr hh)
    simp only [ite_true, if_neg hz]
    ring
  . by_cases hcn : c = -h
    . subst c
      rw [monicQuadraticPairCount_neg_shift hF,
        completedQuadraticPairNumerator_neg_shift hF h hh]
      simp only [if_neg (neg_ne_zero.mpr hh), ite_true]
      ring
    . have hch : Not (c + h = 0) := by
        intro he
        apply hcn
        calc
          c = (c + h) - h := by ring
          _ = -h := by rw [he]; ring
      have hv : completedQuadraticPairNumerator c h =
          4 * monicQuadraticPairCount c h := by
        rw [monicQuadraticPairCount_eq_trace hF c h hc hch hh]
        unfold completedQuadraticPairNumerator
        ring
      rw [hv]
      simp only [if_neg hc, if_neg hcn, sub_zero]
      ring


noncomputable def quadraticPairOffset (h : F) : Int :=
  3 - (quadraticChar F) h - (quadraticChar F) (-h)

theorem sum_monicQuadraticPairCount_square
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0)) :
    16 * (Finset.univ.sum fun c : F => (monicQuadraticPairCount c h) ^ 2) =
      ((Fintype.card F : Int) - quadraticPairOffset h) *
        ((Fintype.card F : Int) ^ 2 +
          (3 - quadraticPairOffset h) * (Fintype.card F : Int) +
            quadraticPairOffset h) := by
  classical
  have hs :
      16 * (Finset.univ.sum fun c : F => (monicQuadraticPairCount c h) ^ 2) =
        (Finset.univ.sum fun c : F => (completedQuadraticPairNumerator c h) ^ 2) -
          2 * (Fintype.card F : Int) ^ 2 := by
    calc
      _ = Finset.univ.sum (fun c : F => 16 * (monicQuadraticPairCount c h) ^ 2) := by
        rw [Finset.mul_sum]
      _ = Finset.univ.sum (fun c : F =>
          (completedQuadraticPairNumerator c h) ^ 2 -
            (if c = 0 then (Fintype.card F : Int) ^ 2 else 0) -
            (if c = -h then (Fintype.card F : Int) ^ 2 else 0)) := by
        apply Finset.sum_congr rfl
        intro c _
        exact quadraticPairCount_square_completion hF c h hh
      _ = _ := by
        simp only [Finset.sum_sub_distrib]
        simp
        ring
  rw [hs]
  unfold completedQuadraticPairNumerator
  rw [completed_trace_numerator_square_sum hF h hh]
  unfold quadraticPairOffset
  have he := quadraticChar_sq_one hh
  have hf := quadraticChar_sq_one (neg_ne_zero.mpr hh)
  apply sub_eq_zero.mp
  ring_nf
  rw [he, hf]
  ring


theorem normalizedPairCount_second_moment
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0))
    (hd : Not ((Fintype.card F : Real) - (quadraticPairOffset h : Real) = 0)) :
    (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F => (QuadraticPairEuler.normalizedPairCount c h) ^ 2) =
      1 + (3 * (Fintype.card F : Real) + (quadraticPairOffset h : Real)) /
        ((Fintype.card F : Real) *
          ((Fintype.card F : Real) - (quadraticPairOffset h : Real))) := by
  let q : Real := Fintype.card F
  let d : Real := quadraticPairOffset h
  let S : Real := Finset.univ.sum (fun c : F => (monicQuadraticPairCount c h : Real))
  have hq : Not (q = 0) := by
    dsimp [q]
    exact_mod_cast (show Not (Fintype.card F = 0) from Fintype.card_ne_zero)
  have htI :
      4 * (Finset.univ.sum fun c : F => monicQuadraticPairCount c h) =
        (Fintype.card F : Int) * ((Fintype.card F : Int) - quadraticPairOffset h) := by
    rw [sum_monicQuadraticPairCount_eq hF h hh]
    unfold quadraticPairOffset
    ring
  have ht : 4 * S = q * (q - d) := by
    dsimp [S, q, d]
    exact_mod_cast htI
  have hS : S = q * (q - d) / 4 := by linarith only [ht]
  have hpoint (c : F) :
      QuadraticPairEuler.normalizedPairCount c h =
        4 * (monicQuadraticPairCount c h : Real) / (q - d) := by
    change q * (monicQuadraticPairCount c h : Real) / S = _
    rw [hS]
    field_simp [hq, hd] <;> ring
  have hsqI := sum_monicQuadraticPairCount_square hF h hh
  have hsq :
      16 * (Finset.univ.sum fun c : F => (monicQuadraticPairCount c h : Real) ^ 2) =
        (q - d) * (q ^ 2 + (3 - d) * q + d) := by
    dsimp [q, d]
    exact_mod_cast hsqI
  have hsq' :
      (Finset.univ.sum fun c : F => (monicQuadraticPairCount c h : Real) ^ 2) =
        (q - d) * (q ^ 2 + (3 - d) * q + d) / 16 := by linarith only [hsq]
  have hp (c : F) :
      (QuadraticPairEuler.normalizedPairCount c h) ^ 2 =
        (16 / (q - d) ^ 2) * (monicQuadraticPairCount c h : Real) ^ 2 := by
    rw [hpoint]
    generalize hz : q - d = z
    have hz0 : Not (z = 0) := by rw [<- hz]; exact hd
    field_simp [hz0] <;> ring
  change (1 / q) *
    (Finset.univ.sum fun c : F => (QuadraticPairEuler.normalizedPairCount c h) ^ 2) =
      1 + (3 * q + d) / (q * (q - d))
  simp_rw [hp]
  rw [<- Finset.mul_sum, hsq']
  generalize hz : q - d = z
  have hz0 : Not (z = 0) := by rw [<- hz]; exact hd
  field_simp [hq, hz0] <;> rw [<- hz] <;> ring


theorem normalizedPairCount_mean_one
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0))
    (hd : Not ((Fintype.card F : Real) - (quadraticPairOffset h : Real) = 0)) :
    (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F => QuadraticPairEuler.normalizedPairCount c h) = 1 := by
  let q : Real := Fintype.card F
  let d : Real := quadraticPairOffset h
  let S : Real := Finset.univ.sum (fun c : F => (monicQuadraticPairCount c h : Real))
  have hq : Not (q = 0) := by
    dsimp [q]
    exact_mod_cast (show Not (Fintype.card F = 0) from Fintype.card_ne_zero)
  have htI :
      4 * (Finset.univ.sum fun c : F => monicQuadraticPairCount c h) =
        (Fintype.card F : Int) * ((Fintype.card F : Int) - quadraticPairOffset h) := by
    rw [sum_monicQuadraticPairCount_eq hF h hh]
    unfold quadraticPairOffset
    ring
  have ht : 4 * S = q * (q - d) := by
    dsimp [S, q, d]
    exact_mod_cast htI
  have hSne : Not (S = 0) := by
    intro hz
    have hp : q * (q - d) = 0 := by linarith only [ht, hz]
    exact (mul_ne_zero hq hd) hp
  have hp (c : F) :
      QuadraticPairEuler.normalizedPairCount c h =
        (q / S) * (monicQuadraticPairCount c h : Real) := by
    change q * (monicQuadraticPairCount c h : Real) / S = _
    ring
  simp_rw [hp]
  rw [<- Finset.mul_sum]
  change (1 / q) * ((q / S) * S) = 1
  field_simp [hq, hSne]

theorem normalizedPairCount_variance
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0))
    (hd : Not ((Fintype.card F : Real) - (quadraticPairOffset h : Real) = 0)) :
    (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F => (QuadraticPairEuler.normalizedPairCount c h - 1) ^ 2) =
      (3 * (Fintype.card F : Real) + (quadraticPairOffset h : Real)) /
        ((Fintype.card F : Real) *
          ((Fintype.card F : Real) - (quadraticPairOffset h : Real))) := by
  have hp (c : F) :
      (QuadraticPairEuler.normalizedPairCount c h - 1) ^ 2 =
        (QuadraticPairEuler.normalizedPairCount c h) ^ 2 -
          2 * QuadraticPairEuler.normalizedPairCount c h + 1 := by ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hq : Not ((Fintype.card F : Real) = 0) := by
    exact_mod_cast (show Not (Fintype.card F = 0) from Fintype.card_ne_zero)
  have hqq : (1 / (Fintype.card F : Real)) * (Fintype.card F : Real) = 1 := by
    field_simp [hq]
  nlinarith only [normalizedPairCount_mean_one hF h hh hd,
    normalizedPairCount_second_moment hF h hh hd, hqq]

theorem quadraticPairOffset_real_cases (h : F) (hh : Not (h = 0)) :
    (quadraticPairOffset h : Real) = 1 \/
      (quadraticPairOffset h : Real) = 3 \/ (quadraticPairOffset h : Real) = 5 := by
  have hoff : (quadraticPairOffset h : Real) =
      3 - ((quadraticChar F) h : Real) - ((quadraticChar F) (-h) : Real) := by
    simp only [quadraticPairOffset, Int.cast_sub, Int.cast_ofNat]
  simp only [hoff]
  rcases QuadraticPairEuler.quadraticChar_real_signs h hh with he | he <;>
    rcases QuadraticPairEuler.quadraticChar_real_signs (-h) (neg_ne_zero.mpr hh) with hf | hf <;>
    rw [he, hf] <;> norm_num

theorem quadraticPairOffset_real_bounds (h : F) (hh : Not (h = 0)) :
    1 <= (quadraticPairOffset h : Real) /\ (quadraticPairOffset h : Real) <= 5 := by
  rcases quadraticPairOffset_real_cases h hh with ho | ho | ho <;>
    rw [ho] <;> constructor <;> norm_num

theorem normalizedPairCount_second_moment_large
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0))
    (hq : 16 <= (Fintype.card F : Real)) :
    (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F => (QuadraticPairEuler.normalizedPairCount c h) ^ 2) =
      1 + (3 * (Fintype.card F : Real) + (quadraticPairOffset h : Real)) /
        ((Fintype.card F : Real) *
          ((Fintype.card F : Real) - (quadraticPairOffset h : Real))) := by
  have hb := quadraticPairOffset_real_bounds h hh
  have hd : 0 < (Fintype.card F : Real) - (quadraticPairOffset h : Real) := by
    linarith only [hq, hb.2]
  exact normalizedPairCount_second_moment hF h hh (ne_of_gt hd)


theorem quadraticPairCount_zero_of_zero_normalizer
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0))
    (hz : (Fintype.card F : Int) - quadraticPairOffset h = 0) (c : F) :
    monicQuadraticPairCount c h = 0 := by
  have hs := sum_monicQuadraticPairCount_square hF h hh
  rw [hz, zero_mul] at hs
  have hsum : (Finset.univ.sum fun t : F => (monicQuadraticPairCount t h) ^ 2) = 0 := by
    linarith only [hs]
  have hterm : (monicQuadraticPairCount c h) ^ 2 <=
      Finset.univ.sum (fun t : F => (monicQuadraticPairCount t h) ^ 2) :=
    Finset.single_le_sum (fun t _ => sq_nonneg (monicQuadraticPairCount t h))
      (Finset.mem_univ c)
  rw [hsum] at hterm
  exact sq_eq_zero_iff.mp (le_antisymm hterm (sq_nonneg (monicQuadraticPairCount c h)))

theorem normalizedPairCount_zero_of_zero_normalizer
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0))
    (hz : (Fintype.card F : Int) - quadraticPairOffset h = 0) (c : F) :
    QuadraticPairEuler.normalizedPairCount c h = 0 := by
  unfold QuadraticPairEuler.normalizedPairCount
  rw [quadraticPairCount_zero_of_zero_normalizer hF h hh hz c]
  simp

end FiniteField
