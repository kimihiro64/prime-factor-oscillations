/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integral anti-invariants in the septic quadratic subfield

The coefficient conditions express an actual integral anti-conjugate vector.
The exponent-two fixedness is used with the full cyclotomic coefficient
relation, and no beta factor or phase is discarded.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace Metaplectic.G2Seven.Edge

theorem septic_tau_square (z : Complex) (hz : IsPrimitiveRoot z 7) :
    (z + z ^ 2 + z ^ 4 - z ^ 3 - z ^ 5 - z ^ 6) ^ 2 =
      -(7 : Complex) := by
  have hroots : (Finset.univ : Finset (Fin 7)).sum
      (fun i => ((1 : Int) : Complex) * z ^ i.val) = 0 :=
    (IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int
      (by decide : Nat.Prime 7) hz (fun _ => 1)).mpr (fun _ _ => rfl)
  norm_num [Fin.sum_univ_succ] at hroots
  linear_combination
    (7 - 7 * z + z ^ 2 + z ^ 3 - 3 * z ^ 4 + z ^ 5 + z ^ 6) * hroots

theorem septic_integral_anti_invariant
    (z : Complex) (hz : IsPrimitiveRoot z 7) (v : Fin 7 -> Int)
    (hv0 : v 0 = 0) (hv6 : v 6 = -v 1)
    (hv5 : v 5 = -v 2) (hv4 : v 4 = -v 3)
    (hfixed :
      (Finset.univ : Finset (Fin 7)).sum
        (fun i => (v i : Complex) * z ^ i.val) =
      (Finset.univ : Finset (Fin 7)).sum
        (fun i => (v i : Complex) * (z ^ 2) ^ i.val)) :
    (Finset.univ : Finset (Fin 7)).sum
      (fun i => (v i : Complex) * z ^ i.val) =
      (v 1 : Complex) *
        (z + z ^ 2 + z ^ 4 - z ^ 3 - z ^ 5 - z ^ 6) := by
  let w : Fin 7 -> Int := fun i =>
    if i.val = 0 then 0 else
    if i.val = 1 then v 1 - v 4 else
    if i.val = 2 then v 2 - v 1 else
    if i.val = 3 then v 3 - v 5 else
    if i.val = 4 then v 4 - v 2 else
    if i.val = 5 then v 5 - v 6 else v 6 - v 3
  have hz7 : z ^ 7 = 1 := hz.pow_eq_one
  have hz8 : z ^ 8 = z := by
    calc
      z ^ 8 = z ^ 7 * z := by ring
      _ = z := by rw [hz7, one_mul]
  have hz10 : z ^ 10 = z ^ 3 := by
    calc
      z ^ 10 = z ^ 7 * z ^ 3 := by ring
      _ = z ^ 3 := by rw [hz7, one_mul]
  have hz12 : z ^ 12 = z ^ 5 := by
    calc
      z ^ 12 = z ^ 7 * z ^ 5 := by ring
      _ = z ^ 5 := by rw [hz7, one_mul]
  have hfix := hfixed
  norm_num [Fin.sum_univ_succ] at hfix
  ring_nf at hfix
  rw [hz8, hz10, hz12] at hfix
  have hzero : (Finset.univ : Finset (Fin 7)).sum
      (fun i => (w i : Complex) * z ^ i.val) = 0 := by
    norm_num [w, Fin.sum_univ_succ]
    linear_combination hfix
  have hall := (IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int
    (by decide : Nat.Prime 7) hz w).mp hzero
  have h2 := hall 2 0
  have h4 := hall 4 0
  norm_num [w] at h2 h4
  have hval2 : v 2 = v 1 := by linarith
  have hval4 : v 4 = v 1 := by linarith
  have hval3 : v 3 = -v 1 := by linarith
  have hval5 : v 5 = -v 1 := by linarith
  norm_num [Fin.sum_univ_succ]
  rw [hv0, hval2, hval3, hval4, hval5, hv6]
  push_cast
  ring

theorem septic_anti_invariant_norm_gap
    (z : Complex) (hz : IsPrimitiveRoot z 7) (m : Int)
    (hm : Not (m = 0)) :
    7 <= Complex.normSq ((m : Complex) *
      (z + z ^ 2 + z ^ 4 - z ^ 3 - z ^ 5 - z ^ 6)) := by
  let tau := z + z ^ 2 + z ^ 4 - z ^ 3 - z ^ 5 - z ^ 6
  have htau : tau ^ 2 = -(7 : Complex) := septic_tau_square z hz
  have hnorm : Complex.normSq tau * Complex.normSq tau = 49 := by
    rw [<- Complex.normSq_mul, <- pow_two, htau]
    norm_num
  have hnonneg := Complex.normSq_nonneg tau
  have htauNorm : Complex.normSq tau = 7 := by nlinarith
  have hmSquare : (1 : Int) <= m * m :=
    Int.add_one_le_of_lt (mul_self_pos.mpr hm)
  have hmReal : (1 : Real) <= (m : Real) * (m : Real) := by
    exact_mod_cast hmSquare
  change 7 <= Complex.normSq ((m : Complex) * tau)
  rw [Complex.normSq_mul, Complex.normSq_intCast, htauNorm]
  nlinarith

noncomputable def septicEval (z : Complex) (v : Fin 7 -> Int) (r : Nat) :
    Complex :=
  (Finset.univ : Finset (Fin 7)).sum
    (fun i => (v i : Complex) * (z ^ r) ^ i.val)

/-- Both profiles and all eight signed terms are retained in the coefficient. -/
theorem septic_integral_packet (z : Complex) (hz : IsPrimitiveRoot z 7)
    (u v : Fin 7 -> Int)
    (hu2 : septicEval z u 2 = septicEval z u 1)
    (hu5 : septicEval z u 5 = septicEval z u 6) :
    (septicEval z u 1 + septicEval z v 3 -
        septicEval z v 1 - septicEval z v 2) -
      (septicEval z u 6 + septicEval z v 4 -
        septicEval z v 6 - septicEval z v 5) =
      (((u 1 - u 6 +
        (v 3 + v 5 + v 6 - v 1 - v 2 - v 4) : Int) : Complex)) *
        (z + z ^ 2 + z ^ 4 - z ^ 3 - z ^ 5 - z ^ 6) := by
  let S : Int := v 3 + v 5 + v 6 - v 1 - v 2 - v 4
  let w : Fin 7 -> Int := fun i =>
    if i.val = 0 then 0 else
    if i.val = 1 then u 1 - u 6 + S else
    if i.val = 2 then u 2 - u 5 + S else
    if i.val = 3 then u 3 - u 4 - S else
    if i.val = 4 then -(u 3 - u 4 - S) else
    if i.val = 5 then -(u 2 - u 5 + S) else -(u 1 - u 6 + S)
  have hpow (k : Nat) : z ^ k = z ^ (k % 7) := by
    calc
      z ^ k = z ^ (k % 7 + 7 * (k / 7)) := by rw [Nat.mod_add_div]
      _ = z ^ (k % 7) := by
        rw [pow_add, pow_mul, hz.pow_eq_one, one_pow, mul_one]
  have h8 := hpow 8
  have h9 := hpow 9
  have h10 := hpow 10
  have h12 := hpow 12
  have h15 := hpow 15
  have h16 := hpow 16
  have h18 := hpow 18
  have h20 := hpow 20
  have h24 := hpow 24
  have h25 := hpow 25
  have h30 := hpow 30
  have h36 := hpow 36
  norm_num at h8 h9 h10 h12 h15 h16 h18 h20 h24 h25 h30 h36
  have hS1 : (Finset.univ : Finset (Fin 7)).sum
      (fun i => (w i : Complex) * z ^ i.val) =
      (septicEval z u 1 + septicEval z v 3 -
        septicEval z v 1 - septicEval z v 2) -
      (septicEval z u 6 + septicEval z v 4 -
        septicEval z v 6 - septicEval z v 5) := by
    norm_num [septicEval, w, S, Fin.sum_univ_succ]
    ring_nf
    simp only [h8, h9, h10, h12, h15, h16, h18, h20, h24, h25, h30, h36]
    ring
  have hS2 : (Finset.univ : Finset (Fin 7)).sum
      (fun i => (w i : Complex) * (z ^ 2) ^ i.val) =
      (septicEval z u 2 + septicEval z v 6 -
        septicEval z v 2 - septicEval z v 4) -
      (septicEval z u 5 + septicEval z v 1 -
        septicEval z v 5 - septicEval z v 3) := by
    norm_num [septicEval, w, S, Fin.sum_univ_succ]
    ring_nf
    simp only [h8, h9, h10, h12, h15, h16, h18, h20, h24, h25, h30, h36]
    ring
  have hfixed : (Finset.univ : Finset (Fin 7)).sum
      (fun i => (w i : Complex) * z ^ i.val) =
      (Finset.univ : Finset (Fin 7)).sum
        (fun i => (w i : Complex) * (z ^ 2) ^ i.val) := by
    rw [hS1, hS2, hu2, hu5]
    ring
  have he := septic_integral_anti_invariant z hz w
    (by norm_num [w]) (by norm_num [w])
    (by norm_num [w]) (by norm_num [w]) hfixed
  have hw1 : w 1 = u 1 - u 6 + S := by norm_num [w]
  rw [hw1] at he
  simpa only [S] using hS1.symm.trans he

end Metaplectic.G2Seven.Edge
