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
# A nonsquare-norm septic cyclotomic integer is not fixed by exponent three

The existing primitive-root coefficient relation is consumed directly.
No positivity restriction is imposed on the integer coefficients.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace Metaplectic.G2Seven.Edge

theorem septic_nonsquare_norm_not_fixed
    (p : Nat) (hp : Not (IsSquare p)) (z : Complex)
    (hz : IsPrimitiveRoot z 7) (v : Fin 7 -> Int)
    (hnorm : Complex.normSq ((Finset.univ : Finset (Fin 7)).sum
      (fun i => (v i : Complex) * z ^ i.val)) = (p : Real)) :
    Not (((Finset.univ : Finset (Fin 7)).sum
      (fun i => (v i : Complex) * z ^ i.val)) =
      ((Finset.univ : Finset (Fin 7)).sum
        (fun i => (v i : Complex) * (z ^ 3) ^ i.val))) := by
  intro hfixed
  let w : Fin 7 -> Int := fun i =>
    if i.val = 0 then 0 else
    if i.val = 1 then v 1 - v 5 else
    if i.val = 2 then v 2 - v 3 else
    if i.val = 3 then v 3 - v 1 else
    if i.val = 4 then v 4 - v 6 else
    if i.val = 5 then v 5 - v 4 else v 6 - v 2
  have hz7 : z ^ 7 = 1 := hz.pow_eq_one
  have hz9 : z ^ 9 = z ^ 2 := by
    calc
      z ^ 9 = z ^ 7 * z ^ 2 := by ring
      _ = z ^ 2 := by rw [hz7, one_mul]
  have hz12 : z ^ 12 = z ^ 5 := by
    calc
      z ^ 12 = z ^ 7 * z ^ 5 := by ring
      _ = z ^ 5 := by rw [hz7, one_mul]
  have hz15 : z ^ 15 = z := by
    calc
      z ^ 15 = (z ^ 7) ^ 2 * z := by ring
      _ = z := by rw [hz7]; ring
  have hz18 : z ^ 18 = z ^ 4 := by
    calc
      z ^ 18 = (z ^ 7) ^ 2 * z ^ 4 := by ring
      _ = z ^ 4 := by rw [hz7]; ring
  have hfix := hfixed
  norm_num [Fin.sum_univ_succ] at hfix
  ring_nf at hfix
  rw [hz9, hz12, hz15, hz18] at hfix
  have hzero : (Finset.univ : Finset (Fin 7)).sum
      (fun i => (w i : Complex) * z ^ i.val) = 0 := by
    norm_num [w, Fin.sum_univ_succ]
    linear_combination hfix
  have hall := (IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int
    (by decide : Nat.Prime 7) hz w).mp hzero
  have h1 := hall 1 0
  have h2 := hall 2 0
  have h3 := hall 3 0
  have h4 := hall 4 0
  have h5 := hall 5 0
  have h6 := hall 6 0
  norm_num [w] at h1 h2 h3 h4 h5 h6
  have hv2 : v 2 = v 1 := by linarith
  have hv3 : v 3 = v 1 := by linarith
  have hv4 : v 4 = v 1 := by linarith
  have hv5 : v 5 = v 1 := by linarith
  have hv6 : v 6 = v 1 := by linarith
  have hroots : (Finset.univ : Finset (Fin 7)).sum
      (fun i => ((1 : Int) : Complex) * z ^ i.val) = 0 :=
    (IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int
      (by decide : Nat.Prime 7) hz (fun _ => 1)).mpr (fun _ _ => rfl)
  norm_num [Fin.sum_univ_succ] at hroots
  have hvalue : (Finset.univ : Finset (Fin 7)).sum
      (fun i => (v i : Complex) * z ^ i.val) =
      ((v 0 - v 1 : Int) : Complex) := by
    norm_num [Fin.sum_univ_succ]
    rw [hv2, hv3, hv4, hv5, hv6]
    linear_combination (v 1 : Complex) * hroots
  rw [hvalue, Complex.normSq_intCast] at hnorm
  have hint : (v 0 - v 1) * (v 0 - v 1) = (p : Int) := by
    exact_mod_cast hnorm
  have hnat := congrArg Int.natAbs hint
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hnat
  apply hp
  refine Exists.intro (v 0 - v 1).natAbs ?_
  nlinarith [hnat]

/-- All three signed beta factors are nonzero on the same septic orbit. -/
theorem septic_nonsquare_full_beta_nonzero
    (p : Nat) (hp : Not (IsSquare p)) (z : Complex)
    (hz : IsPrimitiveRoot z 7) (v : Fin 7 -> Int)
    (hnorm1 : Complex.normSq ((Finset.univ : Finset (Fin 7)).sum
      (fun i => (v i : Complex) * z ^ i.val)) = (p : Real))
    (hnorm2 : Complex.normSq ((Finset.univ : Finset (Fin 7)).sum
      (fun i => (v i : Complex) * (z ^ 2) ^ i.val)) = (p : Real))
    (hnorm4 : Complex.normSq ((Finset.univ : Finset (Fin 7)).sum
      (fun i => (v i : Complex) * (z ^ 4) ^ i.val)) = (p : Real)) :
    Not ((((Finset.univ : Finset (Fin 7)).sum
          (fun i => (v i : Complex) * z ^ i.val)) -
        ((Finset.univ : Finset (Fin 7)).sum
          (fun i => (v i : Complex) * (z ^ 3) ^ i.val))) *
      (((Finset.univ : Finset (Fin 7)).sum
          (fun i => (v i : Complex) * (z ^ 2) ^ i.val)) -
        ((Finset.univ : Finset (Fin 7)).sum
          (fun i => (v i : Complex) * (z ^ 6) ^ i.val))) *
      (((Finset.univ : Finset (Fin 7)).sum
          (fun i => (v i : Complex) * (z ^ 4) ^ i.val)) -
        ((Finset.univ : Finset (Fin 7)).sum
          (fun i => (v i : Complex) * (z ^ 5) ^ i.val))) = 0) := by
  have h1 := septic_nonsquare_norm_not_fixed p hp z hz v hnorm1
  have h2 := septic_nonsquare_norm_not_fixed p hp (z ^ 2)
    (hz.pow_of_coprime 2 (by decide)) v hnorm2
  have h4 := septic_nonsquare_norm_not_fixed p hp (z ^ 4)
    (hz.pow_of_coprime 4 (by decide)) v hnorm4
  have hz2 : (z ^ 2) ^ 3 = z ^ 6 := by ring
  have hz4 : (z ^ 4) ^ 3 = z ^ 5 := by
    calc
      (z ^ 4) ^ 3 = z ^ 7 * z ^ 5 := by ring
      _ = z ^ 5 := by rw [hz.pow_eq_one, one_mul]
  rw [hz2] at h2
  rw [hz4] at h4
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h1)
    (sub_ne_zero.mpr h2)) (sub_ne_zero.mpr h4)

private theorem prime_not_square (p : Nat) (hp : p.Prime) :
    Not (IsSquare p) := by
  intro hs
  cases hs with
  | intro t ht =>
    have hdvd : Dvd.dvd t p := Exists.intro t (by nlinarith [ht])
    cases (Nat.dvd_prime hp).mp hdvd with
    | inl hone =>
      rw [hone] at ht
      have hp2 := hp.two_le
      nlinarith
    | inr hprime =>
      rw [hprime] at ht
      have hp2 := hp.two_le
      nlinarith

theorem septic_prime_norm_not_fixed
    (p : Nat) (hp : p.Prime) (z : Complex)
    (hz : IsPrimitiveRoot z 7) (v : Fin 7 -> Int)
    (hnorm : Complex.normSq ((Finset.univ : Finset (Fin 7)).sum
      (fun i => (v i : Complex) * z ^ i.val)) = (p : Real)) :
    Not (((Finset.univ : Finset (Fin 7)).sum
      (fun i => (v i : Complex) * z ^ i.val)) =
      ((Finset.univ : Finset (Fin 7)).sum
        (fun i => (v i : Complex) * (z ^ 3) ^ i.val))) := by
  exact septic_nonsquare_norm_not_fixed p (prime_not_square p hp) z hz v hnorm

theorem septic_full_beta_nonzero
    (p : Nat) (hp : p.Prime) (z : Complex)
    (hz : IsPrimitiveRoot z 7) (v : Fin 7 -> Int)
    (hnorm1 : Complex.normSq ((Finset.univ : Finset (Fin 7)).sum
      (fun i => (v i : Complex) * z ^ i.val)) = (p : Real))
    (hnorm2 : Complex.normSq ((Finset.univ : Finset (Fin 7)).sum
      (fun i => (v i : Complex) * (z ^ 2) ^ i.val)) = (p : Real))
    (hnorm4 : Complex.normSq ((Finset.univ : Finset (Fin 7)).sum
      (fun i => (v i : Complex) * (z ^ 4) ^ i.val)) = (p : Real)) :
    Not ((((Finset.univ : Finset (Fin 7)).sum
          (fun i => (v i : Complex) * z ^ i.val)) -
        ((Finset.univ : Finset (Fin 7)).sum
          (fun i => (v i : Complex) * (z ^ 3) ^ i.val))) *
      (((Finset.univ : Finset (Fin 7)).sum
          (fun i => (v i : Complex) * (z ^ 2) ^ i.val)) -
        ((Finset.univ : Finset (Fin 7)).sum
          (fun i => (v i : Complex) * (z ^ 6) ^ i.val))) *
      (((Finset.univ : Finset (Fin 7)).sum
          (fun i => (v i : Complex) * (z ^ 4) ^ i.val)) -
        ((Finset.univ : Finset (Fin 7)).sum
          (fun i => (v i : Complex) * (z ^ 5) ^ i.val))) = 0) := by
  exact septic_nonsquare_full_beta_nonzero p (prime_not_square p hp) z hz v
    hnorm1 hnorm2 hnorm4

end Metaplectic.G2Seven.Edge
