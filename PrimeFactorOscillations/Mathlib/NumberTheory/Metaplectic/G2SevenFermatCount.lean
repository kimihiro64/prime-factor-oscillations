/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenCurveFrobenius

/-!
# Actual affine Fermat-septic counts

The complete seventh-root fibers are consumed twice. No character sum,
endpoint or principal contribution is removed by an absolute estimate.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Fermat

open Curve

variable {F : Type*} [Field F] [Fintype F]

noncomputable def affineCount (F : Type*) [Field F] [Fintype F] : Nat := by
  classical
  exact (Finset.univ.filter (fun xy : Prod F F => xy.1 ^ 7 + xy.2 ^ 7 = 1)).card

theorem affine_count_fibers :
    affineCount F = Finset.univ.sum (fun x : F => rootCount (1 - x ^ 7)) := by
  classical
  have he (x y : F) : x ^ 7 + y ^ 7 = 1 <-> y ^ 7 = 1 - x ^ 7 := by
    rw [eq_sub_iff_add_eq, add_comm]
  simp only [affineCount, rootCount, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type, he]

private theorem root_count_as_sum [DecidableEq F] (z : F) :
    (rootCount z : Complex) =
      Finset.univ.sum (fun y : F => if y ^ 7 = z then (1 : Complex) else 0) := by
  unfold rootCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> norm_num

/-- The actual seventh-power pushforward retains every root multiplicity. -/
theorem seventh_power_pushforward (w : F -> Complex) :
    Finset.univ.sum (fun x : F => w (x ^ 7)) =
      Finset.univ.sum (fun z : F => (rootCount z : Complex) * w z) := by
  classical
  simp_rw [root_count_as_sum, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

omit [Fintype F] in
private theorem character_power_ne_one (chi : MulChar F Complex)
    (horder : orderOf chi = 7) (r : Fin 6) :
    Not (chi ^ (r.val + 1) = 1) := by
  intro he
  have hd := orderOf_dvd_of_pow_eq_one he
  rw [horder] at hd
  have hn : Not (Dvd.dvd 7 (r.val + 1)) := by fin_cases r <;> norm_num
  exact hn hd

/-- Every one of the 36 Jacobi terms remains, including the six inverse pairs. -/
theorem affine_count_all_jacobi (chi : MulChar F Complex) (horder : orderOf chi = 7) :
    (affineCount F : Complex) = (Fintype.card F : Complex) +
      Finset.univ.sum (fun r : Fin 6 => Finset.univ.sum (fun s : Fin 6 =>
        jacobi (chi ^ (r.val + 1)) (chi ^ (s.val + 1)))) := by
  classical
  have hs (r : Fin 6) :
      Finset.univ.sum (fun x : F => (chi ^ (r.val + 1)) x) = 0 :=
    MulChar.sum_eq_zero_of_ne_one (character_power_ne_one chi horder r)
  let e : Equiv F F := {
    toFun := fun x => 1 - x
    invFun := fun x => 1 - x
    left_inv := by intro x; dsimp; ring
    right_inv := by intro x; dsimp; ring
  }
  have ht (r : Fin 6) :
      Finset.univ.sum (fun x : F => (chi ^ (r.val + 1)) (1 - x)) = 0 := by
    rw [Fintype.sum_equiv e
      (fun x : F => (chi ^ (r.val + 1)) (1 - x))
      (fun x : F => (chi ^ (r.val + 1)) x) (fun _ => rfl)]
    exact hs r
  have ha : Finset.univ.sum (fun x : F =>
      Finset.univ.sum (fun r : Fin 6 => (chi ^ (r.val + 1)) x)) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [hs]
    simp
  have hb : Finset.univ.sum (fun x : F =>
      Finset.univ.sum (fun r : Fin 6 => (chi ^ (r.val + 1)) (1 - x))) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [ht]
    simp
  have hc : Finset.univ.sum (fun x : F =>
      (Finset.univ.sum (fun r : Fin 6 => (chi ^ (r.val + 1)) x)) *
        Finset.univ.sum (fun s : Fin 6 => (chi ^ (s.val + 1)) (1 - x))) =
      Finset.univ.sum (fun r : Fin 6 => Finset.univ.sum (fun s : Fin 6 =>
        jacobi (chi ^ (r.val + 1)) (chi ^ (s.val + 1)))) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    rfl
  calc
    _ = Finset.univ.sum (fun x : F => (rootCount (1 - x ^ 7) : Complex)) := by
      rw [affine_count_fibers, Nat.cast_sum]
    _ = Finset.univ.sum (fun z : F =>
        (rootCount z : Complex) * (rootCount (1 - z) : Complex)) :=
      seventh_power_pushforward (fun z => (rootCount (1 - z) : Complex))
    _ = _ := by
      simp_rw [seventh_root_fiber chi horder]
      have he (a b : Complex) : (1 + a) * (1 + b) = 1 + a + b + a * b := by ring
      simp_rw [he, Finset.sum_add_distrib]
      rw [ha, hb, hc]
      simp

theorem jacobi_inverse_of_mul_eq_one (chi phi : MulChar F Complex)
    (hne : Not (chi = 1)) (hminus : chi (-1) = 1) (hprod : chi * phi = 1) :
    jacobi chi phi = -1 := by
  classical
  let f : F -> F := fun x => if x = 1 then 1 else x / (x - 1)
  have hi : forall x : F, f (f x) = x := by
    intro x
    by_cases hx : x = 1
    . simp [f, hx]
    have hd : Not (x - 1 = 0) := sub_ne_zero.mpr hx
    have hf : Not (x / (x - 1) = 1) := by
      intro he
      have hh := (div_eq_iff hd).mp he
      simp only [one_mul] at hh
      have hbad : (1 : F) = 0 := by
        calc
          1 = x - (x - 1) := by ring
          _ = 0 := sub_eq_zero.mpr hh
      exact one_ne_zero hbad
    dsimp [f]
    rw [ite_eq_right hx, ite_eq_right hf]
    apply (div_eq_iff (sub_ne_zero.mpr hf)).mpr
    field_simp [hd]
    ring
  let e : Equiv F F := {
    toFun := f
    invFun := f
    left_inv := hi
    right_inv := hi
  }
  have hp (z : F) (hz : Not (z = 0)) : chi z * phi z = 1 := by
    rw [<- MulChar.mul_apply, hprod, MulChar.one_apply (isUnit_iff_ne_zero.mpr hz)]
  have he (x : F) :
      chi x * phi (1 - x) = chi (e x) - (if x = 1 then 1 else 0) := by
    by_cases hx : x = 1
    . subst x
      simp [e, f, MulChar.map_zero]
    have hd : Not (x - 1 = 0) := sub_ne_zero.mpr hx
    have hz : Not (1 - x = 0) := sub_ne_zero.mpr (Ne.symm hx)
    have hxw : e x * (1 - x) = -x := by
      change (if x = 1 then 1 else x / (x - 1)) * (1 - x) = -x
      rw [ite_eq_right hx]
      field_simp [hd]
      ring
    have hn : chi (-x) = chi x := by
      rw [show -x = (-1) * x by ring, map_mul, hminus, one_mul]
    rw [ite_eq_right hx, sub_zero]
    calc
      _ = chi (-x) * phi (1 - x) := by rw [hn]
      _ = chi (e x * (1 - x)) * phi (1 - x) := by rw [hxw]
      _ = chi (e x) * (chi (1 - x) * phi (1 - x)) := by rw [map_mul]; ring
      _ = chi (e x) := by rw [hp _ hz, mul_one]
  unfold jacobi
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Fintype.sum_equiv e
    (fun x : F => chi (e x)) (fun x : F => chi x) (fun _ => rfl),
    MulChar.sum_eq_zero_of_ne_one hne]
  simp

/-- The six excluded inverse-character Jacobi sums are exactly minus one. -/
theorem inverse_jacobi (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (r : Fin 6) :
    jacobi (chi ^ (r.val + 1)) (chi ^ (7 - (r.val + 1))) = -1 := by
  have hseven : chi ^ 7 = 1 := by simpa only [horder] using pow_orderOf_eq_one chi
  have hp : chi ^ (r.val + 1) * chi ^ (7 - (r.val + 1)) = 1 := by
    rw [<- pow_add, show r.val + 1 + (7 - (r.val + 1)) = 7 by omega, hseven]
  have ho : (chi ^ (r.val + 1)) ^ 7 = 1 := by
    rw [<- pow_mul, Nat.mul_comm (r.val + 1) 7, pow_mul, hseven, one_pow]
  exact jacobi_inverse_of_mul_eq_one _ _ (character_power_ne_one chi horder r)
    (MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 7) ho) hp

noncomputable def nondegenerateJacobi (chi : MulChar F Complex) : Complex :=
  Finset.univ.sum (fun r : Fin 6 => Finset.univ.sum (fun s : Fin 6 =>
    if (r.val + 1 + (s.val + 1)) % 7 = 0 then 0
    else jacobi (chi ^ (r.val + 1)) (chi ^ (s.val + 1))))

/-- The complete affine count retains the six negative inverse-pair contributions. -/
theorem affine_count_nondegenerate (chi : MulChar F Complex) (horder : orderOf chi = 7) :
    (affineCount F : Complex) = (Fintype.card F : Complex) - 6 +
      nondegenerateJacobi chi := by
  rw [affine_count_all_jacobi chi horder]
  have h0 := inverse_jacobi chi horder 0
  have h1 := inverse_jacobi chi horder 1
  have h2 := inverse_jacobi chi horder 2
  have h3 := inverse_jacobi chi horder 3
  have h4 := inverse_jacobi chi horder 4
  have h5 := inverse_jacobi chi horder 5
  norm_num [Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5
  norm_num [nondegenerateJacobi, Fin.sum_univ_succ]
  rw [h0, h1, h2, h3, h4, h5]
  ring

/-- The two canonical projective charts: Z=1 and the infinity representatives (z:1:0). -/
noncomputable def chartCount (F : Type*) [Field F] [Fintype F] : Nat :=
  affineCount F + rootCount (-1 : F)

theorem infinity_count (chi : MulChar F Complex) (horder : orderOf chi = 7) :
    rootCount (-1 : F) = 7 := by
  have hseven : chi ^ 7 = 1 := by simpa only [horder] using pow_orderOf_eq_one chi
  have hm : chi (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 7) hseven
  have hp (r : Fin 6) : (chi ^ (r.val + 1)) (-1) = 1 := by
    rw [MulChar.pow_apply' chi (by omega), hm, one_pow]
  have hc : (rootCount (-1 : F) : Complex) = 7 := by
    rw [seventh_root_fiber chi horder]
    simp_rw [hp]
    norm_num
  exact_mod_cast hc

/-- All 30 nondegenerate terms give the complete two-chart Fermat discrepancy. -/
theorem chart_count_nondegenerate (chi : MulChar F Complex) (horder : orderOf chi = 7) :
    (chartCount F : Complex) = (Fintype.card F : Complex) + 1 +
      nondegenerateJacobi chi := by
  unfold chartCount
  rw [Nat.cast_add, affine_count_nondegenerate chi horder, infinity_count chi horder]
  norm_num
  ring

theorem affine_count_coprime (hcop : Nat.Coprime (Fintype.card F - 1) 7) :
    affineCount F = Fintype.card F := by
  rw [affine_count_fibers]
  simp_rw [Curve.root_count_coprime hcop]
  simp

/-- In every nonsplit field size the complete two-chart count is exactly q+1. -/
theorem chart_count_of_card_mod_ne_one (hq : Not (Fintype.card F % 7 = 1)) :
    chartCount F = Fintype.card F + 1 := by
  have hcop : Nat.Coprime (Fintype.card F - 1) 7 := by
    rw [Nat.coprime_comm, (by decide : Nat.Prime 7).coprime_iff_not_dvd]
    intro hd
    have hm := Nat.mod_eq_zero_of_dvd hd
    have hp : 0 < Fintype.card F := Fintype.card_pos
    omega
  unfold chartCount
  rw [affine_count_coprime hcop, Curve.root_count_coprime hcop]


end Metaplectic.G2Seven.Fermat
