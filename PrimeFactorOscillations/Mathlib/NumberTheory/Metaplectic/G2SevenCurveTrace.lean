/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.GaussSum
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenJacobiPackets

/-!
# Finite-field Jacobi point counts behind the sevenfold source packet

The generic Gauss convolution and actual curve point counts are kept
separate from an unproved global automorphic Fourier identification.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Curve

variable {F : Type*} [Field F] [Fintype F]

noncomputable def jacobi (chi phi : MulChar F Complex) : Complex :=
  Finset.univ.sum (fun x : F => chi x * phi (1 - x))

/-- The exact Gauss--Jacobi convolution retains the zero additive fiber. -/
theorem gauss_jacobi (chi phi : MulChar F Complex) (psi : AddChar F Complex)
    (hprod : Not (chi * phi = 1)) :
    gaussSum chi psi * gaussSum phi psi = jacobi chi phi * gaussSum (chi * phi) psi := by
  classical
  have hzero : Finset.univ.sum (fun x : F => chi x * phi (-x)) = 0 := by
    have he (x : F) : chi x * phi (-x) = phi (-1) * (chi * phi) x := by
      rw [show -x = (-1) * x by ring, map_mul, MulChar.mul_apply]
      ring
    simp_rw [he]
    rw [<- Finset.mul_sum, MulChar.sum_eq_zero_of_ne_one hprod, mul_zero]
  have hf (t : F) :
      Finset.univ.sum (fun x : F => chi x * phi (t - x)) =
        chi t * phi t * jacobi chi phi := by
    by_cases ht : t = 0
    . simpa only [ht, zero_sub, MulChar.map_zero, zero_mul] using hzero
    . let e : Equiv F F := {
        toFun := fun y => t * y
        invFun := fun x => x / t
        left_inv := by intro y; dsimp; field_simp [ht]
        right_inv := by intro x; dsimp; field_simp [ht]
      }
      have hs := Fintype.sum_equiv e
        (fun y : F => chi (t * y) * phi (t - t * y))
        (fun x : F => chi x * phi (t - x)) (fun _ => rfl)
      rw [<- hs]
      unfold jacobi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [show t - t * y = t * (1 - y) by ring, map_mul, map_mul]
      ring
  rw [gaussSum_mul]
  simp_rw [<- Finset.sum_mul, hf]
  unfold gaussSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [MulChar.mul_apply]
  ring

noncomputable def rootCount (z : F) : Nat := by
  classical
  exact (Finset.univ.filter (fun y : F => y ^ 7 = z)).card

noncomputable def affineCount (F : Type*) [Field F] [Fintype F] : Nat := by
  classical
  exact (Finset.univ.filter (fun xy : Prod F F => xy.2 ^ 7 = xy.1 * (1 - xy.1))).card

theorem affine_count_fibers :
    affineCount F = Finset.univ.sum (fun x : F => rootCount (x * (1 - x))) := by
  classical
  simp only [affineCount, rootCount, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type]

/-- Character fiber counting gives every diagonal Jacobi sum, with its sign. -/
theorem affine_count_jacobi_of_fibers (chi : MulChar F Complex)
    (hfiber : forall z : F, (rootCount z : Complex) =
      1 + Finset.univ.sum (fun r : Fin 6 => (chi ^ (r.val + 1)) z)) :
    (affineCount F : Complex) = (Fintype.card F : Complex) +
      Finset.univ.sum (fun r : Fin 6 => jacobi (chi ^ (r.val + 1)) (chi ^ (r.val + 1))) := by
  classical
  rw [affine_count_fibers, Nat.cast_sum]
  simp_rw [hfiber, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  unfold jacobi
  apply Finset.sum_congr rfl
  intro x _
  exact map_mul _ _ _

/-- A nontrivial order-seven character detects precisely the nonzero seventh powers. -/
theorem seventh_power_iff_character (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (z : F) (hz : Not (z = 0)) :
    (Exists fun y : F => y ^ 7 = z) <-> chi z = 1 := by
  classical
  have hseven : chi ^ 7 = 1 := by simpa only [horder] using pow_orderOf_eq_one chi
  have hscalar (x : F) (hx : Not (x = 0)) : chi x ^ 7 = 1 := by
    rw [<- MulChar.pow_apply' chi (by decide : Not ((7 : Nat) = 0)),
      hseven, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
  have hne : Not (chi = 1) := by
    intro he
    rw [he, orderOf_one] at horder
    norm_num at horder
  cases @IsCyclic.exists_monoid_generator (Units F) inferInstance inferInstance inferInstance with
  | intro gamma hgamma =>
    have hvalue : Not (chi (gamma : F) = 1) := by
      intro hv
      apply hne
      ext x
      rw [MulChar.one_apply_coe]
      cases (Submonoid.mem_powers_iff x gamma).mp (hgamma x) with
      | intro n hn =>
        have he : (gamma : F) ^ n = (x : F) := by
          simpa only [Units.val_pow_eq_pow_val] using
            congrArg (fun u : Units F => (u : F)) hn
        rw [<- he, map_pow, hv, one_pow]
    have hprim : IsPrimitiveRoot (chi (gamma : F)) 7 := by
      apply IsPrimitiveRoot.iff_orderOf.mpr
      have hd := orderOf_dvd_of_pow_eq_one
        (hscalar (gamma : F) (Units.ne_zero gamma))
      cases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with
      | inl ho => exact False.elim (hvalue (orderOf_eq_one_iff.mp ho))
      | inr ho => exact ho
    constructor
    . intro hy
      cases hy with
      | intro y hy =>
        have hy0 : Not (y = 0) := by
          intro he
          rw [he, zero_pow (by decide : Not ((7 : Nat) = 0))] at hy
          exact hz hy.symm
        rw [<- hy, map_pow]
        exact hscalar y hy0
    . intro hv
      cases (Submonoid.mem_powers_iff (Units.mk0 z hz) gamma).mp
          (hgamma (Units.mk0 z hz)) with
      | intro n hn =>
        have he : (gamma : F) ^ n = z := by
          simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using
            congrArg (fun u : Units F => (u : F)) hn
        have hp : chi (gamma : F) ^ n = 1 := by rw [<- map_pow, he]; exact hv
        cases (hprim.pow_eq_one_iff_dvd n).mp hp with
        | intro k hk =>
          apply Exists.intro ((gamma : F) ^ k)
          calc
            ((gamma : F) ^ k) ^ 7 = (gamma : F) ^ (k * 7) := (pow_mul _ _ _).symm
            _ = (gamma : F) ^ (7 * k) := by rw [Nat.mul_comm]
            _ = z := by rw [<- hk]; exact he

private theorem root_count_of_witness (chi : MulChar F Complex)
    (horder : orderOf chi = 7) (z y : F) (hz : Not (z = 0)) (hy : y ^ 7 = z) :
    rootCount z = 7 := by
  classical
  have hy0 : Not (y = 0) := by
    intro he
    rw [he, zero_pow (by decide : Not ((7 : Nat) = 0))] at hy
    exact hz hy.symm
  let y0 : Units F := Units.mk0 y hy0
  let e : Equiv {x : F // x ^ 7 = z}
      {u : Units F // u ^ 7 = y0 ^ 7} := {
    toFun := fun x => Subtype.mk
      (Units.mk0 x.val (by
        intro hx
        have hh := x.property
        rw [hx, zero_pow (by decide : Not ((7 : Nat) = 0))] at hh
        exact hz hh.symm)) (by
          apply Units.ext
          change x.val ^ 7 = y ^ 7
          rw [x.property, hy])
    invFun := fun u => Subtype.mk (u.val : F) (by
      have hh := congrArg (fun v : Units F => (v : F)) u.property
      simpa only [Units.val_pow_eq_pow_val, y0, Units.val_mk0, hy] using hh)
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro u; apply Subtype.ext; apply Units.ext; rfl
  }
  have hdiv : Dvd.dvd 7 (Nat.card (Units F)) := by
    have hd := MulChar.orderOf_dvd_card_sub_one F chi
    rw [horder] at hd
    simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using hd
  calc
    rootCount z = Nat.card {x : F // x ^ 7 = z} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rfl
    _ = Nat.card {u : Units F // u ^ 7 = y0 ^ 7} := Nat.card_congr e
    _ = Nat.card ((powMonoidHom 7 : MonoidHom (Units F) (Units F)).ker) :=
      Nat.card_congr (MonoidHom.fiberEquivKer
        (powMonoidHom 7 : MonoidHom (Units F) (Units F)) y0)
    _ = (Nat.card (Units F)).gcd 7 := IsCyclic.card_powMonoidHom_ker (Units F) 7
    _ = 7 := Nat.gcd_eq_right_iff_dvd.mpr hdiv

/-- Complete seventh-root fiber law, including zero, with no counting hypothesis. -/
theorem seventh_root_fiber (chi : MulChar F Complex) (horder : orderOf chi = 7) (z : F) :
    (rootCount z : Complex) =
      1 + Finset.univ.sum (fun r : Fin 6 => (chi ^ (r.val + 1)) z) := by
  classical
  by_cases hz : z = 0
  . subst z
    have hr : rootCount (0 : F) = 1 := by
      unfold rootCount
      have he : (Finset.univ.filter (fun y : F => y ^ 7 = 0)) = ({0} : Finset F) := by
        ext y
        simp
      rw [he]
      simp
    rw [hr]
    simp [MulChar.map_zero]
  have hp (r : Fin 6) :
      (chi ^ (r.val + 1)) z = chi z ^ (r.val + 1) :=
    MulChar.pow_apply' chi (by omega) z
  simp_rw [hp]
  by_cases hv : chi z = 1
  . cases (seventh_power_iff_character chi horder z hz).mpr hv with
    | intro y hy =>
      rw [root_count_of_witness chi horder z y hz hy, hv]
      norm_num
  . have hroot : rootCount z = 0 := by
      unfold rootCount
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro y _
      intro hy
      exact hv ((seventh_power_iff_character chi horder z hz).mp (Exists.intro y hy))
    rw [hroot, Nat.cast_zero]
    have hseven : chi ^ 7 = 1 := by simpa only [horder] using pow_orderOf_eq_one chi
    have hz7 : chi z ^ 7 = 1 := by
      rw [<- MulChar.pow_apply' chi (by decide : Not ((7 : Nat) = 0)),
        hseven, MulChar.one_apply (isUnit_iff_ne_zero.mpr hz)]
    have hfac : (chi z - 1) *
        (1 + Finset.univ.sum (fun r : Fin 6 => chi z ^ (r.val + 1))) = 0 := by
      calc
        _ = chi z ^ 7 - 1 := by norm_num [Fin.sum_univ_succ]; ring
        _ = 0 := by rw [hz7]; ring
    exact ((mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hv)).symm

/-- Actual finite-field point count of z^7=x(1-x), using every diagonal Jacobi sum. -/
theorem affine_count_jacobi (chi : MulChar F Complex) (horder : orderOf chi = 7) :
    (affineCount F : Complex) = (Fintype.card F : Complex) +
      Finset.univ.sum (fun r : Fin 6 => jacobi (chi ^ (r.val + 1)) (chi ^ (r.val + 1))) :=
  affine_count_jacobi_of_fibers chi (seventh_root_fiber chi horder)

end Metaplectic.G2Seven.Curve
