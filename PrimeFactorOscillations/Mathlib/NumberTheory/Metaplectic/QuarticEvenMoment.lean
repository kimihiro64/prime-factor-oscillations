/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenCurveTrace

/-!
# The complete quartic fourth-moment Euler factor

The actual finite-field Gauss identity and all four residue classes of
the quartic prime-power coefficient are retained. The resulting numerator
has a plus sign. Thus its Euler interpretation is a direct L-factor,
rather than a reciprocal pole detector. No exponent gain is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Metaplectic.QuarticEvenMoment

variable {F : Type*} [Field F] [Fintype F]

noncomputable def normalizedJacobi (chi : MulChar F Complex) (rho : Complex) :
    Complex := -G2Seven.Curve.jacobi chi chi / rho

/-- The even fourth moment has the positive Jacobi square, with no Mobius sign. -/
theorem gauss_fourth_power (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho : Complex) (horder : orderOf chi = 4) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (hrho2 : rho ^ 2 = (Fintype.card F : Complex)) :
    (gaussSum chi psi / rho) ^ 4 = normalizedJacobi chi rho ^ 2 := by
  have hfour : chi ^ 4 = 1 := by
    simpa only [horder] using pow_orderOf_eq_one chi
  have hquad : Not (chi ^ 2 = 1) := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [horder] at hd
    norm_num at hd
  have hquad2 : (chi ^ 2) ^ 2 = 1 := by
    rw [<- pow_mul]
    exact hfour
  have ho : orderOf (chi ^ 2) = 2 := by
    have hd := orderOf_dvd_of_pow_eq_one hquad2
    cases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with
    | inl he => exact False.elim (hquad (orderOf_eq_one_iff.mp he))
    | inr he => exact he
  have hneg : (chi ^ 2) (-1) = 1 := by
    rw [chi.pow_apply' (by decide : Not ((2 : Nat) = 0)) (-1)]
    rw [<- map_pow]
    norm_num
  have hg := gaussSum_mul_gaussSum_pow_orderOf_sub_one hquad hpsi
  norm_num only [ho, pow_one] at hg
  rw [hneg, one_mul] at hg
  have hmul : chi * chi = chi ^ 2 := (pow_two chi).symm
  have hj := G2Seven.Curve.gauss_jacobi chi chi psi
    (show Not (chi * chi = 1) by rw [hmul]; exact hquad)
  rw [hmul] at hj
  have hraw : gaussSum chi psi ^ 4 =
      G2Seven.Curve.jacobi chi chi ^ 2 * (Fintype.card F : Complex) := by
    calc
      _ = (gaussSum chi psi * gaussSum chi psi) ^ 2 := by ring
      _ = (G2Seven.Curve.jacobi chi chi * gaussSum (chi ^ 2) psi) ^ 2 := by rw [hj]
      _ = G2Seven.Curve.jacobi chi chi ^ 2 *
          (gaussSum (chi ^ 2) psi * gaussSum (chi ^ 2) psi) := by ring
      _ = _ := by rw [hg]
  calc
    (gaussSum chi psi / rho) ^ 4 =
        gaussSum chi psi ^ 4 / rho ^ 4 := div_pow _ _ _
    _ = (G2Seven.Curve.jacobi chi chi ^ 2 * rho ^ 2) / rho ^ 4 := by
      rw [hraw, hrho2]
    _ = normalizedJacobi chi rho ^ 2 := by
      unfold normalizedJacobi
      field_simp [hrho]

/-- The full source coefficient, including the two vanishing residue classes. -/
def coefficient (q g : Complex) (n : Nat) : Complex :=
  if n % 4 = 0 then q ^ (n / 4)
  else if n % 4 = 1 then q ^ (n / 4) * g else 0

/-- Every nonnegative prime-power index is included in its block of four. -/
theorem block_identity (q g T : Complex) (r : Nat) :
    Finset.univ.sum (fun i : Fin 4 =>
      coefficient q g (4 * r + i.val) ^ 4 * T ^ (4 * r + i.val)) =
      (q ^ 4 * T ^ 4) ^ r * (1 + g ^ 4 * T) := by
  have hd (i : Fin 4) : (4 * r + i.val) / 4 = r := by omega
  have hm (i : Fin 4) : (4 * r + i.val) % 4 = i.val := by omega
  have hc (i : Fin 4) :
      coefficient q g (4 * r + i.val) =
        if i.val = 0 then q ^ r else if i.val = 1 then q ^ r * g else 0 := by
    unfold coefficient
    rw [hd, hm]
  simp_rw [hc]
  norm_num [Fin.sum_univ_succ]
  simp only [mul_pow, pow_add, pow_mul]
  ring

theorem blocks_hasSum (q g T : Complex) (h : norm (q ^ 4 * T ^ 4) < 1) :
    HasSum (fun r : Nat => Finset.univ.sum (fun i : Fin 4 =>
      coefficient q g (4 * r + i.val) ^ 4 * T ^ (4 * r + i.val)))
      ((1 + g ^ 4 * T) / (1 - q ^ 4 * T ^ 4)) := by
  have hs := (hasSum_geometric_of_norm_lt_one h).mul_right (1 + g ^ 4 * T)
  convert hs using 1
  . funext r
    exact block_identity q g T r
  . simp only [div_eq_mul_inv]
    ring

/-- The complete actual finite-field fourth-moment factor is direct, not inverse. -/
theorem actual_blocks_hasSum (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho T : Complex) (horder : orderOf chi = 4) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (hrho2 : rho ^ 2 = (Fintype.card F : Complex))
    (h : norm ((Fintype.card F : Complex) ^ 4 * T ^ 4) < 1) :
    HasSum (fun r : Nat => Finset.univ.sum (fun i : Fin 4 =>
      coefficient (Fintype.card F : Complex) (gaussSum chi psi / rho)
        (4 * r + i.val) ^ 4 * T ^ (4 * r + i.val)))
      ((1 + normalizedJacobi chi rho ^ 2 * T) /
        (1 - (Fintype.card F : Complex) ^ 4 * T ^ 4)) := by
  simpa only [gauss_fourth_power chi psi rho horder hpsi hrho hrho2]
    using blocks_hasSum (Fintype.card F : Complex) (gaussSum chi psi / rho) T h

end Metaplectic.QuarticEvenMoment
