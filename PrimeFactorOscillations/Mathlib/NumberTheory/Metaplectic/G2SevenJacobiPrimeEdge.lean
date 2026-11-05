/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenJacobiArithmetic
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenJacobiEdgeAlgebra
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenJacobiUnitCircle

/-!
The actual septic Jacobi packet as an integral quadratic anti-invariant.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

namespace Metaplectic.G2Seven.Edge.Actual

private theorem seventh_power_period {G : Type*} [Group G]
    (t : G) (hseven : t ^ 7 = 1) (r : Nat) :
    t ^ r = t ^ (r % 7) := by
  calc
    t ^ r = t ^ (r % 7 + 7 * (r / 7)) := by rw [Nat.mod_add_div]
    _ = t ^ (r % 7) := by
      rw [pow_add, pow_mul, hseven, one_pow, mul_one]

private theorem seventh_inverse_power {G : Type*} [Group G]
    (t : G) (hseven : t ^ 7 = 1) (r : Nat) :
    Inv.inv (t ^ r) = t ^ (6 * r) := by
  have hprod : t ^ r * (t ^ 6) ^ r = 1 := by
    rw [<- pow_mul, <- pow_add,
      show r + 6 * r = 7 * r by ring, pow_mul, hseven, one_pow]
  calc
    Inv.inv (t ^ r) = Inv.inv (t ^ r) * (t ^ r * (t ^ 6) ^ r) := by
      rw [hprod, mul_one]
    _ = (t ^ 6) ^ r := by rw [<- mul_assoc, inv_mul_cancel, one_mul]
    _ = t ^ (6 * r) := by rw [pow_mul]

private theorem septic_star_row {F : Type*} [Field F] [Fintype F]
    (chi eta : MulChar F Complex) (hchi : chi ^ 7 = 1)
    (heta : eta ^ 7 = 1) (r : Nat) :
    star (jacobiSum (chi ^ r) (eta ^ r)) =
      jacobiSum (chi ^ ((6 * r) % 7)) (eta ^ ((6 * r) % 7)) := by
  have hstar : star (jacobiSum (chi ^ r) (eta ^ r)) =
      jacobiSum (Inv.inv (chi ^ r)) (Inv.inv (eta ^ r)) := by
    simp [jacobiSum, star_mul, MulChar.star_apply', mul_comm]
  rw [hstar, seventh_inverse_power chi hchi r,
    seventh_inverse_power eta heta r,
    seventh_power_period chi hchi (6 * r),
    seventh_power_period eta heta (6 * r)]

/-- The complete actual packet is an integer multiple of the septic tau. -/
theorem septic_actual_integral_packet {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p]
    (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (z : Complex) (hz : IsPrimitiveRoot z 7) :
    Exists fun m : Int =>
      (jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
          jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2)) -
        star (jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
          jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2)) =
        (m : Complex) * (z + z ^ 2 + z ^ 4 - z ^ 3 - z ^ 5 - z ^ 6) := by
  classical
  have hseven : chi ^ 7 = 1 := by
    simpa only [horder] using pow_orderOf_eq_one chi
  let eta : MulChar F Complex := chi ^ 2
  have heta : eta ^ 7 = 1 := by
    change (chi ^ 2) ^ 7 = 1
    rw [pow_right_comm, hseven, one_pow]
  let A : Nat -> Complex := fun r => jacobiSum (chi ^ r) (eta ^ r)
  let B : Nat -> Complex := fun r => jacobiSum (chi ^ r) (chi ^ r)
  have ha (r : Nat) : star (A r) = A ((6 * r) % 7) :=
    septic_star_row chi eta hseven heta r
  have hb (r : Nat) : star (B r) = B ((6 * r) % 7) :=
    septic_star_row chi chi hseven hseven r
  have hd := septic_jacobi_arithmetic p chi horder
  have ha2 : A 2 = A 1 := by
    simpa only [A, eta, pow_one, <- pow_mul] using hd.2.2.2.2.1
  have ha5 : A 5 = A 6 := by
    have hs := congrArg star ha2
    have h2 : star (A 2) = A 5 := ha 2
    have h1 : star (A 1) = A 6 := ha 1
    rw [h2, h1] at hs
    exact hs
  let profileU := Metaplectic.JacobiPower.actual_counting_profile
    7 chi eta z hz hseven heta
  let profileV := Metaplectic.JacobiPower.actual_counting_profile
    7 chi chi z hz hseven hseven
  let u : Fin 7 -> Int := fun j => ((Classical.choose profileU) j : Int)
  let v : Fin 7 -> Int := fun j => ((Classical.choose profileV) j : Int)
  have hu (r : Nat) : A r = septicEval z u r := by
    change jacobiSum (chi ^ r) (eta ^ r) = septicEval z u r
    rw [(Classical.choose_spec profileU).2 r]
    unfold septicEval
    apply Finset.sum_congr rfl
    intro j hj
    simp only [u, Int.cast_natCast]
    rw [<- pow_mul, <- pow_mul, Nat.mul_comm]
  have hv (r : Nat) : B r = septicEval z v r := by
    change jacobiSum (chi ^ r) (chi ^ r) = septicEval z v r
    rw [(Classical.choose_spec profileV).2 r]
    unfold septicEval
    apply Finset.sum_congr rfl
    intro j hj
    simp only [v, Int.cast_natCast]
    rw [<- pow_mul, <- pow_mul, Nat.mul_comm]
  have hu2 : septicEval z u 2 = septicEval z u 1 := by
    rw [<- hu 2, <- hu 1]
    exact ha2
  have hu5 : septicEval z u 5 = septicEval z u 6 := by
    rw [<- hu 5, <- hu 6]
    exact ha5
  have ha1 : star (A 1) = A 6 := ha 1
  have hb1 : star (B 1) = B 6 := hb 1
  have hb2 : star (B 2) = B 5 := hb 2
  have hb3 : star (B 3) = B 4 := hb 3
  have hpacket :
      (A 1 + B 3 - B 1 - B 2) - star (A 1 + B 3 - B 1 - B 2) =
        (((u 1 - u 6 + (v 3 + v 5 + v 6 - v 1 - v 2 - v 4) : Int) :
          Complex)) * (z + z ^ 2 + z ^ 4 - z ^ 3 - z ^ 5 - z ^ 6) := by
    rw [star_sub, star_sub, star_add, ha1, hb3, hb1, hb2]
    rw [hu 1, hv 3, hv 1, hv 2, hu 6, hv 4, hv 6, hv 5]
    exact septic_integral_packet z hz u v hu2 hu5
  exact Exists.intro
    (u 1 - u 6 + (v 3 + v 5 + v 6 - v 1 - v 2 - v 4))
    (by simpa only [A, B, eta, pow_one] using hpacket)

/-- The full signed beta product equals the characteristic times the packet. -/
theorem septic_actual_beta_identity {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p] (hcard : Fintype.card F = p)
    (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive) :
    (jacobiSum chi chi - jacobiSum (chi ^ 3) (chi ^ 3)) *
        (jacobiSum (chi ^ 2) (chi ^ 2) - star (jacobiSum chi chi)) *
        (star (jacobiSum (chi ^ 3) (chi ^ 3)) -
          star (jacobiSum (chi ^ 2) (chi ^ 2))) =
      (p : Complex) *
        ((jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
            jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2)) -
          star (jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
            jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2))) := by
  have hd := septic_jacobi_arithmetic p chi horder
  rw [hcard] at hd
  have hconj (w : Complex) (hw : Complex.normSq w = (p : Real)) :
      w * star w = (p : Complex) := by
    calc
      w * star w = (Complex.normSq w : Complex) := by
        simpa only [Complex.star_def] using Complex.mul_conj w
      _ = (p : Complex) := by rw [hw]; simp
  have hprod := septic_jacobi_product chi horder psi hpsi
  have hstarprod := congrArg star hprod
  simp only [star_mul] at hstarprod
  have hid := signed_beta_identity
    (jacobiSum chi (chi ^ 2)) (star (jacobiSum chi (chi ^ 2)))
    (jacobiSum chi chi) (star (jacobiSum chi chi))
    (jacobiSum (chi ^ 3) (chi ^ 3))
    (star (jacobiSum (chi ^ 3) (chi ^ 3)))
    (jacobiSum (chi ^ 2) (chi ^ 2))
    (star (jacobiSum (chi ^ 2) (chi ^ 2))) (p : Complex)
    (hconj (jacobiSum chi chi) hd.1)
    (hconj (jacobiSum (chi ^ 3) (chi ^ 3)) hd.2.2.1)
    (hconj (jacobiSum (chi ^ 2) (chi ^ 2)) hd.2.1)
    hprod (by simpa only [mul_comm] using hstarprod)
  simpa only [star_sub, star_add] using hid

/-- Prime-field arithmetic forces a nonzero integral quadratic packet. -/
theorem septic_actual_packet_norm_gap {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p] (hcard : Fintype.card F = p)
    (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (z : Complex) (hz : IsPrimitiveRoot z 7) :
    7 <= Complex.normSq
      ((jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
          jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2)) -
        star (jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
          jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2))) := by
  have hseven : chi ^ 7 = 1 := by
    simpa only [horder] using pow_orderOf_eq_one chi
  have hs1 : star (jacobiSum chi chi) =
      jacobiSum (chi ^ 6) (chi ^ 6) := by
    simpa only [pow_one] using septic_star_row chi chi hseven hseven 1
  have hs2 : star (jacobiSum (chi ^ 2) (chi ^ 2)) =
      jacobiSum (chi ^ 5) (chi ^ 5) :=
    septic_star_row chi chi hseven hseven 2
  have hs3 : star (jacobiSum (chi ^ 3) (chi ^ 3)) =
      jacobiSum (chi ^ 4) (chi ^ 4) :=
    septic_star_row chi chi hseven hseven 3
  let beta : Complex :=
    (jacobiSum chi chi - jacobiSum (chi ^ 3) (chi ^ 3)) *
      (jacobiSum (chi ^ 2) (chi ^ 2) - star (jacobiSum chi chi)) *
      (star (jacobiSum (chi ^ 3) (chi ^ 3)) -
        star (jacobiSum (chi ^ 2) (chi ^ 2)))
  have hbeta : Not (beta = 0) := by
    simpa only [beta, hs1, hs2, hs3] using
      septic_actual_beta_nonzero p hcard chi horder z hz
  let T : Complex :=
    jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
      jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2)
  have hid : beta = (p : Complex) * (T - star T) :=
    septic_actual_beta_identity p hcard chi horder psi hpsi
  cases septic_actual_integral_packet p chi horder z hz with
  | intro m hm =>
    have hH : T - star T =
        (m : Complex) * (z + z ^ 2 + z ^ 4 - z ^ 3 - z ^ 5 - z ^ 6) := hm
    have hmne : Not (m = 0) := by
      intro hmzero
      apply hbeta
      rw [hid, hH, hmzero, Int.cast_zero, zero_mul, mul_zero]
    change 7 <= Complex.normSq (T - star T)
    rw [hH]
    exact septic_anti_invariant_norm_gap z hz m hmne


private theorem normalized_packet_product
    (b c d H : Complex) (p rho : Real) (hrho : 0 < rho)
    (hrhosq : rho ^ 2 = p)
    (hb : Complex.normSq b = p)
    (hbeta : (b - c) * (d - (starRingEnd Complex) b) * ((starRingEnd Complex) c - (starRingEnd Complex) d) =
      (p : Complex) * H) :
    p * Complex.normSq (1 - (b / (rho : Complex)) * (d / (rho : Complex))) *
        Complex.normSq (b / (rho : Complex) - c / (rho : Complex)) *
        Complex.normSq (c / (rho : Complex) - d / (rho : Complex)) =
      Complex.normSq H := by
  have hp : 0 < p := by nlinarith [sq_pos_of_pos hrho]
  have hpne : Not (p = 0) := ne_of_gt hp
  have hmul : rho * rho = p := by nlinarith [hrhosq]
  have hsR : (starRingEnd Complex) (rho : Complex) = (rho : Complex) := by simp
  have hbarDiv (w : Complex) :
      (starRingEnd Complex) (w / (rho : Complex)) =
        (starRingEnd Complex) w / (rho : Complex) := by
    simp only [div_eq_mul_inv, map_mul, Complex.conj_inv, hsR]
  let B : Complex := b / (rho : Complex)
  let C : Complex := c / (rho : Complex)
  let D : Complex := d / (rho : Complex)
  have hBn : Complex.normSq B = 1 := by
    dsimp [B]
    rw [Complex.normSq_div, Complex.normSq_ofReal, hb, hmul, div_self hpne]
  have hBconj : B * (starRingEnd Complex) B = 1 := by
    calc
      B * (starRingEnd Complex) B = (Complex.normSq B : Complex) := by
        simpa only [Complex.star_def] using Complex.mul_conj B
      _ = 1 := by rw [hBn]; rfl
  have hbc : B - C = (b - c) / (rho : Complex) := by
    dsimp [B, C]
    rw [sub_div]
  have hdb : D - (starRingEnd Complex) B = (d - (starRingEnd Complex) b) / (rho : Complex) := by
    dsimp [B, D]
    rw [hbarDiv, sub_div]
  have hcd : (starRingEnd Complex) C - (starRingEnd Complex) D =
      ((starRingEnd Complex) c - (starRingEnd Complex) d) / (rho : Complex) := by
    dsimp [C, D]
    rw [hbarDiv, hbarDiv, sub_div]
  let betaN : Complex := (B - C) * (D - (starRingEnd Complex) B) *
    ((starRingEnd Complex) C - (starRingEnd Complex) D)
  have hNbeta : betaN =
      ((b - c) * (d - (starRingEnd Complex) b) *
        ((starRingEnd Complex) c - (starRingEnd Complex) d)) /
          (rho : Complex) ^ 3 := by
    dsimp [betaN]
    rw [hbc, hdb, hcd, <- mul_div_mul_comm, <- mul_div_mul_comm]
    congr 1
    ring
  have hNnorm : Complex.normSq betaN = Complex.normSq H / p := by
    rw [hNbeta, hbeta, Complex.normSq_div, Complex.normSq_mul,
      Complex.normSq_ofReal, map_pow, Complex.normSq_ofReal, hmul]
    field_simp [hpne]
  have hdbNorm : Complex.normSq (D - (starRingEnd Complex) B) =
      Complex.normSq (1 - B * D) := by
    calc
      Complex.normSq (D - (starRingEnd Complex) B) = Complex.normSq (B * (D - (starRingEnd Complex) B)) := by
        rw [Complex.normSq_mul, hBn, one_mul]
      _ = Complex.normSq (B * D - 1) := by rw [mul_sub, hBconj]
      _ = Complex.normSq (1 - B * D) := by
        rw [show B * D - 1 = -(1 - B * D) by ring, Complex.normSq_neg]
  have hcdNorm : Complex.normSq ((starRingEnd Complex) C - (starRingEnd Complex) D) =
      Complex.normSq (C - D) := by
    rw [<- map_sub, Complex.normSq_conj]
  have hnorm : Complex.normSq betaN =
      Complex.normSq (1 - B * D) * Complex.normSq (B - C) *
        Complex.normSq (C - D) := by
    dsimp [betaN]
    rw [Complex.normSq_mul, Complex.normSq_mul, hdbNorm, hcdNorm]
    ring
  change p * Complex.normSq (1 - B * D) * Complex.normSq (B - C) *
    Complex.normSq (C - D) = Complex.normSq H
  calc
    _ = p * Complex.normSq betaN := by rw [hnorm]; ring
    _ = Complex.normSq H := by
      rw [hNnorm]
      field_simp [hpne]


/-- Actual prime-field Jacobi data discharge the complete arithmetic edge bound. -/
theorem septic_actual_unit_edge {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p] (hcard : Fintype.card F = p)
    (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (z : Complex) (hz : IsPrimitiveRoot z 7)
    (rho : Real) (hrho : 0 < rho) (hrhosq : rho ^ 2 = (p : Real)) :
    1512 <= (p : Real) * (30 - abs
      (6 * ((jacobiSum chi chi / (rho : Complex)).re +
        (jacobiSum (chi ^ 3) (chi ^ 3) / (rho : Complex)).re +
        (jacobiSum (chi ^ 2) (chi ^ 2) / (rho : Complex)).re) +
        12 * (jacobiSum chi (chi ^ 2) / (rho : Complex)).re)) ^ 3 := by
  let a : Complex := jacobiSum chi (chi ^ 2)
  let b : Complex := jacobiSum chi chi
  let c : Complex := jacobiSum (chi ^ 3) (chi ^ 3)
  let d : Complex := jacobiSum (chi ^ 2) (chi ^ 2)
  let B : Complex := b / (rho : Complex)
  let C : Complex := c / (rho : Complex)
  let D : Complex := d / (rho : Complex)
  let H : Complex := (a + c - b - d) - star (a + c - b - d)
  have hd := septic_jacobi_arithmetic p chi horder
  rw [hcard] at hd
  have hb : Complex.normSq b = (p : Real) := hd.1
  have hc : Complex.normSq c = (p : Real) := hd.2.2.1
  have hdn : Complex.normSq d = (p : Real) := hd.2.1
  have hp : 0 < (p : Real) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hR : Not ((rho : Complex) = 0) := by
    exact_mod_cast ne_of_gt hrho
  have hrhomul : rho * rho = (p : Real) := by nlinarith [hrhosq]
  have hunit (w : Complex) (hw : Complex.normSq w = (p : Real)) :
      Complex.normSq (w / (rho : Complex)) = 1 := by
    rw [Complex.normSq_div, Complex.normSq_ofReal, hw, hrhomul,
      div_self (ne_of_gt hp)]
  have hBn : Complex.normSq B = 1 := hunit b hb
  have hCn : Complex.normSq C = 1 := hunit c hc
  have hDn : Complex.normSq D = 1 := hunit d hdn
  have hid := septic_actual_beta_identity p hcard chi horder psi hpsi
  have hbeta :
      (b - c) * (d - (starRingEnd Complex) b) *
        ((starRingEnd Complex) c - (starRingEnd Complex) d) =
      ((p : Real) : Complex) * H := by
    simpa only [H, a, b, c, d, Complex.star_def, Complex.ofReal_natCast] using hid
  have hH : 7 <= Complex.normSq H :=
    septic_actual_packet_norm_gap p hcard chi horder psi hpsi z hz
  have hproduct :
      7 <= (p : Real) * Complex.normSq (1 - B * D) *
        Complex.normSq (B - C) * Complex.normSq (C - D) := by
    change 7 <= (p : Real) *
      Complex.normSq (1 - (b / (rho : Complex)) * (d / (rho : Complex))) *
      Complex.normSq (b / (rho : Complex) - c / (rho : Complex)) *
      Complex.normSq (c / (rho : Complex) - d / (rho : Complex))
    rw [normalized_packet_product b c d H (p : Real) rho hrho hrhosq hb hbeta]
    exact hH
  have hcc : c * (starRingEnd Complex) c = (p : Complex) := by
    calc
      c * (starRingEnd Complex) c = (Complex.normSq c : Complex) :=
        Complex.mul_conj c
      _ = (p : Complex) := by rw [hc]; simp
  have hac : a * c = b * d := septic_jacobi_product chi horder psi hpsi
  have hrhoC : (rho : Complex) ^ 2 = (p : Complex) := by
    exact_mod_cast hrhosq
  have hrel : a * (rho : Complex) ^ 2 =
      b * d * (starRingEnd Complex) c := by
    calc
      a * (rho : Complex) ^ 2 = a * (c * (starRingEnd Complex) c) := by
        rw [hrhoC, hcc]
      _ = (a * c) * (starRingEnd Complex) c := by ring
      _ = b * d * (starRingEnd Complex) c := by rw [hac]
  have hsR : (starRingEnd Complex) (rho : Complex) = (rho : Complex) := by simp
  have hbarDiv :
      (starRingEnd Complex) (c / (rho : Complex)) =
        (starRingEnd Complex) c / (rho : Complex) := by
    simp only [div_eq_mul_inv, map_mul, Complex.conj_inv, hsR]
  have hnormal : a / (rho : Complex) = B * D * (starRingEnd Complex) C := by
    dsimp only [B, C, D]
    rw [hbarDiv]
    field_simp [hR]
    linear_combination hrel
  have hgap := unit_absolute_gap B C D (p : Real)
    hBn hCn hDn (le_of_lt hp) hproduct
  rw [<- hnormal] at hgap
  exact hgap

end Metaplectic.G2Seven.Edge.Actual
