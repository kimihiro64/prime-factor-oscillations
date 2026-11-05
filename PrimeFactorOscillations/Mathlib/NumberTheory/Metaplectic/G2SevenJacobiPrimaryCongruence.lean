/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.CyclotomicJetCongruence
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.FiniteRootProductProfile
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenJacobiPrimeEdge

/-!
# Primary congruences from the complete actual Jacobi product

The finite support excludes exactly the two zero coordinates. Inversion
and subtraction from one permute that same support; no factor is dropped.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000


namespace Metaplectic.G2Seven.Edge.Actual

/-- The complete prime-field packet has the extra primary factor seven. -/
theorem septic_actual_primary_packet {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p] (hcard : Fintype.card F = p)
    (hp : p % 7 = 1) (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (z : Complex) (hz : IsPrimitiveRoot z 7) :
    Exists fun m : Int => Dvd.dvd (7 : Int) m /\
      (jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
          jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2)) -
        star (jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
          jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2)) =
        (m : Complex) * (z + z ^ 2 + z ^ 4 - z ^ 3 - z ^ 5 - z ^ 6) := by
  classical
  have hseven : chi ^ 7 = 1 := by
    simpa only [horder] using pow_orderOf_eq_one chi
  cases Metaplectic.JacobiPower.actual_diagonal_counting_product_profile
      7 chi z hz hseven with
  | intro v hv =>
    let P : Polynomial Int := Metaplectic.CyclotomicJet.countingPolynomial 7 v
    have hPr (r : Nat) : Polynomial.aeval (z ^ r) P =
        jacobiSum (chi ^ r) (chi ^ r) := by
      rw [Metaplectic.CyclotomicJet.countingPolynomial_eval, hv.2.1 r]
      apply Finset.sum_congr rfl
      intro j hj
      rw [<- pow_mul, <- pow_mul, Nat.mul_comm]
    have hP1 : Polynomial.aeval z P = jacobiSum chi chi := by
      simpa only [pow_one] using hPr 1
    have hS : Dvd.dvd (7 : Int) (P.derivative.eval 1) :=
      Metaplectic.CyclotomicJet.countingPolynomial_first_moment_divisible
        7 v z hz hv.2.2
    have hpint : Dvd.dvd (7 : Int) ((p : Int) - 1) := by
      refine Exists.intro ((p / 7 : Nat) : Int) ?_
      have ht := Nat.mod_add_div p 7
      rw [hp] at ht
      have htt := congrArg (fun a : Nat => (a : Int)) ht
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at htt
      linarith
    have hs1 : star (jacobiSum chi chi) =
        jacobiSum (chi ^ 6) (chi ^ 6) := by
      simpa only [pow_one] using septic_star_row chi chi hseven hseven 1
    have hs2 : star (jacobiSum (chi ^ 2) (chi ^ 2)) =
        jacobiSum (chi ^ 5) (chi ^ 5) :=
      septic_star_row chi chi hseven hseven 2
    have hs3 : star (jacobiSum (chi ^ 3) (chi ^ 3)) =
        jacobiSum (chi ^ 4) (chi ^ 4) :=
      septic_star_row chi chi hseven hseven 3
    have heval : Polynomial.aeval z (Metaplectic.CyclotomicJet.septicBeta P) =
        (jacobiSum chi chi - jacobiSum (chi ^ 3) (chi ^ 3)) *
          (jacobiSum (chi ^ 2) (chi ^ 2) - jacobiSum (chi ^ 6) (chi ^ 6)) *
          (jacobiSum (chi ^ 4) (chi ^ 4) - jacobiSum (chi ^ 5) (chi ^ 5)) := by
      simp only [Metaplectic.CyclotomicJet.septicBeta, map_mul, map_sub,
        Polynomial.aeval_comp, Polynomial.aeval_X_pow, hPr, hP1]
    have htau : Polynomial.aeval z Metaplectic.CyclotomicJet.septicTau =
        z + z ^ 2 + z ^ 4 - z ^ 3 - z ^ 5 - z ^ 6 := by
      simp [Metaplectic.CyclotomicJet.septicTau]
    cases septic_actual_integral_packet p chi horder z hz with
    | intro m hm =>
      refine Exists.intro m (And.intro ?_ hm)
      apply Metaplectic.CyclotomicJet.septic_signed_primary_divisibility
        z hz P (p : Int) m ?_ hS hpint
      have hraw := septic_actual_beta_identity p hcard chi horder psi hpsi
      rw [hs1, hs2, hs3, hm] at hraw
      calc
        Polynomial.aeval z
            (Metaplectic.CyclotomicJet.septicBeta P -
              Polynomial.C ((p : Int) * m) * Metaplectic.CyclotomicJet.septicTau) =
            (jacobiSum chi chi - jacobiSum (chi ^ 3) (chi ^ 3)) *
                (jacobiSum (chi ^ 2) (chi ^ 2) - jacobiSum (chi ^ 6) (chi ^ 6)) *
                (jacobiSum (chi ^ 4) (chi ^ 4) - jacobiSum (chi ^ 5) (chi ^ 5)) -
              (p : Complex) * ((m : Complex) *
                (z + z ^ 2 + z ^ 4 - z ^ 3 - z ^ 5 - z ^ 6)) := by
          simp [heval, htau, mul_assoc]
        _ = 0 := sub_eq_zero.mpr hraw

/-- Primary divisibility strengthens the nonzero packet norm from seven to 343. -/
theorem septic_actual_primary_norm_gap {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p] (hcard : Fintype.card F = p)
    (hp : p % 7 = 1) (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (z : Complex) (hz : IsPrimitiveRoot z 7) :
    343 <= Complex.normSq
      ((jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
          jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2)) -
        star (jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
          jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2))) := by
  let H : Complex :=
    (jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
        jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2)) -
      star (jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
        jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2))
  cases septic_actual_primary_packet p hcard hp chi horder psi hpsi z hz with
  | intro m hm =>
    cases hm.1 with
    | intro k hk =>
      have hH : H = (7 : Complex) *
          ((k : Complex) * (z + z ^ 2 + z ^ 4 - z ^ 3 - z ^ 5 - z ^ 6)) := by
        change _ - star _ = _
        rw [hm.2, hk]
        norm_num
        ring
      have hbase : 7 <= Complex.normSq H :=
        septic_actual_packet_norm_gap p hcard chi horder psi hpsi z hz
      have hkne : Not (k = 0) := by
        intro hzero
        rw [hH] at hbase
        norm_num [hzero] at hbase
      have hnorm := septic_anti_invariant_norm_gap z hz k hkne
      have h7n : Complex.normSq (7 : Complex) = 49 := by norm_num
      change 343 <= Complex.normSq H
      rw [hH, Complex.normSq_mul, h7n]
      nlinarith [hnorm]

theorem septic_actual_primary_unit_edge {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p] (hcard : Fintype.card F = p)
    (hpmod : p % 7 = 1) (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (z : Complex) (hz : IsPrimitiveRoot z 7)
    (rho : Real) (hrho : 0 < rho) (hrhosq : rho ^ 2 = (p : Real)) :
    74088 <= (p : Real) * (30 - abs
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
  have hH : 343 <= Complex.normSq H :=
    septic_actual_primary_norm_gap p hcard hpmod chi horder psi hpsi z hz
  have hproduct :
      343 <= (p : Real) * Complex.normSq (1 - B * D) *
        Complex.normSq (B - C) * Complex.normSq (C - D) := by
    change 343 <= (p : Real) *
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
  have hscaled : 7 <= ((p : Real) / 49) * Complex.normSq (1 - B * D) *
      Complex.normSq (B - C) * Complex.normSq (C - D) := by
    nlinarith [hproduct]
  have hgap := unit_absolute_gap B C D ((p : Real) / 49)
    hBn hCn hDn (div_nonneg (le_of_lt hp) (by norm_num)) hscaled
  rw [<- hnormal] at hgap
  nlinarith [hgap]

end Metaplectic.G2Seven.Edge.Actual
