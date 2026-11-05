/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenFermatReadout
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenJacobiPrimaryCongruence

/-!
# The actual septic arithmetic edge as a Fermat point-count bound
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Metaplectic.G2Seven.Fermat

open Curve

theorem phase_total_real_channels (g h j : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0))
    (hb : Complex.normSq (g ^ 2 / h) = 1)
    (ha : Complex.normSq (g * h / j) = 1)
    (hc : Complex.normSq (g * j ^ 2) = 1)
    (hd : Complex.normSq (h ^ 2 * j) = 1) :
    (phaseTotal g h j).re =
      6 * ((g ^ 2 / h).re + (g * j ^ 2).re + (h ^ 2 * j).re) +
        12 * (g * h / j).re := by
  have hinv (w : Complex) (hw : Complex.normSq w = 1) :
      1 / w = (starRingEnd Complex) w := by
    have hne : Not (w = 0) := by
      intro he
      rw [he] at hw
      norm_num at hw
    apply (div_eq_iff hne).mpr
    rw [mul_comm, Complex.mul_conj, hw]
    norm_num
  have hsum : phaseTotal g h j =
      3 * ((g ^ 2 / h + 1 / (g ^ 2 / h)) +
        (g * j ^ 2 + 1 / (g * j ^ 2)) +
        (h ^ 2 * j + 1 / (h ^ 2 * j))) +
      6 * (g * h / j + 1 / (g * h / j)) := by
    norm_num [phaseTotal, Jacobi.multiplicity, Jacobi.phase, Fin.sum_univ_succ]
    field_simp [hg, hh, hj]
    ring
  rw [hsum, hinv _ hb, hinv _ ha, hinv _ hc, hinv _ hd,
    Complex.add_conj, Complex.add_conj, Complex.add_conj, Complex.add_conj]
  norm_num [Complex.add_re, Complex.mul_re]
  ring

/-- All thirty Jacobi terms specialize to the four actual real channels. -/
theorem chart_trace_four_channels {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p]
    (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (rho : Real) (hrho : 0 < rho)
    (hrhosq : rho ^ 2 = (Fintype.card F : Real)) :
    ((chartCount F : Real) - (Fintype.card F : Real) - 1) / rho =
      6 * ((jacobiSum chi chi / (rho : Complex)).re +
        (jacobiSum (chi ^ 3) (chi ^ 3) / (rho : Complex)).re +
        (jacobiSum (chi ^ 2) (chi ^ 2) / (rho : Complex)).re) +
        12 * (jacobiSum chi (chi ^ 2) / (rho : Complex)).re := by
  let a : Complex := jacobiSum chi (chi ^ 2)
  let b : Complex := jacobiSum chi chi
  let c : Complex := jacobiSum (chi ^ 3) (chi ^ 3)
  let d : Complex := jacobiSum (chi ^ 2) (chi ^ 2)
  let g : Complex := normalizedGauss chi psi (rho : Complex) 1
  let h : Complex := normalizedGauss chi psi (rho : Complex) 2
  let j : Complex := normalizedGauss chi psi (rho : Complex) 3
  have hR : Not ((rho : Complex) = 0) := by exact_mod_cast ne_of_gt hrho
  have hR2 : (rho : Complex) ^ 2 = (Fintype.card F : Complex) := by
    exact_mod_cast hrhosq
  have hg : Not (g = 0) := normalized_gauss_ne_zero chi psi
    (rho : Complex) horder hpsi hR 0
  have hh : Not (h = 0) := normalized_gauss_ne_zero chi psi
    (rho : Complex) horder hpsi hR 1
  have hj : Not (j = 0) := normalized_gauss_ne_zero chi psi
    (rho : Complex) horder hpsi hR 2
  have h4 : normalizedGauss chi psi (rho : Complex) 4 = 1 / j :=
    normalized_gauss_complement chi psi (rho : Complex) horder hpsi hR hR2 2
  have h6 : normalizedGauss chi psi (rho : Complex) 6 = 1 / g :=
    normalized_gauss_complement chi psi (rho : Complex) horder hpsi hR hR2 0
  have hB : b / (rho : Complex) = g ^ 2 / h := by
    simpa [b, g, h, pow_two, jacobi, jacobiSum] using
      normalized_jacobi_pair chi psi (rho : Complex) horder hpsi hR 0 0 (by decide)
  have hA : a / (rho : Complex) = g * h / j := by
    simpa [a, g, h, j, jacobi, jacobiSum] using
      normalized_jacobi_pair chi psi (rho : Complex) horder hpsi hR 0 1 (by decide)
  have hC : c / (rho : Complex) = g * j ^ 2 := by
    have ht : c / (rho : Complex) =
        j * j / normalizedGauss chi psi (rho : Complex) 6 :=
      normalized_jacobi_pair chi psi (rho : Complex) horder hpsi hR 2 2 (by decide)
    rw [h6] at ht
    rw [ht]
    field_simp [hg]
  have hD : d / (rho : Complex) = h ^ 2 * j := by
    have ht : d / (rho : Complex) =
        h * h / normalizedGauss chi psi (rho : Complex) 4 :=
      normalized_jacobi_pair chi psi (rho : Complex) horder hpsi hR 1 1 (by decide)
    rw [h4] at ht
    rw [ht]
    field_simp [hj]
  have hn := Edge.Actual.septic_jacobi_arithmetic p chi horder
  have hb : Complex.normSq b = (Fintype.card F : Real) := hn.1
  have hc : Complex.normSq c = (Fintype.card F : Real) := hn.2.2.1
  have hd : Complex.normSq d = (Fintype.card F : Real) := hn.2.1
  have hac : a * c = b * d := Edge.Actual.septic_jacobi_product chi horder psi hpsi
  have haq := congrArg Complex.normSq hac
  rw [Complex.normSq_mul, Complex.normSq_mul, hb, hc, hd] at haq
  have hq : 0 < (Fintype.card F : Real) := by nlinarith [sq_pos_of_pos hrho]
  have ha : Complex.normSq a = (Fintype.card F : Real) := by nlinarith
  have hunit (w : Complex) (hw : Complex.normSq w = (Fintype.card F : Real)) :
      Complex.normSq (w / (rho : Complex)) = 1 := by
    rw [Complex.normSq_div, Complex.normSq_ofReal, hw,
      show rho * rho = (Fintype.card F : Real) by nlinarith [hrhosq],
      div_self (ne_of_gt hq)]
  have hphase := phase_total_real_channels g h j hg hh hj
    (by rw [<- hB]; exact hunit b hb)
    (by rw [<- hA]; exact hunit a ha)
    (by rw [<- hC]; exact hunit c hc)
    (by rw [<- hD]; exact hunit d hd)
  rw [<- hB, <- hC, <- hD, <- hA] at hphase
  have htrace := congrArg Complex.re
    (fermat_trace_phases chi psi (rho : Complex) horder hpsi hR hR2)
  simp only [Complex.div_ofReal, Complex.add_re, Complex.sub_re,
    Complex.natCast_re, Complex.one_re, Complex.neg_re] at htrace
  change ((Fintype.card F : Real) + 1 - (chartCount F : Real)) / rho =
    -(phaseTotal g h j).re at htrace
  calc
    _ = -(((Fintype.card F : Real) + 1 - (chartCount F : Real)) / rho) := by ring
    _ = _ := by rw [htrace, hphase]; ring


/-- The actual1512 arithmetic edge applies to the complete Fermat chart count. -/
theorem prime_chart_normalized_edge {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p] (hcard : Fintype.card F = p)
    (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (z : Complex) (hz : IsPrimitiveRoot z 7)
    (rho : Real) (hrho : 0 < rho) (hrhosq : rho ^ 2 = (p : Real)) :
    1512 <= (p : Real) *
      (30 - abs (((chartCount F : Real) - (p : Real) - 1) / rho)) ^ 3 := by
  have hq : rho ^ 2 = (Fintype.card F : Real) := by rw [hcard]; exact hrhosq
  have hread := chart_trace_four_channels p chi horder psi hpsi rho hrho hq
  rw [hcard] at hread
  rw [hread]
  exact Edge.Actual.septic_actual_unit_edge p hcard chi horder psi hpsi z hz
    rho hrho hrhosq

/-- A denominator-free positive gap below both Fermat-septic Hasse edges. -/
theorem prime_chart_cubic_edge {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p] (hcard : Fintype.card F = p)
    (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (z : Complex) (hz : IsPrimitiveRoot z 7)
    (rho : Real) (hrho : 0 < rho) (hrhosq : rho ^ 2 = (p : Real)) :
    1512 * rho <=
      (30 * rho - abs ((chartCount F : Real) - (p : Real) - 1)) ^ 3 := by
  let t : Real := (chartCount F : Real) - (p : Real) - 1
  have he := prime_chart_normalized_edge p hcard chi horder psi hpsi z hz
    rho hrho hrhosq
  change 1512 <= (p : Real) * (30 - abs (t / rho)) ^ 3 at he
  have hscale : (p : Real) * (30 - abs (t / rho)) ^ 3 * rho =
      (30 * rho - abs t) ^ 3 := by
    rw [abs_div, abs_of_pos hrho, <- hrhosq]
    field_simp [ne_of_gt hrho]
  have hm := mul_le_mul_of_nonneg_right he (le_of_lt hrho)
  rw [hscale] at hm
  exact hm

/-- The primary packet strengthens the complete Fermat-septic edge. -/
theorem prime_chart_primary_normalized_edge {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p] (hcard : Fintype.card F = p)
    (hp : p % 7 = 1) (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (z : Complex) (hz : IsPrimitiveRoot z 7)
    (rho : Real) (hrho : 0 < rho) (hrhosq : rho ^ 2 = (p : Real)) :
    74088 <= (p : Real) *
      (30 - abs (((chartCount F : Real) - (p : Real) - 1) / rho)) ^ 3 := by
  have hq : rho ^ 2 = (Fintype.card F : Real) := by rw [hcard]; exact hrhosq
  have hread := chart_trace_four_channels p chi horder psi hpsi rho hrho hq
  rw [hcard] at hread
  rw [hread]
  exact Edge.Actual.septic_actual_primary_unit_edge p hcard hp chi horder psi hpsi z hz
    rho hrho hrhosq

/-- A denominator-free positive gap below both Fermat-septic Hasse edges. -/
theorem prime_chart_primary_cubic_edge {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p] (hcard : Fintype.card F = p)
    (hp : p % 7 = 1) (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (z : Complex) (hz : IsPrimitiveRoot z 7)
    (rho : Real) (hrho : 0 < rho) (hrhosq : rho ^ 2 = (p : Real)) :
    74088 * rho <=
      (30 * rho - abs ((chartCount F : Real) - (p : Real) - 1)) ^ 3 := by
  let t : Real := (chartCount F : Real) - (p : Real) - 1
  have he := prime_chart_primary_normalized_edge p hcard hp chi horder psi hpsi z hz
    rho hrho hrhosq
  change 74088 <= (p : Real) * (30 - abs (t / rho)) ^ 3 at he
  have hscale : (p : Real) * (30 - abs (t / rho)) ^ 3 * rho =
      (30 * rho - abs t) ^ 3 := by
    rw [abs_div, abs_of_pos hrho, <- hrhosq]
    field_simp [ne_of_gt hrho]
  have hm := mul_le_mul_of_nonneg_right he (le_of_lt hrho)
  rw [hscale] at hm
  exact hm

end Metaplectic.G2Seven.Fermat
