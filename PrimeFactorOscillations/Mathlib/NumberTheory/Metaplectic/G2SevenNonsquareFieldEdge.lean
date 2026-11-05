/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenJacobiPrimaryCongruence
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenPrimeFieldEdge

/-!
# The complete septic arithmetic edge over nonsquare finite fields

The field cardinality, its characteristic and the cover order are kept
separate. Every signed beta factor and compensation term is retained.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace Metaplectic.CharacterRoots

theorem complex_primitive_additive_exists
    (F : Type*) [Field F] [Fintype F] :
    Exists fun psi : AddChar F Complex => psi.IsPrimitive := by
  classical
  let p : Nat := ringChar F
  have : Fact p.Prime := Fact.mk (CharP.char_is_prime F p)
  have hpne : Not (p = 0) := (Fact.out : Nat.Prime p).ne_zero
  have : NeZero p := NeZero.mk hpne
  let z : Complex := Complex.exp (2 * (Real.pi : Complex) * Complex.I / p)
  have hz : IsPrimitiveRoot z p := Complex.isPrimitiveRoot_exp p hpne
  let psi : AddChar (ZMod p) Complex := AddChar.zmodChar p hz.pow_eq_one
  have hpsi : psi.IsPrimitive :=
    AddChar.zmodChar_primitive_of_primitive_root p hz
  let : Algebra (ZMod p) F := ZMod.algebra _ _
  let theta : AddChar F Complex :=
    psi.compAddMonoidHom (Algebra.trace (ZMod p) F).toAddMonoidHom
  have htheta : Not (theta = 1) := by
    apply AddChar.ne_one_iff.mpr
    cases FiniteField.trace_to_zmod_nondegenerate F (one_ne_zero : Not ((1 : F) = 0)) with
    | intro a ha =>
      rw [one_mul] at ha
      apply Exists.intro a
      intro he
      exact ha ((hpsi.zmod_char_eq_one_iff p (Algebra.trace (ZMod p) F a)).mp he)
  exact Exists.intro theta (AddChar.IsPrimitive.of_ne_one htheta)

end Metaplectic.CharacterRoots

namespace Metaplectic.G2Seven.Edge.Actual

theorem septic_actual_beta_nonzero_nonsquare {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p]
    (hns : Not (IsSquare (Fintype.card F)))
    (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (z : Complex) (hz : IsPrimitiveRoot z 7) :
    Not ((jacobiSum chi chi - jacobiSum (chi ^ 3) (chi ^ 3)) *
      (jacobiSum (chi ^ 2) (chi ^ 2) - jacobiSum (chi ^ 6) (chi ^ 6)) *
      (jacobiSum (chi ^ 4) (chi ^ 4) - jacobiSum (chi ^ 5) (chi ^ 5)) = 0) := by
  classical
  have hseven : chi ^ 7 = 1 := by
    simpa only [horder] using pow_orderOf_eq_one chi
  cases Metaplectic.JacobiPower.actual_counting_profile
      7 chi chi z hz hseven hseven with
  | intro v hv =>
    let w : Fin 7 -> Int := fun j => (v j : Int)
    have hrepr (r : Nat) :
        jacobiSum (chi ^ r) (chi ^ r) =
          (Finset.univ : Finset (Fin 7)).sum
            (fun j => (w j : Complex) * (z ^ r) ^ j.val) := by
      rw [hv.2 r]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [w, Int.cast_natCast]
      rw [<- pow_mul, <- pow_mul, Nat.mul_comm]
    have h1 : jacobiSum chi chi =
        (Finset.univ : Finset (Fin 7)).sum
          (fun j => (w j : Complex) * z ^ j.val) := by
      simpa only [pow_one] using hrepr 1
    have h2 := hrepr 2
    have h3 := hrepr 3
    have h4 := hrepr 4
    have h5 := hrepr 5
    have h6 := hrepr 6
    have hd := septic_jacobi_arithmetic p chi horder
    have hn1 : Complex.normSq ((Finset.univ : Finset (Fin 7)).sum
        (fun j => (w j : Complex) * z ^ j.val)) = (Fintype.card F : Real) := by
      rw [<- h1]
      exact hd.1
    have hn2 : Complex.normSq ((Finset.univ : Finset (Fin 7)).sum
        (fun j => (w j : Complex) * (z ^ 2) ^ j.val)) = (Fintype.card F : Real) := by
      rw [<- h2]
      exact hd.2.1
    have hn4 : Complex.normSq ((Finset.univ : Finset (Fin 7)).sum
        (fun j => (w j : Complex) * (z ^ 4) ^ j.val)) = (Fintype.card F : Real) := by
      rw [<- h4]
      exact hd.2.2.2.1
    have hbeta := Metaplectic.G2Seven.Edge.septic_nonsquare_full_beta_nonzero
      (Fintype.card F) hns z hz w hn1 hn2 hn4
    intro hzero
    apply hbeta
    rw [<- h1, <- h3, <- h2, <- h6, <- h4, <- h5]
    exact hzero

theorem septic_actual_primary_norm_gap_nonsquare
    {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p]
    (hmod : Fintype.card F % 7 = 1) (hns : Not (IsSquare (Fintype.card F)))
    (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (z : Complex) (hz : IsPrimitiveRoot z 7) :
    343 <= Complex.normSq
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
  let H : Complex :=
    (jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
        jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2)) -
      star (jacobiSum chi (chi ^ 2) + jacobiSum (chi ^ 3) (chi ^ 3) -
        jacobiSum chi chi - jacobiSum (chi ^ 2) (chi ^ 2))
  let beta : Complex :=
    (jacobiSum chi chi - jacobiSum (chi ^ 3) (chi ^ 3)) *
      (jacobiSum (chi ^ 2) (chi ^ 2) - jacobiSum (chi ^ 6) (chi ^ 6)) *
      (jacobiSum (chi ^ 4) (chi ^ 4) - jacobiSum (chi ^ 5) (chi ^ 5))
  have hb : Not (beta = 0) :=
    septic_actual_beta_nonzero_nonsquare p hns chi horder z hz
  have hid : beta = (Fintype.card F : Complex) * H := by
    simpa only [beta, H, hs1, hs2, hs3] using
      septic_actual_beta_identity_card p chi horder psi hpsi
  cases septic_actual_primary_packet_card p (Fintype.card F) rfl hmod
      chi horder psi hpsi z hz with
  | intro m hm =>
    cases hm.1 with
    | intro k hk =>
      have hH : H = (7 : Complex) *
          ((k : Complex) * (z + z ^ 2 + z ^ 4 - z ^ 3 - z ^ 5 - z ^ 6)) := by
        change _ - star _ = _
        rw [hm.2, hk]
        norm_num
        ring
      have hkne : Not (k = 0) := by
        intro hzero
        apply hb
        rw [hid, hH, hzero, Int.cast_zero, zero_mul, mul_zero, mul_zero]
      have hnorm := septic_anti_invariant_norm_gap z hz k hkne
      have h7n : Complex.normSq (7 : Complex) = 49 := by norm_num
      change 343 <= Complex.normSq H
      rw [hH, Complex.normSq_mul, h7n]
      nlinarith [hnorm]

theorem septic_actual_primary_unit_edge_nonsquare {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p]
    (hmod : Fintype.card F % 7 = 1) (hns : Not (IsSquare (Fintype.card F)))
    (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (z : Complex) (hz : IsPrimitiveRoot z 7)
    (rho : Real) (hrho : 0 < rho) (hrhosq : rho ^ 2 = (Fintype.card F : Real)) :
    74088 <= (Fintype.card F : Real) * (30 - abs
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
  have hb : Complex.normSq b = (Fintype.card F : Real) := hd.1
  have hc : Complex.normSq c = (Fintype.card F : Real) := hd.2.2.1
  have hdn : Complex.normSq d = (Fintype.card F : Real) := hd.2.1
  have hp : 0 < (Fintype.card F : Real) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hR : Not ((rho : Complex) = 0) := by
    exact_mod_cast ne_of_gt hrho
  have hrhomul : rho * rho = (Fintype.card F : Real) := by nlinarith [hrhosq]
  have hunit (w : Complex) (hw : Complex.normSq w = (Fintype.card F : Real)) :
      Complex.normSq (w / (rho : Complex)) = 1 := by
    rw [Complex.normSq_div, Complex.normSq_ofReal, hw, hrhomul,
      div_self (ne_of_gt hp)]
  have hBn : Complex.normSq B = 1 := hunit b hb
  have hCn : Complex.normSq C = 1 := hunit c hc
  have hDn : Complex.normSq D = 1 := hunit d hdn
  have hid := septic_actual_beta_identity_card p chi horder psi hpsi
  have hbeta :
      (b - c) * (d - (starRingEnd Complex) b) *
        ((starRingEnd Complex) c - (starRingEnd Complex) d) =
      ((Fintype.card F : Real) : Complex) * H := by
    simpa only [H, a, b, c, d, Complex.star_def, Complex.ofReal_natCast] using hid
  have hH : 343 <= Complex.normSq H :=
    septic_actual_primary_norm_gap_nonsquare p hmod hns chi horder psi hpsi z hz
  have hproduct :
      343 <= (Fintype.card F : Real) * Complex.normSq (1 - B * D) *
        Complex.normSq (B - C) * Complex.normSq (C - D) := by
    change 343 <= (Fintype.card F : Real) *
      Complex.normSq (1 - (b / (rho : Complex)) * (d / (rho : Complex))) *
      Complex.normSq (b / (rho : Complex) - c / (rho : Complex)) *
      Complex.normSq (c / (rho : Complex) - d / (rho : Complex))
    rw [normalized_packet_product b c d H (Fintype.card F : Real) rho hrho hrhosq hb hbeta]
    exact hH
  have hcc : c * (starRingEnd Complex) c = (Fintype.card F : Complex) := by
    calc
      c * (starRingEnd Complex) c = (Complex.normSq c : Complex) :=
        Complex.mul_conj c
      _ = (Fintype.card F : Complex) := by rw [hc]; simp
  have hac : a * c = b * d := septic_jacobi_product chi horder psi hpsi
  have hrhoC : (rho : Complex) ^ 2 = (Fintype.card F : Complex) := by
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
  have hscaled : 7 <= ((Fintype.card F : Real) / 49) * Complex.normSq (1 - B * D) *
      Complex.normSq (B - C) * Complex.normSq (C - D) := by
    nlinarith [hproduct]
  have hgap := unit_absolute_gap B C D ((Fintype.card F : Real) / 49)
    hBn hCn hDn (div_nonneg (le_of_lt hp) (by norm_num)) hscaled
  rw [<- hnormal] at hgap
  nlinarith [hgap]

end Metaplectic.G2Seven.Edge.Actual

namespace Metaplectic.G2Seven.Fermat

/-- A character-free complete point-count edge over every nonsquare finite field q>=3. -/
theorem nonsquare_field_primary_cubic_edge
    (F : Type*) [Field F] [Fintype F]
    (hq : 3 <= Fintype.card F) (hns : Not (IsSquare (Fintype.card F)))
    (rho : Real) (hrho : 0 < rho) (hrhosq : rho ^ 2 = (Fintype.card F : Real)) :
    74088 * rho <= (30 * rho -
      abs ((chartCount F : Real) - (Fintype.card F : Real) - 1)) ^ 3 := by
  classical
  let p : Nat := ringChar F
  have : Fact p.Prime := Fact.mk (CharP.char_is_prime F p)
  by_cases hmod : Fintype.card F % 7 = 1
  . have hd : Dvd.dvd 7 (Fintype.card F - 1) := by
      refine Exists.intro (Fintype.card F / 7) ?_
      have ht := Nat.mod_add_div (Fintype.card F) 7
      rw [hmod] at ht
      omega
    cases Metaplectic.CharacterRoots.complex_character_of_order_exists F 7 hd with
    | intro chi hchi =>
      cases Metaplectic.CharacterRoots.complex_primitive_additive_exists F with
      | intro psi hpsi =>
        let z : Complex := Complex.exp (2 * (Real.pi : Complex) * Complex.I / 7)
        have hz : IsPrimitiveRoot z 7 := Complex.isPrimitiveRoot_exp 7 (by decide)
        have hread := chart_trace_four_channels p chi hchi psi hpsi rho hrho hrhosq
        have he := Edge.Actual.septic_actual_primary_unit_edge_nonsquare
          p hmod hns chi hchi psi hpsi z hz rho hrho hrhosq
        rw [<- hread] at he
        let t : Real := (chartCount F : Real) - (Fintype.card F : Real) - 1
        change 74088 <= (Fintype.card F : Real) * (30 - abs (t / rho)) ^ 3 at he
        have hscale :
            (Fintype.card F : Real) * (30 - abs (t / rho)) ^ 3 * rho =
              (30 * rho - abs t) ^ 3 := by
          rw [abs_div, abs_of_pos hrho, <- hrhosq]
          field_simp [ne_of_gt hrho]
        have hm := mul_le_mul_of_nonneg_right he (le_of_lt hrho)
        rw [hscale] at hm
        exact hm
  . have hN : chartCount F = Fintype.card F + 1 :=
      chart_count_of_card_mod_ne_one hmod
    have hqR : 3 <= (Fintype.card F : Real) := by exact_mod_cast hq
    have hc : 74088 <= 27000 * (Fintype.card F : Real) := by nlinarith [hqR]
    have hraw : 74088 * rho <= (30 * rho) ^ 3 := by
      calc
        74088 * rho <= (27000 * (Fintype.card F : Real)) * rho :=
          mul_le_mul_of_nonneg_right hc (le_of_lt hrho)
        _ = (30 * rho) ^ 3 := by rw [<- hrhosq]; ring
    simpa [hN] using hraw

/-- The sharp uniform cubic constant when the two-element field is included. -/
theorem nonsquare_field_uniform_cubic_edge
    (F : Type*) [Field F] [Fintype F]
    (hns : Not (IsSquare (Fintype.card F)))
    (rho : Real) (hrho : 0 < rho) (hrhosq : rho ^ 2 = (Fintype.card F : Real)) :
    54000 * rho <= (30 * rho -
      abs ((chartCount F : Real) - (Fintype.card F : Real) - 1)) ^ 3 := by
  by_cases hq : 3 <= Fintype.card F
  . have hc : (54000 : Real) <= 74088 := by norm_num
    exact le_trans (mul_le_mul_of_nonneg_right hc (le_of_lt hrho))
      (nonsquare_field_primary_cubic_edge F hq hns rho hrho hrhosq)
  . have hq2 : Fintype.card F = 2 := by
      have ht : 1 < Fintype.card F := Fintype.one_lt_card
      omega
    have hmod : Not (Fintype.card F % 7 = 1) := by rw [hq2]; norm_num
    have hN : chartCount F = Fintype.card F + 1 :=
      chart_count_of_card_mod_ne_one hmod
    have hs : rho ^ 2 = 2 := by simpa only [hq2, Nat.cast_ofNat] using hrhosq
    have hscale : (30 * rho) ^ 3 = 54000 * rho := by
      calc
        (30 * rho) ^ 3 = 27000 * rho ^ 2 * rho := by ring
        _ = 54000 * rho := by rw [hs]; ring
    have hraw : 54000 * rho <= (30 * rho) ^ 3 := by rw [hscale]
    simpa [hN] using hraw

/-- Exact optimality is over the whole nonsquare field class, including q=2. -/
theorem nonsquare_field_uniform_cubic_constant_iff (C : Real) :
    (forall (F : Type) [Field F] [Fintype F],
      Not (IsSquare (Fintype.card F)) ->
      forall rho : Real, 0 < rho -> rho ^ 2 = (Fintype.card F : Real) ->
        C * rho <= (30 * rho -
          abs ((chartCount F : Real) - (Fintype.card F : Real) - 1)) ^ 3) <->
      C <= 54000 := by
  constructor
  . intro hall
    have hnsNat : Not (IsSquare (2 : Nat)) := by
      intro hs
      cases hs with
      | intro t ht =>
        cases t with
        | zero => norm_num at ht
        | succ t =>
          cases t with
          | zero => norm_num at ht
          | succ t =>
            nlinarith [Nat.zero_le t, Nat.zero_le (t * t)]
    let rho : Real := Real.sqrt 2
    have hrho : 0 < rho := Real.sqrt_pos.mpr (by norm_num)
    have hs : rho ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h := hall (ZMod 2) (by simpa using hnsNat) rho hrho (by simpa using hs)
    have hN : chartCount (ZMod 2) = 3 := by
      have ht := chart_count_of_card_mod_ne_one (F := ZMod 2) (by norm_num)
      simpa using ht
    norm_num [hN] at h
    have hscale : (30 * rho) ^ 3 = 54000 * rho := by
      calc
        (30 * rho) ^ 3 = 27000 * rho ^ 2 * rho := by ring
        _ = 54000 * rho := by rw [hs]; ring
    rw [hscale] at h
    by_contra hbad
    have hC : 54000 < C := lt_of_not_ge hbad
    have hm : 0 < (C - 54000) * rho := mul_pos (sub_pos.mpr hC) hrho
    nlinarith [h, hm]
  . intro hC F instF instFin hns rho hrho hrhosq
    exact le_trans (mul_le_mul_of_nonneg_right hC (le_of_lt hrho))
      (nonsquare_field_uniform_cubic_edge F hns rho hrho hrhosq)

end Metaplectic.G2Seven.Fermat
