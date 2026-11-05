/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenCyclotomicNonvanishing
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenJacobiAntiInvariant
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.JacobiPowerProfile

/-!
# Actual seventh-order Jacobi arithmetic

This adapter discharges norms and mixed-channel symmetries on actual
characters. It is an input to the complete signed beta estimate, not a
point-count bound or a new analytic estimate by itself.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace Metaplectic.G2Seven.Edge.Actual

private theorem jacobi_star {F : Type*} [Field F] [Fintype F]
    (chi psi : MulChar F Complex) :
    star (jacobiSum chi psi) =
      jacobiSum (Inv.inv chi) (Inv.inv psi) := by
  simp [jacobiSum, star_mul, MulChar.star_apply', mul_comm]

private theorem jacobi_norm {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p] (chi psi : MulChar F Complex)
    (hchi : Not (chi = 1)) (hpsi : Not (psi = 1))
    (hproduct : Not (chi * psi = 1)) :
    Complex.normSq (jacobiSum chi psi) = (Fintype.card F : Real) := by
  have hchar : Not (ringChar Complex = ringChar F) := by
    rw [ringChar.eq_zero, ringChar.eq F p]
    exact (Fact.out : Nat.Prime p).ne_zero.symm
  have hm := jacobiSum_mul_jacobiSum_inv hchar hchi hpsi hproduct
  rw [<- jacobi_star chi psi] at hm
  have hr := congrArg Complex.re hm
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.natCast_re] at hr
  rw [Complex.normSq_apply]
  nlinarith only [hr]

private theorem seventh_neg_one {F : Type*} [Field F] [Fintype F]
    (chi : MulChar F Complex) (hseven : chi ^ 7 = 1) :
    chi (-1) = 1 :=
  MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 7) hseven

private theorem mixed_symmetry {F : Type*} [Field F] [Fintype F]
    (chi : MulChar F Complex) (hseven : chi ^ 7 = 1) :
    jacobiSum (chi ^ 2) (chi ^ 4) = jacobiSum chi (chi ^ 2) := by
  have hneg : (chi ^ 2) (-1) = 1 := by
    rw [chi.pow_apply' (by decide : Not (2 = 0)) (-1),
      seventh_neg_one chi hseven, one_pow]
  have hmul : chi * chi ^ 2 = chi ^ 3 := by
    calc
      chi * chi ^ 2 = chi ^ 1 * chi ^ 2 := by rw [pow_one]
      _ = chi ^ (1 + 2) := (pow_add chi 1 2).symm
      _ = chi ^ 3 := rfl
  have hproduct : chi ^ 3 * chi ^ 4 = 1 := by
    rw [<- pow_add]
    exact hseven
  have hinv : Inv.inv (chi ^ 3) = chi ^ 4 := by
    calc
      Inv.inv (chi ^ 3) =
          Inv.inv (chi ^ 3) * (chi ^ 3 * chi ^ 4) := by
        rw [hproduct, mul_one]
      _ = chi ^ 4 := by rw [<- mul_assoc, inv_mul_cancel, one_mul]
  have hs := Metaplectic.JacobiPower.inverse_symmetry chi (chi ^ 2)
  rw [hneg, one_mul, hmul, hinv] at hs
  calc
    jacobiSum (chi ^ 2) (chi ^ 4) =
        jacobiSum (chi ^ 4) (chi ^ 2) := jacobiSum_comm _ _
    _ = jacobiSum chi (chi ^ 2) := hs.symm

private theorem diagonal_symmetry {F : Type*} [Field F] [Fintype F]
    (chi : MulChar F Complex) (hseven : chi ^ 7 = 1) :
    jacobiSum chi (chi ^ 3) = jacobiSum (chi ^ 3) (chi ^ 3) := by
  have hneg : (chi ^ 3) (-1) = 1 := by
    rw [chi.pow_apply' (by decide : Not (3 = 0)) (-1),
      seventh_neg_one chi hseven, one_pow]
  have hmul : chi * chi ^ 3 = chi ^ 4 := by
    calc
      chi * chi ^ 3 = chi ^ 1 * chi ^ 3 := by rw [pow_one]
      _ = chi ^ (1 + 3) := (pow_add chi 1 3).symm
      _ = chi ^ 4 := rfl
  have hproduct : chi ^ 4 * chi ^ 3 = 1 := by
    rw [<- pow_add]
    exact hseven
  have hinv : Inv.inv (chi ^ 4) = chi ^ 3 := by
    calc
      Inv.inv (chi ^ 4) =
          Inv.inv (chi ^ 4) * (chi ^ 4 * chi ^ 3) := by
        rw [hproduct, mul_one]
      _ = chi ^ 3 := by rw [<- mul_assoc, inv_mul_cancel, one_mul]
  have hs := Metaplectic.JacobiPower.inverse_symmetry chi (chi ^ 3)
  simpa only [hneg, one_mul, hmul, hinv] using hs

/-- The four same-field norms and both needed symmetries hold together. -/
theorem septic_jacobi_arithmetic {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p]
    (chi : MulChar F Complex) (horder : orderOf chi = 7) :
    (Complex.normSq (jacobiSum chi chi) = (Fintype.card F : Real)) /\
    (Complex.normSq (jacobiSum (chi ^ 2) (chi ^ 2)) =
      (Fintype.card F : Real)) /\
    (Complex.normSq (jacobiSum (chi ^ 3) (chi ^ 3)) =
      (Fintype.card F : Real)) /\
    (Complex.normSq (jacobiSum (chi ^ 4) (chi ^ 4)) =
      (Fintype.card F : Real)) /\
    (jacobiSum (chi ^ 2) (chi ^ 4) = jacobiSum chi (chi ^ 2)) /\
    (jacobiSum chi (chi ^ 3) = jacobiSum (chi ^ 3) (chi ^ 3)) /\
    chi (-1) = 1 := by
  have hseven : chi ^ 7 = 1 := by
    simpa only [horder] using pow_orderOf_eq_one chi
  have hnon : forall k : Nat, Not (Dvd.dvd 7 k) -> Not (chi ^ k = 1) := by
    intro k hk he
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [horder] at hd
    exact hk hd
  have hn : forall r : Nat, Not (Dvd.dvd 7 r) ->
      Not (Dvd.dvd 7 (r + r)) ->
      Complex.normSq (jacobiSum (chi ^ r) (chi ^ r)) =
        (Fintype.card F : Real) := by
    intro r hr hrr
    apply jacobi_norm p (chi ^ r) (chi ^ r) (hnon r hr) (hnon r hr)
    intro he
    apply hnon (r + r) hrr
    simpa only [pow_add] using he
  have h1 : Complex.normSq (jacobiSum chi chi) =
      (Fintype.card F : Real) := by
    simpa only [pow_one] using hn 1 (by decide) (by decide)
  exact And.intro h1
    (And.intro (hn 2 (by decide) (by decide))
      (And.intro (hn 3 (by decide) (by decide))
        (And.intro (hn 4 (by decide) (by decide))
          (And.intro (mixed_symmetry chi hseven)
            (And.intro (diagonal_symmetry chi hseven)
              (seventh_neg_one chi hseven))))))

/-- Actual prime-field Jacobi sums have the complete nonzero beta product. -/
theorem septic_actual_beta_nonzero {F : Type*} [Field F] [Fintype F]
    (p : Nat) [Fact p.Prime] [CharP F p] (hcard : Fintype.card F = p)
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
    rw [hcard] at hd
    have hn1 : Complex.normSq ((Finset.univ : Finset (Fin 7)).sum
        (fun j => (w j : Complex) * z ^ j.val)) = (p : Real) := by
      rw [<- h1]
      exact hd.1
    have hn2 : Complex.normSq ((Finset.univ : Finset (Fin 7)).sum
        (fun j => (w j : Complex) * (z ^ 2) ^ j.val)) = (p : Real) := by
      rw [<- h2]
      exact hd.2.1
    have hn4 : Complex.normSq ((Finset.univ : Finset (Fin 7)).sum
        (fun j => (w j : Complex) * (z ^ 4) ^ j.val)) = (p : Real) := by
      rw [<- h4]
      exact hd.2.2.2.1
    have hbeta := Metaplectic.G2Seven.Edge.septic_full_beta_nonzero
      p (Fact.out : Nat.Prime p) z hz w hn1 hn2 hn4
    intro hzero
    apply hbeta
    rw [<- h1, <- h3, <- h2, <- h6, <- h4, <- h5]
    exact hzero

/-- The actual mixed and diagonal Jacobi channels satisfy the beta product relation. -/
theorem septic_jacobi_product {F : Type*} [Field F] [Fintype F]
    (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive) :
    jacobiSum chi (chi ^ 2) * jacobiSum (chi ^ 3) (chi ^ 3) =
      jacobiSum chi chi * jacobiSum (chi ^ 2) (chi ^ 2) := by
  have hseven : chi ^ 7 = 1 := by
    simpa only [horder] using pow_orderOf_eq_one chi
  rw [<- diagonal_symmetry chi hseven]
  have hnon : forall k : Nat, Not (Dvd.dvd 7 k) -> Not (chi ^ k = 1) := by
    intro k hk he
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [horder] at hd
    exact hk hd
  have hprod (r s : Nat) (hrs : Not (Dvd.dvd 7 (r + s))) :
      Not (chi ^ r * chi ^ s = 1) := by
    rw [<- pow_add]
    exact hnon (r + s) hrs
  let g : Nat -> Complex := fun r => gaussSum (chi ^ r) psi
  have h11 : jacobiSum chi chi * g 2 = g 1 * g 1 := by
    have h := jacobiSum_mul_nontrivial (hprod 1 1 (by decide)) psi
    rw [<- pow_add] at h
    simpa only [g, pow_one, mul_comm] using h
  have h12 : jacobiSum chi (chi ^ 2) * g 3 = g 1 * g 2 := by
    have h := jacobiSum_mul_nontrivial (hprod 1 2 (by decide)) psi
    rw [<- pow_add] at h
    simpa only [g, pow_one, mul_comm] using h
  have h13 : jacobiSum chi (chi ^ 3) * g 4 = g 1 * g 3 := by
    have h := jacobiSum_mul_nontrivial (hprod 1 3 (by decide)) psi
    rw [<- pow_add] at h
    simpa only [g, pow_one, mul_comm] using h
  have h22 : jacobiSum (chi ^ 2) (chi ^ 2) * g 4 = g 2 * g 2 := by
    have h := jacobiSum_mul_nontrivial (hprod 2 2 (by decide)) psi
    rw [<- pow_add] at h
    simpa only [g, mul_comm] using h
  have hc : Not ((Fintype.card F : Complex) = 0) := by
    exact_mod_cast Fintype.card_ne_zero
  have hg3 : Not (g 3 = 0) :=
    gaussSum_ne_zero_of_nontrivial hc (hnon 3 (by decide)) hpsi
  have hg4 : Not (g 4 = 0) :=
    gaussSum_ne_zero_of_nontrivial hc (hnon 4 (by decide)) hpsi
  have hzero :
      (jacobiSum chi (chi ^ 2) * jacobiSum chi (chi ^ 3) -
        jacobiSum chi chi * jacobiSum (chi ^ 2) (chi ^ 2)) *
        (g 3 * g 4) = 0 := by
    calc
      _ = (jacobiSum chi (chi ^ 2) * g 3) *
            (jacobiSum chi (chi ^ 3) * g 4) -
          jacobiSum chi chi * g 3 *
            (jacobiSum (chi ^ 2) (chi ^ 2) * g 4) := by ring
      _ = (g 1 * g 2) * (g 1 * g 3) -
          jacobiSum chi chi * g 3 * (g 2 * g 2) := by
        rw [h12, h13, h22]
      _ = (g 1 * g 2) * (g 1 * g 3) -
          (jacobiSum chi chi * g 2) * (g 2 * g 3) := by ring
      _ = (g 1 * g 2) * (g 1 * g 3) -
          (g 1 * g 1) * (g 2 * g 3) := by rw [h11]
      _ = 0 := by ring
  cases mul_eq_zero.mp hzero with
  | inl hmain => exact sub_eq_zero.mp hmain
  | inr hzero => exact False.elim ((mul_ne_zero hg3 hg4) hzero)

end Metaplectic.G2Seven.Edge.Actual
