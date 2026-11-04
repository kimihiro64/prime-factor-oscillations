/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenPaleyStability

/-!
# Arithmetic Frobenius transfer of sharp sevenfold source stability

Frobenius acts on the source finite field. The complex target has
characteristic zero. Additive-character invariance is an explicit hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Curve

variable {F : Type*} [Field F] [Fintype F]

/-- Source-field Frobenius invariance for the actual complex Gauss sum. -/
theorem source_gauss_frobenius (p : Nat) [Fact (Nat.Prime p)] [CharP F p]
    (chi : MulChar F Complex) (psi : AddChar F Complex)
    (hfixed : forall x : F, psi (x ^ p) = psi x) :
    gaussSum (chi ^ p) psi = gaussSum chi psi := by
  have hp0 : Not (p = 0) := Nat.Prime.ne_zero (Fact.out : Nat.Prime p)
  unfold gaussSum
  apply Fintype.sum_equiv (frobeniusEquiv F p).toEquiv
  intro x
  rw [MulChar.pow_apply' chi hp0]
  change chi x ^ p * psi x = chi (x ^ p) * psi (x ^ p)
  rw [hfixed x, map_pow]

/-- The common positive real normalization gives a genuine unit-circle point. -/
theorem normalized_gauss_unit (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho : Real) (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : 0 < rho) (hrho2 : rho ^ 2 = (Fintype.card F : Real)) :
    (normalizedGauss chi psi (rho : Complex) 1).re ^ 2 +
      (normalizedGauss chi psi (rho : Complex) 1).im ^ 2 = 1 := by
  have hchi : Not (chi = 1) := by
    intro he
    rw [he, orderOf_one] at horder
    norm_num at horder
  have hc : Not ((rho : Complex) = 0) := by exact_mod_cast (ne_of_gt hrho)
  have hc2 : (rho : Complex) ^ 2 = (Fintype.card F : Complex) := by
    exact_mod_cast hrho2
  have hm := gaussSum_mul_gaussSum_eq_card hchi hpsi
  rw [<- star_gaussSum_eq chi psi] at hm
  let g := normalizedGauss chi psi (rho : Complex) 1
  have hunit : g * star g = 1 := by
    calc
      _ = (gaussSum chi psi * star (gaussSum chi psi)) / (rho : Complex) ^ 2 := by
        dsimp [g, normalizedGauss]
        simp only [pow_one]
        simp [Complex.star_def]
        ring
      _ = 1 := by
        rw [hm, <- hc2]
        exact div_self (pow_ne_zero 2 hc)
  have he := congrArg Complex.re hunit
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.one_re] at he
  change g.re ^ 2 + g.im ^ 2 = 1
  nlinarith only [he]

private theorem order_seven_period (chi : MulChar F Complex) (horder : orderOf chi = 7)
    (n : Nat) : chi ^ n = chi ^ (n % 7) := by
  have hseven : chi ^ 7 = 1 := by simpa only [horder] using pow_orderOf_eq_one chi
  calc
    chi ^ n = chi ^ (n % 7 + 7 * (n / 7)) := by rw [Nat.mod_add_div]
    _ = chi ^ (n % 7) := by rw [pow_add, pow_mul, hseven, one_pow, mul_one]

/-- The two order-three residue classes force the actual Gauss Paley sector. -/
theorem gauss_paley_sector (p : Nat) [Fact (Nat.Prime p)] [CharP F p]
    (chi : MulChar F Complex) (psi : AddChar F Complex) (rho : Complex)
    (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (hrho2 : rho ^ 2 = (Fintype.card F : Complex))
    (hfixed : forall x : F, psi (x ^ p) = psi x)
    (hmod : p % 7 = 2 \/ p % 7 = 4) :
    normalizedGauss chi psi rho 2 = normalizedGauss chi psi rho 1 /\
    normalizedGauss chi psi rho 3 = (normalizedGauss chi psi rho 1) ^ (-1 : Int) := by
  let G := normalizedGauss chi psi rho
  have hper (n : Nat) : G n = G (n % 7) := by
    dsimp [G, normalizedGauss]
    rw [order_seven_period chi horder n]
  have hf (n : Nat) : G (n * p) = G n := by
    dsimp [G, normalizedGauss]
    rw [pow_mul]
    rw [source_gauss_frobenius p (chi ^ n) psi hfixed]
  have h1 : G (p % 7) = G 1 := by
    rw [<- hper p]
    simpa only [one_mul] using hf 1
  have h2 : G ((2 * p) % 7) = G 2 := by rw [<- hper (2 * p)]; exact hf 2
  have htwo : G 2 = G 1 /\ G 4 = G 1 := by
    cases hmod with
    | inl hp =>
      rw [hp] at h1
      norm_num [Nat.mul_mod, hp] at h2
      exact And.intro h1 (h2.trans h1)
    | inr hp =>
      rw [hp] at h1
      norm_num [Nat.mul_mod, hp] at h2
      exact And.intro h2.symm h1
  have h4 : G 4 = 1 / G 3 :=
    normalized_gauss_complement chi psi rho horder hpsi hrho hrho2 2
  rw [htwo.2] at h4
  have h3 : G 3 = (G 1) ^ (-1 : Int) := by
    rw [zpow_neg_one]
    simpa only [one_div, inv_inv] using (congrArg Inv.inv h4).symm
  exact And.intro htwo.1 h3

/-- The sharp bound controls the actual signed normalized Fermat point count. -/
theorem fermat_paley_stability (p : Nat) [Fact (Nat.Prime p)] [CharP F p]
    (chi : MulChar F Complex) (psi : AddChar F Complex) (rho : Real)
    (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : 0 < rho) (hrho2 : rho ^ 2 = (Fintype.card F : Real))
    (hfixed : forall x : F, psi (x ^ p) = psi x)
    (hmod : p % 7 = 2 \/ p % 7 = 4) :
    let g := normalizedGauss chi psi (rho : Complex) 1
    (6 + 3 * (Real.sqrt 2 / 2)) *
      min (6 - 6 * g.re) (6 + g.re - Real.sqrt 7 * |g.im|) - 30 <=
      (((Fintype.card F : Complex) + 1 - (Fermat.chartCount F : Complex)) /
        (rho : Complex)).re := by
  have hc : Not ((rho : Complex) = 0) := by exact_mod_cast (ne_of_gt hrho)
  have hc2 : (rho : Complex) ^ 2 = (Fintype.card F : Complex) := by
    exact_mod_cast hrho2
  have hs := gauss_paley_sector p chi psi (rho : Complex) horder hpsi hc hc2 hfixed hmod
  have hunit := normalized_gauss_unit chi psi rho horder hpsi hrho hrho2
  have hb := Paley.cubic_source_stability _ hunit
  have he := Fermat.fermat_trace_phases chi psi (rho : Complex) horder hpsi hc hc2
  rw [hs.1, hs.2] at he
  have hre := congrArg Complex.re he
  simp only [Complex.neg_re] at hre
  dsimp
  linarith only [hb, hre]

end Metaplectic.G2Seven.Curve
