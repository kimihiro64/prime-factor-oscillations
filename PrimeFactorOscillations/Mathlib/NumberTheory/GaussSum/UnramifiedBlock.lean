/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.ZMod.Basic
import PrimeFactorOscillations.Mathlib.Analysis.Complex.RankOneBlock
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.QuadraticEnergy

/-!
# The complete tame unramified two-support block

The finite matrix retains both the Gauss permutation and the geometric
antidiagonal term, including their common entry. These are the two supports
in Szpruch, On Shahidi local coefficients matrix, arXiv:1609.08122v4,
Proposition 4.17. The p-adic identification, basis changes, spectral
parameters and global reflection are not asserted here.

If q * normSq z >= 1, norm z <= 1, and norm z ^ m <= 1 / q, its squared
operator norm is at most four, uniformly in the finite-field size q.
Principal characters are included. For m=5 the parameter range contains
the annulus q^(-1/2) <= norm z <= q^(-1/5).
-/

set_option autoImplicit false
set_option Elab.async false

namespace MulChar

variable {F : Type*} [Field F] [Fintype F]

theorem gaussSum_principal_eq_neg_one (psi : AddChar F Complex)
    (hpsi : Not (psi = 1)) : gaussSum (1 : MulChar F Complex) psi = -1 := by
  classical
  have hterm (x : F) : (1 : MulChar F Complex) x * psi x =
      psi x - if x = 0 then 1 else 0 := by
    by_cases hx : x = 0
    . subst x; simp
    . simp [MulChar.one_apply, hx]
  unfold gaussSum
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, AddChar.sum_eq_zero_of_ne_one hpsi]
  simp

theorem normSq_gaussSum_le_card (chi : MulChar F Complex)
    (psi : AddChar F Complex) (hpsi : Not (psi = 1)) :
    Complex.normSq (gaussSum chi psi) <= (Fintype.card F : Real) := by
  by_cases hc : chi = 1
  . rw [hc, gaussSum_principal_eq_neg_one psi hpsi]
    norm_num [Complex.normSq_apply]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  . exact (normSq_gaussSum_eq_card chi hc psi hpsi).le

private theorem normSq_add_le_twice (a b : Complex) :
    Complex.normSq (a + b) <= 2 * (Complex.normSq a + Complex.normSq b) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (a.re - b.re), sq_nonneg (a.im - b.im)]

private theorem energy_two_permutations {I : Type*} [Fintype I]
    (p t : Equiv.Perm I) (a b v : I -> Complex)
    (ha : forall i, Complex.normSq (a i) <= 1)
    (hb : forall i, Complex.normSq (b i) <= 1) :
    Finset.univ.sum (fun i => Complex.normSq (a i * v (p i) + b i * v (t i))) <=
      4 * Finset.univ.sum (fun i => Complex.normSq (v i)) := by
  have hp : Finset.univ.sum (fun i => Complex.normSq (v (p i))) =
      Finset.univ.sum (fun i => Complex.normSq (v i)) :=
    Fintype.sum_equiv p _ _ (fun _ => rfl)
  have ht : Finset.univ.sum (fun i => Complex.normSq (v (t i))) =
      Finset.univ.sum (fun i => Complex.normSq (v i)) :=
    Fintype.sum_equiv t _ _ (fun _ => rfl)
  calc
    _ <= Finset.univ.sum (fun i =>
        2 * (Complex.normSq (v (p i)) + Complex.normSq (v (t i)))) := by
      apply Finset.sum_le_sum
      intro i _
      have hh := normSq_add_le_twice (a i * v (p i)) (b i * v (t i))
      rw [map_mul, map_mul] at hh
      have hpa := mul_le_mul_of_nonneg_right (ha i) (Complex.normSq_nonneg (v (p i)))
      have htb := mul_le_mul_of_nonneg_right (hb i) (Complex.normSq_nonneg (v (t i)))
      linarith
    _ = _ := by rw [<- Finset.mul_sum, Finset.sum_add_distrib, hp, ht]; ring

/-- Both terms of the complete local block remain, including their intersection. -/
noncomputable def twoPermutationGaussBlock {I : Type*} [DecidableEq I]
    (chi : I -> MulChar F Complex) (psi : AddChar F Complex)
    (p t : Equiv.Perm I) (e : I -> Nat) (m : Nat) (z : Complex) (i j : I) : Complex :=
  (if j = p i then gaussSum (chi i) psi / ((Fintype.card F : Complex) * z) else 0) +
  (if j = t i then ((1 - (Fintype.card F : Real) ^ (-1 : Int) : Real) : Complex) *
    z ^ e i / (1 - z ^ m) else 0)

/-- A uniform full-block estimate on the conductor annulus. All characters,
including principal entries, and both intersecting permutation supports remain. -/
theorem sum_normSq_twoPermutationGaussBlock_le {I : Type*} [Fintype I] [DecidableEq I]
    (chi : I -> MulChar F Complex) (psi : AddChar F Complex) (hpsi : Not (psi = 1))
    (p t : Equiv.Perm I) (e : I -> Nat) (m : Nat) (z : Complex)
    (hz : norm z <= 1)
    (hlower : 1 <= (Fintype.card F : Real) * Complex.normSq z)
    (hupper : norm z ^ m <= (Fintype.card F : Real) ^ (-1 : Int)) (v : I -> Complex) :
    Finset.univ.sum (fun i => Complex.normSq
      (Finset.univ.sum (fun j => twoPermutationGaussBlock chi psi p t e m z i j * v j))) <=
      4 * Finset.univ.sum (fun i => Complex.normSq (v i)) := by
  let q : Real := Fintype.card F
  have hq : 1 < q := by
    change 1 < (Fintype.card F : Real)
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hnum : 0 < 1 - q ^ (-1 : Int) := by
    rw [zpow_neg_one, inv_eq_one_div]
    exact sub_pos.mpr ((div_lt_one hq0).mpr hq)
  have hden : 1 - q ^ (-1 : Int) <= norm (1 - z ^ m) := by
    have hrev := norm_sub_norm_le (1 : Complex) (z ^ m)
    rw [norm_one, norm_pow] at hrev
    exact le_trans (sub_le_sub_left hupper 1) hrev
  have hdenpos : 0 < norm (1 - z ^ m) := lt_of_lt_of_le hnum hden
  have hb0 : norm (((1 - q ^ (-1 : Int) : Real) : Complex) / (1 - z ^ m)) <= 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnum]
    exact (div_le_one hdenpos).mpr hden
  have hzpow (n : Nat) : norm z ^ n <= 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      exact le_trans (mul_le_mul_of_nonneg_right ih (norm_nonneg z)) (by simpa using hz)
  have ha (i : I) : Complex.normSq
      (gaussSum (chi i) psi / ((Fintype.card F : Complex) * z)) <= 1 := by
    have hbase : q <= q ^ 2 * Complex.normSq z := by
      have hh := mul_le_mul_of_nonneg_left hlower hq0.le
      change q * 1 <= q * (q * Complex.normSq z) at hh
      nlinarith
    have hdenq : 0 < q ^ 2 * Complex.normSq z := lt_of_lt_of_le hq0 hbase
    rw [Complex.normSq_div, map_mul, Complex.normSq_natCast]
    simpa only [pow_two] using
      (div_le_one hdenq).mpr (le_trans (normSq_gaussSum_le_card (chi i) psi hpsi) hbase)
  have hb (i : I) : Complex.normSq
      (((1 - q ^ (-1 : Int) : Real) : Complex) * z ^ e i / (1 - z ^ m)) <= 1 := by
    have hr : norm (((1 - q ^ (-1 : Int) : Real) : Complex) * z ^ e i /
        (1 - z ^ m)) <= 1 := by
      rw [mul_div_right_comm, norm_mul, norm_pow]
      exact le_trans (mul_le_mul_of_nonneg_right hb0 (pow_nonneg (norm_nonneg z) _))
        (by simpa using hzpow (e i))
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (((1 - q ^ (-1 : Int) : Real) : Complex) * z ^ e i / (1 - z ^ m))]
  have hrow (i : I) : Finset.univ.sum (fun j =>
      twoPermutationGaussBlock chi psi p t e m z i j * v j) =
      gaussSum (chi i) psi / ((Fintype.card F : Complex) * z) * v (p i) +
      (((1 - q ^ (-1 : Int) : Real) : Complex) * z ^ e i / (1 - z ^ m)) * v (t i) := by
    simp [twoPermutationGaussBlock, add_mul, Finset.sum_add_distrib, ite_mul, q]
  simp_rw [hrow]
  exact energy_two_permutations p t _ _ v ha hb

/-- The full five-by-five two-support block. The row where the supports
intersect retains both summands, including the principal Gauss sum. -/
theorem sum_normSq_quintic_unramified_block_le
    (kappa : MulChar F Complex) (psi : AddChar F Complex) (hpsi : Not (psi = 1))
    (z : Complex) (hz : norm z <= 1)
    (hlower : 1 <= (Fintype.card F : Real) * Complex.normSq z)
    (hupper : norm z ^ 5 <= (Fintype.card F : Real) ^ (-1 : Int))
    (v : ZMod 5 -> Complex) :
    Finset.univ.sum (fun i : ZMod 5 => Complex.normSq
      (Finset.univ.sum (fun j : ZMod 5 =>
        ((if j = i - 1 then
          gaussSum (kappa ^ (2 * i - 1).val) psi /
            ((Fintype.card F : Complex) * z) else 0) +
        (if j = -i then
          ((1 - (Fintype.card F : Real) ^ (-1 : Int) : Real) : Complex) *
            z ^ (-2 * i).val / (1 - z ^ 5) else 0)) * v j))) <=
      4 * Finset.univ.sum (fun i => Complex.normSq (v i)) := by
  let p : Equiv.Perm (ZMod 5) := Equiv.addRight (-1)
  let t : Equiv.Perm (ZMod 5) := Equiv.neg (ZMod 5)
  have h := sum_normSq_twoPermutationGaussBlock_le
    (fun i : ZMod 5 => kappa ^ (2 * i - 1).val) psi hpsi p t
    (fun i => (-2 * i).val) 5 z hz hlower hupper v
  simpa only [twoPermutationGaussBlock, p, t, Equiv.coe_addRight,
    Equiv.neg_apply, sub_eq_add_neg] using h

end MulChar
