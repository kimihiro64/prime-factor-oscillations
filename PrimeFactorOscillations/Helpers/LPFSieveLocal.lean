/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import BombieriVinogradov.Proof.LargeSieve.CharacterReduction
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Exact local Fourier certificates for the LPF upper sieve -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def localSieveTest {q : Nat} (A : Finset (ZMod q)) (x : ZMod q) : Complex :=
  1 - if Membership.mem A x then (q : Complex) / (A.card : Complex) else 0

noncomputable def localSieveCoefficient {q : Nat} [NeZero q]
    (A : Finset (ZMod q)) (a : ZMod q) : Complex :=
  (q : Complex) ^ (-1 : Int) * ZMod.dft (localSieveTest A) a

private theorem sum_local_indicator {q : Nat} [NeZero q] {R : Type*} [Semiring R]
    (A : Finset (ZMod q)) (c : R) :
    Finset.sum Finset.univ (fun x => if Membership.mem A x then c else 0) =
      (A.card : R) * c := by
  classical
  have hFilter : Finset.univ.filter (fun x => Membership.mem A x) = A := by
    ext x
    simp
  have h := Finset.sum_filter (s := Finset.univ) (p := fun x => Membership.mem A x)
    (f := fun _ => c)
  simpa only [hFilter, Finset.sum_const, nsmul_eq_mul] using h.symm

theorem localSieveTest_eq_one {q : Nat} (A : Finset (ZMod q)) (x : ZMod q)
    (hx : Not (Membership.mem A x)) : localSieveTest A x = 1 := by
  simp only [localSieveTest, if_neg hx, sub_zero]

theorem sum_localSieveTest_eq_zero {q : Nat} [NeZero q] (A : Finset (ZMod q))
    (hA : 0 < A.card) : Finset.sum Finset.univ (localSieveTest A) = 0 := by
  have hCard : Not ((A.card : Complex) = 0) := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA)
  change Finset.sum Finset.univ (fun x : ZMod q =>
    (1 : Complex) - if Membership.mem A x then (q : Complex) / (A.card : Complex) else 0) = 0
  rw [Finset.sum_sub_distrib, sum_local_indicator, Finset.sum_const]
  simp only [Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  field_simp <;> ring

theorem localSieveCoefficient_zero {q : Nat} [NeZero q] (A : Finset (ZMod q))
    (hA : 0 < A.card) : localSieveCoefficient A 0 = 0 := by
  simp only [localSieveCoefficient, ZMod.dft_apply_zero, sum_localSieveTest_eq_zero A hA, mul_zero]

theorem localSieveTest_fourier {q : Nat} [NeZero q] (A : Finset (ZMod q)) (x : ZMod q)
    (hA : 0 < A.card) :
    Finset.sum (Finset.univ.erase (0 : ZMod q))
      (fun a => localSieveCoefficient A a * ZMod.stdAddChar (a * x)) = localSieveTest A x := by
  classical
  have hInv := congrFun (ZMod.dft.symm_apply_apply (localSieveTest A)) x
  rw [ZMod.invDFT_apply] at hInv
  simp only [smul_eq_mul, Finset.mul_sum] at hInv
  have hAll : Finset.sum Finset.univ
      (fun a => localSieveCoefficient A a * ZMod.stdAddChar (a * x)) = localSieveTest A x := by
    calc
      _ = Finset.sum Finset.univ (fun a =>
          (q : Complex) ^ (-1 : Int) * (ZMod.stdAddChar (a * x) * ZMod.dft (localSieveTest A) a)) := by
        apply Finset.sum_congr rfl
        intro a ha
        dsimp [localSieveCoefficient]
        ring
      _ = _ := by simpa only [zpow_neg_one] using hInv
  have hErase := Finset.sum_erase_add Finset.univ
    (fun a => localSieveCoefficient A a * ZMod.stdAddChar (a * x)) (Finset.mem_univ (0 : ZMod q))
  rw [localSieveCoefficient_zero A hA, zero_mul, add_zero] at hErase
  exact hErase.trans hAll

private theorem dft_energy_complex {q : Nat} [NeZero q] (f : ZMod q -> Complex) :
    Finset.sum Finset.univ (fun a => star (ZMod.dft f a) * ZMod.dft f a) =
      (q : Complex) * Finset.sum Finset.univ (fun x => star (f x) * f x) := by
  classical
  calc
    _ = Finset.sum Finset.univ (fun x => Finset.sum Finset.univ (fun y =>
        (star (f y) * f x) * Finset.sum Finset.univ (fun a =>
          star (ZMod.stdAddChar ((-y) * a)) * ZMod.stdAddChar ((-x) * a)))) := by
      simp only [ZMod.dft_apply, smul_eq_mul, star_sum, star_mul, Finset.sum_mul,
        Finset.mul_sum, neg_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = _ := by
      simp_rw [BombieriVinogradov.LargeSieve.stdAddCharOrthogonality]
      simp only [neg_inj, Finset.mul_sum, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      apply Finset.sum_congr rfl
      intro x hx
      ring

theorem dft_normSq_sum {q : Nat} [NeZero q] (f : ZMod q -> Complex) :
    Finset.sum Finset.univ (fun a => Complex.normSq (ZMod.dft f a)) =
      (q : Real) * Finset.sum Finset.univ (fun x => Complex.normSq (f x)) := by
  have h := dft_energy_complex f
  have h' : Finset.sum Finset.univ (fun a => (Complex.normSq (ZMod.dft f a) : Complex)) =
      (q : Complex) * Finset.sum Finset.univ (fun x => (Complex.normSq (f x) : Complex)) := by
    simpa only [Complex.normSq_eq_conj_mul_self, Complex.star_def] using h
  exact_mod_cast h'

theorem localSieveTest_normSq_sum {q : Nat} [NeZero q] (A : Finset (ZMod q))
    (hA : 0 < A.card) :
    Finset.sum Finset.univ (fun x => Complex.normSq (localSieveTest A x)) =
      (q : Real) * ((q : Real) - (A.card : Real)) / (A.card : Real) := by
  classical
  have hCard : Not ((A.card : Real) = 0) := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA)
  have hNorm : forall x : ZMod q, Complex.normSq (localSieveTest A x) =
      1 + if Membership.mem A x then (1 - (q : Real) / (A.card : Real)) ^ 2 - 1 else 0 := by
    intro x
    have hCast : localSieveTest A x =
        ((1 - if Membership.mem A x then (q : Real) / (A.card : Real) else 0 : Real) : Complex) := by
      by_cases hx : Membership.mem A x <;> simp [localSieveTest, hx]
    rw [hCast, Complex.normSq_ofReal]
    split_ifs <;> ring
  calc
    _ = Finset.sum Finset.univ (fun x : ZMod q =>
        (1 : Real) + if Membership.mem A x then (1 - (q : Real) / (A.card : Real)) ^ 2 - 1 else 0) :=
      Finset.sum_congr rfl (fun x _ => hNorm x)
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_local_indicator, Finset.sum_const]
      simp only [Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
      field_simp <;> ring

theorem localSieveCoefficient_normSq_sum {q : Nat} [NeZero q] (A : Finset (ZMod q))
    (hA : 0 < A.card) :
    Finset.sum Finset.univ (fun a => Complex.normSq (localSieveCoefficient A a)) =
      ((q : Real) - (A.card : Real)) / (A.card : Real) := by
  have hq : Not ((q : Real) = 0) := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hCard : Not ((A.card : Real) = 0) := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA)
  have hCoeff : forall a : ZMod q, Complex.normSq (localSieveCoefficient A a) =
      ((q : Real) ^ (-1 : Int)) ^ 2 * Complex.normSq (ZMod.dft (localSieveTest A) a) := by
    intro a
    simp [localSieveCoefficient, Complex.normSq_eq_norm_sq, norm_mul, mul_pow]
  calc
    _ = ((q : Real) ^ (-1 : Int)) ^ 2 *
        Finset.sum Finset.univ (fun a => Complex.normSq (ZMod.dft (localSieveTest A) a)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _ => hCoeff a)
    _ = _ := by
      rw [dft_normSq_sum, localSieveTest_normSq_sum A hA, zpow_neg_one]
      field_simp <;> ring

theorem localSieveCoefficient_nonzero_normSq_sum {q : Nat} [NeZero q] (A : Finset (ZMod q))
    (hA : 0 < A.card) :
    Finset.sum (Finset.univ.erase (0 : ZMod q)) (fun a => Complex.normSq (localSieveCoefficient A a)) =
      ((q : Real) - (A.card : Real)) / (A.card : Real) := by
  classical
  have h := Finset.sum_erase_add Finset.univ
    (fun a => Complex.normSq (localSieveCoefficient A a)) (Finset.mem_univ (0 : ZMod q))
  simp only [localSieveCoefficient_zero A hA, map_zero, add_zero] at h
  exact h.trans (localSieveCoefficient_normSq_sum A hA)

theorem localSieveCoefficient_eq_zero_of_not_isUnit {q : Nat} [NeZero q]
    (hq : Nat.Prime q) (A : Finset (ZMod q)) (hA : 0 < A.card) (a : ZMod q)
    (ha : Not (IsUnit a)) : localSieveCoefficient A a = 0 := by
  letI : Fact (Nat.Prime q) := Fact.mk hq
  have ha0 : a = 0 := by
    by_contra hne
    exact ha (isUnit_iff_ne_zero.mpr hne)
  rw [ha0]
  exact localSieveCoefficient_zero A hA

theorem localSieveCertificate {q : Nat} [NeZero q] (A : Finset (ZMod q))
    (hA : 0 < A.card) (x : ZMod q) (hx : Not (Membership.mem A x)) :
    Finset.sum (Finset.univ.erase (0 : ZMod q))
      (fun a => localSieveCoefficient A a * ZMod.stdAddChar (a * x)) = 1 := by
  rw [localSieveTest_fourier A x hA]
  exact localSieveTest_eq_one A x hx

noncomputable def localSieveSample {q : Nat} [NeZero q]
    (X : Finset Nat) (a : ZMod q) : Complex :=
  Finset.sum X (fun n => ZMod.stdAddChar (a * (n : ZMod q)))

/-- A prime's actual forbidden residues force primitive-frequency energy. -/
theorem localSieve_prime_energy_lower_bound {q : Nat} [NeZero q]
    (hq : Nat.Prime q) (A : Finset (ZMod q)) (hA : 0 < A.card) (hProper : A.card < q)
    (X : Finset Nat) (hAvoid : forall n, Membership.mem X n ->
      Not (Membership.mem A (n : ZMod q))) :
    ((A.card : Real) / ((q : Real) - (A.card : Real))) * (X.card : Real) ^ 2 <=
      Finset.sum (Finset.univ.filter (fun a : ZMod q => IsUnit a))
        (fun a => norm (localSieveSample X a) ^ 2) := by
  classical
  letI : Fact (Nat.Prime q) := Fact.mk hq
  let F : Finset (ZMod q) := Finset.univ.erase 0
  have hFreq : Finset.univ.filter (fun a : ZMod q => IsUnit a) = F := by
    ext a
    simp [F, isUnit_iff_ne_zero]
  rw [hFreq]
  have hMass : Finset.sum F (fun a => localSieveCoefficient A a * localSieveSample X a) =
      (X.card : Complex) := by
    simp only [localSieveSample, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = Finset.sum X (fun _ => (1 : Complex)) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact localSieveCertificate A hA (n : ZMod q) (hAvoid n hn)
      _ = _ := by simp
  have hTriangle : (X.card : Real) <= Finset.sum F
      (fun a => norm (localSieveCoefficient A a) * norm (localSieveSample X a)) := by
    have h := norm_sum_le F (fun a => localSieveCoefficient A a * localSieveSample X a)
    rw [hMass] at h
    simpa [norm_mul] using h
  have hNonneg : 0 <= Finset.sum F
      (fun a => norm (localSieveCoefficient A a) * norm (localSieveSample X a)) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hSquare : (X.card : Real) ^ 2 <= (Finset.sum F
      (fun a => norm (localSieveCoefficient A a) * norm (localSieveSample X a))) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hTriangle hTriangle (Nat.cast_nonneg X.card) hNonneg
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq F
    (fun a => norm (localSieveCoefficient A a)) (fun a => norm (localSieveSample X a))
  have hCoeff : Finset.sum F (fun a => norm (localSieveCoefficient A a) ^ 2) =
      ((q : Real) - (A.card : Real)) / (A.card : Real) := by
    simpa only [Complex.normSq_eq_norm_sq] using localSieveCoefficient_nonzero_normSq_sum A hA
  rw [hCoeff] at hCS
  have hBound := hSquare.trans hCS
  have hCard : (0 : Real) < (A.card : Real) := by exact_mod_cast hA
  have hQ : (A.card : Real) < (q : Real) := by exact_mod_cast hProper
  have hDiff : 0 < (q : Real) - (A.card : Real) := by linarith
  have h := mul_le_mul_of_nonneg_left hBound (div_pos hCard hDiff).le
  have hCancel : ((A.card : Real) / ((q : Real) - (A.card : Real))) *
      ((((q : Real) - (A.card : Real)) / (A.card : Real)) *
        Finset.sum F (fun a => norm (localSieveSample X a) ^ 2)) =
      Finset.sum F (fun a => norm (localSieveSample X a) ^ 2) := by field_simp
  rwa [hCancel] at h

end PrimeFactorOscillations.LPF
