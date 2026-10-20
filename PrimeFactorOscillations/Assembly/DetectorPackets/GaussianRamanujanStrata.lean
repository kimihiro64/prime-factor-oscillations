/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianCoprimePoisson

/-!
# GaussianRamanujanStrata

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Exact shared-prime Ramanujan weight and quartic phase descent

Use S as the finite prime-ideal support of the squarefree common factor.
Only its shared-prime product enters the absolute Ramanujan bound.
The missing-prime signs and the full quartic phase are retained exactly.
The analytic quadratic-sieve application is separate.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianRamanujanStrata

open GaussianMobiusDivisors GaussianIdealPoisson
open scoped Classical

def localWeight (p : NonzeroIdeal) (K : Ideal G) : Complex :=
  if Dvd.dvd p.val K then (((Ideal.absNorm p.val : Real) - 1 : Real) : Complex)
  else -1

def weight (S : Finset NonzeroIdeal) (K : Ideal G) : Complex :=
  S.prod fun p => localWeight p K

def sharedFactor (S : Finset NonzeroIdeal) (K : Ideal G) : Complex :=
  S.prod fun p => if Dvd.dvd p.val K then
    (((Ideal.absNorm p.val : Real) - 1 : Real) : Complex) else 1

def missingSign (S : Finset NonzeroIdeal) (K : Ideal G) : Complex :=
  S.prod fun p => if Dvd.dvd p.val K then 1 else -1

def sharedTotient (S : Finset NonzeroIdeal) (K : Ideal G) : Real :=
  S.prod fun p => if Dvd.dvd p.val K then (Ideal.absNorm p.val : Real) - 1 else 1

def sharedIdeal (S : Finset NonzeroIdeal) (K : Ideal G) : Ideal G :=
  S.prod fun p => if Dvd.dvd p.val K then p.val else 1

def unsharedIdeal (S : Finset NonzeroIdeal) (K : Ideal G) : Ideal G :=
  S.prod fun p => if Dvd.dvd p.val K then 1 else p.val

theorem norm_ge_one (p : NonzeroIdeal) : (1 : Real) <= Ideal.absNorm p.val := by
  have hn : Not (Ideal.absNorm p.val = 0) := by
    intro h
    exact p.property (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn

theorem ideal_partition (S : Finset NonzeroIdeal) (K : Ideal G) :
    sharedIdeal S K * unsharedIdeal S K = S.prod (fun p => p.val) := by
  unfold sharedIdeal unsharedIdeal
  rw [<- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases h : Dvd.dvd p.val K <;> simp [h]

theorem weight_factorization (S : Finset NonzeroIdeal) (K : Ideal G) :
    weight S K = sharedFactor S K * missingSign S K := by
  unfold weight sharedFactor missingSign
  rw [<- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases h : Dvd.dvd p.val K <;> simp [localWeight, h]

theorem missingSign_norm (S : Finset NonzeroIdeal) (K : Ideal G) :
    norm (missingSign S K) = 1 := by
  unfold missingSign
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro p hp
  by_cases h : Dvd.dvd p.val K <;> simp [h]

theorem weight_norm (S : Finset NonzeroIdeal) (K : Ideal G) :
    norm (weight S K) = sharedTotient S K := by
  rw [weight_factorization, norm_mul, missingSign_norm, mul_one]
  unfold sharedFactor sharedTotient
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases h : Dvd.dvd p.val K
  . simp only [h, ite_true]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact sub_nonneg.mpr (norm_ge_one p)
  . simp [h]

theorem sharedIdeal_norm (S : Finset NonzeroIdeal) (K : Ideal G) :
    (Ideal.absNorm (sharedIdeal S K) : Real) =
      S.prod (fun p => if Dvd.dvd p.val K then (Ideal.absNorm p.val : Real) else 1) := by
  unfold sharedIdeal
  rw [map_prod, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases h : Dvd.dvd p.val K <;> simp [h]

theorem weight_norm_le_shared (S : Finset NonzeroIdeal) (K : Ideal G) :
    norm (weight S K) <= (Ideal.absNorm (sharedIdeal S K) : Real) := by
  rw [weight_norm, sharedIdeal_norm]
  unfold sharedTotient
  let f : NonzeroIdeal -> Real := fun p =>
    if Dvd.dvd p.val K then (Ideal.absNorm p.val : Real) - 1 else 1
  let g : NonzeroIdeal -> Real := fun p =>
    if Dvd.dvd p.val K then (Ideal.absNorm p.val : Real) else 1
  have hlocal (p : NonzeroIdeal) : 0 <= f p /\ f p <= g p /\ 0 <= g p := by
    dsimp only [f, g]
    by_cases h : Dvd.dvd p.val K
    . simp only [h, ite_true]
      have hn := norm_ge_one p
      exact And.intro (sub_nonneg.mpr hn)
        (And.intro (sub_le_self _ zero_le_one) (zero_le_one.trans hn))
    . simp [h]
  have hprod (T : Finset NonzeroIdeal) : 0 <= T.prod f /\ T.prod f <= T.prod g := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert p T hp ih =>
      simp only [Finset.prod_insert hp]
      exact And.intro (mul_nonneg (hlocal p).1 ih.1)
        (mul_le_mul (hlocal p).2.1 ih.2 ih.1 (hlocal p).2.2)
  exact (hprod S).2

theorem quartic_inverse (z : Complex) (hz : z ^ 4 = 1) (hu : z * star z = 1) :
    star z = z ^ 3 := by
  have hne : Not (z = 0) := by
    intro h
    rw [h, zero_mul] at hu
    exact zero_ne_one hu
  have hm : z * (star z - z ^ 3) = 0 := by
    rw [mul_sub, hu]
    have hp : z * z ^ 3 = z ^ 4 := by ring
    rw [hp, hz, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hne)

theorem phase_descent (e b k : Complex) (he : e * star e = 1)
    (hb : b ^ 4 = 1) (hbu : b * star b = 1) :
    (e * b) * star (e * k) = star (b ^ 3 * k) := by
  have hb3 : star (b ^ 3) = b := by
    rw [star_pow, quartic_inverse b hb hbu]
    calc
      (b ^ 3) ^ 3 = b * (b ^ 4) ^ 2 := by ring
      _ = b := by rw [hb]; ring
  rw [star_mul, star_mul, hb3]
  calc
    (e * b) * (star k * star e) = (e * star e) * b * star k := by ring
    _ = star k * b := by rw [he]; ring

end PrimeFactorOscillations.GaussianRamanujanStrata

