/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfilePrimeRatio

/-!
# Arithmetic asymptotics of matching prime-indexed profile tails

Here a(n) and b(n) are probabilities at the n-th prime, not functions of a
divisor cutoff. Exact matching after fixed index shifts and reciprocal
asymptotics determine the leading scale. Once the scale agrees, the shifted
prime difference has the specified finite limit. These are consumers of the
proved profile-to-tail matching theorem, not new zero-free estimates.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter

private theorem tendsto_nat_add_right (a : Nat) :
    Tendsto (fun n : Nat => n + a) atTop atTop := by
  apply StrictMono.tendsto_atTop
  intro i j hij
  exact Nat.add_lt_add_right hij a

/-- A fixed tail match forces equality of reciprocal leading scales. -/
theorem profile_scale_eq_of_tail_match
    (a b : Nat -> Real) (A B : Nat) (nu1 nu2 c1 c2 : Real)
    (hnu1 : 0 < nu1) (hnu2 : 0 < nu2)
    (hmatch : forall n, a (n + A) = b (n + B))
    (ha : Tendsto (fun n : Nat =>
      1 / a n - (PrimeFactorUnimodality.primeAt n : Real) / nu1 - c1)
        atTop (nhds 0))
    (hb : Tendsto (fun n : Nat =>
      1 / b n - (PrimeFactorUnimodality.primeAt n : Real) / nu2 - c2)
        atTop (nhds 0)) :
    nu1 = nu2 := by
  let X : Nat -> Real := fun n => (PrimeFactorUnimodality.primeAt (n + A) : Real)
  let Y : Nat -> Real := fun n => (PrimeFactorUnimodality.primeAt (n + B) : Real)
  let ra : Nat -> Real := fun n => 1 / a (n + A) - X n / nu1 - c1
  let rb : Nat -> Real := fun n => 1 / b (n + B) - Y n / nu2 - c2
  have hra : Tendsto ra atTop (nhds 0) := ha.comp (tendsto_nat_add_right A)
  have hrb : Tendsto rb atTop (nhds 0) := hb.comp (tendsto_nat_add_right B)
  have hX : Tendsto X atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (PrimeFactorUnimodality.primeAt_strictMono.tendsto_atTop.comp
        (tendsto_nat_add_right A))
  have hinv : Tendsto (fun n => 1 / X n) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hX
  have hratio : Tendsto (fun n => Y n / X n) atTop (nhds 1) :=
    tendsto_primeAt_shift_div_shift A B
  have hsignal : Tendsto (fun n =>
      1 / nu1 - (Y n / X n) / nu2 +
        (c1 - c2) * (1 / X n) + (ra n - rb n) * (1 / X n))
      atTop (nhds (1 / nu1 - 1 / nu2)) := by
    simpa only [Pi.sub_def, Pi.add_def, Pi.mul_def, Pi.div_def,
      sub_self, mul_zero, add_zero] using
      ((tendsto_const_nhds.sub (hratio.div_const nu2)).add
        (tendsto_const_nhds.mul hinv)).add ((hra.sub hrb).mul hinv)
  have hzero : Filter.Eventually (fun n =>
      1 / nu1 - (Y n / X n) / nu2 +
        (c1 - c2) * (1 / X n) + (ra n - rb n) * (1 / X n) = 0) atTop := by
    apply Eventually.of_forall
    intro n
    have hX0 : Not (X n = 0) := by
      dsimp [X]
      exact_mod_cast (PrimeFactorUnimodality.prime_primeAt (n + A)).ne_zero
    have hnu10 := ne_of_gt hnu1
    have hnu20 := ne_of_gt hnu2
    dsimp [ra, rb]
    rw [hmatch n]
    field_simp
    ring
  have hconstant : Tendsto (fun _ : Nat => (0 : Real)) atTop
      (nhds (1 / nu1 - 1 / nu2)) := hsignal.congr' hzero
  have hlim : 1 / nu1 - 1 / nu2 = 0 :=
    tendsto_nhds_unique hconstant tendsto_const_nhds
  have heq : 1 / nu1 = 1 / nu2 := sub_eq_zero.mp hlim
  exact inv_injective (by simpa only [one_div] using heq)

/-- The remaining additive prime shift converges to the reciprocal intercept gap. -/
theorem tendsto_prime_shift_difference_of_tail_match
    (a b : Nat -> Real) (A B : Nat) (nu c1 c2 : Real) (hnu : 0 < nu)
    (hmatch : forall n, a (n + A) = b (n + B))
    (ha : Tendsto (fun n : Nat =>
      1 / a n - (PrimeFactorUnimodality.primeAt n : Real) / nu - c1)
        atTop (nhds 0))
    (hb : Tendsto (fun n : Nat =>
      1 / b n - (PrimeFactorUnimodality.primeAt n : Real) / nu - c2)
        atTop (nhds 0)) :
    Tendsto (fun n : Nat =>
      (PrimeFactorUnimodality.primeAt (n + B) : Real) -
        (PrimeFactorUnimodality.primeAt (n + A) : Real))
      atTop (nhds (nu * (c1 - c2))) := by
  let ra : Nat -> Real := fun n =>
    1 / a (n + A) - (PrimeFactorUnimodality.primeAt (n + A) : Real) / nu - c1
  let rb : Nat -> Real := fun n =>
    1 / b (n + B) - (PrimeFactorUnimodality.primeAt (n + B) : Real) / nu - c2
  have hra : Tendsto ra atTop (nhds 0) := ha.comp (tendsto_nat_add_right A)
  have hrb : Tendsto rb atTop (nhds 0) := hb.comp (tendsto_nat_add_right B)
  have hlim : Tendsto (fun n => nu * (ra n - rb n + c1 - c2))
      atTop (nhds (nu * (c1 - c2))) := by
    simpa only [Pi.sub_def, Pi.add_def, Pi.mul_def, sub_self, zero_add] using
      tendsto_const_nhds.mul (((hra.sub hrb).add_const c1).sub_const c2)
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  have hnu0 := ne_of_gt hnu
  dsimp [ra, rb]
  rw [hmatch n]
  field_simp
  ring

end PrimeFactorOscillations
