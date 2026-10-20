/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileShiftRigidity
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.BernoulliProfileFinitePermutation
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.BernoulliProfileTailMatching

/-!
# Prime-coordinate reconstruction from canonical probability profiles

Probabilities are indexed by the increasing enumeration of primes.
Reciprocal affine asymptotics imply positivity, convergence to zero and
strict ordering on a tail. The proved profile matching and arithmetic shift
rigidity then recover the scale, intercept and every sufficiently late
prime-labelled coordinate without an RH hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

open Filter

private theorem reciprocal_tail_order (a : Nat -> Real) (nu c : Real)
    (hnu : 0 < nu)
    (hrecip : Tendsto (fun n : Nat =>
      1 / a n - (PrimeFactorUnimodality.primeAt n : Real) / nu - c)
        atTop (nhds 0)) :
    Tendsto a atTop (nhds 0) /\
      exists M, (forall n, M <= n -> 0 < a n) /\
        StrictAnti (fun n => a (M + n)) := by
  let r : Nat -> Real := fun n =>
    1 / a n - (PrimeFactorUnimodality.primeAt n : Real) / nu - c
  have hr : Tendsto r atTop (nhds 0) := hrecip
  have hpTop : Tendsto (fun n : Nat => (PrimeFactorUnimodality.primeAt n : Real))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      PrimeFactorUnimodality.primeAt_strictMono.tendsto_atTop
  have hscaled : Tendsto
      (fun n : Nat => (PrimeFactorUnimodality.primeAt n : Real) / nu) atTop atTop := by
    apply (hpTop.const_mul_atTop (one_div_pos.mpr hnu)).congr'
    exact Eventually.of_forall (fun _ => by ring)
  have hinverse : Tendsto (fun n => 1 / a n) atTop atTop := by
    apply ((hr.add_const c).add_atTop hscaled).congr'
    exact Eventually.of_forall (fun n => by dsimp [r]; ring)
  have ha0 : Tendsto a atTop (nhds 0) := by
    simpa only [Function.comp_def, one_div, inv_inv] using
      tendsto_inv_atTop_zero.comp hinverse
  have hpos : Filter.Eventually (fun n => 0 < a n) atTop := by
    filter_upwards [hinverse.eventually_gt_atTop 0] with n hn
    exact one_div_pos.mp hn
  let eps := (1 / nu) / 4
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hsmall : Filter.Eventually (fun n => -eps < r n /\ r n < eps) atTop :=
    (hr.eventually (lt_mem_nhds (by linarith : -eps < 0))).and
      (hr.eventually (gt_mem_nhds heps))
  have hex := eventually_atTop.mp (hpos.and hsmall)
  let M := Classical.choose hex
  have hM := Classical.choose_spec hex
  refine And.intro ha0 (Exists.intro M (And.intro (fun n hn => (hM n hn).1) ?_))
  intro i j hij
  have hi := hM (M + i) (by omega)
  have hj := hM (M + j) (by omega)
  have hprime : PrimeFactorUnimodality.primeAt (M + i) <
      PrimeFactorUnimodality.primeAt (M + j) :=
    PrimeFactorUnimodality.primeAt_strictMono (Nat.add_lt_add_left hij M)
  have hgap : (PrimeFactorUnimodality.primeAt (M + i) : Real) + 1 <=
      (PrimeFactorUnimodality.primeAt (M + j) : Real) := by
    exact_mod_cast Nat.succ_le_of_lt hprime
  have hscaledGap : (PrimeFactorUnimodality.primeAt (M + i) : Real) / nu + 1 / nu <=
      (PrimeFactorUnimodality.primeAt (M + j) : Real) / nu := by
    simpa only [add_div] using div_le_div_of_nonneg_right hgap hnu.le
  have hrecipLt : 1 / a (M + i) < 1 / a (M + j) := by
    have hnuInv : 0 < 1 / nu := one_div_pos.mpr hnu
    dsimp [r, eps] at hi hj
    linarith only [hi.2.2, hj.2.1, hscaledGap, hnuInv]
  by_contra hn
  have hle : a (M + i) <= a (M + j) := le_of_not_gt hn
  exact not_lt_of_ge (one_div_le_one_div_of_le hi.1 hle) hrecipLt

/-- Equal profiles with reciprocal affine prime asymptotics have identical labelled tails. -/
theorem prime_coordinates_rigid
    (a b : Nat -> Real) (nu1 nu2 c1 c2 : Real)
    (ha : forall n, 0 <= a n) (ha1 : forall n, a n <= 1)
    (hb : forall n, 0 <= b n) (hb1 : forall n, b n <= 1)
    (hsa : Summable (fun n => (a n) ^ 2)) (hsb : Summable (fun n => (b n) ^ 2))
    (hnu1 : 0 < nu1) (hnu2 : 0 < nu2)
    (hrecipA : Tendsto (fun n : Nat =>
      1 / a n - (PrimeFactorUnimodality.primeAt n : Real) / nu1 - c1)
        atTop (nhds 0))
    (hrecipB : Tendsto (fun n : Nat =>
      1 / b n - (PrimeFactorUnimodality.primeAt n : Real) / nu2 - c2)
        atTop (nhds 0))
    (hprofile : Complex.canonicalBernoulliProfile a =
      Complex.canonicalBernoulliProfile b) :
    nu1 = nu2 /\ c1 = c2 /\ Filter.Eventually (fun n => a n = b n) atTop := by
  have horderA := reciprocal_tail_order a nu1 c1 hnu1 hrecipA
  have horderB := reciprocal_tail_order b nu2 c2 hnu2 hrecipB
  let Ma := Classical.choose horderA.2
  let Mb := Classical.choose horderB.2
  have hMa := Classical.choose_spec horderA.2
  have hMb := Classical.choose_spec horderB.2
  have htail := Complex.exists_tail_shift_of_canonicalBernoulliProfile_eq
    a b Ma Mb ha ha1 hb hb1 hsa hsb hprofile horderA.1 hMa.1 hMb.1 hMa.2 hMb.2
  let A := Classical.choose htail
  let B := Classical.choose (Classical.choose_spec htail)
  have hAB := Classical.choose_spec (Classical.choose_spec htail)
  change Ma <= A /\ Mb <= B /\ forall n, a (A + n) = b (B + n) at hAB
  have hmatch : forall n, a (n + A) = b (n + B) := by
    intro n
    simpa only [Nat.add_comm] using hAB.2.2 n
  have hparams := profile_parameters_eq_of_tail_match
    a b A B nu1 nu2 c1 c2 hnu1 hnu2 hmatch hrecipA hrecipB
  refine And.intro hparams.1 (And.intro hparams.2.1 ?_)
  apply eventually_atTop.mpr
  refine Exists.intro A ?_
  intro n hn
  simpa only [<- hparams.2.2, Nat.sub_add_cancel hn] using hmatch (n - A)

/-- Complete profile classification, including every finite zero and unit probability. -/
theorem prime_profile_eq_iff_finite_permutation
    (a b : Nat -> Real) (nu1 nu2 c1 c2 : Real)
    (ha : forall n, 0 <= a n) (ha1 : forall n, a n <= 1)
    (hb : forall n, 0 <= b n) (hb1 : forall n, b n <= 1)
    (hsa : Summable (fun n => (a n) ^ 2)) (hsb : Summable (fun n => (b n) ^ 2))
    (hnu1 : 0 < nu1) (hnu2 : 0 < nu2)
    (hrecipA : Tendsto (fun n : Nat =>
      1 / a n - (PrimeFactorUnimodality.primeAt n : Real) / nu1 - c1)
        atTop (nhds 0))
    (hrecipB : Tendsto (fun n : Nat =>
      1 / b n - (PrimeFactorUnimodality.primeAt n : Real) / nu2 - c2)
        atTop (nhds 0)) :
    Complex.canonicalBernoulliProfile a = Complex.canonicalBernoulliProfile b <->
      nu1 = nu2 /\ c1 = c2 /\ exists N, exists e : Equiv.Perm Nat,
        (forall n, N <= n -> e n = n) /\ forall n, a n = b (e n) := by
  constructor
  . intro hprofile
    have hrigid := prime_coordinates_rigid a b nu1 nu2 c1 c2
      ha ha1 hb hb1 hsa hsb hnu1 hnu2 hrecipA hrecipB hprofile
    have hex := eventually_atTop.mp hrigid.2.2
    let N := Classical.choose hex
    have htail : forall n, N <= n -> a n = b n := Classical.choose_spec hex
    exact And.intro hrigid.1 (And.intro hrigid.2.1
      (Exists.intro N (Complex.exists_bounded_perm_of_canonicalBernoulliProfile_eq
        a b N ha ha1 hb hb1 hsa hsb hprofile htail)))
  . intro h
    have hN := Classical.choose_spec h.2.2
    let e := Classical.choose hN
    have he : forall n, a n = b (e n) := (Classical.choose_spec hN).2
    funext z
    calc
      Complex.canonicalBernoulliProfile a z =
          Complex.canonicalBernoulliProfile (fun n => b (e n)) z :=
        congrArg (fun f : Nat -> Real => Complex.canonicalBernoulliProfile f z) (funext he)
      _ = Complex.canonicalBernoulliProfile b z :=
        Complex.canonicalBernoulliProfile_comp_equiv b e z

/-- Equality accumulating at a finite point gives the full prime-labelled classification. -/
theorem prime_coordinates_rigid_of_frequently_eq
    (a b : Nat -> Real) (nu1 nu2 c1 c2 : Real)
    (ha : forall n, 0 <= a n) (ha1 : forall n, a n <= 1)
    (hb : forall n, 0 <= b n) (hb1 : forall n, b n <= 1)
    (hsa : Summable (fun n => (a n) ^ 2)) (hsb : Summable (fun n => (b n) ^ 2))
    (hnu1 : 0 < nu1) (hnu2 : 0 < nu2)
    (hrecipA : Tendsto (fun n : Nat =>
      1 / a n - (PrimeFactorUnimodality.primeAt n : Real) / nu1 - c1)
        atTop (nhds 0))
    (hrecipB : Tendsto (fun n : Nat =>
      1 / b n - (PrimeFactorUnimodality.primeAt n : Real) / nu2 - c2)
        atTop (nhds 0))
    (z0 : Complex)
    (heq : Filter.Frequently (fun z => Complex.canonicalBernoulliProfile a z =
      Complex.canonicalBernoulliProfile b z) (nhdsWithin z0 (Set.singleton z0).compl)) :
    nu1 = nu2 /\ c1 = c2 /\ exists N, exists e : Equiv.Perm Nat,
      (forall n, N <= n -> e n = n) /\ forall n, a n = b (e n) := by
  apply (prime_profile_eq_iff_finite_permutation a b nu1 nu2 c1 c2
    ha ha1 hb hb1 hsa hsb hnu1 hnu2 hrecipA hrecipB).mp
  exact Complex.canonicalBernoulliProfile_eq_of_frequently_eq
    a b ha ha1 hb hb1 hsa hsb z0 heq

end PrimeFactorOscillations.PrimeProfileRigidity
