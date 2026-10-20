/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleCarrierSum

/-!
# PowerSampleExceptionalProduct

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

set_option maxHeartbeats 1800000

noncomputable section
namespace OAI.SevenEighths.ProbePowerGauss
open scoped Classical BigOperators
open ActualEisensteinCubic IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem exceptional_prime_product_small_power (eps : Real) (heps : 0 < eps) :
    exists B : Real, 0 < B /\
      forall (I : Ideal O), Not (I = 0) ->
      forall (S : Finset (Ideal O)),
        (forall P, Membership.mem S P -> Membership.mem (primeSupport I) P) ->
      forall (F : Ideal O -> Complex),
        (forall P, Membership.mem S P -> norm (F P) <= 3) ->
        norm (S.prod F) <= B * (Ideal.absNorm I : Real) ^ eps := by
  choose C hC hbound using SquarefreeDivisorBound.prime_support_subsets_bound
    (eps / 2) (by linarith)
  refine Exists.intro (C ^ 2) (And.intro (sq_pos_of_pos hC) ?_)
  intro I hI S hS F hF
  have hNI : 0 < (Ideal.absNorm I : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have htwo := hbound I hI
  have hthree : (3 : Real) ^ (primeSupport I).card <=
      C ^ 2 * (Ideal.absNorm I : Real) ^ eps := by
    calc
      _ <= ((2 : Real) * 2) ^ (primeSupport I).card := by
        gcongr <;> norm_num
      _ = (2 : Real) ^ (primeSupport I).card *
          (2 : Real) ^ (primeSupport I).card := by rw [mul_pow]
      _ <= (C * (Ideal.absNorm I : Real) ^ (eps / 2)) *
          (C * (Ideal.absNorm I : Real) ^ (eps / 2)) :=
        mul_le_mul htwo htwo (by positivity) (by positivity)
      _ = C ^ 2 * ((Ideal.absNorm I : Real) ^ (eps / 2) *
          (Ideal.absNorm I : Real) ^ (eps / 2)) := by ring
      _ = C ^ 2 * (Ideal.absNorm I : Real) ^ (eps / 2 + eps / 2) := by
        rw [Real.rpow_add hNI]
      _ = _ := by congr 2; ring
  have hlocal : norm (S.prod F) <= (3 : Real) ^ S.card := by
    rw [norm_prod]
    calc
      _ <= S.prod (fun _ => (3 : Real)) := by
        gcongr with P hP
        exact hF P hP
      _ = _ := by rw [Finset.prod_const]
  have hcard : S.card <= (primeSupport I).card := Finset.card_le_card hS
  have hpow : (3 : Real) ^ S.card <= (3 : Real) ^ (primeSupport I).card := by
    gcongr <;> norm_num
  exact hlocal.trans (hpow.trans hthree)

end OAI.SevenEighths.ProbePowerGauss
