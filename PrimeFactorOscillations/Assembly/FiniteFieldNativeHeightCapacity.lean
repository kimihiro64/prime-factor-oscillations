/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeAsymptoticPacking
import PrimeFactorOscillations.Assembly.FiniteFieldNativeFlatEnergy
import PrimeFactorOscillations.Helpers.PrimeCountingLocation

/-!
# Optimal height order and sharp physical stability of native codebooks

The cardinality upper bound applies to every actual prime-pair codebook.
The constructed lower codebook is fixed before its independent field-scale
limit. This is not a uniform simultaneous limit in height and field scale.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

open Filter

private theorem prime_pair_height_card_le (Y : Nat) (V : Finset (Prod Nat Nat))
    (hV : forall a : Prod Nat Nat, Membership.mem V a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ a.1 + a.2 <= Y) :
    V.card <= (Nat.primeCounting Y) ^ 2 := by
  classical
  let f : Prod Nat Nat -> Prod Nat Nat := fun a => Prod.mk a.1 (a.1 + a.2)
  have hmem : forall a, Membership.mem V a ->
      Membership.mem ((Nat.primesLE Y).product (Nat.primesLE Y)) (f a) := by
    intro a ha
    have h := hV a ha
    change Membership.mem ((Nat.primesLE Y).product (Nat.primesLE Y))
      (Prod.mk a.1 (a.1 + a.2))
    apply Finset.mem_product.mpr
    exact And.intro
      (Nat.mem_primesLE.mpr (And.intro (by omega) h.1))
      (Nat.mem_primesLE.mpr (And.intro h.2.2 h.2.1))
  have hinj : Set.InjOn f (V : Set (Prod Nat Nat)) := by
    intro a ha b hb he
    have hfirst : a.1 = b.1 := by
      have hp := congrArg (fun z : Prod Nat Nat => z.1) he
      exact hp
    have hsecond : a.1 + a.2 = b.1 + b.2 := by
      have hp := congrArg (fun z : Prod Nat Nat => z.2) he
      exact hp
    exact Prod.ext hfirst (by omega)
  have hc := Finset.card_le_card_of_injOn f hmem hinj
  have hp : ((Nat.primesLE Y).product (Nat.primesLE Y)).card =
      (Nat.primesLE Y).card * (Nat.primesLE Y).card :=
    Finset.card_product (Nat.primesLE Y) (Nat.primesLE Y)
  rw [hp, Nat.primesLE_card_eq_primeCounting] at hc
  simpa only [pow_two] using hc

/-- Every actual prime-pair codebook has at most the optimal log-squared order. -/
theorem eventually_prime_pair_height_card_upper :
    Filter.Eventually (fun Y : Nat =>
      forall V : Finset (Prod Nat Nat),
        (forall a : Prod Nat Nat, Membership.mem V a ->
          Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ a.1 + a.2 <= Y) ->
        (V.card : Real) <=
          4 * (Y : Real) ^ 2 / Real.log (Y : Real) ^ 2) atTop := by
  have hp := PrimeFactorOscillations.eventually_thetaPrefix_and_primeCounting_bounds
    (1 : Real) (by norm_num)
  filter_upwards [hp] with Y hY V hV
  have hpi : (Nat.primeCounting Y : Real) <=
      2 * (Y : Real) / Real.log (Y : Real) := by
    simpa only [one_add_one_eq_two] using hY.2.2
  have hc : (V.card : Real) <= (Nat.primeCounting Y : Real) ^ 2 := by
    exact_mod_cast prime_pair_height_card_le Y V hV
  have hs := mul_self_le_mul_self (Nat.cast_nonneg (Nat.primeCounting Y)) hpi
  have heq : (2 * (Y : Real) / Real.log (Y : Real)) *
      (2 * (Y : Real) / Real.log (Y : Real)) =
        4 * (Y : Real) ^ 2 / Real.log (Y : Real) ^ 2 := by ring
  rw [heq] at hs
  exact hc.trans (by simpa only [pow_two] using hs)

/-- Height-optimal actual native codebooks have exact physical energy and sharp
five-eighths stability. No simultaneous growing-codebook limit is asserted. -/
theorem eventually_native_prime_pair_height_capacity :
    Filter.Eventually (fun Y : Nat =>
      (forall V : Finset (Prod Nat Nat),
        (forall a : Prod Nat Nat, Membership.mem V a ->
          Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ a.1 + a.2 <= Y) ->
        (V.card : Real) <= 4 * (Y : Real) ^ 2 / Real.log (Y : Real) ^ 2) /\
      exists M : Finset (Prod Nat Nat),
        (forall a : Prod Nat Nat, Membership.mem M a ->
          Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\
            a.2 < a.1 /\ a.1 + a.2 <= Y) /\
        (Y : Real) ^ 2 / (4096 * Real.log (Y : Real) ^ 2) <= (M.card : Real) /\
        2 <= M.card /\
        (forall a : Prod Nat Nat, Membership.mem M a ->
          forall b : Prod Nat Nat, Membership.mem M b -> Not (a = b) ->
            nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8) /\
        let n : M -> Nat := fun a => a.val.1
        let h : M -> Nat := fun a => a.val.2
        (forall c : M -> Real,
          Tendsto (nativeAgreementMassForm n h c) atTop
            (nhds ((3 / 8 : Real) * (Finset.univ.sum c) ^ 2 +
              (5 / 8 : Real) * Finset.univ.sum (fun i => (c i) ^ 2)))) /\
        (forall kappa : Real,
          (forall c : M -> Real,
            kappa * Finset.univ.sum (fun i => (c i) ^ 2) <=
              nativeAgreementForm n h c) <-> kappa <= 5 / 8)) atTop := by
  classical
  have hg := Real.eventually_const_mul_log_natpow_le_rpow
    (8192 : Real) 2 (show (0 : Real) < 2 by norm_num)
  filter_upwards [eventually_prime_pair_height_card_upper,
    eventually_native_prime_pair_height_packing, hg] with Y hUpper hPack hGrow
  choose M hGeometry hLower hFlat using hPack.2.2
  have hLogPos : 0 < Real.log (Y : Real) := lt_of_lt_of_le zero_lt_one hPack.2.1
  have hden : 0 < 4096 * Real.log (Y : Real) ^ 2 := by positivity
  have hGrowNat : 8192 * Real.log (Y : Real) ^ 2 <= (Y : Real) ^ 2 := by
    norm_num [Real.rpow_natCast] at hGrow
    exact hGrow
  have hTwoReal : (2 : Real) <= (M.card : Real) := by
    have ht : (2 : Real) <= (Y : Real) ^ 2 /
        (4096 * Real.log (Y : Real) ^ 2) := by
      have ht : (2 : Real) * (4096 * Real.log (Y : Real) ^ 2) <=
          (Y : Real) ^ 2 := by nlinarith only [hGrowNat]
      have hd := div_nonneg (sub_nonneg.mpr ht) hden.le
      have he : ((Y : Real) ^ 2 - 2 * (4096 * Real.log (Y : Real) ^ 2)) /
          (4096 * Real.log (Y : Real) ^ 2) =
            (Y : Real) ^ 2 / (4096 * Real.log (Y : Real) ^ 2) - 2 := by
        field_simp
      rw [he] at hd
      linarith only [hd]
    exact ht.trans hLower
  have hTwo : 2 <= M.card := by exact_mod_cast hTwoReal
  refine And.intro hUpper (Exists.intro M
    (And.intro hGeometry (And.intro hLower (And.intro hTwo (And.intro hFlat ?_)))))
  let n : M -> Nat := fun a => a.val.1
  let h : M -> Nat := fun a => a.val.2
  have hn (a : M) : Nat.Prime (n a) := (hGeometry a.val a.property).1
  have hnh (a : M) : Nat.Prime (n a + h a) := (hGeometry a.val a.property).2.1
  have hh (a : M) : 0 < h a := (hGeometry a.val a.property).2.2.1
  have hinj : Function.Injective (fun a : M => Prod.mk (n a) (h a)) := by
    intro a b he
    apply Subtype.ext
    exact he
  have hflat (a b : M) (hab : Not (a = b)) :
      nativeAgreementRate (n a) (h a) (n b) (h b) = 3 / 8 := by
    apply hFlat a.val a.property b.val b.property
    intro he
    exact hab (Subtype.ext he)
  refine And.intro ?_ ?_
  . intro c
    exact native_flat_agreement_mass_form_tendsto n h hn hnh hh hinj hflat c
  . intro kappa
    apply Iff.intro
    . intro hBound
      choose a ha b hb hab using Finset.one_lt_card.mp (show 1 < M.card by omega)
      let i : M := Subtype.mk a ha
      let j : M := Subtype.mk b hb
      have hij : Not (i = j) := by
        intro he
        have hv := congrArg (fun v : M => v.val) he
        exact hab hv
      exact native_flat_agreement_stability_optimal n h hflat i j hij kappa hBound
    . intro hk c
      have hs : 0 <= Finset.univ.sum (fun i : M => (c i) ^ 2) :=
        Finset.sum_nonneg (fun i hi => sq_nonneg (c i))
      exact (mul_le_mul_of_nonneg_right hk hs).trans
        (native_flat_agreement_stability n h hflat c)

end PrimeFactorOscillations.FiniteFieldIntegerSignature
