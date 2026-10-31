/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeAgreement

/-!
# The half-mass native-profile reconstruction threshold is optimal

The actual prime pairs (5,7) and (5,13) have identical native weights
exactly on the character class chi_91=1 above the finite exceptional set.
Their retained reciprocal mass approaches one half of the full band mass.
The witness is existential; no consecutive-pair or moving-height sharpness
is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer

def nativeSharpRetentionSet (U : Nat) : Finset Nat := by
  classical
  exact ((Finset.Ico (preciseCore U + 1)
    (preciseCore U * preciseCore U + 1)).filter Nat.Prime).filter
      (fun p => And (13 < p) ((numeratorKernel (91 : Int) p).re = 1))

theorem native_sharp_pair_match_iff (p : Nat) [Fact (Nat.Prime p)] (hp13 : 13 < p) :
    (integerNativeWeight 5 2 p = integerNativeWeight 5 8 p) <->
      (numeratorKernel (91 : Int) p).re = 1 := by
  have hmod (N : Nat) (hN : 0 < N) (hNp : N < p) :
      Not (((N : Int) : ZMod p) = 0) := by
    have hn : Not ((N : ZMod p) = 0) := by
      intro hz
      exact (Nat.not_dvd_of_pos_of_lt hN hNp) ((ZMod.natCast_eq_zero_iff N p).mp hz)
    simpa only [Int.cast_natCast] using hn
  have hs2 := real_kernel_square_of_nonzero (2 : Int) p (by omega)
    (hmod 2 (by decide) (by omega))
  have h4 : (numeratorKernel (4 : Int) p).re = 1 := by
    have he : (4 : Int) = 2 * 2 := by norm_num
    rw [he, real_kernel_mul, <- pow_two, hs2]
  have hA : (numeratorKernel (-40 : Int) p).re =
      (numeratorKernel (-10 : Int) p).re := by
    have he : (-40 : Int) = 4 * (-10) := by norm_num
    rw [he, real_kernel_mul, h4, one_mul]
  have h104 : (numeratorKernel (104 : Int) p).re =
      (numeratorKernel (26 : Int) p).re := by
    have he : (104 : Int) = 4 * 26 := by norm_num
    rw [he, real_kernel_mul, h4, one_mul]
  have h14 : Not (((14 : Int) : ZMod p) = 0) := by
    have he : (14 : Int) = 2 * 7 := by norm_num
    rw [he, Int.cast_mul]
    exact mul_ne_zero (hmod 2 (by decide) (by omega)) (hmod 7 (by decide) (by omega))
  have h26 : Not (((26 : Int) : ZMod p) = 0) := by
    have he : (26 : Int) = 2 * 13 := by norm_num
    rw [he, Int.cast_mul]
    exact mul_ne_zero (hmod 2 (by decide) (by omega)) (hmod 13 (by decide) (by omega))
  have hs26 := real_kernel_square_of_nonzero (26 : Int) p (by omega) h26
  have hproduct : (numeratorKernel (14 : Int) p).re * (numeratorKernel (26 : Int) p).re =
      (numeratorKernel (91 : Int) p).re := by
    have he : (14 : Int) * 26 = 4 * 91 := by norm_num
    rw [<- real_kernel_mul, he, real_kernel_mul, h4, one_mul]
  have hN := native_weight_large_prime_trace 5 2 p (by decide) (by omega) (by omega)
  have hM := native_weight_large_prime_trace 5 8 p (by decide) (by omega) (by omega)
  change ((p : Real) - 3) * integerNativeWeight 5 2 p - ((p : Real) - 1) =
    (numeratorKernel (-10 : Int) p).re + (numeratorKernel (14 : Int) p).re at hN
  change ((p : Real) - 3) * integerNativeWeight 5 8 p - ((p : Real) - 1) =
    (numeratorKernel (-40 : Int) p).re + (numeratorKernel (104 : Int) p).re at hM
  rw [hA, h104] at hM
  have hdiff : ((p : Real) - 3) *
      (integerNativeWeight 5 2 p - integerNativeWeight 5 8 p) =
        (numeratorKernel (14 : Int) p).re - (numeratorKernel (26 : Int) p).re := by
    nlinarith only [hN, hM]
  have hpR : (13 : Real) < p := by exact_mod_cast hp13
  have hden : Not ((p : Real) - 3 = 0) := by linarith only [hpR]
  constructor
  . intro hw
    have heq : (numeratorKernel (14 : Int) p).re = (numeratorKernel (26 : Int) p).re := by
      rw [hw, sub_self, mul_zero] at hdiff
      linarith only [hdiff]
    rw [<- hproduct, heq, <- pow_two, hs26]
  . intro hc
    have heq : (numeratorKernel (14 : Int) p).re = (numeratorKernel (26 : Int) p).re := by
      calc
        _ = (numeratorKernel (14 : Int) p).re *
            ((numeratorKernel (26 : Int) p).re * (numeratorKernel (26 : Int) p).re) := by
          rw [<- pow_two, hs26, mul_one]
        _ = ((numeratorKernel (14 : Int) p).re * (numeratorKernel (26 : Int) p).re) *
            (numeratorKernel (26 : Int) p).re := by ring
        _ = _ := by rw [hproduct, hc, one_mul]
    have hz : ((p : Real) - 3) *
        (integerNativeWeight 5 2 p - integerNativeWeight 5 8 p) = 0 := by
      rw [hdiff, heq, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hden)

theorem native_sharp_character_square (p : Nat) [Fact (Nat.Prime p)] (hp13 : 13 < p) :
    (numeratorKernel (91 : Int) p).re ^ 2 = 1 := by
  have hmod (N : Nat) (hN : 0 < N) (hNp : N < p) :
      Not (((N : Int) : ZMod p) = 0) := by
    have hn : Not ((N : ZMod p) = 0) := by
      intro hz
      exact (Nat.not_dvd_of_pos_of_lt hN hNp) ((ZMod.natCast_eq_zero_iff N p).mp hz)
    simpa only [Int.cast_natCast] using hn
  have h91 : Not (((91 : Int) : ZMod p) = 0) := by
    have he : (91 : Int) = 7 * 13 := by norm_num
    rw [he, Int.cast_mul]
    exact mul_ne_zero (hmod 7 (by decide) (by omega)) (hmod 13 (by decide) (by omega))
  exact real_kernel_square_of_nonzero (91 : Int) p (by omega) h91

theorem native_sharp_agreement_identity (Y X : Nat) (hY : 13 < Y) :
    nativeAgreementMass 5 2 5 8 Y X =
      (reciprocalBand Y X + primeCorrelation (91 : Int) Y X) / 2 := by
  classical
  calc
    nativeAgreementMass 5 2 5 8 Y X =
        ((Finset.Ico Y X).filter Nat.Prime).sum (fun p =>
          ((1 / (p : Real)) * (1 + (numeratorKernel (91 : Int) p).re)) / 2) := by
      unfold nativeAgreementMass
      apply Finset.sum_congr rfl
      intro p hp
      have hdata := Finset.mem_filter.mp hp
      have hband := Finset.mem_Ico.mp hdata.1
      have : Fact (Nat.Prime p) := Fact.mk hdata.2
      have hp13 : 13 < p := by omega
      have hi := native_sharp_pair_match_iff p hp13
      by_cases hw : integerNativeWeight 5 2 p = integerNativeWeight 5 8 p
      . have hc := hi.mp hw
        rw [ite_eq_left hw, hc]
        ring
      . have hc : Not ((numeratorKernel (91 : Int) p).re = 1) := by
          intro he
          exact hw (hi.mpr he)
        have hs := native_sharp_character_square p hp13
        have hf : ((numeratorKernel (91 : Int) p).re - 1) *
            ((numeratorKernel (91 : Int) p).re + 1) = 0 := by nlinarith only [hs]
        have hleft : Not ((numeratorKernel (91 : Int) p).re - 1 = 0) := by
          intro he
          apply hc
          linarith only [he]
        have hplus := (mul_eq_zero.mp hf).resolve_left hleft
        have hneg : (numeratorKernel (91 : Int) p).re = -1 := by linarith only [hplus]
        rw [ite_eq_right hw, hneg]
        ring
    _ = _ := by
      unfold reciprocalBand primeCorrelation
      apply (eq_div_iff (by norm_num : Not ((2 : Real) = 0))).mpr
      rw [Finset.sum_mul]
      calc
        _ = ((Finset.Ico Y X).filter Nat.Prime).sum (fun p =>
            1 / (p : Real) + (1 / (p : Real)) * (numeratorKernel (91 : Int) p).re) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ = _ := Finset.sum_add_distrib

theorem native_sharp_agreement_approx (eta : Real) (heta : 0 < eta) :
    Filter.Eventually (fun U : Nat =>
      abs (nativeAgreementMass 5 2 5 8 (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) -
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) / 2) < eta)
      atTop := by
  choose B hB hbound using exists_eventual_fixed_prime_correlation_bound 13 7
    (by decide) (by decide) (by decide) (by decide) (91 : Int) (Or.inl (by norm_num))
  have herr := (relative_error_tendsto_zero B).eventually
    (Iio_mem_nhds (show (0 : Real) < 2 * eta by linarith only [heta]))
  filter_upwards [hbound, herr, precise_core_tendsto_atTop.eventually_ge_atTop 14]
    with U hb he hcore
  have hid := native_sharp_agreement_identity (preciseCore U + 1)
    (preciseCore U * preciseCore U + 1) (by omega)
  have hdiff : nativeAgreementMass 5 2 5 8 (preciseCore U + 1)
      (preciseCore U * preciseCore U + 1) -
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) / 2 =
      primeCorrelation (91 : Int) (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) / 2 := by rw [hid]; ring
  rw [hdiff, abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
  linarith only [hb, he]

theorem native_sharp_retention_data :
    And (forall U p, Membership.mem (nativeSharpRetentionSet U) p ->
      Membership.mem ((Finset.Ico (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1)).filter Nat.Prime) p)
      (forall U p, Membership.mem (nativeSharpRetentionSet U) p ->
        integerNativeWeight 5 2 p = integerNativeWeight 5 8 p) := by
  constructor
  . intro U p hp
    exact (Finset.mem_filter.mp hp).1
  . intro U p hp
    have hd := Finset.mem_filter.mp hp
    have hprime := (Finset.mem_filter.mp hd.1).2
    have : Fact (Nat.Prime p) := Fact.mk hprime
    exact (native_sharp_pair_match_iff p hd.2.1).mpr hd.2.2

theorem native_sharp_retention_mass_approx (eta : Real) (heta : 0 < eta) :
    Filter.Eventually (fun U : Nat =>
      abs ((nativeSharpRetentionSet U).sum (fun p => 1 / (p : Real)) -
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) / 2) < eta)
      atTop := by
  classical
  filter_upwards [native_sharp_agreement_approx eta heta,
    precise_core_tendsto_atTop.eventually_ge_atTop 14] with U he hcore
  have hid : (nativeSharpRetentionSet U).sum (fun p => 1 / (p : Real)) =
      nativeAgreementMass 5 2 5 8 (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) := by
    unfold nativeSharpRetentionSet nativeAgreementMass
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    have hd := Finset.mem_filter.mp hp
    have hband := Finset.mem_Ico.mp hd.1
    have : Fact (Nat.Prime p) := Fact.mk hd.2
    have hp13 : 13 < p := by omega
    have hi := native_sharp_pair_match_iff p hp13
    by_cases hw : integerNativeWeight 5 2 p = integerNativeWeight 5 8 p
    . have hc : And (13 < p) ((numeratorKernel (91 : Int) p).re = 1) :=
        And.intro hp13 (hi.mp hw)
      rw [ite_eq_left hc, ite_eq_left hw]
    . have hc : Not (And (13 < p) ((numeratorKernel (91 : Int) p).re = 1)) := by
        intro hz
        exact hw (hi.mpr hz.2)
      rw [ite_eq_right hc, ite_eq_right hw]
  rw [hid]
  exact he

theorem native_sharp_retention_above_subhalf (c : Real) (hc : c < 1 / 2) :
    Filter.Eventually (fun U : Nat =>
      c * reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) <
        (nativeSharpRetentionSet U).sum (fun p => 1 / (p : Real))) atTop := by
  have hgap : 0 < 1 / 2 - c := by linarith only [hc]
  have heta : 0 < (1 / 2 - c) * Real.log 2 / 4 := by positivity
  have hm := precise_core_tendsto_atTop.eventually eventually_reciprocal_square_band_positive
  filter_upwards [native_sharp_retention_mass_approx
    ((1 / 2 - c) * Real.log 2 / 4) heta, hm] with U he hmass
  have hlo := (abs_lt.mp he).1
  have hscale := mul_le_mul_of_nonneg_left hmass hgap.le
  nlinarith only [hlo, hscale, heta]

theorem native_half_retention_is_sharp :
    exists n h m k : Nat, And (Nat.Prime n) (And (Nat.Prime (n + h))
      (And (Nat.Prime m) (And (Nat.Prime (m + k)) (And (0 < h) (And (0 < k)
        (And (Not (And (n = m) (h = k)))
          (exists S : Nat -> Finset Nat,
            And (forall U p, Membership.mem (S U) p ->
              Membership.mem ((Finset.Ico (preciseCore U + 1)
                (preciseCore U * preciseCore U + 1)).filter Nat.Prime) p)
              (And (forall U p, Membership.mem (S U) p ->
                integerNativeWeight n h p = integerNativeWeight m k p)
                (forall c : Real, c < 1 / 2 -> Filter.Eventually (fun U : Nat =>
                  c * reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) <
                    (S U).sum (fun p => 1 / (p : Real))) atTop))))))))) := by
  refine Exists.intro 5 (Exists.intro 2 (Exists.intro 5 (Exists.intro 8 ?_)))
  refine And.intro (by decide) (And.intro (by decide)
    (And.intro (by decide) (And.intro (by decide)
      (And.intro (by decide) (And.intro (by decide) (And.intro (by norm_num) ?_))))))
  exact Exists.intro nativeSharpRetentionSet (And.intro native_sharp_retention_data.1
    (And.intro native_sharp_retention_data.2 native_sharp_retention_above_subhalf))

end PrimeFactorOscillations.FiniteFieldIntegerSignature
