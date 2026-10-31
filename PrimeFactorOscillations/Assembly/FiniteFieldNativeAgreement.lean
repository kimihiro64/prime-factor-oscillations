/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeGlobalReturn

/-!
# Reconstruction from adaptive native-profile observations above half mass

The actual integer pairs are fixed before the independent field scale grows.
A complete signed endpoint-product correlation bounds the entire agreement
mass. Arbitrary adaptive subsets above half mass then retain the inverse.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer FiniteFieldIntegerGapWindows PrimeProfileRigidity

def nativeAgreementMass (n h m k Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun p =>
    if integerNativeWeight n h p = integerNativeWeight m k p then 1 / (p : Real) else 0)

theorem real_kernel_ge_neg_one (D : Int) (p : Nat) [Fact (Nat.Prime p)]
    (hp2 : 2 < p) : -1 <= (numeratorKernel D p).re := by
  by_cases hD : (D : ZMod p) = 0
  . rw [numerator_kernel_prime D p (by omega)]
    simp [hD]
  . have hs := real_kernel_square_of_nonzero D p hp2 hD
    nlinarith only [hs]

theorem native_agreement_mass_le_character (n h m k Y X : Nat)
    (hn : 0 < n) (hh : 0 < h) (hm : 0 < m) (hk : 0 < k)
    (hY : 5 <= Y) (hnh : n + h < Y) (hmk : m + k < Y) :
    nativeAgreementMass n h m k Y X <=
      (reciprocalBand Y X +
        primeCorrelation ((n * (n + h) * m * (m + k) : Nat) : Int) Y X) / 2 := by
  classical
  calc
    nativeAgreementMass n h m k Y X <=
        ((Finset.Ico Y X).filter Nat.Prime).sum (fun p =>
          ((1 / (p : Real)) *
            (1 + (numeratorKernel ((n * (n + h) * m * (m + k) : Nat) : Int) p).re)) / 2) := by
      unfold nativeAgreementMass
      apply Finset.sum_le_sum
      intro p hp
      have hdata := Finset.mem_filter.mp hp
      have hband := Finset.mem_Ico.mp hdata.1
      have : Fact (Nat.Prime p) := Fact.mk hdata.2
      by_cases hw : integerNativeWeight n h p = integerNativeWeight m k p
      . have hc := native_weight_match_product_one n h m k p hn hh hm hk
          (by omega) (by omega) (by omega) hw
        simp only [ite_eq_left hw, hc]
        ring_nf
        exact le_rfl
      . rw [ite_eq_right hw]
        have hc := real_kernel_ge_neg_one
          ((n * (n + h) * m * (m + k) : Nat) : Int) p (by omega)
        exact div_nonneg (mul_nonneg (by positivity) (by linarith only [hc])) (by norm_num)
    _ = _ := by
      unfold reciprocalBand primeCorrelation
      apply (eq_div_iff (by norm_num : Not ((2 : Real) = 0))).mpr
      rw [Finset.sum_mul]
      calc
        _ = ((Finset.Ico Y X).filter Nat.Prime).sum (fun p =>
            1 / (p : Real) + (1 / (p : Real)) *
              (numeratorKernel ((n * (n + h) * m * (m + k) : Nat) : Int) p).re) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ = _ := Finset.sum_add_distrib

theorem exists_eventual_fixed_prime_correlation_bound (A P : Nat)
    (hA : 0 < A) (hP : Nat.Prime P) (hP2 : 2 < P) (hcop : Nat.Coprime P A)
    (D : Int) (hsign : Or (D = (A : Int) * (P : Int))
      (D = -((A : Int) * (P : Int)))) :
    exists B : Real, And (0 <= B) (Filter.Eventually (fun U : Nat =>
      abs (primeCorrelation D (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1)) <= relativeError B U) atTop) := by
  choose C hCpos hC using exists_coprime_prime_correlation_bound
  let B : Real := C * (3 + Real.log ((4 * A * P : Nat) : Real)) ^ 2
  have hB : 0 <= B := by dsimp only [B]; positivity
  refine Exists.intro B (And.intro hB ?_)
  have hfit : Filter.Eventually (fun U : Nat =>
      6 <= U /\ 1 <= Real.log (U : Real) /\
        1 <= Real.log (Real.log (U : Real)) /\ preciseCore U <= U) atTop :=
    eventually_atTop.mpr eventually_precise_core_fits
  filter_upwards [hfit] with U hf
  have hb := hC A P hA hP hP2 hcop D hsign
    (preciseCore U + 1) (preciseCore U * preciseCore U + 1) (by omega)
  change abs (primeCorrelation D (preciseCore U + 1)
    (preciseCore U * preciseCore U + 1)) <=
      B * ((preciseCore U + 1 : Nat) : Real) ^ (-1 / 32 : Real) at hb
  have hUpos : 0 < U := by omega
  have hprod : 0 < 4 * 1 * 1 * (U * U) * (U * U) := by positivity
  have hlevel : (1 : Real) <= ((4 * 1 * 1 * (U * U) * (U * U) : Nat) : Real) := by
    exact_mod_cast (show 1 <= 4 * 1 * 1 * (U * U) * (U * U) by omega)
  have hlog := Real.log_nonneg hlevel
  have hsq : (1 : Real) <=
      (3 + Real.log ((4 * 1 * 1 * (U * U) * (U * U) : Nat) : Real)) ^ 2 := by
    nlinarith only [hlog]
  have hscale := mul_le_mul_of_nonneg_left hsq hB
  have heps := mul_le_mul_of_nonneg_right hscale
    (Real.rpow_nonneg (show 0 <= ((preciseCore U + 1 : Nat) : Real) from Nat.cast_nonneg _)
      (-1 / 32 : Real))
  simp only [mul_one] at heps
  have hcost := signature_uniform_cost_le B hB 1 U (by decide) (by omega) (by omega) hf.2.1
  exact hb.trans (heps.trans hcost)

theorem exists_eventual_native_agreement_upper (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hneq : Not (And (n = m) (h = k))) :
    exists B : Real, And (0 <= B) (Filter.Eventually (fun U : Nat =>
      nativeAgreementMass n h m k (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) <=
      reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) / 2 +
        relativeError B U / 2) atTop) := by
  choose A P hA hP hP2 hcop hD using
    distinct_prime_pairs_have_odd_carrier n h m k hn hnh hm hmk hh hk hneq
  have hDcast : ((n * (n + h) * m * (m + k) : Nat) : Int) = (A : Int) * (P : Int) := by
    exact_mod_cast hD
  choose B hB hbound using exists_eventual_fixed_prime_correlation_bound A P hA hP hP2 hcop
    ((n * (n + h) * m * (m + k) : Nat) : Int) (Or.inl hDcast)
  refine Exists.intro B (And.intro hB ?_)
  filter_upwards [hbound,
    precise_core_tendsto_atTop.eventually_ge_atTop (max (n + h) (m + k) + 5)]
    with U hb hcore
  have ha := native_agreement_mass_le_character n h m k (preciseCore U + 1)
    (preciseCore U * preciseCore U + 1) hn.pos hh hm.pos hk
    (by omega) (by omega) (by omega)
  have hc := (le_abs_self (primeCorrelation
    ((n * (n + h) * m * (m + k) : Nat) : Int)
      (preciseCore U + 1) (preciseCore U * preciseCore U + 1))).trans hb
  linarith only [ha, hc]

theorem retained_mass_le_native_agreement (n h m k Y X : Nat) (S : Finset Nat)
    (hS : forall p, Membership.mem S p ->
      Membership.mem ((Finset.Ico Y X).filter Nat.Prime) p)
    (hw : forall p, Membership.mem S p ->
      integerNativeWeight n h p = integerNativeWeight m k p) :
    S.sum (fun p => 1 / (p : Real)) <= nativeAgreementMass n h m k Y X := by
  classical
  have heq : S.sum (fun p => 1 / (p : Real)) =
      S.sum (fun p => if integerNativeWeight n h p = integerNativeWeight m k p
        then 1 / (p : Real) else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [ite_eq_left (hw p hp)]
  rw [heq]
  unfold nativeAgreementMass
  apply Finset.sum_le_sum_of_subset_of_nonneg hS
  intro p hp hnot
  split_ifs <;> positivity

theorem native_pair_rigidity_of_retained_mass (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k)) (hh : 0 < h) (hk : 0 < k)
    (S : Nat -> Finset Nat) (eps : Real) (heps : 0 < eps)
    (hS : forall U p, Membership.mem (S U) p ->
      Membership.mem ((Finset.Ico (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1)).filter Nat.Prime) p)
    (hw : forall U p, Membership.mem (S U) p ->
      integerNativeWeight n h p = integerNativeWeight m k p)
    (hlarge : forall U0 : Nat, exists U : Nat, And (U0 <= U)
      (reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) / 2 + eps <=
        (S U).sum (fun p => 1 / (p : Real)))) :
    And (n = m) (h = k) := by
  classical
  by_contra hneq
  choose B hB hbound using
    exists_eventual_native_agreement_upper n h m k hn hnh hm hmk hh hk hneq
  have herr := (relative_error_tendsto_zero B).eventually
    (Iio_mem_nhds (show (0 : Real) < 2 * eps by linarith only [heps]))
  choose U0 hU0 using eventually_atTop.mp (hbound.and herr)
  choose U hUge hmass using hlarge U0
  have hb := hU0 U hUge
  have hr := retained_mass_le_native_agreement n h m k
    (preciseCore U + 1) (preciseCore U * preciseCore U + 1) (S U) (hS U) (hw U)
  linarith only [hb.1, hb.2, hr, hmass]

theorem native_pair_rigidity_of_retained_fraction (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k)) (hh : 0 < h) (hk : 0 < k)
    (S : Nat -> Finset Nat) (delta : Real) (hdelta : 0 < delta)
    (hS : forall U p, Membership.mem (S U) p ->
      Membership.mem ((Finset.Ico (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1)).filter Nat.Prime) p)
    (hw : forall U p, Membership.mem (S U) p ->
      integerNativeWeight n h p = integerNativeWeight m k p)
    (hlarge : forall U0 : Nat, exists U : Nat, And (U0 <= U)
      ((1 / 2 + delta) *
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) <=
        (S U).sum (fun p => 1 / (p : Real)))) :
    And (n = m) (h = k) := by
  have heps : 0 < delta * Real.log 2 / 2 := by positivity
  apply native_pair_rigidity_of_retained_mass n h m k hn hnh hm hmk hh hk S
    (delta * Real.log 2 / 2) heps hS hw
  have hm := precise_core_tendsto_atTop.eventually eventually_reciprocal_square_band_positive
  choose N hN using eventually_atTop.mp hm
  intro U0
  choose U hUge hmass using hlarge (max U0 N)
  refine Exists.intro U (And.intro ((le_max_left _ _).trans hUge) ?_)
  have hM := hN U ((le_max_right _ _).trans hUge)
  have hscale := mul_le_mul_of_nonneg_left hM hdelta.le
  nlinarith only [hscale, hmass]

theorem unbounded_least_gap_retained_native_frames (R : Nat) :
    exists Q i : Nat, And (R <= Q) (And (leastGapFrame Q i)
      (forall m k : Nat, Nat.Prime m -> Nat.Prime (m + k) -> 0 < k ->
        forall S : Nat -> Finset Nat, forall delta : Real, 0 < delta ->
        (forall U p, Membership.mem (S U) p ->
          Membership.mem ((Finset.Ico (preciseCore U + 1)
            (preciseCore U * preciseCore U + 1)).filter Nat.Prime) p) ->
        (forall U p, Membership.mem (S U) p ->
          integerNativeWeight (Q + 1) leastRecurringPrimeGap p = integerNativeWeight m k p) ->
        (forall U0 : Nat, exists U : Nat, And (U0 <= U)
          ((1 / 2 + delta) * reciprocalBand (preciseCore U + 1)
            (preciseCore U * preciseCore U + 1) <= (S U).sum (fun p => 1 / (p : Real)))) ->
        And (m = Q + 1) (k = leastRecurringPrimeGap))) := by
  choose Q i hRQ hf using unbounded_least_gap_positive_windows R
  refine Exists.intro Q (Exists.intro i (And.intro hRQ (And.intro hf ?_)))
  intro m k hm hmk hk S delta hdelta hS hw hlarge
  have hn : Nat.Prime (Q + 1) := by
    rw [<- hf.2.2.2.2.2.1]
    exact PrimeFactorUnimodality.prime_primeAt i
  have hnh : Nat.Prime (Q + 1 + leastRecurringPrimeGap) := by
    rw [<- hf.2.2.2.2.2.2.1]
    exact PrimeFactorUnimodality.prime_primeAt (i + 1)
  have hH : 0 < leastRecurringPrimeGap := by
    have h := two_le_leastRecurringPrimeGap
    omega
  have he := native_pair_rigidity_of_retained_fraction (Q + 1) leastRecurringPrimeGap m k
    hn hnh hm hmk hH hk S delta hdelta hS hw hlarge
  exact And.intro he.1.symm he.2.symm

end PrimeFactorOscillations.FiniteFieldIntegerSignature
