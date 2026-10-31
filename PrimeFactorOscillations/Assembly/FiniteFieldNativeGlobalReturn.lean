/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeEndpointReadout

/-!
# Global reconstruction from cofinite native probability profiles

Actual oriented prime pairs are determined by their scalar local weights
outside an arbitrary finite set of prime fields. No common integer height
window or fixed gap bound is assumed. The endpoint-product readout and
the existing full-conductor character estimate supply the inverse.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer FiniteFieldIntegerGapWindows PrimeProfileRigidity

def cofiniteNativeWeightMatch (n h m k : Nat) : Prop :=
  Filter.Eventually (fun p : Nat => Nat.Prime p ->
    integerNativeWeight n h p = integerNativeWeight m k p) atTop

theorem distinct_prime_pairs_have_odd_carrier (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hneq : Not (And (n = m) (h = k))) :
    exists A P : Nat, And (0 < A) (And (Nat.Prime P)
      (And (2 < P) (And (Nat.Coprime P A)
        (n * (n + h) * m * (m + k) = A * P)))) := by
  have hn2 := hn.two_le
  have hm2 := hm.two_le
  have hcop (P R : Nat) (hP : Nat.Prime P) (hR : Nat.Prime R)
      (hne : Not (P = R)) : Nat.Coprime P R := by
    apply hP.coprime_iff_not_dvd.mpr
    intro hd
    cases (Nat.dvd_prime hR).mp hd with
    | inl he => exact hP.ne_one he
    | inr he => exact hne he
  have hthree (P a b c : Nat) (hP : Nat.Prime P)
      (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
      (hPa : Not (P = a)) (hPb : Not (P = b)) (hPc : Not (P = c)) :
      Nat.Coprime P (a * b * c) :=
    Nat.coprime_mul_iff_right.mpr
      (And.intro (Nat.coprime_mul_iff_right.mpr
        (And.intro (hcop P a hP ha hPa) (hcop P b hP hb hPb)))
        (hcop P c hP hc hPc))
  rcases lt_trichotomy (n + h) (m + k) with hlt | heq | hgt
  . refine Exists.intro (n * (n + h) * m) (Exists.intro (m + k) ?_)
    refine And.intro (by positivity) (And.intro hmk
      (And.intro (by omega) (And.intro ?_ ?_)))
    . exact hthree (m + k) n (n + h) m hmk hn hnh hm
        (by omega) (by omega) (by omega)
    . ring
  . have hnmneq : Not (n = m) := by
      intro he
      apply hneq
      exact And.intro he (by omega)
    by_cases hnm : n < m
    . refine Exists.intro (n * (n + h) * (m + k)) (Exists.intro m ?_)
      refine And.intro (by positivity) (And.intro hm
        (And.intro (by omega) (And.intro ?_ ?_)))
      . exact hthree m n (n + h) (m + k) hm hn hnh hmk
          (by omega) (by omega) (by omega)
      . ring
    . refine Exists.intro ((n + h) * m * (m + k)) (Exists.intro n ?_)
      refine And.intro (by positivity) (And.intro hn
        (And.intro (by omega) (And.intro ?_ ?_)))
      . exact hthree n (n + h) m (m + k) hn hnh hm hmk
          (by omega) (by omega) (by omega)
      . ring
  . refine Exists.intro (n * m * (m + k)) (Exists.intro (n + h) ?_)
    refine And.intro (by positivity) (And.intro hnh
      (And.intro (by omega) (And.intro ?_ ?_)))
    . exact hthree (n + h) n m (m + k) hnh hn hm hmk
        (by omega) (by omega) (by omega)
    . ring

theorem not_eventually_prime_kernel_one (A P : Nat)
    (hA : 0 < A) (hP : Nat.Prime P) (hP2 : 2 < P) (hcop : Nat.Coprime P A)
    (D : Int) (hsign : Or (D = (A : Int) * (P : Int))
      (D = -((A : Int) * (P : Int)))) :
    Not (Filter.Eventually (fun p : Nat => Nat.Prime p ->
      (numeratorKernel D p).re = 1) atTop) := by
  classical
  choose C hCpos hC using exists_coprime_prime_correlation_bound
  intro hconstant
  choose N hN using eventually_atTop.mp hconstant
  let B : Real := C * (3 + Real.log ((4 * A * P : Nat) : Real)) ^ 2
  have hB : 0 <= B := by dsimp only [B]; positivity
  choose Q0 hQ0 using eventually_atTop.mp
    ((eventually_uniform_signature_margin 1 (by decide) B hB).and
      (precise_core_tendsto_atTop.eventually_ge_atTop (max N 4)))
  have hdata := hQ0 Q0 (Nat.le_refl _)
  have hmargin := hdata.1
  have hcore := hdata.2
  have hmatch : primeCorrelation D (preciseCore Q0 + 1)
      (preciseCore Q0 * preciseCore Q0 + 1) =
      reciprocalBand (preciseCore Q0 + 1) (preciseCore Q0 * preciseCore Q0 + 1) := by
    unfold primeCorrelation reciprocalBand
    apply Finset.sum_congr rfl
    intro p hp
    have hpdata := Finset.mem_filter.mp hp
    have hpband := Finset.mem_Ico.mp hpdata.1
    have hNp : N <= p := by omega
    rw [hN p hNp hpdata.2, mul_one]
  have hbound := hC A P hA hP hP2 hcop D hsign
    (preciseCore Q0 + 1) (preciseCore Q0 * preciseCore Q0 + 1) (by omega)
  change abs (primeCorrelation D (preciseCore Q0 + 1)
    (preciseCore Q0 * preciseCore Q0 + 1)) <=
      B * ((preciseCore Q0 + 1 : Nat) : Real) ^ (-1 / 32 : Real) at hbound
  have hQpos : 0 < Q0 := by
    have hfit := hmargin.2.2.1
    omega
  have hprod : 0 < 4 * 1 * 1 * (Q0 * Q0) * (Q0 * Q0) := by positivity
  have hlevel : (1 : Real) <= ((4 * 1 * 1 * (Q0 * Q0) * (Q0 * Q0) : Nat) : Real) := by
    exact_mod_cast (show 1 <= 4 * 1 * 1 * (Q0 * Q0) * (Q0 * Q0) by omega)
  have hlog := Real.log_nonneg hlevel
  have hsq : (1 : Real) <=
      (3 + Real.log ((4 * 1 * 1 * (Q0 * Q0) * (Q0 * Q0) : Nat) : Real)) ^ 2 := by
    nlinarith only [hlog]
  have hscale := mul_le_mul_of_nonneg_left hsq hB
  have heps := mul_le_mul_of_nonneg_right hscale
    (Real.rpow_nonneg (show 0 <= ((preciseCore Q0 + 1 : Nat) : Real) from Nat.cast_nonneg _)
      (-1 / 32 : Real))
  simp only [mul_one] at heps
  have hsmall := heps.trans_lt hmargin.2.2.2
  rw [hmatch] at hbound
  have hmass := (le_abs_self
    (reciprocalBand (preciseCore Q0 + 1) (preciseCore Q0 * preciseCore Q0 + 1))).trans hbound
  linarith only [hmass, hsmall]

theorem cofinite_native_weight_pair_rigidity (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hmatch : cofiniteNativeWeightMatch n h m k) :
    And (n = m) (h = k) := by
  classical
  by_contra hneq
  choose A P hA hP hP2 hcop hD using
    distinct_prime_pairs_have_odd_carrier n h m k hn hnh hm hmk hh hk hneq
  have hDcast : ((n * (n + h) * m * (m + k) : Nat) : Int) = (A : Int) * (P : Int) := by
    exact_mod_cast hD
  apply not_eventually_prime_kernel_one A P hA hP hP2 hcop
    ((n * (n + h) * m * (m + k) : Nat) : Int) (Or.inl hDcast)
  unfold cofiniteNativeWeightMatch at hmatch
  filter_upwards [hmatch, eventually_ge_atTop (n + h + m + k + 5)] with p hw hpbound
  intro hp
  have : Fact (Nat.Prime p) := Fact.mk hp
  exact native_weight_match_product_one n h m k p hn.pos hh hm.pos hk
    (by omega) (by omega) (by omega) (hw hp)

theorem unbounded_least_gap_global_native_frames (R : Nat) :
    exists Q i : Nat, And (R <= Q) (And (leastGapFrame Q i)
      (forall m k : Nat, Nat.Prime m -> Nat.Prime (m + k) -> 0 < k ->
        cofiniteNativeWeightMatch (Q + 1) leastRecurringPrimeGap m k ->
        And (m = Q + 1) (k = leastRecurringPrimeGap))) := by
  choose Q i hRQ hf using unbounded_least_gap_positive_windows R
  refine Exists.intro Q (Exists.intro i (And.intro hRQ (And.intro hf ?_)))
  intro m k hm hmk hk hmatch
  have hn : Nat.Prime (Q + 1) := by
    rw [<- hf.2.2.2.2.2.1]
    exact PrimeFactorUnimodality.prime_primeAt i
  have hnh : Nat.Prime (Q + 1 + leastRecurringPrimeGap) := by
    rw [<- hf.2.2.2.2.2.2.1]
    exact PrimeFactorUnimodality.prime_primeAt (i + 1)
  have hH : 0 < leastRecurringPrimeGap := by
    have h := two_le_leastRecurringPrimeGap
    omega
  have he := cofinite_native_weight_pair_rigidity (Q + 1) leastRecurringPrimeGap m k
    hn hnh hm hmk hH hk hmatch
  exact And.intro he.1.symm he.2.symm

end PrimeFactorOscillations.FiniteFieldIntegerSignature
