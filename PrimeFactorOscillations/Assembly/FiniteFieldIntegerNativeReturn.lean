/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerNativeRigidity

/-!
# Native probability weights determine bounded integer prime pairs

The local scalar law uses only the sum of the two original characters.
The full signed energy bound applies without recovering their labels first.
Its positive diagonal survives every possible shared endpoint, and the
existing uniform prime-band margin proves actual integer return rigidity.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer FiniteFieldIntegerCharacter
open FiniteFieldIntegerGapWindows PrimeProfileRigidity

def nativeWeightMatch (Q n h m k : Nat) : Prop :=
  forall p : Nat, forall hp : Nat.Prime p,
    preciseCore Q < p -> p <= preciseCore Q * preciseCore Q ->
    letI : Fact (Nat.Prime p) := Fact.mk hp
    FiniteField.traceFreePairWeight (n : ZMod p) (h : ZMod p) =
      FiniteField.traceFreePairWeight (m : ZMod p) (k : ZMod p)

theorem native_weight_trace_eq (n h m k p : Nat) [Fact (Nat.Prime p)]
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hp5 : 5 <= p) (hpn : p < n) (hpm : p < m)
    (hweight : FiniteField.traceFreePairWeight (n : ZMod p) (h : ZMod p) =
      FiniteField.traceFreePairWeight (m : ZMod p) (k : ZMod p)) :
    nativeTrace n h p = nativeTrace m k p := by
  have hmod (P : Nat) (hP : Nat.Prime P) (hpP : p < P) :
      Not ((P : ZMod p) = 0) := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff P p).mp hz
    cases (Nat.dvd_prime hP).mp hd with
    | inl he => exact (show Nat.Prime p from Fact.out).ne_one he
    | inr he => omega
  have hn0 := hmod n hn hpn
  have hnh0 := hmod (n + h) hnh (by omega)
  have hm0 := hmod m hm hpm
  have hmk0 := hmod (m + k) hmk (by omega)
  have hnneg : Not ((n : ZMod p) = -(h : ZMod p)) := by
    intro he
    apply hnh0
    simp only [Nat.cast_add, he, neg_add_cancel]
  have hmneg : Not ((m : ZMod p) = -(k : ZMod p)) := by
    intro he
    apply hmk0
    simp only [Nat.cast_add, he, neg_add_cancel]
  have hsN := FiniteField.QuadraticPairTwistEuler.traceFreePairWeight_scalar
    (n : ZMod p) (h : ZMod p) hn0 hnneg
  have hsM := FiniteField.QuadraticPairTwistEuler.traceFreePairWeight_scalar
    (m : ZMod p) (k : ZMod p) hm0 hmneg
  have hw := (hsN.symm.trans hweight).trans hsM
  simp only [ZMod.card] at hw
  have hden : Not ((p : Real) - 3 = 0) := by
    have hpR : (5 : Real) <= p := by exact_mod_cast hp5
    linarith only [hpR]
  have hx := congrArg (fun z : Real => z * ((p : Real) - 3)) hw
  field_simp [hden] at hx
  have htrace (s d : Nat) : nativeTrace s d p =
      FiniteField.QuadraticPairTwistEuler.characterA (s : ZMod p) (d : ZMod p) +
        FiniteField.QuadraticPairTwistEuler.characterB (s : ZMod p) (d : ZMod p) := by
    have ha := congrArg Complex.re (integer_characterA d s p (by omega))
    have hb := congrArg Complex.re (integer_characterB d s p (by omega))
    simp only [Complex.ofReal_re] at ha hb
    unfold nativeTrace
    rw [<- ha, <- hb]
  rw [htrace n h, htrace m k]
  linarith only [hx]

theorem native_energy_zero_of_weight_match (Q n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hK : 4 <= preciseCore Q) (hband : preciseCore Q * preciseCore Q < Q)
    (hQn : Q < n) (hQm : Q < m) (hmatch : nativeWeightMatch Q n h m k) :
    nativeTraceEnergy n h m k (preciseCore Q + 1)
      (preciseCore Q * preciseCore Q + 1) = 0 := by
  unfold nativeTraceEnergy
  apply Finset.sum_eq_zero
  intro p hp
  have hdata := Finset.mem_filter.mp hp
  have hpband := Finset.mem_Ico.mp hdata.1
  have : Fact (Nat.Prime p) := Fact.mk hdata.2
  have hw := hmatch p hdata.2 (by omega) (by omega)
  have ht := native_weight_trace_eq n h m k p hn hnh hm hmk (by omega)
    (by omega) (by omega) hw
  simp only [ht, sub_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero]

theorem eventually_native_weight_pair_rigidity (H : Nat) (hH : 0 < H) :
    Filter.Eventually (fun Q : Nat =>
      forall n m h k : Nat,
        Nat.Prime n -> Nat.Prime (n + h) -> Nat.Prime m -> Nat.Prime (m + k) ->
        0 < h -> 0 < k -> h <= H -> k <= H ->
        Q < n -> Q < m -> n + h <= Q * Q -> m + k <= Q * Q ->
        nativeWeightMatch Q n h m k -> And (n = m) (h = k)) atTop := by
  classical
  choose C hCpos hC using exists_native_trace_energy_lower
  filter_upwards [eventually_uniform_signature_margin H hH (5 * C) (by positivity),
    precise_core_tendsto_atTop.eventually_ge_atTop 4] with Q hmargin hK
  intro n m h k hn hnh hm hmk hh hk hhH hkH hQn hQm hnQ hmQ hmatch
  by_contra hneq
  have hYX : preciseCore Q + 1 < preciseCore Q * preciseCore Q + 1 := by
    nlinarith only [hK]
  have hlower := hC H (Q * Q) n m h k (preciseCore Q + 1)
    (preciseCore Q * preciseCore Q + 1) hn hnh hm hmk hh hk hhH hkH
    hmargin.1 hmargin.2.1 hYX (by omega) (by omega) hnQ hmQ hneq
  have hsmall :
      5 * (C * (3 + Real.log ((4 * H * H * (Q * Q) * (Q * Q) : Nat) : Real)) ^ 2 *
        ((preciseCore Q + 1 : Nat) : Real) ^ (-1 / 32 : Real)) <
          reciprocalBand (preciseCore Q + 1) (preciseCore Q * preciseCore Q + 1) := by
    simpa only [mul_assoc] using hmargin.2.2.2
  have hzero := native_energy_zero_of_weight_match Q n h m k hn hnh hm hmk
    hK hmargin.2.2.1 hQn hQm hmatch
  rw [hzero] at hlower
  linarith only [hlower, hsmall]

theorem unbounded_least_gap_native_rigid_frames (R : Nat) :
    exists Q i : Nat, And (R <= Q) (And (leastGapFrame Q i)
      (forall m k : Nat, Nat.Prime m -> Nat.Prime (m + k) ->
        0 < k -> k <= leastRecurringPrimeGap -> Q < m -> m + k <= Q * Q ->
        nativeWeightMatch Q (Q + 1) leastRecurringPrimeGap m k ->
        And (m = Q + 1) (k = leastRecurringPrimeGap))) := by
  have hH : 0 < leastRecurringPrimeGap := by
    have hh := two_le_leastRecurringPrimeGap
    omega
  choose Q0 hQ0 using eventually_atTop.mp
    (eventually_native_weight_pair_rigidity leastRecurringPrimeGap hH)
  choose Q i hRQ hf using unbounded_least_gap_positive_windows (max R Q0)
  have hQge : Q0 <= Q := (le_max_right _ _).trans hRQ
  have hRge : R <= Q := (le_max_left _ _).trans hRQ
  refine Exists.intro Q (Exists.intro i (And.intro hRge (And.intro hf ?_)))
  intro m k hm hmk hk hkH hQm hmQ hmatch
  have hn : Nat.Prime (Q + 1) := by
    rw [<- hf.2.2.2.2.2.1]
    exact PrimeFactorUnimodality.prime_primeAt i
  have hnh : Nat.Prime (Q + 1 + leastRecurringPrimeGap) := by
    rw [<- hf.2.2.2.2.2.2.1]
    exact PrimeFactorUnimodality.prime_primeAt (i + 1)
  have hnQ : Q + 1 + leastRecurringPrimeGap <= Q * Q := by
    have hHQ := hf.2.2.2.2.1
    have hQ6 := hf.1
    nlinarith only [hHQ, hQ6]
  have he := hQ0 Q hQge (Q + 1) m leastRecurringPrimeGap k hn hnh hm hmk
    hH hk (Nat.le_refl _) hkH (by omega) hQm hnQ hmQ hmatch
  exact And.intro he.1.symm he.2.symm

end PrimeFactorOscillations.FiniteFieldIntegerSignature
