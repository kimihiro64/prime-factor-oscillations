/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerHeight

/-!
# Split-core integer packet envelopes

The actual local factors are retained up to K. Beyond K the exact flat
fallback has half the leading exponent of the actual envelope. The two
Mertens budgets give log(Q)^2 log(K)^2 with the existing absolute constant.
All shift-dividing rows and opening masks remain in the packet.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerAmplitude

open FiniteFieldIntegerMass
open FiniteFieldIntegerTail

def splitExponent (K p : Nat) : Real :=
  envelopeExponent p / 2 + if p <= K then envelopeExponent p / 2 else 0

def splitEnvelope (K p : Nat) : Real :=
  smallMultiplier p * Real.exp (splitExponent K p)

theorem flat_scalar_half_cap (p : Nat) (hp : 7 <= p) :
    (p : Real) / ((p : Real) - 2) <=
      Real.exp ((4 / (p : Real) + 21 / (p : Real) ^ 2) / 2) := by
  have hpr : (7 : Real) <= (p : Real) := by exact_mod_cast hp
  have h0 : Not ((p : Real) = 0) := ne_of_gt (by linarith only [hpr])
  have h2 : Not ((p : Real) - 2 = 0) := ne_of_gt (by linarith only [hpr])
  have he :
      (4 / (p : Real) + 21 / (p : Real) ^ 2) / 2 - 2 / ((p : Real) - 2) =
        (13 * (p : Real) - 42) / (2 * (p : Real) ^ 2 * ((p : Real) - 2)) := by
    field_simp [h0, h2]
    ring
  have hn : 0 <=
      (13 * (p : Real) - 42) / (2 * (p : Real) ^ 2 * ((p : Real) - 2)) :=
    div_nonneg (by linarith only [hpr])
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith only [hpr]))
  have hr : (p : Real) / ((p : Real) - 2) = 1 + 2 / ((p : Real) - 2) := by
    field_simp [h2]
    ring
  have hx := Real.add_one_le_exp ((4 / (p : Real) + 21 / (p : Real) ^ 2) / 2)
  rw [hr]
  linarith only [he, hn, hx]

theorem flat_fallback_half_envelope {Q : Nat} (h : Int) (q : BoundedModulus Q)
    (hp : Nat.Prime q.val) (hq : 7 <= q.val) (c : ZMod q.val) :
    flatFallback h q c <= Real.exp (envelopeExponent q.val / 2) := by
  have hqr : (7 : Real) <= (q.val : Real) := by exact_mod_cast hq
  have hb := flat_fallback_le_scalar h q (by omega) c
  have hd : flatFallback h q c <= (q.val : Real) / ((q.val : Real) - 2) := by
    by_cases hh : (h : ZMod q.val) = 0
    . rw [if_pos hh] at hb
      apply le_trans hb
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith only [hqr])
        (show (q.val : Real) - 2 <= (q.val : Real) - 1 from by linarith)
    . rwa [if_neg hh] at hb
  have he := flat_scalar_half_cap q.val hq
  simpa only [envelopeExponent, if_pos (And.intro hp hq)] using hd.trans he

theorem split_envelope_ge_one (K p : Nat) : 1 <= splitEnvelope K p := by
  have hs := small_multiplier_ge_one p
  have hE : 0 <= envelopeExponent p := by
    unfold envelopeExponent
    split_ifs <;> positivity
  have hsplit : 0 <= splitExponent K p := by
    unfold splitExponent
    split_ifs <;> positivity
  have he : 1 <= Real.exp (splitExponent K p) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hsplit
  unfold splitEnvelope
  nlinarith only [hs, he, mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr he)]

theorem hybrid_local_split_envelope {Q : Nat} (K : Nat) (h : Int) (hK : 6 <= K)
    (q : BoundedModulus Q) (c : ZMod q.val) :
    hybridLocal K h q c <= splitEnvelope K q.val := by
  by_cases hp : Nat.Prime q.val
  . by_cases hk : q.val <= K
    . have he : splitEnvelope K q.val = localEnvelope q.val := by
        unfold splitEnvelope splitExponent localEnvelope
        rw [if_pos hk]
        congr 1
        congr 1
        ring
      rw [he]
      simp only [hybridLocal, if_pos hp, if_pos hk]
      exact actual_local_envelope h q c
    . have h7 : 7 <= q.val := by omega
      have h2 : Not (q.val = 2) := by omega
      have h3 : Not (q.val = 3) := by omega
      have h5 : Not (q.val = 5) := by omega
      have hb := flat_fallback_half_envelope h q hp h7 c
      simpa only [hybridLocal, if_pos hp, if_neg hk, splitEnvelope, splitExponent,
        smallMultiplier, if_neg h2, if_neg h3, if_neg h5, one_mul, add_zero] using hb
  . simpa only [hybridLocal, if_neg hp] using split_envelope_ge_one K q.val

theorem split_exponent_sum_bound (K Q : Nat) (hK : 6 <= K) (hKQ : K <= Q) :
    (Finset.Icc 1 Q).sum (splitExponent K) <=
      2 * PrimeFactorUnimodality.reciprocalPrimeSumBelow (Q + 1) +
        2 * PrimeFactorUnimodality.reciprocalPrimeSumBelow (K + 1) + 4 := by
  have hset : (Finset.Icc 1 Q).filter (fun p => p <= K) = Finset.Icc 1 K := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hid :
      (Finset.Icc 1 Q).sum (splitExponent K) =
        ((Finset.Icc 1 Q).sum envelopeExponent) / 2 +
          ((Finset.Icc 1 K).sum envelopeExponent) / 2 := by
    unfold splitExponent
    rw [Finset.sum_add_distrib, <- Finset.sum_filter, hset]
    simp only [Finset.sum_div]
  have hQ := exponent_sum_bound Q (by omega)
  have hCore := exponent_sum_bound K hK
  rw [hid]
  linarith only [hQ, hCore]

theorem split_envelope_product_bound (K Q : Nat) (hK : 6 <= K) (hKQ : K <= Q) :
    (Finset.Icc 1 Q).prod (splitEnvelope K) <=
      replacementConstant * (Real.log (Q : Real)) ^ 2 * (Real.log (K : Real)) ^ 2 := by
  have hs := split_exponent_sum_bound K Q hK hKQ
  have hmQ := reciprocal_prime_log_bound Q (by omega)
  have hmK := reciprocal_prime_log_bound K (by omega)
  have hlogQ : 0 < Real.log (Q : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q from by omega))
  have hlogK : 0 < Real.log (K : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < K from by omega))
  have heq : Real.exp (2 * Real.log (Real.log (Q : Real)) +
      2 * Real.log (Real.log (K : Real))) =
        (Real.log (Q : Real)) ^ 2 * (Real.log (K : Real)) ^ 2 := by
    rw [show 2 * Real.log (Real.log (Q : Real)) + 2 * Real.log (Real.log (K : Real)) =
      Real.log (Real.log (Q : Real)) + Real.log (Real.log (Q : Real)) +
        (Real.log (Real.log (K : Real)) + Real.log (Real.log (K : Real))) from by ring]
    simp only [Real.exp_add, Real.exp_log hlogQ, Real.exp_log hlogK]
    ring
  calc
    _ = 18 * Real.exp ((Finset.Icc 1 Q).sum (splitExponent K)) := by
      unfold splitEnvelope
      rw [Finset.prod_mul_distrib, small_multiplier_product Q (by omega), Real.exp_sum]
    _ <= 18 * Real.exp
        (2 * PrimeFactorUnimodality.reciprocalPrimeSumBelow (Q + 1) +
          2 * PrimeFactorUnimodality.reciprocalPrimeSumBelow (K + 1) + 4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) (by norm_num)
    _ <= 18 * Real.exp
        (2 * (Real.log (Real.log (Q : Real)) + mertensBudget) +
          2 * (Real.log (Real.log (K : Real)) + mertensBudget) + 4) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith only [hmQ, hmK])) (by norm_num)
    _ = _ := by
      rw [show 2 * (Real.log (Real.log (Q : Real)) + mertensBudget) +
          2 * (Real.log (Real.log (K : Real)) + mertensBudget) + 4 =
        (4 + 4 * mertensBudget) + (2 * Real.log (Real.log (Q : Real)) +
          2 * Real.log (Real.log (K : Real))) from by ring,
        Real.exp_add, heq]
      unfold replacementConstant
      ring

theorem hybrid_packet_split_envelope (K : Nat) (h : Int) (Q n : Nat)
    (hK : 6 <= K) (hKQ : K <= Q) :
    hybridPacket K h Q n <=
      replacementConstant * (Real.log (Q : Real)) ^ 2 * (Real.log (K : Real)) ^ 2 := by
  calc
    _ <= (Finset.Icc 1 Q).attach.prod (fun q => splitEnvelope K q.val) := by
      apply real_product_le_of_nonneg
      . intro q _
        exact hybrid_local_nonneg K h q _
      . intro q _
        exact hybrid_local_split_envelope K h hK q _
    _ = (Finset.Icc 1 Q).prod (splitEnvelope K) :=
      Finset.prod_attach (Finset.Icc 1 Q) (splitEnvelope K)
    _ <= _ := split_envelope_product_bound K Q hK hKQ


theorem exists_natural_height_split_amplitude :
    exists A : Real, And (0 < A)
      (forall K h Q n : Nat, 6 <= K -> 0 < h -> h < Q -> K <= Q ->
        Q < n -> n + h <= Q * Q ->
        (3 + Real.log ((4 * h * (Q * Q) : Nat) : Real)) ^ 64 <= ((K + 1 : Nat) : Real) ->
        actualPacket (h : Int) Q n <=
          A * (Real.log (Q : Real)) ^ 2 * (Real.log (K : Real)) ^ 2) := by
  let C : Real := Classical.choose FiniteFieldIntegerHeight.exists_natural_height_packet_comparison
  have hSpec := Classical.choose_spec FiniteFieldIntegerHeight.exists_natural_height_packet_comparison
  let A : Real := Real.exp (2 * C + 2) * replacementConstant
  have hA : 0 < A := by
    dsimp [A, replacementConstant]
    positivity
  refine Exists.intro A (And.intro hA ?_)
  intro K h Q n hK hh hhQ hKQ hQn hnQ hcut
  have hc := hSpec.2 K h Q n hK hh hhQ hKQ hQn hnQ hcut
  have hV := hybrid_packet_split_envelope K (h : Int) Q n hK hKQ
  have hKreal : (6 : Real) <= (K : Real) := by exact_mod_cast hK
  have h8 : 8 / (K : Real) <= 2 := by
    calc
      _ <= (8 : Real) / 6 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKreal
      _ <= _ := by norm_num
  calc
    _ <= Real.exp (2 * C + 8 / (K : Real)) * hybridPacket K (h : Int) Q n := hc.2
    _ <= Real.exp (2 * C + 8 / (K : Real)) *
        (replacementConstant * (Real.log (Q : Real)) ^ 2 * (Real.log (K : Real)) ^ 2) :=
      mul_le_mul_of_nonneg_left hV (Real.exp_pos _).le
    _ <= Real.exp (2 * C + 2) *
        (replacementConstant * (Real.log (Q : Real)) ^ 2 * (Real.log (K : Real)) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (by linarith only [h8]))
        (by unfold replacementConstant; positivity)
    _ = _ := by dsimp [A]; ring

end PrimeFactorOscillations.FiniteFieldIntegerAmplitude
