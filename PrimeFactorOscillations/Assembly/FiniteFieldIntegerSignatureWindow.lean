/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerSignature
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerWindowTransfer
import PrimeFactorOscillations.Helpers.GenericOddMertens

/-!
# Reciprocal-prime windows for integer quadratic signatures

The unconditional Mertens estimate retains a positive logarithmic main term
on the square band. The existing polylogarithmic core tends to infinity,
so the finite signature certificate can be applied uniformly at large height.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter PrimeFactorUnimodality
open FiniteFieldIntegerWindowTransfer

theorem reciprocal_band_eq_sub (Y X : Nat) (hYX : Y <= X) :
    reciprocalBand Y X =
      reciprocalPrimeSumBelow X - reciprocalPrimeSumBelow Y := by
  simp only [reciprocalBand, reciprocalPrimeSumBelow, Nat.primesBelow,
    Finset.sum_filter]
  exact Finset.sum_Ico_eq_sub _ hYX

theorem reciprocal_square_band_lower (K : Nat) (hK : 2 <= K) :
    Real.log 2 - 2 * mertensErrorConstant / Real.log (K : Real) <=
      reciprocalBand (K + 1) (K * K + 1) := by
  have hK0 : (0 : Real) < K := by exact_mod_cast (by omega : 0 < K)
  have hl : 0 < Real.log (K : Real) := Real.log_pos (by exact_mod_cast hK)
  have hKK : 2 <= K * K := by nlinarith only [hK]
  have hlow := reciprocalPrimeSumBelow_lower_of_estimate
    hasMertensReciprocalPrimeEstimate hKK
  have hupp := reciprocalPrimeSumBelow_upper_of_estimate
    hasMertensReciprocalPrimeEstimate hK
  have hlog : Real.log ((K * K : Nat) : Real) = 2 * Real.log (K : Real) := by
    rw [Nat.cast_mul, Real.log_mul (ne_of_gt hK0) (ne_of_gt hK0)]
    ring
  have hloglog : Real.log (Real.log ((K * K : Nat) : Real)) =
      Real.log 2 + Real.log (Real.log (K : Real)) := by
    rw [hlog, Real.log_mul (by norm_num) (ne_of_gt hl)]
  have herror : mertensErrorConstant / Real.log ((K * K : Nat) : Real) <=
      mertensErrorConstant / Real.log (K : Real) := by
    rw [hlog]
    exact div_le_div_of_nonneg_left mertensErrorConstant_nonneg hl (by linarith)
  rw [reciprocal_band_eq_sub (K + 1) (K * K + 1) (by nlinarith only [hK])]
  rw [hloglog] at hlow
  rw [mul_div_assoc]
  linarith only [hlow, hupp, herror]

theorem eventually_reciprocal_square_band_positive :
    Filter.Eventually (fun K : Nat =>
      Real.log 2 / 2 <= reciprocalBand (K + 1) (K * K + 1)) atTop := by
  have hNat : Tendsto (fun K : Nat => (K : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hNat)
  have he : Tendsto (fun K : Nat =>
      2 * mertensErrorConstant / Real.log (K : Real)) atTop (nhds 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
      hi.const_mul (2 * mertensErrorConstant)
  have hpos : (0 : Real) < Real.log 2 / 2 := by positivity
  filter_upwards [he.eventually (Iio_mem_nhds hpos), eventually_ge_atTop (2 : Nat)]
    with K heK hK
  have hm := reciprocal_square_band_lower K hK
  linarith only [hm, heK]

theorem precise_core_tendsto_atTop :
    Tendsto preciseCore atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hNat : Tendsto (fun Q : Nat => (Q : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hNat
  filter_upwards [hlog.eventually_ge_atTop (b : Real), hlog.eventually_ge_atTop 1]
    with Q hb hQ
  change (b : Real) <= Real.log (Q : Real) at hb
  change 1 <= Real.log (Q : Real) at hQ
  have hs := precise_core_ge_square Q hQ
  have hl : Real.log (Q : Real) <= (10 * Real.log (Q : Real)) ^ 2 := by
    nlinarith only [sq_nonneg (Real.log (Q : Real) - 1), hQ]
  exact_mod_cast hb.trans (hl.trans hs)

theorem eventually_precise_core_square_fits :
    Filter.Eventually (fun Q : Nat => preciseCore Q * preciseCore Q < Q) atTop := by
  have hNat : Tendsto (fun Q : Nat => (Q : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hpoly (d : Nat) : Tendsto
      (fun Q : Nat => (10 * Real.log (Q : Real)) ^ d / (Q : Real)) atTop (nhds 0) := by
    have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 d (by norm_num)).comp hNat
    simpa only [Function.comp_apply, one_mul, add_zero, mul_zero, mul_pow,
      mul_div_assoc] using ht.const_mul ((10 : Real) ^ d)
  have hi : Tendsto (fun Q : Nat => 1 / (Q : Real)) atTop (nhds 0) := by
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hNat
  have ht := (hpoly 256).add (((hpoly 128).const_mul 2).add hi)
  have hsmall := ht.eventually
    (Iio_mem_nhds (by norm_num : (0 : Real) + (2 * 0 + 0) < 1))
  filter_upwards [hsmall, eventually_ge_atTop (1 : Nat)] with Q hs hQ
  have hQ0 : (0 : Real) < Q := by exact_mod_cast (by omega : 0 < Q)
  let L : Real := 10 * Real.log (Q : Real)
  have hceil : (preciseCore Q : Real) <= L ^ 128 + 1 := by
    exact (Nat.ceil_lt_add_one (pow_nonneg (by
      exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hQ))) 128)).le
  have hsq : (preciseCore Q : Real) ^ 2 <= (L ^ 128 + 1) ^ 2 := by
    gcongr
  have hid : (L ^ 128 + 1) ^ 2 / (Q : Real) =
      L ^ 256 / (Q : Real) + (2 * (L ^ 128 / (Q : Real)) + 1 / (Q : Real)) := by
    ring
  have hquot : (preciseCore Q : Real) ^ 2 / (Q : Real) < 1 := by
    calc
      _ <= (L ^ 128 + 1) ^ 2 / (Q : Real) :=
        div_le_div_of_nonneg_right hsq hQ0.le
      _ < 1 := by rw [hid]; exact hs
  have hresult := (div_lt_one hQ0).mp hquot
  simpa only [pow_two] using (show preciseCore Q ^ 2 < Q by exact_mod_cast hresult)

theorem signature_uniform_log_bound (H Q : Nat)
    (hH : 0 < H) (hHQ : H <= Q) (hQ : 4 <= Q)
    (hlog : 1 <= Real.log (Q : Real)) :
    3 + Real.log ((4 * H * H * (Q * Q) * (Q * Q) : Nat) : Real) <=
      10 * Real.log (Q : Real) := by
  have hH0 : (0 : Real) < H := by exact_mod_cast hH
  have hQ0 : (0 : Real) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hLH := Real.log_le_log hH0 (Nat.cast_le.mpr hHQ)
  have hL4 := Real.log_le_log (by norm_num : (0 : Real) < 4)
    (Nat.cast_le.mpr hQ)
  have hid : ((4 * H * H * (Q * Q) * (Q * Q) : Nat) : Real) =
      4 * (H : Real) ^ 2 * (Q : Real) ^ 4 := by push_cast; ring
  rw [hid, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [hLH, hL4, hlog]

theorem signature_uniform_cost_le (C : Real) (hC : 0 <= C) (H Q : Nat)
    (hH : 0 < H) (hHQ : H <= Q) (hQ : 4 <= Q)
    (hlog : 1 <= Real.log (Q : Real)) :
    C * (3 + Real.log ((4 * H * H * (Q * Q) * (Q * Q) : Nat) : Real)) ^ 2 *
      ((preciseCore Q + 1 : Nat) : Real) ^ (-1 / 32 : Real) <= relativeError C Q := by
  let L : Real := 10 * Real.log (Q : Real)
  have hL : 0 < L := by dsimp [L]; linarith only [hlog]
  have hlevel := signature_uniform_log_bound H Q hH hHQ hQ hlog
  have hconductor : (1 : Real) <=
      ((4 * H * H * (Q * Q) * (Q * Q) : Nat) : Real) := by
    have hQ0 : 0 < Q := by omega
    have hp : 0 < 4 * H * H * (Q * Q) * (Q * Q) := by positivity
    exact_mod_cast (show 1 <= 4 * H * H * (Q * Q) * (Q * Q) by omega)
  have hnon : 0 <= 3 +
      Real.log ((4 * H * H * (Q * Q) * (Q * Q) : Nat) : Real) := by
    have hl := Real.log_nonneg hconductor
    linarith only [hl]
  have hsq : (3 + Real.log ((4 * H * H * (Q * Q) * (Q * Q) : Nat) : Real)) ^ 2 <= L ^ 2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hlevel) (add_nonneg hnon hL.le)
    nlinarith only [hm]
  have hcut : L ^ 128 <= ((preciseCore Q + 1 : Nat) : Real) := by
    calc
      _ <= (preciseCore Q : Real) := Nat.le_ceil _
      _ <= _ := by simp only [Nat.cast_add, Nat.cast_one]; linarith
  have hdecay := precise_core_decay L ((preciseCore Q + 1 : Nat) : Real) hL hcut
  calc
    _ <= C * L ^ 2 * ((preciseCore Q + 1 : Nat) : Real) ^ (-1 / 32 : Real) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = C * (L ^ 2 * ((preciseCore Q + 1 : Nat) : Real) ^ (-1 / 32 : Real)) := by ring
    _ <= C * (1 / L ^ 2) := mul_le_mul_of_nonneg_left hdecay hC
    _ <= relativeError C Q := by
      dsimp only [relativeError, L]
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (by linarith only [hC]) (sq_nonneg _)

theorem eventually_uniform_signature_margin (H : Nat) (hH : 0 < H)
    (C : Real) (hC : 0 <= C) :
    Filter.Eventually (fun Q : Nat =>
      And (H < preciseCore Q + 1)
        (And (2 < preciseCore Q + 1)
          (And (preciseCore Q * preciseCore Q < Q)
            (C * (3 + Real.log ((4 * H * H * (Q * Q) * (Q * Q) : Nat) : Real)) ^ 2 *
              ((preciseCore Q + 1 : Nat) : Real) ^ (-1 / 32 : Real) <
                reciprocalBand (preciseCore Q + 1) (preciseCore Q * preciseCore Q + 1)))))
      atTop := by
  have hmass := precise_core_tendsto_atTop.eventually eventually_reciprocal_square_band_positive
  have herror := (relative_error_tendsto_zero C).eventually
    (Iio_mem_nhds (by positivity : (0 : Real) < Real.log 2 / 2))
  have hcore := precise_core_tendsto_atTop.eventually_ge_atTop (max H 3)
  have hfit : Filter.Eventually (fun Q : Nat =>
      6 <= Q /\ 1 <= Real.log (Q : Real) /\
        1 <= Real.log (Real.log (Q : Real)) /\ preciseCore Q <= Q) atTop :=
    eventually_atTop.mpr eventually_precise_core_fits
  filter_upwards [hmass, herror, hcore, hfit,
    eventually_precise_core_square_fits, eventually_ge_atTop H] with Q hm he hc hf hs hHQ
  have hcost := signature_uniform_cost_le C hC H Q hH hHQ (by omega) hf.2.1
  exact And.intro (by omega) (And.intro (by omega)
    (And.intro hs (hcost.trans_lt (he.trans_le hm))))

theorem eventually_prime_pair_signature_rigidity (H : Nat) (hH : 0 < H) :
    Filter.Eventually (fun Q : Nat =>
      forall n m h k : Nat,
        Nat.Prime n -> Nat.Prime (n + h) -> Nat.Prime m -> Nat.Prime (m + k) ->
        0 < h -> 0 < k -> h <= H -> k <= H ->
        Q < n -> Q < m -> n + h <= Q * Q -> m + k <= Q * Q ->
        (forall p : Nat, Nat.Prime p -> preciseCore Q < p ->
          p <= preciseCore Q * preciseCore Q ->
          And
            (IntegerQuadraticCharacter.numeratorKernel ((h : Int) * (n : Int)) p =
              IntegerQuadraticCharacter.numeratorKernel ((k : Int) * (m : Int)) p)
            (IntegerQuadraticCharacter.numeratorKernel ((h : Int) * ((n + h : Nat) : Int)) p =
              IntegerQuadraticCharacter.numeratorKernel ((k : Int) * ((m + k : Nat) : Int)) p)) ->
        And (n = m) (h = k)) atTop := by
  classical
  choose C hC hfinite using exists_finite_prime_pair_signature_rigidity
  filter_upwards [eventually_uniform_signature_margin H hH C hC.le] with Q hmargin
  intro n m h k hn hnh hm hmk hh hk hhH hkH hQn hQm hnQ hmQ hmatch
  apply hfinite H (Q * Q) n m h k (preciseCore Q + 1)
    (preciseCore Q * preciseCore Q + 1) hn hnh hm hmk hh hk hhH hkH
    hmargin.1 hmargin.2.1 (by omega) (by omega) hnQ hmQ hmargin.2.2.2
  intro p hp
  have hpdata := Finset.mem_filter.mp hp
  have hpband := Finset.mem_Ico.mp hpdata.1
  exact hmatch p hpdata.2 (by omega) (by omega)

end PrimeFactorOscillations.FiniteFieldIntegerSignature
