/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerCrestQuantitative

/-!
# Shift-uniform height of full integer crests

The exceptional prime divisors of the shift have a logarithmic budget.
At the exact conductor core this gives an absolute lower likelihood ratio,
which can be compared with the proved one-character upper ratio.
All local rows, including exceptional and small primes, are retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerCrestUniform

attribute [local instance] Classical.propDecidable

open FiniteFieldIntegerMass
open FiniteFieldIntegerTail
open FiniteFieldIntegerPrimes
open FiniteFieldIntegerExtrema
open FiniteFieldFrozenGrowth
open FiniteFieldOneCharacterHeight

theorem prime_divisor_log_budget (h : Nat) (hh : 0 < h) :
    h.primeFactors.sum (fun p => Real.log (p : Real)) <= Real.log (h : Real) := by
  have hprod : 0 < h.primeFactors.prod (fun p => p) := by
    apply Finset.prod_pos
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1.pos
  have hle := Nat.le_of_dvd hh (Nat.prod_primeFactors_dvd h)
  have hreal : ((h.primeFactors.prod (fun p => p) : Nat) : Real) <= (h : Real) := by
    exact_mod_cast hle
  have hpos : 0 < ((h.primeFactors.prod (fun p => p) : Nat) : Real) := by
    exact_mod_cast hprod
  have hlog := Real.log_le_log hpos hreal
  rw [Nat.cast_prod, Real.log_prod] at hlog
  . exact hlog
  . intro p hp
    exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero

theorem prime_divisor_tail_budget (K h : Nat) (hK : 0 < K) (hh : 0 < h) :
    (h.primeFactors.filter (fun p => K < p)).sum (fun p => (1 : Real) / (p : Real)) <=
      Real.log (h : Real) / ((K : Real) * Real.log 2) := by
  let T := h.primeFactors.filter (fun p => K < p)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKR : 0 < (K : Real) := by exact_mod_cast hK
  have hpoint : forall p, Membership.mem T p ->
      (1 : Real) / (p : Real) <= Real.log (p : Real) / ((K : Real) * Real.log 2) := by
    intro p hp
    have hd := Finset.mem_filter.mp hp
    have hp2 := (Nat.mem_primeFactors.mp hd.1).1.two_le
    have hpR : 0 < (p : Real) := by exact_mod_cast (show 0 < p by omega)
    have hlogp : Real.log 2 <= Real.log (p : Real) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
    have hkp : (K : Real) <= (p : Real) := by exact_mod_cast (Nat.le_of_lt hd.2)
    have hlogratio : 1 <= Real.log (p : Real) / Real.log 2 :=
      (one_le_div hlog2).mpr hlogp
    calc
      _ <= 1 / (K : Real) := one_div_le_one_div_of_le hKR hkp
      _ = 1 * (1 / (K : Real)) := by ring
      _ <= (Real.log (p : Real) / Real.log 2) * (1 / (K : Real)) :=
        mul_le_mul_of_nonneg_right hlogratio (by positivity)
      _ = _ := by ring
  have hs := Finset.sum_le_sum hpoint
  have hsub : T <= h.primeFactors := Finset.filter_subset _ _
  have hlogs : T.sum (fun p => Real.log (p : Real)) <=
      h.primeFactors.sum (fun p => Real.log (p : Real)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p hp _ => Real.log_nonneg
        (by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.one_lt.le))
  have hb := prime_divisor_log_budget h hh
  calc
    _ <= T.sum (fun p => Real.log (p : Real) / ((K : Real) * Real.log 2)) := hs
    _ = T.sum (fun p => Real.log (p : Real)) / ((K : Real) * Real.log 2) :=
      (Finset.sum_div T (fun p => Real.log (p : Real)) ((K : Real) * Real.log 2)).symm
    _ <= Real.log (h : Real) / ((K : Real) * Real.log 2) :=
      div_le_div_of_nonneg_right (hlogs.trans hb) (mul_pos hKR hlog2).le

theorem tail_reciprocal_logarithmic_missing_mass (K h Q : Nat)
    (hK : 0 < K) (hh : 0 < h) (hKQ : K <= Q) :
    PrimeFactorUnimodality.reciprocalPrimeSumBelow (Q + 1) -
      PrimeFactorUnimodality.reciprocalPrimeSumBelow (K + 1) <=
        (tailPrimeSet K h Q).sum (fun p => (1 : Real) / (p : Real)) +
          Real.log (h : Real) / ((K : Real) * Real.log 2) := by
  let A := tailPrimeSet K h Q
  let T := h.primeFactors.filter (fun p => K < p)
  have hsub : allTailPrimes K Q <= Union.union A T := by
    intro p hp
    have hd := Finset.mem_filter.mp hp
    by_cases hdiv : Dvd.dvd p h
    . apply Finset.mem_union_right A
      exact Finset.mem_filter.mpr (And.intro
        (Nat.mem_primeFactors.mpr (And.intro hd.2.1
          (And.intro hdiv (Nat.ne_of_gt hh)))) hd.2.2)
    . exact Finset.mem_union_left T
        (Finset.mem_filter.mpr (And.intro hd.1
          (And.intro hd.2.1 (And.intro hd.2.2 hdiv))))
  have hfirst := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => (show (0 : Real) <= 1 / (p : Real) from by positivity))
  have hsum : (Union.union A T).sum (fun p => (1 : Real) / (p : Real)) +
      (Inter.inter A T).sum (fun p => (1 : Real) / (p : Real)) =
      A.sum (fun p => (1 : Real) / (p : Real)) +
        T.sum (fun p => (1 : Real) / (p : Real)) := Finset.sum_union_inter
  have hn : 0 <= (Inter.inter A T).sum (fun p => (1 : Real) / (p : Real)) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hb := prime_divisor_tail_budget K h hK hh
  have he := all_tail_reciprocal_sum K Q hKQ
  change _ <= A.sum (fun p => (1 : Real) / (p : Real)) +
    Real.log (h : Real) / ((K : Real) * Real.log 2)
  change T.sum (fun p => (1 : Real) / (p : Real)) <= _ at hb
  linarith only [hfirst, hsum, hn, hb, he]

def uniformGrowth : Real := Real.exp (-4 * mertensBudget - 2 / Real.log 2)

def comparisonCap (C : Real) : Real := Real.exp (C + 2 * mertensBudget + 2)

def uniformExponent (C : Real) : Real := min 1 (uniformGrowth / comparisonCap C) / 64

theorem uniform_exponent_pos (C : Real) : 0 < uniformExponent C := by
  unfold uniformExponent uniformGrowth comparisonCap
  exact div_pos (lt_min (by norm_num) (div_pos (Real.exp_pos _) (Real.exp_pos _)))
    (by norm_num)

theorem uniform_exponent_le (C : Real) : uniformExponent C <= 1 / 64 := by
  unfold uniformExponent
  exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

theorem uniform_tail_log_lower (K h Q n : Nat) (hK : 12 <= K)
    (hKQ : K <= Q) (hh : 0 < h) (hshift : Real.log (h : Real) <= (K : Real))
    (hrows : forall q : BoundedModulus Q,
      crestFactor h q.val <= actualLocal (h : Int) q (n : ZMod q.val)) :
    2 * (Real.log (Real.log (Q : Real)) - Real.log (Real.log (K : Real))) -
      4 * mertensBudget - 2 / Real.log 2 <= tailLogSum K (h : Int) Q n := by
  have hm := tail_reciprocal_logarithmic_missing_mass K h Q (by omega) hh hKQ
  have hlQ := reciprocal_prime_lower Q (by omega)
  have huK := reciprocal_prime_log_bound K (by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKR : 0 < (K : Real) := by exact_mod_cast (show 0 < K by omega)
  have hbudget : Real.log (h : Real) / ((K : Real) * Real.log 2) <= 1 / Real.log 2 := by
    calc
      _ = (Real.log (h : Real) / (K : Real)) / Real.log 2 := by rw [div_div]
      _ <= 1 / Real.log 2 :=
        div_le_div_of_nonneg_right ((div_le_one hKR).mpr hshift) hlog2.le
  have hlo := (envelope_sum_bounds K h Q hK hKQ).1
  have he := tail_log_sum_at_crest K h Q n hK hrows
  have htwo : (2 : Real) / Real.log 2 = 2 * (1 / Real.log 2) := by ring
  rw [htwo]
  linarith only [hm, hlQ, huK, hbudget, hlo, he]

theorem uniform_packet_ratio_lower (K h Q n : Nat) (hK : 12 <= K)
    (hKQ : K <= Q) (hh : 0 < h) (hshift : Real.log (h : Real) <= (K : Real))
    (hrows : forall q : BoundedModulus Q,
      crestFactor h q.val <= actualLocal (h : Int) q (n : ZMod q.val)) :
    uniformGrowth * (Real.log (Q : Real) / Real.log (K : Real)) ^ 2 <=
      actualPacket (h : Int) Q n / hybridPacket K (h : Int) Q n := by
  have hV := hybrid_packet_pos_at_crest K h Q n (by omega) hrows
  rw [packet_quotient_eq_exp_tail K Q n (h : Int) (by omega) hV]
  have hid : uniformGrowth * (Real.log (Q : Real) / Real.log (K : Real)) ^ 2 =
      Real.exp (2 * (Real.log (Real.log (Q : Real)) -
        Real.log (Real.log (K : Real))) - 4 * mertensBudget - 2 / Real.log 2) := by
    change uniformGrowth * normalizedRatio K Q = _
    rw [<- exp_log_cutoff_ratio K Q hK hKQ]
    unfold uniformGrowth
    rw [<- Real.exp_add]
    congr 1
    ring
  rw [hid]
  exact Real.exp_le_exp.mpr (uniform_tail_log_lower K h Q n hK hKQ hh hshift hrows)

theorem rows_give_quartic_crest (h Q n : Nat) (hh : 0 < h) (hQ : 13 <= Q)
    (hrows : forall q : BoundedModulus Q,
      crestFactor h q.val <= actualLocal (h : Int) q (n : ZMod q.val)) :
    lowerConstant h * (Real.log (Q : Real)) ^ 4 <= actualPacket (h : Int) Q n := by
  apply (crest_product_logarithmic_lower h Q hh hQ).trans
  unfold actualPacket
  rw [<- Finset.prod_attach (Finset.Icc 1 Q) (crestFactor h)]
  apply real_product_le_of_nonneg
  . intro q _
    exact le_trans (by norm_num) (crest_factor_ge_one h q.val)
  . intro q _
    exact hrows q


theorem uniform_crest_log_height (C : Real)
    (hBound : forall K h Q n : Nat, 6 <= K -> 0 < h -> 0 < n -> K <= Q ->
      (3 + Real.log ((4 * h * n : Nat) : Real)) ^ 64 <= ((K + 1 : Nat) : Real) ->
      actualPacket (h : Int) Q n <=
        Real.exp (C + 2 * mertensBudget + 8 / (K : Real)) *
          (Real.log (Q : Real) / Real.log (K : Real)) * hybridPacket K (h : Int) Q n)
    (h Q n : Nat) (hh : 0 < h) (hQ : 13 <= Q)
    (hrows : forall q : BoundedModulus Q,
      crestFactor h q.val <= actualLocal (h : Int) q (n : ZMod q.val)) :
    min 1 (uniformGrowth / comparisonCap C) * Real.log (Q : Real) <=
      Real.log 2 + 64 * Real.log (3 + Real.log ((4 * h * n : Nat) : Real)) := by
  have hn := FiniteFieldIntegerCrestQuantitative.crest_input_pos h Q n (by omega)
    (rows_give_quartic_crest h Q n hh hQ hrows)
  let H : Real := 3 + Real.log ((4 * h * n : Nat) : Real)
  let K : Nat := Nat.ceil (H ^ 64)
  have hhR : 0 < (h : Real) := by exact_mod_cast hh
  have hN1 : (1 : Real) <= ((4 * h * n : Nat) : Real) := by
    have hp : 0 < 4 * h * n := by positivity
    exact_mod_cast (show 1 <= 4 * h * n by omega)
  have hH3 : 3 <= H := by
    have ht := Real.log_nonneg hN1
    dsimp [H]
    linarith only [ht]
  have hH : 0 < H := by linarith only [hH3]
  have hH1 : 1 <= H := by linarith only [hH3]
  have hpow : (3 : Real) ^ 64 <= H ^ 64 := by gcongr
  have hX12 : (12 : Real) <= H ^ 64 := by
    calc
      _ <= (3 : Real) ^ 64 := by norm_num
      _ <= _ := hpow
  have hK12 : 12 <= K := by
    have ht : (12 : Real) <= (K : Real) := hX12.trans (Nat.le_ceil _)
    exact_mod_cast ht
  have hHpow : H <= H ^ 64 := by
    have h63 : (1 : Real) <= H ^ 63 := by
      calc
        _ = (1 : Real) ^ 63 := by norm_num
        _ <= _ := by gcongr
    calc
      _ = H * 1 := by ring
      _ <= H * H ^ 63 := mul_le_mul_of_nonneg_left h63 hH.le
      _ = _ := by ring
  have hshift : Real.log (h : Real) <= (K : Real) := by
    have hhn : (h : Real) <= ((4 * h * n : Nat) : Real) := by
      exact_mod_cast (show h <= 4 * h * n by nlinarith only [hn, hh])
    have hlog := Real.log_le_log hhR hhn
    have hHK : H <= (K : Real) := hHpow.trans (Nat.le_ceil _)
    dsimp [H] at hHK
    linarith only [hlog, hHK]
  have hLQ : 0 < Real.log (Q : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hLK : 0 < Real.log (K : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < K by omega))
  have hlog2 : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
  change min 1 (uniformGrowth / comparisonCap C) * Real.log (Q : Real) <=
    Real.log 2 + 64 * Real.log H
  by_cases hKQ : K <= Q
  . let R : Real := Real.log (Q : Real) / Real.log (K : Real)
    have hR : 0 < R := div_pos hLQ hLK
    have hV := hybrid_packet_pos_at_crest K h Q n (by omega) hrows
    have hlower := uniform_packet_ratio_lower K h Q n hK12 hKQ hh hshift hrows
    have hcut : H ^ 64 <= ((K + 1 : Nat) : Real) := by
      calc
        _ <= (K : Real) := Nat.le_ceil _
        _ <= _ := by simp only [Nat.cast_add, Nat.cast_one]; linarith
    have hu := hBound K h Q n (by omega) hh hn hKQ hcut
    have hKR : 0 < (K : Real) := by exact_mod_cast (show 0 < K by omega)
    have h8 : (8 : Real) / (K : Real) <= 2 := by
      have h1 : (8 : Real) / (K : Real) <= 1 :=
        (div_le_one hKR).mpr (by exact_mod_cast (show 8 <= K by omega))
      linarith only [h1]
    have he : Real.exp (C + 2 * mertensBudget + 8 / (K : Real)) <= comparisonCap C :=
      Real.exp_le_exp.mpr (by linarith only [h8])
    have hupperU : actualPacket (h : Int) Q n <=
        (comparisonCap C * R) * hybridPacket K (h : Int) Q n := by
      exact hu.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right he hR.le) hV.le)
    have hdiv : (actualPacket (h : Int) Q n / hybridPacket K (h : Int) Q n) *
        hybridPacket K (h : Int) Q n = actualPacket (h : Int) Q n := by
      field_simp [ne_of_gt hV]
    have hupper : actualPacket (h : Int) Q n / hybridPacket K (h : Int) Q n <=
        comparisonCap C * R := by
      by_contra hf
      have ht := mul_lt_mul_of_pos_right (lt_of_not_ge hf) hV
      rw [hdiv] at ht
      linarith only [ht, hupperU]
    change uniformGrowth * R ^ 2 <= _ at hlower
    have hcancel : uniformGrowth * R <= comparisonCap C := by
      by_contra hf
      have ht := mul_lt_mul_of_pos_right (lt_of_not_ge hf) hR
      nlinarith only [ht, hlower, hupper]
    have hRidentity : R * Real.log (K : Real) = Real.log (Q : Real) := by
      dsimp [R]
      field_simp [ne_of_gt hLK]
    have hscaled := mul_le_mul_of_nonneg_right hcancel hLK.le
    rw [mul_assoc, hRidentity] at hscaled
    have hratio : (uniformGrowth / comparisonCap C) * Real.log (Q : Real) <=
        Real.log (K : Real) := by
      have hE : 0 < comparisonCap C := Real.exp_pos _
      calc
        _ = (uniformGrowth * Real.log (Q : Real)) / comparisonCap C := by ring
        _ <= (comparisonCap C * Real.log (K : Real)) / comparisonCap C :=
          div_le_div_of_nonneg_right hscaled hE.le
        _ = _ := by field_simp [ne_of_gt hE]
    have hsmall : min 1 (uniformGrowth / comparisonCap C) * Real.log (Q : Real) <=
        Real.log (K : Real) :=
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hLQ.le).trans hratio
    have hceil := Nat.ceil_lt_add_one (pow_nonneg hH.le 64)
    have hKupper : (K : Real) <= 2 * H ^ 64 := by
      change (K : Real) < H ^ 64 + 1 at hceil
      linarith only [hceil, hX12]
    have hlogK := Real.log_le_log hKR hKupper
    rw [Real.log_mul (by norm_num) (pow_ne_zero 64 (ne_of_gt hH)), Real.log_pow] at hlogK
    exact hsmall.trans hlogK
  . have hlarge : (Q : Real) < H ^ 64 := by
      apply lt_of_not_ge
      intro hx
      exact hKQ (Nat.ceil_le.mpr hx)
    have hQR : 0 < (Q : Real) := by exact_mod_cast (show 0 < Q by omega)
    have hlogQ := Real.log_le_log hQR hlarge.le
    rw [Real.log_pow] at hlogQ
    norm_num at hlogQ
    have hsmall : min 1 (uniformGrowth / comparisonCap C) * Real.log (Q : Real) <=
        Real.log (Q : Real) := by
      calc
        _ <= 1 * Real.log (Q : Real) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hLQ.le
        _ = _ := by ring
    linarith only [hsmall, hlogQ, hlog2]

theorem exists_absolute_integer_crest_exponent :
    exists delta : Real, And (0 < delta) (And (delta <= 1 / 64)
      (forall h Q n : Nat, 0 < h -> 13 <= Q ->
        (forall q : BoundedModulus Q,
          crestFactor h q.val <= actualLocal (h : Int) q (n : ZMod q.val)) ->
        Real.exp ((Q : Real) ^ delta / 2 - 3) / (4 * (h : Real)) <= (n : Real))) := by
  let C : Real := Classical.choose exists_one_character_packet_comparison
  have hC := Classical.choose_spec exists_one_character_packet_comparison
  refine Exists.intro (uniformExponent C)
    (And.intro (uniform_exponent_pos C) (And.intro (uniform_exponent_le C) ?_))
  intro h Q n hh hQ hrows
  have hn := FiniteFieldIntegerCrestQuantitative.crest_input_pos h Q n (by omega)
    (rows_give_quartic_crest h Q n hh hQ hrows)
  have hhR : 0 < (h : Real) := by exact_mod_cast hh
  have hN : 0 < 4 * h * n := by positivity
  have hNR : 0 < ((4 * h * n : Nat) : Real) := by exact_mod_cast hN
  let H : Real := 3 + Real.log ((4 * h * n : Nat) : Real)
  have hH : 0 < H := by
    have ht : 0 <= Real.log ((4 * h * n : Nat) : Real) :=
      Real.log_nonneg (by exact_mod_cast (show 1 <= 4 * h * n by omega))
    dsimp [H]
    linarith only [ht]
  have hlog := uniform_crest_log_height C hC.2 h Q n hh hQ hrows
  have hlog2 : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
  have hscale : uniformExponent C * Real.log (Q : Real) <= Real.log 2 + Real.log H := by
    dsimp [uniformExponent, H]
    linarith only [hlog, hlog2]
  have hQR : 0 < (Q : Real) := by exact_mod_cast (show 0 < Q by omega)
  have hpower : (Q : Real) ^ (uniformExponent C) <= 2 * H := by
    rw [Real.rpow_def_of_pos hQR]
    calc
      _ <= Real.exp (Real.log 2 + Real.log H) :=
        Real.exp_le_exp.mpr (by linarith only [hscale])
      _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hH]
  have hprodlog : (Q : Real) ^ (uniformExponent C) / 2 - 3 <=
      Real.log ((4 * h * n : Nat) : Real) := by
    dsimp [H] at hpower
    linarith only [hpower]
  have he := Real.exp_le_exp.mpr hprodlog
  rw [Real.exp_log hNR] at he
  calc
    _ <= ((4 * h * n : Nat) : Real) / (4 * (h : Real)) :=
      div_le_div_of_nonneg_right he (by positivity)
    _ = (n : Real) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      field_simp [ne_of_gt hhR]

theorem exists_shift_uniform_integer_crest_family :
    exists delta : Real, And (0 < delta) (And (delta <= 1 / 64)
      (forall h : Nat, 0 < h -> Dvd.dvd 2 h ->
        exists a : Nat -> Nat, forall Q : Nat, 13 <= Q ->
          And (a Q < primePeriod Q)
            (And
              (forall t : Nat, forall q : BoundedModulus Q,
                crestFactor h q.val <=
                  actualLocal (h : Int) q ((a Q + primePeriod Q * t : Nat) : ZMod q.val))
              (And
                (forall t : Nat, lowerConstant h * (Real.log (Q : Real)) ^ 4 <=
                  actualPacket (h : Int) Q (a Q + primePeriod Q * t))
                (And
                  (forall n : Nat, actualPacket (h : Int) Q n <=
                    replacementConstant * (Real.log (Q : Real)) ^ 4)
                  (forall t : Nat, Real.exp ((Q : Real) ^ delta / 2 - 3) /
                    (4 * (h : Real)) <= ((a Q + primePeriod Q * t : Nat) : Real))))))) := by
  let delta : Real := Classical.choose exists_absolute_integer_crest_exponent
  have hd := Classical.choose_spec exists_absolute_integer_crest_exponent
  refine Exists.intro delta (And.intro hd.1 (And.intro hd.2.1 ?_))
  intro h hh heven
  let a : Nat -> Nat := fun Q => Classical.choose (exists_integer_crest_rows h Q heven)
  have ha : forall Q, a Q < primePeriod Q /\
      forall t : Nat, forall q : BoundedModulus Q,
        crestFactor h q.val <= actualLocal (h : Int) q ((a Q + primePeriod Q * t : Nat) : ZMod q.val) :=
    fun Q => Classical.choose_spec (exists_integer_crest_rows h Q heven)
  refine Exists.intro a ?_
  intro Q hQ
  exact And.intro (ha Q).1 (And.intro (ha Q).2 (And.intro
    (fun t => rows_give_quartic_crest h Q _ hh hQ ((ha Q).2 t))
    (And.intro
      (fun n => actual_packet_envelope (h : Int) Q n (by omega))
      (fun t => hd.2.2 h Q _ hh hQ ((ha Q).2 t)))))

end PrimeFactorOscillations.FiniteFieldIntegerCrestUniform
