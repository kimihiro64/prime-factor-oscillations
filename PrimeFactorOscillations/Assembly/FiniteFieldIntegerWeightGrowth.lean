/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerCrestUniform
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerGapProfile

/-!
# Lower weights on actual integer prime pairs

The full opening masks equal one on prime pairs above the cutoff. Every
core row is at least one, and the flat tail rows retain a two-power Mertens
supply. The logarithmic shift-divisor budget is uniform in the shift.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerWeightGrowth
attribute [local instance] Classical.propDecidable

open FiniteFieldIntegerMass
open FiniteFieldIntegerTail
open FiniteFieldIntegerExtrema
open FiniteFieldFrozenGrowth
open FiniteFieldIntegerCrestUniform
open FiniteFieldIntegerNaturalAmplitude
open Filter

theorem prime_pair_shift_even (h Q n : Nat) (hQ : 2 <= Q) (hQn : Q < n)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h)) : Dvd.dvd 2 h := by
  have hp := hn.eq_two_or_odd
  have hq := hnh.eq_two_or_odd
  apply Nat.dvd_of_mod_eq_zero
  omega

theorem prime_pair_residue_nonzero {Q : Nat} (q : BoundedModulus Q)
    (hq : Nat.Prime q.val) (P : Nat) (hP : Nat.Prime P) (hQP : Q < P) :
    Not ((P : ZMod q.val) = 0) := by
  intro hz
  have hd := (CharP.cast_eq_zero_iff (ZMod q.val) q.val P).mp hz
  have hqQ := (Finset.mem_Icc.mp q.property).2
  cases (Nat.dvd_prime hP).mp hd with
  | inl he => exact hq.ne_one he
  | inr he => omega

theorem prime_pair_mask_one {Q : Nat} (h n : Nat) (q : BoundedModulus Q)
    (hq : Nat.Prime q.val) (hQn : Q < n)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h)) :
    integerMask (h : Int) q (n : ZMod q.val) = 1 := by
  have hc := prime_pair_residue_nonzero q hq n hn hQn
  have hch : Not ((n : ZMod q.val) = -((h : Int) : ZMod q.val)) := by
    intro hz
    apply prime_pair_residue_nonzero q hq (n + h) hnh (by omega)
    have he : (n : ZMod q.val) + ((h : Int) : ZMod q.val) = 0 := by
      rw [hz]
      ring
    simpa only [Int.cast_natCast, Nat.cast_add] using he
  simp only [integerMask, ite_eq_right hc, ite_eq_right hch]

theorem actual_prime_pair_row_ge_one {Q : Nat} (h n : Nat) (q : BoundedModulus Q)
    (heven : Dvd.dvd 2 h) (hq : Nat.Prime q.val) (hQn : Q < n)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h)) :
    1 <= actualLocal (h : Int) q (n : ZMod q.val) := by
  have hsmall : q.val = 2 -> ((h : Int) : ZMod q.val) = 0 := by
    intro he
    have hd : Dvd.dvd q.val h := by rwa [he]
    simpa only [Int.cast_natCast] using
      (CharP.cast_eq_zero_iff (ZMod q.val) q.val h).mpr hd
  have hc := prime_pair_residue_nonzero q hq n hn hQn
  have hch : Not ((n : ZMod q.val) + ((h : Int) : ZMod q.val) = 0) := by
    intro hz
    apply prime_pair_residue_nonzero q hq (n + h) hnh (by omega)
    simpa only [Int.cast_natCast, Nat.cast_add] using hz
  exact actual_local_ge_one h q hq hsmall (n : ZMod q.val) hc hch

theorem flat_scalar_exp_lower (p : Nat) (hp : 7 <= p) :
    Real.exp (2 / (p : Real)) <= (p : Real) / ((p : Real) - 2) := by
  have hpr : (7 : Real) <= (p : Real) := by exact_mod_cast hp
  have hp0 : 0 < (p : Real) := by linarith only [hpr]
  have hp2 : 0 < (p : Real) - 2 := by linarith only [hpr]
  have he := Real.add_one_le_exp (-(2 / (p : Real)))
  have hh := mul_le_mul_of_nonneg_left he (Real.exp_pos (2 / (p : Real))).le
  have hid : Real.exp (2 / (p : Real)) * Real.exp (-(2 / (p : Real))) = 1 := by
    rw [<- Real.exp_add]
    simp
  rw [hid] at hh
  have hr : Real.exp (2 / (p : Real)) * ((p : Real) - 2) / (p : Real) <= 1 := by
    convert hh using 1
    field_simp [ne_of_gt hp0]
    ring
  have ht := mul_le_mul_of_nonneg_right hr hp0.le
  have hc : Real.exp (2 / (p : Real)) * ((p : Real) - 2) <= (p : Real) := by
    convert ht using 1 <;> field_simp [ne_of_gt hp0]
  calc
    _ = (Real.exp (2 / (p : Real)) * ((p : Real) - 2)) / ((p : Real) - 2) := by
      field_simp [ne_of_gt hp2]
    _ <= _ := div_le_div_of_nonneg_right hc hp2.le

def lowerExponent (K h p : Nat) : Real :=
  if Nat.Prime p /\ K < p /\ Not (Dvd.dvd p h) then 2 / (p : Real) else 0

theorem hybrid_prime_pair_row_lower {Q : Nat} (K h n : Nat) (q : BoundedModulus Q)
    (hK : 6 <= K) (heven : Dvd.dvd 2 h) (hQn : Q < n)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h)) :
    Real.exp (lowerExponent K h q.val) <=
      hybridLocal K (h : Int) q (n : ZMod q.val) := by
  by_cases hp : Nat.Prime q.val
  . have hm := prime_pair_mask_one h n q hp hQn hn hnh
    by_cases hk : q.val <= K
    . have hnot : Not (K < q.val) := by omega
      have hr := actual_prime_pair_row_ge_one h n q heven hp hQn hn hnh
      simpa only [lowerExponent, hnot, and_false, false_and, ite_false,
        Real.exp_zero, hybridLocal, ite_eq_left hp, ite_eq_left hk] using hr
    . have h7 : 7 <= q.val := by omega
      have hqr : (7 : Real) <= (q.val : Real) := by exact_mod_cast h7
      by_cases hd : Dvd.dvd q.val h
      . have hz : ((h : Int) : ZMod q.val) = 0 := by
          simpa only [Int.cast_natCast] using
            (CharP.cast_eq_zero_iff (ZMod q.val) q.val h).mpr hd
        simp only [lowerExponent, not_true_eq_false, hd, and_false, ite_false,
          Real.exp_zero, hybridLocal, ite_eq_left hp, ite_eq_right hk, flatFallback, ite_eq_left hz, hm, mul_one]
        exact (one_le_div (show 0 < (q.val : Real) - 1 by linarith only [hqr])).mpr
          (by linarith)
      . have hz : Not (((h : Int) : ZMod q.val) = 0) := by
          intro he
          apply hd
          apply (CharP.cast_eq_zero_iff (ZMod q.val) q.val h).mp
          simpa only [Int.cast_natCast] using he
        have hlt : K < q.val := by omega
        simp only [lowerExponent, ite_eq_left (And.intro hp (And.intro hlt hd)),
          hybridLocal, ite_eq_left hp, ite_eq_right hk, flatFallback, ite_eq_right hz, hm, mul_one]
        exact flat_scalar_exp_lower q.val h7
  . simp only [lowerExponent, hp, false_and, ite_false, Real.exp_zero,
      hybridLocal, le_refl]

theorem hybrid_prime_pair_exp_lower (K h Q n : Nat)
    (hK : 6 <= K) (heven : Dvd.dvd 2 h) (hQn : Q < n)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h)) :
    Real.exp (2 * (tailPrimeSet K h Q).sum (fun p => (1 : Real) / (p : Real))) <=
      hybridPacket K (h : Int) Q n := by
  have hid : (Finset.Icc 1 Q).sum (lowerExponent K h) =
      2 * (tailPrimeSet K h Q).sum (fun p => (1 : Real) / (p : Real)) := by
    unfold lowerExponent tailPrimeSet
    rw [<- Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  calc
    _ = Real.exp ((Finset.Icc 1 Q).sum (lowerExponent K h)) := by rw [hid]
    _ = (Finset.Icc 1 Q).prod (fun p => Real.exp (lowerExponent K h p)) :=
      Real.exp_sum _ _
    _ = (Finset.Icc 1 Q).attach.prod (fun q => Real.exp (lowerExponent K h q.val)) :=
      (Finset.prod_attach _ _).symm
    _ <= hybridPacket K (h : Int) Q n := by
      apply real_product_le_of_nonneg
      . intro q _
        exact (Real.exp_pos _).le
      . intro q _
        exact hybrid_prime_pair_row_lower K h n q hK heven hQn hn hnh


theorem hybrid_prime_pair_log_lower (K h Q n : Nat)
    (hK : 12 <= K) (hKQ : K <= Q) (hh : 0 < h)
    (hshift : Real.log (h : Real) <= (K : Real))
    (heven : Dvd.dvd 2 h) (hQn : Q < n)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h)) :
    uniformGrowth * (Real.log (Q : Real) / Real.log (K : Real)) ^ 2 <=
      hybridPacket K (h : Int) Q n := by
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
  have hs : 2 * (Real.log (Real.log (Q : Real)) - Real.log (Real.log (K : Real))) -
      4 * mertensBudget - 2 / Real.log 2 <=
        2 * (tailPrimeSet K h Q).sum (fun p => (1 : Real) / (p : Real)) := by
    have ht : (2 : Real) / Real.log 2 = 2 * (1 / Real.log 2) := by ring
    rw [ht]
    linarith only [hm, hlQ, huK, hbudget]
  have heq : Real.exp (2 * (Real.log (Real.log (Q : Real)) -
      Real.log (Real.log (K : Real))) - 4 * mertensBudget - 2 / Real.log 2) =
        uniformGrowth * (Real.log (Q : Real) / Real.log (K : Real)) ^ 2 := by
    rw [show 2 * (Real.log (Real.log (Q : Real)) - Real.log (Real.log (K : Real))) -
      4 * mertensBudget - 2 / Real.log 2 =
        (-4 * mertensBudget - 2 / Real.log 2) +
          2 * (Real.log (Real.log (Q : Real)) - Real.log (Real.log (K : Real))) by ring,
      Real.exp_add, exp_log_cutoff_ratio K Q hK hKQ]
    rfl
  rw [<- heq]
  exact (Real.exp_le_exp.mpr hs).trans
    (hybrid_prime_pair_exp_lower K h Q n (by omega) heven hQn hn hnh)

theorem natural_core_log_supply (Q : Nat) (hlog : 1 <= Real.log (Q : Real)) :
    And (12 <= naturalCore Q) (Real.log (Q : Real) <= ((naturalCore Q : Nat) : Real)) := by
  have hp64 : (10 : Real) ^ 64 <= (10 * Real.log (Q : Real)) ^ 64 := by
    gcongr
    linarith only [hlog]
  have hceil : (10 * Real.log (Q : Real)) ^ 64 <= ((naturalCore Q : Nat) : Real) :=
    Nat.le_ceil _
  have hp63 : (1 : Real) <= (10 * Real.log (Q : Real)) ^ 63 := by
    calc
      _ = (1 : Real) ^ 63 := by norm_num
      _ <= _ := by gcongr; linarith only [hlog]
  have hm := mul_le_mul_of_nonneg_right hp63
    (show 0 <= 10 * Real.log (Q : Real) by linarith only [hlog])
  have hbase : Real.log (Q : Real) <= (10 * Real.log (Q : Real)) ^ 64 := by
    calc
      _ <= 10 * Real.log (Q : Real) := by linarith only [hlog]
      _ <= (10 * Real.log (Q : Real)) ^ 63 * (10 * Real.log (Q : Real)) := by
        simpa only [one_mul] using hm
      _ = _ := (pow_succ _ 63).symm
  refine And.intro ?_ (hbase.trans hceil)
  have h12 : (12 : Real) <= ((naturalCore Q : Nat) : Real) := by
    calc
      _ <= (10 : Real) ^ 64 := by norm_num
      _ <= _ := hp64.trans hceil
  exact_mod_cast h12

theorem exists_uniform_prime_pair_weight_bounds :
    exists c B : Real, And (0 < c) (And (0 < B) (exists Q0 : Nat,
      forall Q : Nat, Q0 <= Q ->
        And (1 <= Real.log (Q : Real)) (And (1 <= Real.log (Real.log (Q : Real)))
          (forall h n : Nat, 0 < h -> h < Q -> Q < n -> n + h <= Q * Q ->
            Nat.Prime n -> Nat.Prime (n + h) ->
            And
              (c * (Real.log (Q : Real)) ^ 2 / (Real.log (Real.log (Q : Real))) ^ 2 <=
                actualPacket (h : Int) Q n)
              (actualPacket (h : Int) Q n <=
                B * (Real.log (Q : Real)) ^ 2 * (Real.log (Real.log (Q : Real))) ^ 2))))) := by
  let C : Real := Classical.choose FiniteFieldIntegerHeight.exists_natural_height_packet_comparison
  have hC := Classical.choose_spec FiniteFieldIntegerHeight.exists_natural_height_packet_comparison
  let B : Real := Classical.choose exists_uniform_natural_height_amplitude
  have hB := Classical.choose_spec exists_uniform_natural_height_amplitude
  let QB : Nat := Classical.choose hB.2
  have hQB := Classical.choose_spec hB.2
  let Qfit : Nat := Classical.choose eventually_natural_core_fits
  have hfit := Classical.choose_spec eventually_natural_core_fits
  let A : Real := Real.exp (-(2 * C) - 3) * uniformGrowth
  let c : Real := A / 641 ^ 2
  have hA : 0 < A := by dsimp [A, uniformGrowth]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine Exists.intro c (Exists.intro B (And.intro hc (And.intro hB.1
    (Exists.intro (max QB Qfit) ?_))))
  intro Q hQQ
  have hf := hfit Q (le_trans (le_max_right _ _) hQQ)
  refine And.intro hf.2.1 (And.intro hf.2.2.1 ?_)
  intro h n hh hhQ hQn hnQ hn hnh
  have hK := natural_core_log_supply Q hf.2.1
  have hKR : (6 : Real) <= ((naturalCore Q : Nat) : Real) := by exact_mod_cast (show 6 <= naturalCore Q by omega)
  have hQpos : 0 < (Q : Real) := by exact_mod_cast (show 0 < Q by have ht := hf.1; omega)
  have hhpos : 0 < (h : Real) := by exact_mod_cast hh
  have hshift : Real.log (h : Real) <= ((naturalCore Q : Nat) : Real) :=
    (Real.log_le_log hhpos (by exact_mod_cast hhQ.le)).trans hK.2
  have heven := prime_pair_shift_even h Q n (by have ht := hf.1; omega) hQn hn hnh
  have hV := hybrid_prime_pair_log_lower (naturalCore Q) h Q n hK.1 hf.2.2.2
    hh hshift heven hQn hn hnh
  have hcomp := hC.2 (naturalCore Q) h Q n (by omega) hh hhQ hf.2.2.2 hQn hnQ
    (natural_core_covers_level h Q hh hhQ hf.2.1)
  have h18 : 18 / ((naturalCore Q : Nat) : Real) <= 3 := by
    calc
      _ <= (18 : Real) / 6 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKR
      _ = _ := by norm_num
  have hlow : A * (Real.log (Q : Real) / Real.log ((naturalCore Q : Nat) : Real)) ^ 2 <=
      actualPacket (h : Int) Q n := by
    calc
      _ = Real.exp (-(2 * C) - 3) *
          (uniformGrowth * (Real.log (Q : Real) / Real.log ((naturalCore Q : Nat) : Real)) ^ 2) := by
        dsimp [A]
        ring
      _ <= Real.exp (-(2 * C) - 3) * hybridPacket (naturalCore Q) (h : Int) Q n :=
        mul_le_mul_of_nonneg_left hV (Real.exp_pos _).le
      _ <= Real.exp (-(2 * C) - 18 / ((naturalCore Q : Nat) : Real)) *
          hybridPacket (naturalCore Q) (h : Int) Q n :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [h18]))
          (hybrid_packet_nonneg _ _ _ _)
      _ <= _ := hcomp.1
  have hLKpos : 0 < Real.log ((naturalCore Q : Nat) : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < naturalCore Q by omega))
  have hLLpos : 0 < Real.log (Real.log (Q : Real)) := by linarith only [hf.2.2.1]
  have hLK := natural_core_log_bound Q hf.2.1 hf.2.2.1
  have hs := mul_self_le_mul_self hLKpos.le hLK
  have hpow : (Real.log ((naturalCore Q : Nat) : Real)) ^ 2 <=
      (641 * Real.log (Real.log (Q : Real))) ^ 2 := by nlinarith only [hs]
  have hr := div_le_div_of_nonneg_left (sq_nonneg (Real.log (Q : Real)))
    (sq_pos_of_pos hLKpos) hpow
  have hscaled := mul_le_mul_of_nonneg_left hr hA.le
  have hfinal : c * (Real.log (Q : Real)) ^ 2 / (Real.log (Real.log (Q : Real))) ^ 2 <=
      A * (Real.log (Q : Real) / Real.log ((naturalCore Q : Nat) : Real)) ^ 2 := by
    dsimp only [c]
    convert hscaled using 1 <;> field_simp [ne_of_gt hLKpos, ne_of_gt hLLpos] <;> ring
  exact And.intro (hfinal.trans hlow)
    (hQB Q (le_trans (le_max_left _ _) hQQ) h n hh hhQ hQn hnQ)

end PrimeFactorOscillations.FiniteFieldIntegerWeightGrowth
