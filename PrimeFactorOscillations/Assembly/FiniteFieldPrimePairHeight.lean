/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerWeightGrowth

/-!
# Two-character comparison at the actual prime-pair height

Actual primality keeps both numerator characters nonprincipal beyond
the natural sieve window. Their common conductor level uses n+h rather
than Q squared. The complete factorization and all exceptional rows
are retained in the two-sided packet and amplitude comparisons.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldPrimePairHeight

open IntegerQuadraticCharacter
open FiniteFieldIntegerCharacter
open FiniteFieldIntegerHeight
open FiniteFieldIntegerMass
open FiniteFieldIntegerTail
open FiniteFieldIntegerAmplitude
open FiniteFieldIntegerCrestUniform
open FiniteFieldIntegerWeightGrowth

def pairHeightLevel (h n : Nat) : Real :=
  3 + Real.log ((4 * h * (n + h) : Nat) : Real)

theorem pair_height_level_pos (h n : Nat) (hh : 0 < h) (hn : 0 < n) :
    0 < pairHeightLevel h n := by
  have htpos : 0 < 4 * h * (n + h) := by positivity
  have ht : 1 <= 4 * h * (n + h) := by omega
  have hl := Real.log_nonneg (show (1 : Real) <= ((4 * h * (n + h) : Nat) : Real)
    from by exact_mod_cast ht)
  dsimp [pairHeightLevel]
  linarith only [hl]

theorem exists_prime_pair_joint_tail_bound :
    exists C : Real, And (0 < C)
      (forall h n : Nat, 0 < h -> 2 < n -> h < n ->
        Nat.Prime n -> Nat.Prime (n + h) ->
        forall Y X : Nat, 1 <= Y ->
          norm (Finset.sum ((Finset.Ico Y X).filter Nat.Prime)
            (fun p => HSMul.hSMul (1 / (p : Real))
              (numeratorKernel (-((h : Int) * (n : Int))) p +
                numeratorKernel ((h : Int) * ((n + h : Nat) : Int)) p))) <=
            2 * C * (pairHeightLevel h n) ^ 2 * (Y : Real) ^ (-1 / 32 : Real)) := by
  let C : Real := Classical.choose exists_prime_factor_numerator_tail_bound
  have hC := Classical.choose_spec exists_prime_factor_numerator_tail_bound
  refine Exists.intro C (And.intro hC.1 ?_)
  intro h n hh hn2 hhn hn hnh Y X hY
  have hA := hC.2 h n hh hn hn2 hhn (-((h : Int) * (n : Int)))
    (Or.inr rfl) Y X hY
  have hB := hC.2 h (n + h) hh hnh (by omega) (by omega)
    ((h : Int) * ((n + h : Nat) : Int)) (Or.inl rfl) Y X hY
  have hlow : 0 <= 3 + Real.log ((4 * h * n : Nat) : Real) := by
    have hnpos : 0 < n := by omega
    have htpos : 0 < 4 * h * n := by positivity
    have ht : 1 <= 4 * h * n := by omega
    have hl := Real.log_nonneg
      (show (1 : Real) <= ((4 * h * n : Nat) : Real) from by exact_mod_cast ht)
    linarith only [hl]
  have hprod : 0 < ((4 * h * n : Nat) : Real) := by positivity
  have hle : ((4 * h * n : Nat) : Real) <= ((4 * h * (n + h) : Nat) : Real) := by
    exact_mod_cast Nat.mul_le_mul_left (4 * h) (show n <= n + h by omega)
  have hl := Real.log_le_log hprod hle
  have hsq : (3 + Real.log ((4 * h * n : Nat) : Real)) ^ 2 <=
      (pairHeightLevel h n) ^ 2 := by
    dsimp [pairHeightLevel]
    nlinarith only [hlow, hl]
  have hA' := hA.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq hC.1.le) (Real.rpow_nonneg (Nat.cast_nonneg Y) _))
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib]
  calc
    _ <= _ := norm_add_le _ _
    _ <= _ := add_le_add hA' hB
    _ = _ := by dsimp [pairHeightLevel]; ring

theorem exists_prime_pair_packet_comparison :
    exists C : Real, And (0 < C)
      (forall K h Q n : Nat, 6 <= K -> K <= Q -> 0 < h -> h < Q -> Q < n ->
        Nat.Prime n -> Nat.Prime (n + h) ->
        (pairHeightLevel h n) ^ 64 <= ((K + 1 : Nat) : Real) ->
        And
          (Real.exp (-(2 * C) - 18 / (K : Real)) * hybridPacket K (h : Int) Q n <=
            actualPacket (h : Int) Q n)
          (actualPacket (h : Int) Q n <=
            Real.exp (2 * C + 8 / (K : Real)) * hybridPacket K (h : Int) Q n)) := by
  let C : Real := Classical.choose exists_prime_pair_joint_tail_bound
  have hC := Classical.choose_spec exists_prime_pair_joint_tail_bound
  refine Exists.intro C (And.intro hC.1 ?_)
  intro K h Q n hK hKQ hh hhQ hQn hn hnh hcut
  have ht := hC.2 h n hh (by omega) (by omega) hn hnh
    (K + 1) (Q + 1) (by omega)
  have hscale := power_cutoff_decay_le_one (pairHeightLevel h n)
    ((K + 1 : Nat) : Real) (pair_height_level_pos h n hh (by omega)) hcut
  have htail : norm (Finset.sum ((Finset.Ico (K + 1) (Q + 1)).filter Nat.Prime)
      (fun p => HSMul.hSMul (1 / (p : Real))
        (numeratorKernel (-((h : Int) * (n : Int))) p +
          numeratorKernel ((h : Int) * ((n + h : Nat) : Int)) p))) <= 2 * C := by
    calc
      _ <= 2 * C * (pairHeightLevel h n) ^ 2 *
          (((K + 1 : Nat) : Real) ^ (-1 / 32 : Real)) := ht
      _ = (2 * C) * ((pairHeightLevel h n) ^ 2 *
          (((K + 1 : Nat) : Real) ^ (-1 / 32 : Real))) := by ring
      _ <= 2 * C := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hscale (mul_nonneg (by norm_num) hC.1.le)
  have hsignal : abs (primeCharacterSignal K h Q n) <= 2 * C := by
    rw [prime_signal_eq_re]
    exact (Complex.abs_re_le_norm _).trans htail
  have hs := abs_le.mp hsignal
  have hb := tail_log_character_band K h Q n hK hKQ hQn hn hnh
  have hf := full_packet_factorization K (h : Int) hK Q n
  have hv := hybrid_packet_nonneg K (h : Int) Q n
  constructor
  . calc
      _ <= Real.exp (tailLogSum K (h : Int) Q n) * hybridPacket K (h : Int) Q n :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (by linarith only [hs.1, hb.1])) hv
      _ = _ := by rw [mul_comm, <- hf]
  . calc
      _ = Real.exp (tailLogSum K (h : Int) Q n) * hybridPacket K (h : Int) Q n := by
        rw [hf, mul_comm]
      _ <= _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
        (by linarith only [hs.2, hb.2])) hv

theorem exists_prime_pair_split_bounds :
    exists a b : Real, And (0 < a) (And (0 < b)
      (forall K h Q n : Nat, 12 <= K -> K <= Q -> 0 < h -> h < Q -> Q < n ->
        Nat.Prime n -> Nat.Prime (n + h) ->
        Real.log (h : Real) <= (K : Real) ->
        (pairHeightLevel h n) ^ 64 <= ((K + 1 : Nat) : Real) ->
        And
          (a * (Real.log (Q : Real) / Real.log (K : Real)) ^ 2 <=
            actualPacket (h : Int) Q n)
          (actualPacket (h : Int) Q n <=
            b * (Real.log (Q : Real)) ^ 2 * (Real.log (K : Real)) ^ 2))) := by
  let C : Real := Classical.choose exists_prime_pair_packet_comparison
  have hC := Classical.choose_spec exists_prime_pair_packet_comparison
  let a : Real := Real.exp (-(2 * C) - 3) * uniformGrowth
  let b : Real := Real.exp (2 * C + 2) * replacementConstant
  have ha : 0 < a := by dsimp [a, uniformGrowth]; positivity
  have hbp : 0 < b := by dsimp [b, replacementConstant]; positivity
  refine Exists.intro a (Exists.intro b (And.intro ha (And.intro hbp ?_)))
  intro K h Q n hK hKQ hh hhQ hQn hn hnh hshift hcut
  have hcomp := hC.2 K h Q n (by omega) hKQ hh hhQ hQn hn hnh hcut
  have heven := prime_pair_shift_even h Q n (by omega) hQn hn hnh
  have hVlo := hybrid_prime_pair_log_lower K h Q n hK hKQ hh hshift heven hQn hn hnh
  have hVhi := hybrid_packet_split_envelope K (h : Int) Q n (by omega) hKQ
  have hKR : (6 : Real) <= (K : Real) := by exact_mod_cast (show 6 <= K by omega)
  have h18 : 18 / (K : Real) <= 3 := by
    calc
      _ <= (18 : Real) / 6 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKR
      _ = _ := by norm_num
  have h8 : 8 / (K : Real) <= 2 := by
    calc
      _ <= (8 : Real) / 6 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKR
      _ <= _ := by norm_num
  constructor
  . calc
      _ = Real.exp (-(2 * C) - 3) *
          (uniformGrowth * (Real.log (Q : Real) / Real.log (K : Real)) ^ 2) := by
        dsimp [a]
        ring
      _ <= Real.exp (-(2 * C) - 3) * hybridPacket K (h : Int) Q n :=
        mul_le_mul_of_nonneg_left hVlo (Real.exp_pos _).le
      _ <= Real.exp (-(2 * C) - 18 / (K : Real)) * hybridPacket K (h : Int) Q n :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (by linarith only [h18])) (hybrid_packet_nonneg _ _ _ _)
      _ <= _ := hcomp.1
  . calc
      _ <= Real.exp (2 * C + 8 / (K : Real)) * hybridPacket K (h : Int) Q n := hcomp.2
      _ <= Real.exp (2 * C + 8 / (K : Real)) *
          (replacementConstant * (Real.log (Q : Real)) ^ 2 * (Real.log (K : Real)) ^ 2) :=
        mul_le_mul_of_nonneg_left hVhi (Real.exp_pos _).le
      _ <= Real.exp (2 * C + 2) *
          (replacementConstant * (Real.log (Q : Real)) ^ 2 * (Real.log (K : Real)) ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (by linarith only [h8])) (by unfold replacementConstant; positivity)
      _ = _ := by dsimp [b]; ring

end PrimeFactorOscillations.FiniteFieldPrimePairHeight
