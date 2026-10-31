/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerCrestUniform

/-!
# Vanishing relative transfer on actual integer prime-pair windows

A larger polylogarithmic core retains the decay in the proved joint
character estimate. On the nonzero support it gives a small signed tail;
on the zero support the exact factorization makes both packets zero.
The result is a multiplicative comparison uniform in the shift and in
every finite sample, without an interval-length error.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerWindowTransfer
attribute [local instance] Classical.propDecidable

open FiniteFieldIntegerTail
open FiniteFieldIntegerMass
open FiniteFieldIntegerPrimes
open FiniteFieldIntegerCharacter
open FiniteFieldIntegerHeight
open FiniteFieldIntegerNaturalAmplitude
open Filter

def preciseCore (Q : Nat) : Nat :=
  Nat.ceil ((10 * Real.log (Q : Real)) ^ 128)

def relativeError (C : Real) (Q : Nat) : Real :=
  (2 * C + 18) / (10 * Real.log (Q : Real)) ^ 2

theorem precise_core_ge_six (Q : Nat) (hlog : 1 <= Real.log (Q : Real)) :
    6 <= preciseCore Q := by
  have hb : (10 : Real) <= 10 * Real.log (Q : Real) := by linarith only [hlog]
  have hp : (10 : Real) ^ 128 <= (10 * Real.log (Q : Real)) ^ 128 := by gcongr
  have h6 : (6 : Real) <= (preciseCore Q : Real) := by
    calc
      _ <= (10 : Real) ^ 128 := by norm_num
      _ <= _ := hp
      _ <= _ := Nat.le_ceil _
  exact_mod_cast h6

theorem precise_core_ge_square (Q : Nat) (hlog : 1 <= Real.log (Q : Real)) :
    (10 * Real.log (Q : Real)) ^ 2 <= (preciseCore Q : Real) := by
  let L : Real := 10 * Real.log (Q : Real)
  have hL : 1 <= L := by dsimp [L]; linarith only [hlog]
  have h126 : (1 : Real) <= L ^ 126 := by
    calc
      _ = (1 : Real) ^ 126 := by norm_num
      _ <= _ := by gcongr
  calc
    _ = L ^ 2 * 1 := by ring
    _ <= L ^ 2 * L ^ 126 := mul_le_mul_of_nonneg_left h126 (sq_nonneg L)
    _ = L ^ 128 := by ring
    _ <= _ := Nat.le_ceil _

theorem precise_core_decay (L x : Real) (hL : 0 < L) (hcut : L ^ 128 <= x) :
    L ^ 2 * x ^ (-1 / 32 : Real) <= 1 / L ^ 2 := by
  have hid : L ^ 4 * (L ^ 128) ^ (-1 / 32 : Real) = 1 := by
    rw [<- Real.rpow_natCast L (128 : Nat), <- Real.rpow_mul hL.le]
    norm_num only [Nat.cast_ofNat]
    rw [<- Real.rpow_natCast L (4 : Nat), <- Real.rpow_add hL]
    norm_num
  have hs : L ^ 4 * x ^ (-1 / 32 : Real) <= 1 := by
    calc
      _ <= L ^ 4 * (L ^ 128) ^ (-1 / 32 : Real) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (pow_pos hL 128) hcut (by norm_num))
          (pow_nonneg hL.le 4)
      _ = 1 := hid
  calc
    _ = (L ^ 4 * x ^ (-1 / 32 : Real)) / L ^ 2 := by
      field_simp [ne_of_gt hL]
    _ <= _ := div_le_div_of_nonneg_right hs (sq_nonneg L)

theorem eventually_precise_core_fits :
    exists Q0 : Nat, forall Q : Nat, Q0 <= Q ->
      And (6 <= Q) (And (1 <= Real.log (Q : Real))
        (And (1 <= Real.log (Real.log (Q : Real))) (preciseCore Q <= Q))) := by
  have hNat : Tendsto (fun Q : Nat => (Q : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun Q : Nat => (10 * Real.log (Q : Real)) ^ 128 / (Q : Real))
      atTop (nhds 0) := by
    have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 128 (by norm_num)).comp hNat
    have hc := ht.const_mul ((10 : Real) ^ 128)
    simpa only [Function.comp_apply, one_mul, add_zero, mul_zero, mul_pow, mul_div_assoc] using hc
  have hsmall : Filter.Eventually
      (fun Q : Nat => (10 * Real.log (Q : Real)) ^ 128 / (Q : Real) < 1) atTop :=
    hlim.eventually (Iio_mem_nhds (by norm_num))
  have hlog := (Real.tendsto_log_atTop.comp hNat).eventually_ge_atTop 1
  have hloglog :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hNat)).eventually_ge_atTop 1
  have hsix : Filter.Eventually (fun Q : Nat => 6 <= Q) atTop :=
    Filter.eventually_atTop.mpr (Exists.intro 6 (fun Q hQ => hQ))
  apply Filter.eventually_atTop.mp
  apply (hsmall.and (hlog.and (hloglog.and hsix))).mono
  intro Q hQ
  refine And.intro hQ.2.2.2 (And.intro hQ.2.1 (And.intro hQ.2.2.1 ?_))
  apply Nat.ceil_le.mpr
  have hQR : 0 < (Q : Real) := by exact_mod_cast (show 0 < Q by omega)
  exact ((div_lt_one hQR).mp hQ.1).le

theorem relative_error_tendsto_zero (C : Real) :
    Tendsto (fun Q : Nat => relativeError C Q) atTop (nhds 0) := by
  have hNat : Tendsto (fun Q : Nat => (Q : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hNat)
  have hs := hi.pow 2
  have hc := hs.const_mul ((2 * C + 18) / (10 : Real) ^ 2)
  simpa [relativeError, mul_pow, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hc

theorem exists_precise_natural_height_comparison :
    exists C : Real, And (0 < C)
      (forall Q h n : Nat, 1 <= Real.log (Q : Real) -> preciseCore Q <= Q ->
        0 < h -> h < Q -> Q < n -> n + h <= Q * Q ->
        And
          (Real.exp (-relativeError C Q) * hybridPacket (preciseCore Q) (h : Int) Q n <=
            actualPacket (h : Int) Q n)
          (actualPacket (h : Int) Q n <=
            Real.exp (relativeError C Q) * hybridPacket (preciseCore Q) (h : Int) Q n)) := by
  let C : Real := Classical.choose exists_natural_height_joint_tail_bound
  have hC := Classical.choose_spec exists_natural_height_joint_tail_bound
  have hCpos : 0 < C := hC.1
  refine Exists.intro C (And.intro hCpos ?_)
  intro Q h n hlog hKQ hh hhQ hQn hnQ
  let K : Nat := preciseCore Q
  let L : Real := 10 * Real.log (Q : Real)
  have hK : 6 <= K := precise_core_ge_six Q hlog
  have hL : 0 < L := by dsimp [L]; linarith only [hlog]
  have hLK : L ^ 2 <= (K : Real) := precise_core_ge_square Q hlog
  have hfactor := full_packet_factorization K (h : Int) hK Q n
  have hV := hybrid_packet_nonneg K (h : Int) Q n
  by_cases hU : actualPacket (h : Int) Q n = 0
  . have hVzero : hybridPacket K (h : Int) Q n = 0 := by
      have ht : hybridPacket K (h : Int) Q n * Real.exp (tailLogSum K (h : Int) Q n) = 0 := by
        rw [<- hfactor]
        exact hU
      exact (mul_eq_zero.mp ht).resolve_right (Real.exp_ne_zero _)
    rw [hU]
    change And (Real.exp (-relativeError C Q) * hybridPacket K (h : Int) Q n <= 0)
      (0 <= Real.exp (relativeError C Q) * hybridPacket K (h : Int) Q n)
    simp only [hVzero, mul_zero, le_refl, and_self]
  . have hU0 : 0 <= actualPacket (h : Int) Q n := by
      unfold actualPacket
      apply Finset.prod_nonneg
      intro q _
      exact actual_local_nonneg (h : Int) q _
    have hUpos : 0 < actualPacket (h : Int) Q n := lt_of_le_of_ne hU0 (Ne.symm hU)
    have hpair := actual_packet_positive_gives_prime_pair h Q n (by omega) hQn hnQ hUpos
    have hband := tail_log_character_band K h Q n hK hKQ hQn hpair.1 hpair.2
    have hComplex := hC.2 h Q n hh (by omega) hhQ hQn hnQ hUpos
      (K + 1) (Q + 1) (by omega)
    have hlevel := uniform_log_level_bound h Q hh hhQ hlog
    have hcut : L ^ 128 <= ((K + 1 : Nat) : Real) := by
      calc
        _ <= (K : Real) := Nat.le_ceil _
        _ <= _ := by simp only [Nat.cast_add, Nat.cast_one]; linarith
    have hdecay := precise_core_decay L ((K + 1 : Nat) : Real) hL hcut
    have hcomplexSmall :
        norm (Finset.sum ((Finset.Ico (K + 1) (Q + 1)).filter Nat.Prime)
          (fun p => HSMul.hSMul (1 / (p : Real))
            (IntegerQuadraticCharacter.numeratorKernel (-((h : Int) * (n : Int))) p +
              IntegerQuadraticCharacter.numeratorKernel ((h : Int) * ((n + h : Nat) : Int)) p))) <=
            2 * C / L ^ 2 := by
      calc
        _ <= 2 * C * (3 + Real.log ((4 * h * (Q * Q) : Nat) : Real)) ^ 2 *
            ((K + 1 : Nat) : Real) ^ (-1 / 32 : Real) := hComplex
        _ <= 2 * C * L ^ 2 * ((K + 1 : Nat) : Real) ^ (-1 / 32 : Real) := by
          have hcpos := hC.1.le
          have hnonneg := hlevel.1
          have hupper := hlevel.2
          gcongr
        _ = (2 * C) * (L ^ 2 * ((K + 1 : Nat) : Real) ^ (-1 / 32 : Real)) := by ring
        _ <= (2 * C) * (1 / L ^ 2) :=
          mul_le_mul_of_nonneg_left hdecay (by positivity)
        _ = _ := by ring
    have hSignal : abs (primeCharacterSignal K h Q n) <= 2 * C / L ^ 2 := by
      rw [prime_signal_eq_re]
      exact (Complex.abs_re_le_norm _).trans hcomplexSmall
    have hs := abs_le.mp hSignal
    have hK0 : 0 < (K : Real) := by exact_mod_cast (show 0 < K by omega)
    have h18 : 18 / (K : Real) <= 18 / L ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos hL 2) hLK
    have h8 : (8 : Real) / (K : Real) <= 18 / L ^ 2 :=
      (div_le_div_of_nonneg_right (by norm_num : (8 : Real) <= 18) hK0.le).trans h18
    have hsum : 2 * C / L ^ 2 + 18 / L ^ 2 = relativeError C Q := by
      dsimp [relativeError, L]
      ring
    have hlo : -relativeError C Q <= tailLogSum K (h : Int) Q n := by
      rw [<- hsum]
      linarith only [hband.1, hs.1, h18]
    have hup : tailLogSum K (h : Int) Q n <= relativeError C Q := by
      rw [<- hsum]
      linarith only [hband.2, hs.2, h8]
    constructor
    . calc
        _ = hybridPacket K (h : Int) Q n * Real.exp (-relativeError C Q) := mul_comm _ _
        _ <= hybridPacket K (h : Int) Q n * Real.exp (tailLogSum K (h : Int) Q n) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlo) hV
        _ = _ := hfactor.symm
    . calc
        _ = hybridPacket K (h : Int) Q n * Real.exp (tailLogSum K (h : Int) Q n) := hfactor
        _ <= hybridPacket K (h : Int) Q n * Real.exp (relativeError C Q) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hup) hV
        _ = _ := mul_comm _ _


def actualWindowMass {N : Nat} (h Q : Nat) (x : Fin N -> Nat) (w : Fin N -> Real) : Real :=
  Finset.univ.sum (fun j => w j * actualPacket (h : Int) Q (x j))

def coreWindowMass {N : Nat} (h Q : Nat) (x : Fin N -> Nat) (w : Fin N -> Real) : Real :=
  Finset.univ.sum (fun j => w j * hybridPacket (preciseCore Q) (h : Int) Q (x j))

def signedWindowMass {N : Nat} (h Q : Nat) (x : Fin N -> Nat) (w : Fin N -> Real) : Real :=
  Finset.univ.sum (fun j => w j *
    (actualPacket (h : Int) Q (x j) - hybridPacket (preciseCore Q) (h : Int) Q (x j)))

theorem signed_window_mass_eq_sub {N : Nat} (h Q : Nat)
    (x : Fin N -> Nat) (w : Fin N -> Real) :
    signedWindowMass h Q x w = actualWindowMass h Q x w - coreWindowMass h Q x w := by
  simp only [signedWindowMass, actualWindowMass, coreWindowMass, mul_sub, Finset.sum_sub_distrib]

theorem exists_uniform_window_mass_transfer :
    exists C : Real, And (0 < C) (exists Q0 : Nat,
      forall Q : Nat, Q0 <= Q -> forall h : Nat, 0 < h -> h < Q ->
        forall N : Nat, forall x : Fin N -> Nat, forall w : Fin N -> Real,
          (forall j, Q < x j /\ x j + h <= Q * Q) ->
          (forall j, 0 <= w j) ->
          And
            (And
              (Real.exp (-relativeError C Q) * coreWindowMass h Q x w <= actualWindowMass h Q x w)
              (actualWindowMass h Q x w <= Real.exp (relativeError C Q) * coreWindowMass h Q x w))
            (And
              ((Real.exp (-relativeError C Q) - 1) * coreWindowMass h Q x w <= signedWindowMass h Q x w)
              (signedWindowMass h Q x w <= (Real.exp (relativeError C Q) - 1) * coreWindowMass h Q x w))) := by
  let C : Real := Classical.choose exists_precise_natural_height_comparison
  have hC := Classical.choose_spec exists_precise_natural_height_comparison
  let Q0 : Nat := Classical.choose eventually_precise_core_fits
  have hQ0 := Classical.choose_spec eventually_precise_core_fits
  refine Exists.intro C (And.intro hC.1 (Exists.intro Q0 ?_))
  intro Q hQQ h hh hhQ N x w hwindow hw
  have hfit := hQ0 Q hQQ
  have hp : forall j : Fin N,
      Real.exp (-relativeError C Q) * hybridPacket (preciseCore Q) (h : Int) Q (x j) <=
        actualPacket (h : Int) Q (x j) /\
      actualPacket (h : Int) Q (x j) <=
        Real.exp (relativeError C Q) * hybridPacket (preciseCore Q) (h : Int) Q (x j) :=
    fun j => hC.2 Q h (x j) hfit.2.1 hfit.2.2.2 hh hhQ (hwindow j).1 (hwindow j).2
  have hlo : Real.exp (-relativeError C Q) * coreWindowMass h Q x w <= actualWindowMass h Q x w := by
    unfold coreWindowMass actualWindowMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc
      _ = w j * (Real.exp (-relativeError C Q) *
          hybridPacket (preciseCore Q) (h : Int) Q (x j)) := by ring
      _ <= _ := mul_le_mul_of_nonneg_left (hp j).1 (hw j)
  have hup : actualWindowMass h Q x w <=
      Real.exp (relativeError C Q) * coreWindowMass h Q x w := by
    unfold coreWindowMass actualWindowMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc
      _ <= w j * (Real.exp (relativeError C Q) *
          hybridPacket (preciseCore Q) (h : Int) Q (x j)) :=
        mul_le_mul_of_nonneg_left (hp j).2 (hw j)
      _ = _ := by ring
  refine And.intro (And.intro hlo hup) ?_
  rw [signed_window_mass_eq_sub]
  constructor
  . nlinarith only [hlo]
  . nlinarith only [hup]

def pairIndices {N : Nat} (h : Nat) (x : Fin N -> Nat) : Finset (Fin N) :=
  Finset.univ.filter (fun j => Nat.Prime (x j) /\ Nat.Prime (x j + h))

theorem exists_uniform_prime_pair_count_transfer :
    exists C : Real, And (0 < C) (exists B : Real, And (0 < B) (exists Q0 : Nat,
      forall Q : Nat, Q0 <= Q ->
        And
          (And (6 <= Q) (And (1 <= Real.log (Q : Real))
            (And (1 <= Real.log (Real.log (Q : Real))) (preciseCore Q <= Q))))
          (forall h : Nat, 0 < h -> h < Q ->
            And
              (forall N : Nat, forall x : Fin N -> Nat, forall w : Fin N -> Real,
                (forall j, Q < x j /\ x j + h <= Q * Q) -> (forall j, 0 <= w j) ->
                And
                  (And
                    (Real.exp (-relativeError C Q) * coreWindowMass h Q x w <= actualWindowMass h Q x w)
                    (actualWindowMass h Q x w <= Real.exp (relativeError C Q) * coreWindowMass h Q x w))
                  (And
                    ((Real.exp (-relativeError C Q) - 1) * coreWindowMass h Q x w <= signedWindowMass h Q x w)
                    (signedWindowMass h Q x w <= (Real.exp (relativeError C Q) - 1) * coreWindowMass h Q x w)))
              (forall N : Nat, forall x : Fin N -> Nat,
                (forall j, Q < x j /\ x j + h <= Q * Q) ->
                Real.exp (-relativeError C Q) * coreWindowMass h Q x (fun _ => 1) <=
                  (B * (Real.log (Q : Real)) ^ 2 * (Real.log (Real.log (Q : Real))) ^ 2) *
                    ((pairIndices h x).card : Real))))) := by
  let C : Real := Classical.choose exists_uniform_window_mass_transfer
  have hC := Classical.choose_spec exists_uniform_window_mass_transfer
  let Qmass : Nat := Classical.choose hC.2
  have hmass := Classical.choose_spec hC.2
  let B : Real := Classical.choose exists_uniform_natural_height_amplitude
  have hB := Classical.choose_spec exists_uniform_natural_height_amplitude
  let Qamp : Nat := Classical.choose hB.2
  have hamp := Classical.choose_spec hB.2
  let Qfit : Nat := Classical.choose eventually_precise_core_fits
  have hfit := Classical.choose_spec eventually_precise_core_fits
  refine Exists.intro C (And.intro hC.1 (Exists.intro B
    (And.intro hB.1 (Exists.intro (max Qmass (max Qamp Qfit)) ?_))))
  intro Q hQQ
  have hqm : Qmass <= Q := le_trans (le_max_left _ _) hQQ
  have hqa : Qamp <= Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQQ
  have hqf : Qfit <= Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQQ
  refine And.intro (hfit Q hqf) ?_
  intro h hh hhQ
  refine And.intro (hmass Q hqm h hh hhQ) ?_
  intro N x hwindow
  have ht := hmass Q hqm h hh hhQ N x (fun _ => 1) hwindow (fun _ => by norm_num)
  let A : Real := B * (Real.log (Q : Real)) ^ 2 * (Real.log (Real.log (Q : Real))) ^ 2
  have hlocal : forall j : Fin N, actualPacket (h : Int) Q (x j) <=
      if Nat.Prime (x j) /\ Nat.Prime (x j + h) then A else 0 := by
    intro j
    by_cases hj : Nat.Prime (x j) /\ Nat.Prime (x j + h)
    . rw [ite_eq_left hj]
      exact hamp Q hqa h (x j) hh hhQ (hwindow j).1 (hwindow j).2
    . rw [ite_eq_right hj]
      apply le_of_not_gt
      intro hp
      exact hj (actual_packet_positive_gives_prime_pair h Q (x j) (by omega)
        (hwindow j).1 (hwindow j).2 hp)
  have hcount : actualWindowMass h Q x (fun _ => 1) <= A * ((pairIndices h x).card : Real) := by
    calc
      _ = Finset.univ.sum (fun j : Fin N => actualPacket (h : Int) Q (x j)) := by
        simp only [actualWindowMass, one_mul]
      _ <= Finset.univ.sum (fun j : Fin N =>
          if Nat.Prime (x j) /\ Nat.Prime (x j + h) then A else 0) :=
        Finset.sum_le_sum (fun j _ => hlocal j)
      _ = _ := by
        rw [<- Finset.sum_filter]
        simp [pairIndices, mul_comm]
  exact ht.1.1.trans hcount

theorem prime_pair_of_positive_core_mass {N : Nat} (Q h : Nat)
    (hlog : 1 <= Real.log (Q : Real)) (hQ : 1 <= Q)
    (x : Fin N -> Nat) (hwindow : forall j, Q < x j /\ x j + h <= Q * Q)
    (hmass : 0 < coreWindowMass h Q x (fun _ => 1)) :
    exists j : Fin N, Nat.Prime (x j) /\ Nat.Prime (x j + h) := by
  have hK := precise_core_ge_six Q hlog
  by_contra hnone
  have hVle : forall j : Fin N, hybridPacket (preciseCore Q) (h : Int) Q (x j) <= 0 := by
    intro j
    by_contra hf
    have hVpos : 0 < hybridPacket (preciseCore Q) (h : Int) Q (x j) := lt_of_not_ge hf
    have hfactor := full_packet_factorization (preciseCore Q) (h : Int) hK Q (x j)
    have hUpos : 0 < actualPacket (h : Int) Q (x j) := by
      rw [hfactor]
      exact mul_pos hVpos (Real.exp_pos _)
    exact hnone (Exists.intro j
      (actual_packet_positive_gives_prime_pair h Q (x j) hQ
        (hwindow j).1 (hwindow j).2 hUpos))
  have hsum : coreWindowMass h Q x (fun _ => 1) <= 0 := by
    unfold coreWindowMass
    apply Finset.sum_nonpos
    intro j _
    simpa only [one_mul] using hVle j
  linarith only [hmass, hsum]

end PrimeFactorOscillations.FiniteFieldIntegerWindowTransfer
