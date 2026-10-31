/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerGapWindows
import PrimeFactorOscillations.Proof.PrimeClassDeletion.RepairHellinger

/-!
# Normalized integer prime-pair profiles on genuine recurrence windows

The actual/core likelihood comparison controls a normalized finite
Hellinger energy quadratically, even after arbitrary nonnegative
reweighting with positive retained mass. Exact least-gap recurrence
supplies unbounded actual integer windows on which the profiles exist.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerGapProfile
attribute [local instance] Classical.propDecidable

open PrimeClassDeletion
open FiniteFieldIntegerTail
open FiniteFieldIntegerMass
open FiniteFieldIntegerExtrema
open FiniteFieldIntegerPrimes
open FiniteFieldIntegerWindowTransfer
open PrimeProfileRigidity
open Filter

def normalizedWeight {N : Nat} (u : Fin N -> Real) (j : Fin N) : Real :=
  u j / Finset.univ.sum u

def profileEnergy {N : Nat} (u v : Fin N -> Real) : Real :=
  Finset.univ.sum (fun j =>
    repairHellingerEnergy (normalizedWeight v j) (normalizedWeight u j) 0)

theorem normalized_weight_nonneg {N : Nat} (u : Fin N -> Real)
    (hu : forall j, 0 <= u j) (j : Fin N) : 0 <= normalizedWeight u j := by
  exact div_nonneg (hu j) (Finset.sum_nonneg (fun i _ => hu i))

theorem normalized_weights_sum_one {N : Nat} (u : Fin N -> Real)
    (hu : 0 < Finset.univ.sum u) :
    Finset.univ.sum (normalizedWeight u) = 1 := by
  unfold normalizedWeight
  rw [<- Finset.sum_div, div_self (ne_of_gt hu)]

theorem scalar_energy_le_square_ratio (a p q : Real) (ha : 1 <= a)
    (hp : 0 <= p) (hq : 0 <= q)
    (hpq : p <= a ^ 2 * q) (hqp : q <= a ^ 2 * p) :
    repairHellingerEnergy q p 0 <= (a - 1) ^ 2 * q := by
  have ha0 : 0 <= a := by linarith only [ha]
  have hrootpq := Real.sqrt_le_sqrt hpq
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha0] at hrootpq
  have hrootqp := Real.sqrt_le_sqrt hqp
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha0] at hrootqp
  unfold repairHellingerEnergy
  simp only [add_zero]
  by_cases h : q <= p
  . have hd : 0 <= Real.sqrt p - Real.sqrt q :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt h)
    have hb : Real.sqrt p - Real.sqrt q <= (a - 1) * Real.sqrt q := by
      nlinarith only [hrootpq]
    have hs := mul_self_le_mul_self hd hb
    calc
      _ <= ((a - 1) * Real.sqrt q) ^ 2 := by nlinarith only [hs]
      _ = _ := by rw [mul_pow, Real.sq_sqrt hq]
  . have hpqOrder : p <= q := (lt_of_not_ge h).le
    have hd : 0 <= Real.sqrt q - Real.sqrt p :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt hpqOrder)
    have hb : Real.sqrt q - Real.sqrt p <= (a - 1) * Real.sqrt p := by
      nlinarith only [hrootqp]
    have hs := mul_self_le_mul_self hd hb
    calc
      _ = (Real.sqrt q - Real.sqrt p) ^ 2 := by ring
      _ <= ((a - 1) * Real.sqrt p) ^ 2 := by nlinarith only [hs]
      _ = (a - 1) ^ 2 * p := by rw [mul_pow, Real.sq_sqrt hp]
      _ <= _ := mul_le_mul_of_nonneg_left hpqOrder (sq_nonneg (a - 1))

theorem normalized_reciprocal_comparison {N : Nat} (a : Real) (ha : 1 <= a)
    (u v : Fin N -> Real) (hu : forall j, 0 <= u j) (hv : forall j, 0 <= v j)
    (hV : 0 < Finset.univ.sum v)
    (hcomp : forall j, And (u j <= a * v j) (v j <= a * u j)) :
    And (0 < Finset.univ.sum u)
      (forall j, And (normalizedWeight u j <= a ^ 2 * normalizedWeight v j)
        (normalizedWeight v j <= a ^ 2 * normalizedWeight u j)) := by
  let SU : Real := Finset.univ.sum u
  let SV : Real := Finset.univ.sum v
  have hSV : 0 < SV := hV
  have ha0 : 0 <= a := by linarith only [ha]
  have hSU0 : 0 <= SU := Finset.sum_nonneg (fun j _ => hu j)
  have hSV0 : 0 <= SV := Finset.sum_nonneg (fun j _ => hv j)
  have hUV : SU <= a * SV := by
    dsimp [SU, SV]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => (hcomp j).1)
  have hVU : SV <= a * SU := by
    dsimp [SU, SV]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => (hcomp j).2)
  have hSU : 0 < SU := by
    by_contra hf
    have ht := mul_nonpos_of_nonneg_of_nonpos ha0 (le_of_not_gt hf)
    linarith only [ht, hVU, hV]
  refine And.intro hSU ?_
  intro j
  have hcrossUV : u j * SV <= a ^ 2 * v j * SU := by
    calc
      _ <= (a * v j) * (a * SU) :=
        mul_le_mul (hcomp j).1 hVU hSV0 (mul_nonneg ha0 (hv j))
      _ = _ := by ring
  have hcrossVU : v j * SU <= a ^ 2 * u j * SV := by
    calc
      _ <= (a * u j) * (a * SV) :=
        mul_le_mul (hcomp j).2 hUV hSU0 (mul_nonneg ha0 (hu j))
      _ = _ := by ring
  constructor
  . have ht : normalizedWeight u j * (SU * SV) <=
        (a ^ 2 * normalizedWeight v j) * (SU * SV) := by
      change (u j / SU) * (SU * SV) <= (a ^ 2 * (v j / SV)) * (SU * SV)
      calc
        _ = u j * SV := by field_simp [ne_of_gt hSU, ne_of_gt hSV]
        _ <= a ^ 2 * v j * SU := hcrossUV
        _ = _ := by field_simp [ne_of_gt hSU, ne_of_gt hSV]
    exact le_of_mul_le_mul_right ht (mul_pos hSU hV)
  . have ht : normalizedWeight v j * (SU * SV) <=
        (a ^ 2 * normalizedWeight u j) * (SU * SV) := by
      change (v j / SV) * (SU * SV) <= (a ^ 2 * (u j / SU)) * (SU * SV)
      calc
        _ = v j * SU := by field_simp [ne_of_gt hSU, ne_of_gt hSV]
        _ <= a ^ 2 * u j * SV := hcrossVU
        _ = _ := by field_simp [ne_of_gt hSU, ne_of_gt hSV]
    exact le_of_mul_le_mul_right ht (mul_pos hSU hV)

theorem profile_energy_le_square_ratio {N : Nat} (a : Real) (ha : 1 <= a)
    (u v : Fin N -> Real) (hu : forall j, 0 <= u j) (hv : forall j, 0 <= v j)
    (hV : 0 < Finset.univ.sum v)
    (hcomp : forall j, And (u j <= a * v j) (v j <= a * u j)) :
    And (0 < Finset.univ.sum u)
      (And (Finset.univ.sum (normalizedWeight u) = 1)
        (And (Finset.univ.sum (normalizedWeight v) = 1)
          (profileEnergy u v <= (a - 1) ^ 2))) := by
  have hc := normalized_reciprocal_comparison a ha u v hu hv hV hcomp
  have hnormU := normalized_weights_sum_one u hc.1
  have hnormV := normalized_weights_sum_one v hV
  refine And.intro hc.1 (And.intro hnormU (And.intro hnormV ?_))
  calc
    _ <= Finset.univ.sum (fun j => (a - 1) ^ 2 * normalizedWeight v j) := by
      apply Finset.sum_le_sum
      intro j _
      exact scalar_energy_le_square_ratio a _ _ ha
        (normalized_weight_nonneg u hu j) (normalized_weight_nonneg v hv j)
        (hc.2 j).1 (hc.2 j).2
    _ = _ := by rw [<- Finset.mul_sum, hnormV, mul_one]


def actualWeights {N : Nat} (h Q : Nat) (x : Fin N -> Nat) (w : Fin N -> Real) :
    Fin N -> Real := fun j => w j * actualPacket (h : Int) Q (x j)

def coreWeights {N : Nat} (h Q : Nat) (x : Fin N -> Nat) (w : Fin N -> Real) :
    Fin N -> Real := fun j => w j * hybridPacket (preciseCore Q) (h : Int) Q (x j)

def informationConstant (C : Real) : Real := 4 * ((2 * C + 18) / 100) ^ 2

def windowProfileControl (C : Real) (Q h : Nat) : Prop :=
  forall N : Nat, forall x : Fin N -> Nat, forall w : Fin N -> Real,
    (forall j, Q < x j /\ x j + h <= Q * Q) ->
    (forall j, 0 <= w j) -> 0 < coreWindowMass h Q x w ->
    And (0 < actualWindowMass h Q x w)
      (And
        (forall j, And (0 <= normalizedWeight (actualWeights h Q x w) j)
          (0 <= normalizedWeight (coreWeights h Q x w) j))
        (And (Finset.univ.sum (normalizedWeight (actualWeights h Q x w)) = 1)
          (And (Finset.univ.sum (normalizedWeight (coreWeights h Q x w)) = 1)
            (And
              (profileEnergy (actualWeights h Q x w) (coreWeights h Q x w) <=
                (Real.exp (relativeError C Q) - 1) ^ 2)
              (profileEnergy (actualWeights h Q x w) (coreWeights h Q x w) <=
                informationConstant C / (Real.log (Q : Real)) ^ 4)))))

theorem small_exp_energy (E : Real) (hE : 0 <= E) (hE1 : E <= 1) :
    (Real.exp E - 1) ^ 2 <= 4 * E ^ 2 := by
  have he := Real.abs_exp_sub_one_le (x := E) (by rw [abs_of_nonneg hE]; exact hE1)
  rw [abs_of_nonneg hE] at he
  have hs := mul_self_le_mul_self (abs_nonneg (Real.exp E - 1)) he
  nlinarith only [hs, sq_abs (Real.exp E - 1)]

theorem information_error_identity (C : Real) (Q : Nat)
    (hlog : 0 < Real.log (Q : Real)) :
    4 * (relativeError C Q) ^ 2 =
      informationConstant C / (Real.log (Q : Real)) ^ 4 := by
  unfold relativeError informationConstant
  field_simp [ne_of_gt hlog]
  ring

theorem exists_uniform_window_profile_control :
    exists C : Real, And (0 < C) (exists Q0 : Nat,
      forall Q : Nat, Q0 <= Q ->
        And
          (And (6 <= Q) (And (1 <= Real.log (Q : Real))
            (And (1 <= Real.log (Real.log (Q : Real))) (preciseCore Q <= Q))))
          (And (0 <= relativeError C Q) (And (relativeError C Q <= 1)
            (forall h : Nat, 0 < h -> h < Q -> windowProfileControl C Q h)))) := by
  let C : Real := Classical.choose exists_precise_natural_height_comparison
  have hC := Classical.choose_spec exists_precise_natural_height_comparison
  have hCpos : 0 < C := hC.1
  let Qfit : Nat := Classical.choose eventually_precise_core_fits
  have hfit := Classical.choose_spec eventually_precise_core_fits
  have hevent : Filter.Eventually (fun Q : Nat => relativeError C Q < 1) atTop :=
    (relative_error_tendsto_zero C).eventually (Iio_mem_nhds (by norm_num))
  let Qerr : Nat := Classical.choose (Filter.eventually_atTop.mp hevent)
  have herr := Classical.choose_spec (Filter.eventually_atTop.mp hevent)
  refine Exists.intro C (And.intro hCpos (Exists.intro (max Qfit Qerr) ?_))
  intro Q hQQ
  have hFQ : Qfit <= Q := le_trans (le_max_left _ _) hQQ
  have hEQ : Qerr <= Q := le_trans (le_max_right _ _) hQQ
  have hf := hfit Q hFQ
  have hE0 : 0 <= relativeError C Q := by unfold relativeError; positivity
  have hE1 : relativeError C Q <= 1 := (herr Q hEQ).le
  refine And.intro hf (And.intro hE0 (And.intro hE1 ?_))
  intro h hh hhQ N x w hwindow hw hmass
  let u : Fin N -> Real := actualWeights h Q x w
  let v : Fin N -> Real := coreWeights h Q x w
  let a : Real := Real.exp (relativeError C Q)
  have ha0 : 0 <= a := (Real.exp_pos _).le
  have ha : 1 <= a := by
    have ht := Real.exp_le_exp.mpr hE0
    simpa only [Real.exp_zero] using ht
  have hu : forall j, 0 <= u j := by
    intro j
    apply mul_nonneg (hw j)
    unfold actualPacket
    exact Finset.prod_nonneg (fun q _ => actual_local_nonneg (h : Int) q _)
  have hv : forall j, 0 <= v j :=
    fun j => mul_nonneg (hw j) (hybrid_packet_nonneg (preciseCore Q) (h : Int) Q _)
  have hab : a * Real.exp (-relativeError C Q) = 1 := by
    dsimp [a]
    rw [<- Real.exp_add]
    simp
  have hcomp : forall j, And (u j <= a * v j) (v j <= a * u j) := by
    intro j
    have hp := hC.2 Q h (x j) hf.2.1 hf.2.2.2 hh hhQ
      (hwindow j).1 (hwindow j).2
    have hupp : u j <= a * v j := by
      calc
        _ <= w j * (Real.exp (relativeError C Q) *
            hybridPacket (preciseCore Q) (h : Int) Q (x j)) :=
          mul_le_mul_of_nonneg_left hp.2 (hw j)
        _ = _ := by dsimp [u, v, actualWeights, coreWeights, a]; ring
    have hlow : Real.exp (-relativeError C Q) * v j <= u j := by
      calc
        _ = w j * (Real.exp (-relativeError C Q) *
            hybridPacket (preciseCore Q) (h : Int) Q (x j)) := by
          dsimp [v, coreWeights]
          ring
        _ <= _ := mul_le_mul_of_nonneg_left hp.1 (hw j)
    refine And.intro hupp ?_
    calc
      _ = a * (Real.exp (-relativeError C Q) * v j) := by rw [<- mul_assoc, hab, one_mul]
      _ <= _ := mul_le_mul_of_nonneg_left hlow ha0
  have he := profile_energy_le_square_ratio a ha u v hu hv hmass hcomp
  refine And.intro he.1 (And.intro
    (fun j => And.intro (normalized_weight_nonneg u hu j) (normalized_weight_nonneg v hv j))
    (And.intro he.2.1 (And.intro he.2.2.1 (And.intro he.2.2.2 ?_))))
  calc
    _ <= (a - 1) ^ 2 := he.2.2.2
    _ <= 4 * (relativeError C Q) ^ 2 := small_exp_energy _ hE0 hE1
    _ = _ := information_error_identity C Q (by have ht := hf.2.1; linarith only [ht])


theorem information_constant_pos (C : Real) (hC : 0 < C) : 0 < informationConstant C := by
  unfold informationConstant
  positivity

theorem information_bound_tendsto_zero (C : Real) :
    Tendsto (fun Q : Nat => informationConstant C / (Real.log (Q : Real)) ^ 4)
      atTop (nhds 0) := by
  have hNat : Tendsto (fun Q : Nat => (Q : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hNat)
  have hc := (hi.pow 4).const_mul (informationConstant C)
  simpa [div_eq_mul_inv] using hc

theorem exists_integer_least_gap_profile_frames :
    exists C : Real, And (0 < C) (exists Q0 : Nat,
      And
        (forall Q : Nat, Q0 <= Q ->
          And
            (And (6 <= Q) (And (1 <= Real.log (Q : Real))
              (And (1 <= Real.log (Real.log (Q : Real))) (preciseCore Q <= Q))))
            (And (0 <= relativeError C Q) (And (relativeError C Q <= 1)
              (forall h : Nat, 0 < h -> h < Q -> windowProfileControl C Q h))))
        (forall R : Nat, exists Q i : Nat, And (R <= Q) (And (Q0 <= Q)
          (And (FiniteFieldIntegerGapWindows.leastGapFrame Q i)
            (windowProfileControl C Q leastRecurringPrimeGap))))) := by
  let C : Real := Classical.choose exists_uniform_window_profile_control
  have hC := Classical.choose_spec exists_uniform_window_profile_control
  let Q0 : Nat := Classical.choose hC.2
  have hQ0 := Classical.choose_spec hC.2
  refine Exists.intro C (And.intro hC.1 (Exists.intro Q0 (And.intro hQ0 ?_)))
  intro R
  let Q : Nat := Classical.choose
    (FiniteFieldIntegerGapWindows.unbounded_least_gap_positive_windows (max R Q0))
  let i : Nat := Classical.choose (Classical.choose_spec
    (FiniteFieldIntegerGapWindows.unbounded_least_gap_positive_windows (max R Q0)))
  have hi : max R Q0 <= Q /\ FiniteFieldIntegerGapWindows.leastGapFrame Q i :=
    Classical.choose_spec (Classical.choose_spec
      (FiniteFieldIntegerGapWindows.unbounded_least_gap_positive_windows (max R Q0)))
  have hRQ : R <= Q := le_trans (le_max_left _ _) hi.1
  have hQQ : Q0 <= Q := le_trans (le_max_right _ _) hi.1
  have hHQ : leastRecurringPrimeGap < Q := hi.2.2.2.2.2.1
  have hprofile := (hQ0 Q hQQ).2.2.2 leastRecurringPrimeGap
    (by have ht := two_le_leastRecurringPrimeGap; omega) hHQ
  exact Exists.intro Q (Exists.intro i (And.intro hRQ
    (And.intro hQQ (And.intro hi.2 hprofile))))


theorem arbitrarily_accurate_least_gap_profiles (eps : Real) (heps : 0 < eps) (R : Nat) :
    exists Q i : Nat, And (R <= Q) (And (FiniteFieldIntegerGapWindows.leastGapFrame Q i)
      (forall N : Nat, forall x : Fin N -> Nat, forall w : Fin N -> Real,
        (forall j, Q < x j /\ x j + leastRecurringPrimeGap <= Q * Q) ->
        (forall j, 0 <= w j) ->
        0 < coreWindowMass leastRecurringPrimeGap Q x w ->
        profileEnergy (actualWeights leastRecurringPrimeGap Q x w)
          (coreWeights leastRecurringPrimeGap Q x w) <= eps)) := by
  let C : Real := Classical.choose exists_integer_least_gap_profile_frames
  have hC := Classical.choose_spec exists_integer_least_gap_profile_frames
  let Q0 : Nat := Classical.choose hC.2
  have hQ0 := Classical.choose_spec hC.2
  have hevent : Filter.Eventually
      (fun Q : Nat => informationConstant C / (Real.log (Q : Real)) ^ 4 < eps) atTop :=
    (information_bound_tendsto_zero C).eventually (Iio_mem_nhds heps)
  let Qeps : Nat := Classical.choose (Filter.eventually_atTop.mp hevent)
  have herr := Classical.choose_spec (Filter.eventually_atTop.mp hevent)
  let Q : Nat := Classical.choose (hQ0.2 (max R Qeps))
  let i : Nat := Classical.choose (Classical.choose_spec (hQ0.2 (max R Qeps)))
  have hi : max R Qeps <= Q /\ Q0 <= Q /\
      FiniteFieldIntegerGapWindows.leastGapFrame Q i /\
      windowProfileControl C Q leastRecurringPrimeGap :=
    Classical.choose_spec (Classical.choose_spec (hQ0.2 (max R Qeps)))
  refine Exists.intro Q (Exists.intro i
    (And.intro (le_trans (le_max_left _ _) hi.1) (And.intro hi.2.2.1 ?_)))
  intro N x w hwindow hw hmass
  have hp := hi.2.2.2 N x w hwindow hw hmass
  exact hp.2.2.2.2.2.trans (herr Q (le_trans (le_max_right _ _) hi.1)).le

end PrimeFactorOscillations.FiniteFieldIntegerGapProfile
