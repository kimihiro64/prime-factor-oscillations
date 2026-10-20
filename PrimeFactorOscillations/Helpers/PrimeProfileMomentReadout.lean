/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileTransportParity
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.ReciprocalMomentTransport

/-!
# Exact prime transport from logarithmically many centered moments

Every even moment order retains the complete signed transport and has a
geometrically decreasing one-sided error. A one-eighth linear probe budget
therefore admits exact even readout under an explicit power-of-four degree
threshold. The observables are finite polynomials in the probabilities.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- A finite degree-m polynomial observation of the reciprocal probabilities. -/
def primePrefixMomentTransport (m : Nat) (e : Equiv.Perm Nat) (n : Nat) : Real :=
  Finset.prefixDefect
    (fun j => Real.reciprocalMomentTransport m
      (PrimeFactorUnimodality.primeAt n : Real)
      (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1)

/-- Full signed comparison for every even moment order. -/
theorem primePrefixMomentTransport_bounds_of_cost_le
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n k : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    (1 - (4 * C / (PrimeFactorUnimodality.primeAt n : Real)) ^ (2 * k)) *
        Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
          e (n + 1) <= primePrefixMomentTransport (2 * k) e n /\
      primePrefixMomentTransport (2 * k) e n <=
        Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
          e (n + 1) := by
  let p : Nat -> Real := fun j => PrimeFactorUnimodality.primeAt j
  let r : Real := p n
  let g : Nat -> Real := fun j => Real.reciprocalMomentTransport (2 * k) r (p j)
  let s := (Finset.range (n + 1)).image e
  let u := Finset.range (n + 1)
  have hc : s.card = u.card := Finset.card_image_iff.mpr
    (fun _ _ _ _ h => e.injective h)
  have hr : 0 < r := by
    dsimp only [r, p]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hmono : Monotone p := by
    intro i j hij
    dsimp only [p]
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone hij
  have hlocal := prime_prefix_coordinates_localized_of_cost_le e t n C ht hC hcost
  have hin : forall j, Membership.mem (s \ u) j ->
      (1 - (4 * C / r) ^ (2 * k)) * (p j - r) <= g j - 0 /\
        g j - 0 <= 1 * (p j - r) := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).2
    change Not (Membership.mem (Finset.range (n + 1)) j) at hn
    rw [Finset.mem_range] at hn
    have hidx : n <= j := by omega
    have hb := Real.reciprocalMomentTransport_entering_bounds (2 * k) r (p j) C hr hC0
      (hmono hidx) (hlocal.1 j hj)
    simpa only [sub_zero, one_mul] using hb
  have hout : forall j, Membership.mem (u \ s) j ->
      (1 - (4 * C / r) ^ (2 * k)) * (r - p j) <= 0 - g j /\
        0 - g j <= 1 * (r - p j) := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).1
    change Membership.mem (Finset.range (n + 1)) j at hn
    rw [Finset.mem_range] at hn
    have hidx : j <= n := by omega
    have hb := Real.reciprocalMomentTransport_leaving_bounds k r (p j) C hr hC0
      (hmono hidx) (hlocal.2 j hj) (by linarith only [hC])
    simpa only [zero_sub, one_mul] using hb
  have hb := Finset.reference_transport_comparison s u p g r 0
    (1 - (4 * C / r) ^ (2 * k)) 1 hc hin hout
  have hf : s.sum p - u.sum p = Finset.prefixDefect p e (n + 1) := by
    dsimp only [s, u]
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    rfl
  have hg : s.sum g - u.sum g = primePrefixMomentTransport (2 * k) e n := by
    dsimp only [s, u]
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    rfl
  rw [hf, hg, one_mul] at hb
  exact hb

/-- The error decreases geometrically in the even moment order. -/
theorem primePrefixMomentTransport_error_of_cost_le
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n k : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    0 <= Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixMomentTransport (2 * k) e n /\
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixMomentTransport (2 * k) e n <=
          4 * C * (4 * C / (PrimeFactorUnimodality.primeAt n : Real)) ^ (2 * k) := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  let S : Real := Finset.prefixDefect
    (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1)
  have hr : 0 < r := by
    dsimp only [r]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hb := primePrefixMomentTransport_bounds_of_cost_le e t n k C ht hC0 hC hcost
  have hSC : S <= 4 * C := prime_prefix_transport_le_four_mul_cost e t n C ht hC0 hC hcost
  have hm := mul_le_mul_of_nonneg_left hSC
    (by positivity : 0 <= (4 * C / r) ^ (2 * k))
  refine And.intro (sub_nonneg.mpr hb.2) ?_
  have hlo : (1 - (4 * C / r) ^ (2 * k)) * S <=
      primePrefixMomentTransport (2 * k) e n := hb.1
  nlinarith only [hlo, hm]

/-- An explicit finite-accuracy certificate at every even order. -/
theorem primePrefixMomentTransport_exact_even_readout
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n k : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hp3 : (3 : Real) <= PrimeFactorUnimodality.primeAt n)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hprecision : 4 * C * (4 * C / (PrimeFactorUnimodality.primeAt n : Real)) ^ (2 * k) < 2)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    exists K : Nat,
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) = 2 * (K : Real) /\
      (0 <= 2 * (K : Real) - primePrefixMomentTransport (2 * k) e n /\
        2 * (K : Real) - primePrefixMomentTransport (2 * k) e n < 2) /\
      (forall j : Nat, 0 <= 2 * (j : Real) - primePrefixMomentTransport (2 * k) e n ->
        2 * (j : Real) - primePrefixMomentTransport (2 * k) e n < 2 -> j = K) := by
  have hsmall : 2 < (PrimeFactorUnimodality.primeAt n : Real) - C := by
    linarith only [hC, hp3]
  have heven := prime_prefix_transport_even_of_cost_le e t n C ht hC0 hC hcost hsmall
  let K := Classical.choose heven
  have hK : Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
      e (n + 1) = 2 * (K : Real) := Classical.choose_spec heven
  have he := primePrefixMomentTransport_error_of_cost_le e t n k C ht hC0 hC hcost
  rw [hK] at he
  have hread : 0 <= 2 * (K : Real) - primePrefixMomentTransport (2 * k) e n /\
      2 * (K : Real) - primePrefixMomentTransport (2 * k) e n < 2 :=
    And.intro he.1 (he.2.trans_lt hprecision)
  refine Exists.intro K (And.intro hK (And.intro hread ?_))
  intro j hj0 hj2
  have hjK : (j : Real) < (K : Real) + 1 := by linarith only [hj2, hread.1]
  have hKj : (K : Real) < (j : Real) + 1 := by linarith only [hread.2, hj0]
  have hjKn : j < K + 1 := by exact_mod_cast hjK
  have hKjn : K < j + 1 := by exact_mod_cast hKj
  omega

/-- At a one-eighth linear budget, an explicit power-of-four threshold
certifies the sufficient number of moments. -/
theorem primePrefixMomentTransport_logarithmic_readout
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n k : Nat)
    (ht : 0 < t n)
    (hp3 : (3 : Real) <= PrimeFactorUnimodality.primeAt n)
    (hdegree : (PrimeFactorUnimodality.primeAt n : Real) < (4 : Real) ^ (k + 1))
    (hcost : normalizedPrimePrefixDefect e t n <=
      (PrimeFactorUnimodality.primeAt n : Real) / 8) :
    exists K : Nat,
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) = 2 * (K : Real) /\
      (0 <= 2 * (K : Real) - primePrefixMomentTransport (2 * k) e n /\
        2 * (K : Real) - primePrefixMomentTransport (2 * k) e n < 2) /\
      (forall j : Nat, 0 <= 2 * (j : Real) - primePrefixMomentTransport (2 * k) e n ->
        2 * (j : Real) - primePrefixMomentTransport (2 * k) e n < 2 -> j = K) := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  have hr : 0 < r := by linarith only [hp3]
  have hhalf : 4 * (r / 8) / r = (1 / 2 : Real) := by
    field_simp [hr.ne']
    norm_num
  have hpower : (1 / 2 : Real) ^ (2 * k) * (4 : Real) ^ k = 1 := by
    rw [pow_mul, <- mul_pow]
    norm_num
  have hcancel : (4 * (r / 8) * (1 / 2 : Real) ^ (2 * k)) * (4 : Real) ^ k =
      r / 2 := by
    calc
      _ = (r / 2) * ((1 / 2 : Real) ^ (2 * k) * (4 : Real) ^ k) := by ring
      _ = _ := by rw [hpower, mul_one]
  have hprecision : 4 * (r / 8) * (4 * (r / 8) / r) ^ (2 * k) < 2 := by
    rw [hhalf]
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn)
      (by positivity : 0 <= (4 : Real) ^ k)
    rw [hcancel] at hm
    have hd : r < (4 : Real) ^ k * 4 := by simpa only [pow_succ] using hdegree
    linarith only [hm, hd]
  exact primePrefixMomentTransport_exact_even_readout e t n k (r / 8)
    ht (by positivity) hp3 (by linarith only [hr]) hprecision hcost

/-- No unspecified degree remains: twice the base-four natural logarithm
of the boundary prime suffices under a one-eighth linear cost budget. -/
theorem primePrefixMomentTransport_logarithmic_degree_readout
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat)
    (ht : 0 < t n)
    (hp3 : (3 : Real) <= PrimeFactorUnimodality.primeAt n)
    (hcost : normalizedPrimePrefixDefect e t n <=
      (PrimeFactorUnimodality.primeAt n : Real) / 8) :
    let m : Nat := 2 * Nat.log 4 (PrimeFactorUnimodality.primeAt n)
    exists K : Nat,
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) = 2 * (K : Real) /\
      (0 <= 2 * (K : Real) - primePrefixMomentTransport m e n /\
        2 * (K : Real) - primePrefixMomentTransport m e n < 2) /\
      (forall j : Nat, 0 <= 2 * (j : Real) - primePrefixMomentTransport m e n ->
        2 * (j : Real) - primePrefixMomentTransport m e n < 2 -> j = K) := by
  have hdNat : PrimeFactorUnimodality.primeAt n <
      4 ^ (Nat.log 4 (PrimeFactorUnimodality.primeAt n) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (PrimeFactorUnimodality.primeAt n)
  have hd : (PrimeFactorUnimodality.primeAt n : Real) <
      (4 : Real) ^ (Nat.log 4 (PrimeFactorUnimodality.primeAt n) + 1) := by
    exact_mod_cast hdNat
  exact primePrefixMomentTransport_logarithmic_readout e t n
    (Nat.log 4 (PrimeFactorUnimodality.primeAt n)) ht hp3 hd hcost

/-- Two extra centered moments make the recovery stable under any observation
error strictly below one half, uniformly for every such observation. -/
theorem primePrefixMomentTransport_noisy_logarithmic_readout
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat)
    (ht : 0 < t n)
    (hp3 : (3 : Real) <= PrimeFactorUnimodality.primeAt n)
    (hcost : normalizedPrimePrefixDefect e t n <=
      (PrimeFactorUnimodality.primeAt n : Real) / 8) :
    let m : Nat := 2 * (Nat.log 4 (PrimeFactorUnimodality.primeAt n) + 1)
    exists K : Nat,
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) = 2 * (K : Real) /\
      (forall y : Real, abs (y - primePrefixMomentTransport m e n) < (1 / 2 : Real) ->
        abs (y - 2 * (K : Real)) < 1 /\
        (forall j : Nat, abs (y - 2 * (j : Real)) < 1 -> j = K)) := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  let k : Nat := Nat.log 4 (PrimeFactorUnimodality.primeAt n) + 1
  have hr3 : 3 <= r := hp3
  have hr : 0 < r := by linarith only [hr3]
  have hC0 : 0 <= r / 8 := by positivity
  have hbudget : r / 8 < r / 4 := by linarith only [hr]
  have hsmall : 2 < r - r / 8 := by linarith only [hr3]
  have heven := prime_prefix_transport_even_of_cost_le e t n (r / 8)
    ht hC0 hbudget hcost hsmall
  let K := Classical.choose heven
  have hK : Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
      e (n + 1) = 2 * (K : Real) := Classical.choose_spec heven
  have hdNat : PrimeFactorUnimodality.primeAt n <
      4 ^ (Nat.log 4 (PrimeFactorUnimodality.primeAt n) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (PrimeFactorUnimodality.primeAt n)
  have hd : r < (4 : Real) ^ k := by
    dsimp only [r, k]
    exact_mod_cast hdNat
  have hhalf : 4 * (r / 8) / r = (1 / 2 : Real) := by
    field_simp [hr.ne']
    norm_num
  have hpower : (1 / 2 : Real) ^ (2 * k) * (4 : Real) ^ k = 1 := by
    rw [pow_mul, <- mul_pow]
    norm_num
  have hcancel : (4 * (r / 8) * (1 / 2 : Real) ^ (2 * k)) * (4 : Real) ^ k =
      r / 2 := by
    calc
      _ = (r / 2) * ((1 / 2 : Real) ^ (2 * k) * (4 : Real) ^ k) := by ring
      _ = _ := by rw [hpower, mul_one]
  have hprecision : 4 * (r / 8) * (4 * (r / 8) / r) ^ (2 * k) < (1 / 2 : Real) := by
    rw [hhalf]
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn)
      (by positivity : 0 <= (4 : Real) ^ k)
    rw [hcancel] at hm
    linarith only [hm, hd]
  have he := primePrefixMomentTransport_error_of_cost_le e t n k (r / 8)
    ht hC0 hbudget hcost
  rw [hK] at he
  have herror : 2 * (K : Real) - primePrefixMomentTransport (2 * k) e n < (1 / 2 : Real) :=
    he.2.trans_lt hprecision
  refine Exists.intro K (And.intro hK ?_)
  intro y hy
  change abs (y - primePrefixMomentTransport (2 * k) e n) < (1 / 2 : Real) at hy
  have hybounds := abs_lt.mp hy
  have hread : abs (y - 2 * (K : Real)) < 1 := by
    apply abs_lt.mpr
    constructor <;> linarith only [hybounds.1, hybounds.2, he.1, herror]
  refine And.intro hread ?_
  intro j hj
  have hKb := abs_lt.mp hread
  have hjb := abs_lt.mp hj
  have hjK : (j : Real) < (K : Real) + 1 := by linarith only [hjb.1, hKb.2]
  have hKj : (K : Real) < (j : Real) + 1 := by linarith only [hKb.1, hjb.2]
  have hjKn : j < K + 1 := by exact_mod_cast hjK
  have hKjn : K < j + 1 := by exact_mod_cast hKj
  omega

end PrimeFactorOscillations.PrimeProfileRigidity
