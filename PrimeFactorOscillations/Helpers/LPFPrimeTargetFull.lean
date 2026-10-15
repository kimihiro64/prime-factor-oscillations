/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPrimeTargetLogPower
import PrimeFactorOscillations.Helpers.LPFPrimeTargetTail
import PrimeFactorOscillations.Helpers.PrimeCountingLocation

/-!
# Full prime-target products and their finite moment

The divisor product uses the finite primeFactors support. Its auxiliary value
at zero is not an arithmetic product over all divisors of zero. Every use of
the large-prime tail below proves the difference strictly positive.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def singularDivisorProduct (v : Nat) : Real :=
  Finset.prod (v.primeFactors.filter (fun p => 3 <= p)) singularFactor

def primeTargetSeparation (r s : Nat) : Nat :=
  (primeTargetSum r - primeTargetSum s) + (primeTargetSum s - primeTargetSum r)

noncomputable def primeTargetCutoff (M : Nat) : Finset Nat :=
  (Finset.range (Nat.floor (Real.log (M : Real)) + 1)).filter
    (fun p => And (Nat.Prime p) (3 < p))

theorem nextPrimeWindow_eq_row (M : Nat) :
    nextPrimeWindow M = Nat.largestPrimeFactorRow (5 * M / 4) M 1 := by
  have hOne : Nat.largestPrimeFactor 1 = 1 := by norm_num [Nat.largestPrimeFactor]
  simp only [nextPrimeWindow, Nat.largestPrimeFactorRow, hOne, Nat.div_one,
    max_eq_left (show 1 <= M + 1 by omega)]

theorem primeTargetSeparation_pos (M r s : Nat) (hM : 3 <= M)
    (hr : Membership.mem (nextPrimeWindow M) r)
    (hs : Membership.mem (nextPrimeWindow M) s) (hne : Not (s = r)) :
    0 < primeTargetSeparation r s := by
  have hr' := nextPrimeWindow_spec M r hr
  have hs' := nextPrimeWindow_spec M s hs
  by_contra h
  have heq : primeTargetSum r = primeTargetSum s := by
    dsimp [primeTargetSeparation] at h
    omega
  exact hne (primeTarget_injective_window M r s hM hr'.1 hs'.1 hr'.2 hs'.2 heq).symm

theorem primeTargetSeparation_le (M r s : Nat) (hM : 4 <= M)
    (hr : Membership.mem (nextPrimeWindow M) r)
    (hs : Membership.mem (nextPrimeWindow M) s) :
    primeTargetSeparation r s <= 2 * M := by
  have hLiftBound : forall p, Membership.mem (nextPrimeWindow M) p ->
      primeTargetSum p <= 2 * M := by
    intro p hp
    have h := nextPrimeWindow_spec M p hp
    have hl := primeTarget_lift p h.1 (by omega)
    unfold primeTargetCofactor at hl
    split_ifs at hl <;> omega
  have hrBound := hLiftBound r hr
  have hsBound := hLiftBound s hs
  unfold primeTargetSeparation
  omega

theorem eventually_nextPrimeWindow_card_le :
    Filter.Eventually (fun M : Nat =>
      ((nextPrimeWindow M).card : Real) <= 4 * (M : Real) / Real.log (M : Real))
      Filter.atTop := by
  have hExists := (eventually_thetaPrefix_and_primeCounting_bounds 1 (by norm_num)).exists_forall_of_atTop
  let M0 : Nat := Classical.choose hExists
  have hM0 := Classical.choose_spec hExists
  filter_upwards [Filter.eventually_ge_atTop (max M0 2)] with M hM
  have hM2 : 2 <= M := by omega
  have hUpper := (hM0 (2 * M) (by dsimp [M0] at hM; omega)).2.2
  have hSubset : nextPrimeWindow M <= Nat.primesLE (2 * M) := by
    intro p hp
    have h := nextPrimeWindow_spec M p hp
    exact Nat.mem_primesLE.mpr (And.intro (by omega) h.1)
  have hCard : ((nextPrimeWindow M).card : Real) <= (Nat.primeCounting (2 * M) : Real) := by
    have h := Finset.card_le_card hSubset
    rw [Nat.primesLE_card_eq_primeCounting] at h
    exact_mod_cast h
  have hMR : (1 : Real) < (M : Real) := by exact_mod_cast (show 1 < M by omega)
  have hLog : 0 < Real.log (M : Real) := Real.log_pos hMR
  have hLogCompare : Real.log (M : Real) <= Real.log ((2 * M : Nat) : Real) :=
    Real.log_le_log (by linarith) (by exact_mod_cast (show M <= 2 * M by omega))
  calc
    _ <= (Nat.primeCounting (2 * M) : Real) := hCard
    _ <= (1 + 1 : Real) * ((2 * M : Nat) : Real) /
        Real.log ((2 * M : Nat) : Real) := hUpper
    _ = (4 * (M : Real)) / Real.log ((2 * M : Nat) : Real) := by push_cast; ring
    _ <= _ := div_le_div_of_nonneg_left (by positivity) hLog hLogCompare

theorem primeTargetCutoff_mem (M p : Nat) (hM : 1 <= M) :
    Membership.mem (primeTargetCutoff M) p <->
      And (Nat.Prime p) (And (3 < p) ((p : Real) <= Real.log (M : Real))) := by
  have hLog : 0 <= Real.log (M : Real) := Real.log_nonneg (by exact_mod_cast hM)
  have hFloor : p < Nat.floor (Real.log (M : Real)) + 1 <->
      (p : Real) <= Real.log (M : Real) := by
    rw [Nat.lt_succ_iff, Nat.le_floor_iff hLog]
  unfold primeTargetCutoff
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  next => intro h; exact And.intro h.2.1 (And.intro h.2.2 (hFloor.mp h.1))
  next => intro h; exact And.intro (hFloor.mpr h.2.2) (And.intro h.1 h.2.1)

private theorem singularFactor_nonneg_of_three_le (p : Nat) (hp : 3 <= p) :
    0 <= singularFactor p := by
  have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast hp
  have h : 0 <= 1 / ((p : Real) - 2) := one_div_nonneg.mpr (by linarith)
  dsimp [singularFactor]
  linarith

theorem singularDivisorProduct_le_cutoff (M v : Nat) (hM : 4 <= M)
    (hv : 0 < v) (hvM : v <= 2 * M)
    (hLog : 4 <= Real.log (M : Real))
    (hLogLog : 1 <= Real.log (Real.log (M : Real))) :
    singularDivisorProduct v <= (2 * Real.exp 4) *
      Finset.prod ((primeTargetCutoff M).filter (fun p => Dvd.dvd p v)) singularFactor := by
  classical
  let Q := v.primeFactors.filter (fun p => 3 <= p)
  have hQ : forall p, Membership.mem Q p ->
      And (Nat.Prime p) (And (3 <= p) (Dvd.dvd p v)) := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    exact And.intro (Nat.prime_of_mem_primeFactors h.1)
      (And.intro h.2 (Nat.dvd_of_mem_primeFactors h.1))
  have hSmallSet : Q.filter (fun (p : Nat) => And (3 < p) ((p : Real) <= Real.log (M : Real))) =
      (primeTargetCutoff M).filter (fun p => Dvd.dvd p v) := by
    apply Finset.ext
    intro p
    constructor
    next =>
      intro hp
      have h := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr (And.intro
        ((primeTargetCutoff_mem M p (by omega)).mpr
          (And.intro (hQ p h.1).1 h.2)) (hQ p h.1).2.2)
    next =>
      intro hp
      have h := Finset.mem_filter.mp hp
      have hc := (primeTargetCutoff_mem M p (by omega)).mp h.1
      apply Finset.mem_filter.mpr
      refine And.intro ?_ hc.2
      apply Finset.mem_filter.mpr
      exact And.intro
        (Nat.mem_primeFactors.mpr (And.intro hc.1 (And.intro h.2 (by omega))))
        (by omega)
  have hTail := singular_product_le_truncated Q v (Real.log (M : Real)) hv hLog hQ
  rw [hSmallSet] at hTail
  have hMpos : (0 : Real) < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  have hLogV : Real.log (v : Real) <= 2 * Real.log (M : Real) := by
    calc
      _ <= Real.log (2 * (M : Real)) :=
        Real.log_le_log (by exact_mod_cast hv) (by exact_mod_cast hvM)
      _ = Real.log 2 + Real.log (M : Real) :=
        Real.log_mul (by norm_num) (ne_of_gt hMpos)
      _ <= _ := by
        have h : Real.log 2 <= Real.log (M : Real) :=
          Real.log_le_log (by norm_num : (0 : Real) < 2)
          (by exact_mod_cast (show 2 <= M by omega))
        linarith
  have hY : 0 < Real.log (M : Real) := by linarith
  have hLL : 0 < Real.log (Real.log (M : Real)) := by linarith
  have hFraction : 2 * Real.log (v : Real) /
      (Real.log (M : Real) * Real.log (Real.log (M : Real))) <= 4 := by
    calc
      _ <= (2 * (2 * Real.log (M : Real))) /
          (Real.log (M : Real) * Real.log (Real.log (M : Real))) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLogV (by norm_num))
          (mul_pos hY hLL).le
      _ = 4 / Real.log (Real.log (M : Real)) := by
        field_simp [ne_of_gt hY, ne_of_gt hLL] <;> norm_num
      _ <= 4 := div_le_self (by norm_num) hLogLog
  have hLow : 0 <= Finset.prod
      ((primeTargetCutoff M).filter (fun p => Dvd.dvd p v)) singularFactor := by
    apply Finset.prod_nonneg
    intro p hp
    have h := (primeTargetCutoff_mem M p (by omega)).mp (Finset.mem_filter.mp hp).1
    exact singularFactor_nonneg_of_three_le p (by omega)
  exact hTail.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hFraction) (by norm_num)) hLow)

private theorem nonneg_pow_mono (a b : Real) (ha : 0 <= a) (hab : a <= b) (q : Nat) :
    a ^ q <= b ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (pow_nonneg (ha.trans hab) q)

/-- Full off-diagonal divisor moments on the actual target window, with every error. -/
theorem exists_primeTarget_full_finite_bound :
    exists C : Real, And (0 < C) (forall M r q : Nat,
      4 <= M -> 4 <= Real.log (M : Real) ->
      1 <= Real.log (Real.log (M : Real)) ->
      Membership.mem (nextPrimeWindow M) r -> 1 <= q ->
      Finset.sum ((nextPrimeWindow M).erase r) (fun s =>
        singularDivisorProduct (primeTargetSeparation r s) ^ q) <=
      (2 * Real.exp 4) ^ q *
        (2 * ((nextPrimeWindow M).card : Real) *
          (2 * Real.exp (singularMertensBound + 12) * Real.log ((q : Real) + 2)) ^ q +
        C * ((5 * M / 4 : Nat) : Real) ^ (7 / 8 : Real) *
          (1 + Real.log ((Finset.prod (primeTargetCutoff M) (fun p => p) : Nat) : Real) +
            Real.log (((5 * M / 4 : Nat) : Real) + 2)) ^ 2 *
          (Finset.prod (primeTargetCutoff M) singularFactor) ^ q)) := by
  classical
  let C : Real := Classical.choose exists_primeTarget_truncated_moment_bound
  have hC := Classical.choose_spec exists_primeTarget_truncated_moment_bound
  refine Exists.intro C (And.intro hC.1 ?_)
  intro M r q hM hLog hLogLog hr hq
  have hr' := nextPrimeWindow_spec M r hr
  have hMpos : (0 : Real) < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  have hLogLt : Real.log (M : Real) < (M : Real) := by
    have h := Real.log_le_sub_one_of_pos hMpos
    linarith
  have hCutoff : forall p, Membership.mem (primeTargetCutoff M) p ->
      And (Nat.Prime p) (And (3 < p) (p < r)) := by
    intro p hp
    have h := (primeTargetCutoff_mem M p (by omega)).mp hp
    have hpM : p < M := by exact_mod_cast h.2.2.trans_lt hLogLt
    exact And.intro h.1 (And.intro h.2.1 (by omega))
  have hSub : (nextPrimeWindow M).erase r <=
      Nat.largestPrimeFactorRow (5 * M / 4) M 1 := by
    rw [<- nextPrimeWindow_eq_row]
    exact Finset.erase_subset _ _
  have hPrimes : forall s, Membership.mem ((nextPrimeWindow M).erase r) s ->
      And (Nat.Prime s) (3 <= s) := by
    intro s hs
    have h := nextPrimeWindow_spec M s (Finset.mem_erase.mp hs).2
    exact And.intro h.1 (by omega)
  have hMoment := hC.2 (5 * M / 4) M 1 r q (primeTargetCutoff M)
    ((nextPrimeWindow M).erase r) hr'.1 (by omega) hq hCutoff hSub hPrimes
  rw [<- nextPrimeWindow_eq_row] at hMoment
  let F (s : Nat) : Real := (Finset.prod
    ((primeTargetCutoff M).filter (fun p => Dvd.dvd p (primeTargetSeparation r s)))
      singularFactor) ^ q
  have hPoint : forall s, Membership.mem ((nextPrimeWindow M).erase r) s ->
      singularDivisorProduct (primeTargetSeparation r s) ^ q <= (2 * Real.exp 4) ^ q * F s := by
    intro s hs
    have hs' := Finset.mem_erase.mp hs
    have hv := primeTargetSeparation_pos M r s (by omega) hr hs'.2 hs'.1
    have hvM := primeTargetSeparation_le M r s hM hr hs'.2
    have hProduct := singularDivisorProduct_le_cutoff M _ hM hv hvM hLog hLogLog
    have hNonneg : 0 <= singularDivisorProduct (primeTargetSeparation r s) := by
      apply Finset.prod_nonneg
      intro p hp
      exact singularFactor_nonneg_of_three_le p (Finset.mem_filter.mp hp).2
    have h := nonneg_pow_mono _ _ hNonneg hProduct q
    simpa only [mul_pow] using h
  calc
    _ <= Finset.sum ((nextPrimeWindow M).erase r) (fun s => (2 * Real.exp 4) ^ q * F s) :=
      Finset.sum_le_sum hPoint
    _ = (2 * Real.exp 4) ^ q * Finset.sum ((nextPrimeWindow M).erase r) F :=
      (Finset.mul_sum _ _ _).symm
    _ <= _ := mul_le_mul_of_nonneg_left hMoment (by positivity)

end PrimeFactorOscillations.LPF
