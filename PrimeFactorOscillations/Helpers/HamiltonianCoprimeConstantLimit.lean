/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeConstantTail

/-! # Monotonicity and the full odd-prime limit of the arithmetic constant

The actual prime products remain coupled. The uniform geometric majorant
justifies passing the odd-primorial limit through the full series.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_product_antitone_unit_interval {Iota : Type*} [DecidableEq Iota]
    {S T : Finset Iota} (hST : (forall i, Membership.mem S i -> Membership.mem T i)) (f : Iota -> Real)
    (hf : forall i, Membership.mem T i -> 0 <= f i /\ f i <= 1) :
    T.prod f <= S.prod f := by
  have hS := hamiltonian_product_unit_interval S f (fun i hi => hf i (hST i hi))
  have hDiff := hamiltonian_product_unit_interval (SDiff.sdiff T S) f
    (fun i hi => hf i (Finset.mem_sdiff.mp hi).1)
  calc
    T.prod f = (SDiff.sdiff T S).prod f * S.prod f := (Finset.prod_sdiff hST).symm
    _ <= 1 * S.prod f := mul_le_mul_of_nonneg_right hDiff.2 hS.1
    _ = S.prod f := one_mul _

theorem hamiltonian_odd_prime_euler_factor_bounds (p j : Nat)
    (hp : Nat.Prime p) (hOdd : Odd p) :
    0 <= 1 - 1 / ((p : Real) - 1) ^ (2 * j) /\
      1 - 1 / ((p : Real) - 1) ^ (2 * j) <= 1 := by
  have hp3 : 3 <= p := by
    have hp2 := hp.two_le
    have hk := hOdd.choose_spec
    omega
  have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast hp3
  have hBase : 1 <= (p : Real) - 1 := by linarith only [hpR]
  have hPower := hamiltonian_one_le_power ((p : Real) - 1) hBase (2 * j)
  have hInv := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hPower
  have hU : 0 <= 1 / ((p : Real) - 1) ^ (2 * j) := by positivity
  norm_num only [one_div_one] at hInv
  exact And.intro (sub_nonneg.mpr hInv) (by linarith only [hU])

theorem hamiltonian_coprime_log_coefficient_mono (n m j : Nat) [NeZero n] [NeZero m]
    (hnOdd : Odd n) (hmOdd : Odd m) (hSupport : (forall p, Membership.mem n.primeFactors p -> Membership.mem m.primeFactors p)) :
    hamiltonianCoprimeLogCoefficient n j <= hamiltonianCoprimeLogCoefficient m j := by
  by_cases hj : j = 0
  case pos => simp only [hamiltonianCoprimeLogCoefficient, if_pos hj, le_refl]
  case neg =>
    have hProd := hamiltonian_product_antitone_unit_interval hSupport
      (fun p : Nat => 1 - 1 / ((p : Real) - 1) ^ (2 * j)) (by
        intro p hp
        have hData := hamiltonian_odd_prime_factor_data m p hmOdd hp
        exact hamiltonian_odd_prime_euler_factor_bounds p j
          (Nat.mem_primeFactors.mp hp).1 hData.1)
    rw [hamiltonianCoprimeLogCoefficient, hamiltonianCoprimeLogCoefficient,
      if_neg hj, if_neg hj]
    apply div_le_div_of_nonneg_right (by linarith only [hProd])
    positivity

theorem hamiltonian_coprime_constant_log_mono (n m : Nat) [NeZero n] [NeZero m]
    (hnOdd : Odd n) (hmOdd : Odd m) (hn : 1 < n) (hm : 1 < m)
    (hSupport : (forall p, Membership.mem n.primeFactors p -> Membership.mem m.primeFactors p)) :
    Real.log (hamiltonianCoprimeArithmeticConstant n) <=
      Real.log (hamiltonianCoprimeArithmeticConstant m) :=
  hasSum_le (fun j => hamiltonian_coprime_log_coefficient_mono n m j hnOdd hmOdd hSupport)
    (hamiltonian_coprime_odd_constant_prime_product_series n hnOdd hn)
    (hamiltonian_coprime_odd_constant_prime_product_series m hmOdd hm)

theorem hamiltonian_coprime_constant_mono (n m : Nat) [NeZero n] [NeZero m]
    (hnOdd : Odd n) (hmOdd : Odd m) (hn : 1 < n) (hm : 1 < m)
    (hSupport : (forall p, Membership.mem n.primeFactors p -> Membership.mem m.primeFactors p)) :
    hamiltonianCoprimeArithmeticConstant n <= hamiltonianCoprimeArithmeticConstant m := by
  have h := Real.exp_le_exp.mpr
    (hamiltonian_coprime_constant_log_mono n m hnOdd hmOdd hn hm hSupport)
  simpa only [Real.exp_log (hamiltonian_coprime_odd_constant_positive hnOdd),
    Real.exp_log (hamiltonian_coprime_odd_constant_positive hmOdd)] using h

def hamiltonianOddPrimeEulerFactor (j p : Nat) : Real :=
  if Nat.Prime p /\ Odd p then 1 - 1 / ((p : Real) - 1) ^ (2 * j) else 1

theorem hamiltonian_all_odd_prime_euler_factor_bounds (j p : Nat) :
    0 <= hamiltonianOddPrimeEulerFactor j p /\
      hamiltonianOddPrimeEulerFactor j p <= 1 := by
  unfold hamiltonianOddPrimeEulerFactor
  split
  case isTrue h => exact hamiltonian_odd_prime_euler_factor_bounds p j h.1 h.2
  case isFalse h => exact And.intro (by norm_num) le_rfl

theorem hamiltonian_all_odd_prime_euler_multipliable (j : Nat) :
    Multipliable (hamiltonianOddPrimeEulerFactor j) := by
  have hAnti : Antitone (fun S : Finset Nat => S.prod (hamiltonianOddPrimeEulerFactor j)) := by
    intro S T hST
    exact hamiltonian_product_antitone_unit_interval hST _
      (fun p _ => hamiltonian_all_odd_prime_euler_factor_bounds j p)
  have hBdd : BddBelow (Set.range
      (fun S : Finset Nat => S.prod (hamiltonianOddPrimeEulerFactor j))) := by
    refine Exists.intro 0 ?_
    intro x hx
    let S := hx.choose
    have hS : S.prod (hamiltonianOddPrimeEulerFactor j) = x := hx.choose_spec
    rw [<- hS]
    exact (hamiltonian_product_unit_interval S _
      (fun p _ => hamiltonian_all_odd_prime_euler_factor_bounds j p)).1
  exact Exists.intro _ (tendsto_atTop_ciInf hAnti hBdd)

def hamiltonianOddPrimorial (k : Nat) : Nat :=
  ((Finset.range (k + 4)).filter (fun p => Nat.Prime p /\ Odd p)).prod id

theorem hamiltonian_odd_primorial_data (k : Nat) :
    Odd (hamiltonianOddPrimorial k) /\ 1 < hamiltonianOddPrimorial k /\
      (hamiltonianOddPrimorial k).primeFactors =
        (Finset.range (k + 4)).filter (fun p => Nat.Prime p /\ Odd p) := by
  let S := (Finset.range (k + 4)).filter (fun p => Nat.Prime p /\ Odd p)
  have hPrime : forall p, Membership.mem S p -> Nat.Prime p :=
    fun p hp => (Finset.mem_filter.mp hp).2.1
  have hOddFactors : forall p, Membership.mem S p -> Odd p :=
    fun p hp => (Finset.mem_filter.mp hp).2.2
  have hOdd : Odd (S.prod id) := by
    revert hOddFactors
    induction S using Finset.induction_on with
    | empty =>
      intro hOddFactors
      norm_num
    | @insert p S hp ih =>
      intro hOddFactors
      rw [Finset.prod_insert hp]
      exact (hOddFactors p (Finset.mem_insert_self p S)).mul
        (ih (fun q hq => hOddFactors q (Finset.mem_insert_of_mem hq)))
  have hNZ : Not (S.prod id = 0) := Finset.prod_ne_zero_iff.mpr
    (fun p hp => (hPrime p hp).ne_zero)
  have hFactors : (S.prod id).primeFactors = S := Nat.primeFactors_prod hPrime
  have h3 : Membership.mem S 3 := by
    apply Finset.mem_filter.mpr
    exact And.intro (Finset.mem_range.mpr (by omega))
      (And.intro (by norm_num) (Exists.intro 1 (by norm_num)))
  have hNE : Not (S.prod id = 1) := by
    intro h
    rw [h, Nat.primeFactors_one] at hFactors
    rw [<- hFactors] at h3
    simpa using h3
  have hGt : 1 < S.prod id := by omega
  exact And.intro hOdd (And.intro hGt hFactors)

instance (k : Nat) : NeZero (hamiltonianOddPrimorial k) where
  out := ne_of_gt (lt_trans (by norm_num) (hamiltonian_odd_primorial_data k).2.1)

theorem hamiltonian_odd_primorial_support_mono (k l : Nat) (hkl : k <= l) :
    (forall p, Membership.mem (hamiltonianOddPrimorial k).primeFactors p ->
      Membership.mem (hamiltonianOddPrimorial l).primeFactors p) := by
  rw [(hamiltonian_odd_primorial_data k).2.2, (hamiltonian_odd_primorial_data l).2.2]
  intro p hp
  have h := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr (And.intro
    (Finset.mem_range.mpr (by have hRange := Finset.mem_range.mp h.1; omega)) h.2)

theorem hamiltonian_odd_primorial_constant_mono :
    Monotone (fun k => hamiltonianCoprimeArithmeticConstant (hamiltonianOddPrimorial k)) := by
  intro k l hkl
  have hK := hamiltonian_odd_primorial_data k
  have hL := hamiltonian_odd_primorial_data l
  exact hamiltonian_coprime_constant_mono _ _ hK.1 hL.1 hK.2.1 hL.2.1
    (hamiltonian_odd_primorial_support_mono k l hkl)

def hamiltonianCoprimeInfiniteLogCoefficient (j : Nat) : Real :=
  if j = 0 then 1 else
    (1 - (tprod (hamiltonianOddPrimeEulerFactor j))) / ((2 * j + 1 : Nat) : Real)

def hamiltonianCoprimeInfiniteConstant : Real :=
  Real.exp (tsum hamiltonianCoprimeInfiniteLogCoefficient)

theorem hamiltonian_coprime_primorial_coefficient_limit (j : Nat) :
    Filter.Tendsto
      (fun k => hamiltonianCoprimeLogCoefficient (hamiltonianOddPrimorial k) j)
      Filter.atTop (nhds (hamiltonianCoprimeInfiniteLogCoefficient j)) := by
  by_cases hj : j = 0
  case pos =>
    simpa only [hamiltonianCoprimeLogCoefficient, hamiltonianCoprimeInfiniteLogCoefficient,
      if_pos hj] using (tendsto_const_nhds : Filter.Tendsto (fun _ : Nat => (1 : Real))
        Filter.atTop (nhds 1))
  case neg =>
    have hProd := ((hamiltonian_all_odd_prime_euler_multipliable j).hasProd.tendsto_prod_nat).comp
      (Filter.tendsto_add_atTop_nat 4)
    have hOne : Filter.Tendsto (fun _ : Nat => (1 : Real)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    have hLim := (hOne.sub hProd).div_const ((2 * j + 1 : Nat) : Real)
    have hEq : (fun k => hamiltonianCoprimeLogCoefficient (hamiltonianOddPrimorial k) j) =
        (fun k => (1 - (Finset.range (k + 4)).prod (hamiltonianOddPrimeEulerFactor j)) /
          ((2 * j + 1 : Nat) : Real)) := by
      funext k
      rw [hamiltonianCoprimeLogCoefficient, if_neg hj,
        (hamiltonian_odd_primorial_data k).2.2, Finset.prod_filter]
      rfl
    rw [hEq, hamiltonianCoprimeInfiniteLogCoefficient, if_neg hj]
    exact hLim

theorem hamiltonian_coprime_primorial_coefficient_domination (k j : Nat) :
    norm (hamiltonianCoprimeLogCoefficient (hamiltonianOddPrimorial k) j) <=
      2 * (1 / 4 : Real) ^ j := by
  by_cases hj : j = 0
  case pos => norm_num [hamiltonianCoprimeLogCoefficient, hj]
  case neg =>
    have h := hamiltonian_coprime_log_coefficient_bounds (hamiltonianOddPrimorial k) j
      (hamiltonian_odd_primorial_data k).1 (by omega)
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))

theorem hamiltonian_coprime_infinite_coefficient_bounds (j : Nat) :
    0 <= hamiltonianCoprimeInfiniteLogCoefficient j /\
      hamiltonianCoprimeInfiniteLogCoefficient j <= 2 * (1 / 4 : Real) ^ j := by
  have hLim := hamiltonian_coprime_primorial_coefficient_limit j
  have hNonneg : forall k, 0 <=
      hamiltonianCoprimeLogCoefficient (hamiltonianOddPrimorial k) j := by
    intro k
    by_cases hj : j = 0
    case pos => norm_num [hamiltonianCoprimeLogCoefficient, hj]
    case neg => exact (hamiltonian_coprime_log_coefficient_bounds
      (hamiltonianOddPrimorial k) j (hamiltonian_odd_primorial_data k).1 (by omega)).1
  refine And.intro (ge_of_tendsto hLim (Filter.Eventually.of_forall hNonneg)) ?_
  apply le_of_tendsto hLim (Filter.Eventually.of_forall (fun k => ?_))
  have h := hamiltonian_coprime_primorial_coefficient_domination k j
  rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg k)] at h
  exact h

theorem hamiltonian_coprime_infinite_series_summable :
    Summable hamiltonianCoprimeInfiniteLogCoefficient := by
  have hGeom : Summable (fun j : Nat => 2 * (1 / 4 : Real) ^ j) :=
    (hasSum_geometric_of_norm_lt_one (by norm_num : norm (1 / 4 : Real) < 1)).summable.mul_left 2
  apply hGeom.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (hamiltonian_coprime_infinite_coefficient_bounds j).1]
  exact (hamiltonian_coprime_infinite_coefficient_bounds j).2

theorem hamiltonian_coprime_primorial_log_limit :
    Filter.Tendsto
      (fun k => Real.log (hamiltonianCoprimeArithmeticConstant (hamiltonianOddPrimorial k)))
      Filter.atTop (nhds (tsum hamiltonianCoprimeInfiniteLogCoefficient)) := by
  have hGeom : Summable (fun j : Nat => 2 * (1 / 4 : Real) ^ j) :=
    (hasSum_geometric_of_norm_lt_one (by norm_num : norm (1 / 4 : Real) < 1)).summable.mul_left 2
  have hLim := tendsto_tsum_of_dominated_convergence hGeom
    hamiltonian_coprime_primorial_coefficient_limit
    (Filter.Eventually.of_forall hamiltonian_coprime_primorial_coefficient_domination)
  have hEq : (fun k => Real.log (hamiltonianCoprimeArithmeticConstant
      (hamiltonianOddPrimorial k))) =
      (fun k => tsum (hamiltonianCoprimeLogCoefficient (hamiltonianOddPrimorial k))) := by
    funext k
    exact (hamiltonian_coprime_odd_constant_prime_product_series
      (hamiltonianOddPrimorial k) (hamiltonian_odd_primorial_data k).1
        (hamiltonian_odd_primorial_data k).2.1).tsum_eq.symm
  rw [hEq]
  exact hLim

theorem hamiltonian_coprime_primorial_constant_limit :
    Filter.Tendsto
      (fun k => hamiltonianCoprimeArithmeticConstant (hamiltonianOddPrimorial k))
      Filter.atTop (nhds hamiltonianCoprimeInfiniteConstant) := by
  have hLim := Real.continuous_exp.continuousAt.tendsto.comp
    hamiltonian_coprime_primorial_log_limit
  have hEq : (fun k => Real.exp (Real.log (hamiltonianCoprimeArithmeticConstant
      (hamiltonianOddPrimorial k)))) =
      (fun k => hamiltonianCoprimeArithmeticConstant (hamiltonianOddPrimorial k)) := by
    funext k
    exact Real.exp_log (hamiltonian_coprime_odd_constant_positive
      (hamiltonian_odd_primorial_data k).1)
  change Filter.Tendsto _ _ (nhds (Real.exp (tsum hamiltonianCoprimeInfiniteLogCoefficient)))
  rw [<- hEq]
  exact hLim

theorem hamiltonian_coprime_infinite_constant_bounds :
    Real.exp 1 <= hamiltonianCoprimeInfiniteConstant /\
      hamiltonianCoprimeInfiniteConstant <= Real.exp (11 / 9 : Real) := by
  refine And.intro (ge_of_tendsto hamiltonian_coprime_primorial_constant_limit
    (Filter.Eventually.of_forall (fun k => ?_)))
    (le_of_tendsto hamiltonian_coprime_primorial_constant_limit
      (Filter.Eventually.of_forall (fun k => ?_)))
  all_goals
    have h := hamiltonian_coprime_constant_absolute_bounds
      (hamiltonianOddPrimorial k) (hamiltonian_odd_primorial_data k).1
      (hamiltonian_odd_primorial_data k).2.1
    first | exact h.1 | exact h.2

theorem hamiltonian_coprime_infinite_constant_series :
    HasSum hamiltonianCoprimeInfiniteLogCoefficient
      (Real.log hamiltonianCoprimeInfiniteConstant) := by
  rw [hamiltonianCoprimeInfiniteConstant, Real.log_exp]
  exact hamiltonian_coprime_infinite_series_summable.hasSum

end PrimeFactorOscillations
