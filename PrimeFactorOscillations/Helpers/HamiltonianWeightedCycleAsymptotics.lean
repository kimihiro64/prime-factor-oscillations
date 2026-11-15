/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianWeightedCycleComparison

/-! # Scalar closure of the actual weighted cycle comparison

The same two independently proved allowances are retained. The
permanent allowance is made at most one and the divided tail is
absorbed into two inverse powers of the matrix order.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_cycle_error_allowances_linear
    (p e : Real) (hp : 0 <= p) (hp1 : p <= 1) (he : 0 <= e) :
    (1 + p) ^ 2 * e + (2 + p) * p <= 4 * e + 3 * p := by
  have hSquare : (1 + p) ^ 2 <= 4 := by nlinarith only [hp, hp1]
  have hFirst := mul_le_mul_of_nonneg_right hSquare he
  have hSecond := mul_le_mul_of_nonneg_right hp1 hp
  nlinarith only [hFirst, hSecond]

theorem hamiltonian_divided_tail_inverse_square
    (n a c delta L : Real) (hn : 1 <= n) (hDelta : 0 < delta)
    (hc : 0 <= c) (hL : 1 <= L) (hLog : 1 <= Real.log L)
    (hNLog : Real.log n <= L) (hA : a <= c * L)
    (hLarge : 4 * (c / delta + 2) <= L) :
    Real.exp (-(L ^ 3 * Real.log L) / 4 + (a - 1) / delta) <= 1 / n ^ 2 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hL0 : 0 <= L := le_trans (by norm_num) hL
  have hLSquare : L <= L ^ 2 := by nlinarith only [hL]
  have hLarge2 : 4 * (c / delta + 2) <= L ^ 2 := le_trans hLarge hLSquare
  have hLarge3 := mul_le_mul_of_nonneg_right hLarge2 hL0
  have hDamping := mul_le_mul_of_nonneg_left hLog (pow_nonneg hL0 3)
  have hAMinus : a - 1 <= c * L := by linarith only [hA]
  have hDiv := div_le_div_of_nonneg_right hAMinus (le_of_lt hDelta)
  have hRatio : (c * L) / delta = (c / delta) * L := by ring
  rw [hRatio] at hDiv
  have hExponent :
      -(L ^ 3 * Real.log L) / 4 + (a - 1) / delta <= -2 * Real.log n := by
    nlinarith only [hLarge3, hDamping, hDiv, hNLog]
  have hPower : Real.exp (2 * Real.log n) = n ^ (2 : Nat) := by
    have h := hamiltonian_exp_nat_scalar (Real.log n) 2
    norm_num only [Nat.cast_ofNat] at h
    rw [Real.exp_log hn0] at h
    exact h
  calc
    _ <= Real.exp (-2 * Real.log n) := Real.exp_le_exp.mpr hExponent
    _ = 1 / n ^ 2 := by
      rw [show -2 * Real.log n = -(2 * Real.log n) by ring, Real.exp_neg, hPower, one_div]

theorem hamiltonian_permanent_count_allowance_unit_uniform
    (delta c : Real) (hDelta : 0 < delta) (hc : 0 <= c) :
    exists N0 : Nat, 256 <= N0 /\
      forall n : Nat, N0 <= n -> forall a : Real,
        1 <= a -> a <= c * Real.log (2 * (n : Real)) ->
          0 <= hamiltonianPermanentCountAllowance n a delta /\
          hamiltonianPermanentCountAllowance n a delta <= 1 := by
  have hRange := hamiltonian_permanent_polylog_first_order_budget delta 2 hDelta (by norm_num)
  refine hRange.elim ?_
  intro NP hNP
  let N0 := max 256 (max NP (Nat.ceil (Real.exp (2 * c))))
  refine Exists.intro N0 (And.intro (le_max_left _ _) ?_)
  intro n hn a ha hA
  have hnP : NP <= n := le_trans (le_trans (le_max_left NP _) (le_max_right 256 _)) hn
  have hnCeil : Nat.ceil (Real.exp (2 * c)) <= n :=
    le_trans (le_trans (le_max_right NP _) (le_max_right 256 _)) hn
  have hn256 : (256 : Real) <= n := by exact_mod_cast le_trans (le_max_left 256 _) hn
  have hn2 : (2 : Real) <= n := by linarith only [hn256]
  have hn1 : (1 : Real) <= n := by linarith only [hn256]
  have hExp : Real.exp (2 * c) <= (n : Real) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hnCeil)
  have hLog : 2 * c <= Real.log (n : Real) := by
    have h := Real.log_le_log (Real.exp_pos _) hExp
    simpa only [Real.log_exp] using h
  have hAPolyNat := hamiltonian_logarithmic_cap_square (n : Real) a c hn2 hc hLog hA
  have hRealTwo : (Real.log (n : Real)) ^ (2 : Real) =
      (Real.log (n : Real)) ^ (2 : Nat) := by
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log (n : Real)) 2
  have hAPoly : a <= (Real.log (n : Real)) ^ (2 : Real) := by rw [hRealTwo]; exact hAPolyNat
  have hScalar := hNP.2 n hnP a ha hAPoly
  have hp : 0 <= hamiltonianPermanentCountAllowance n a delta := by
    unfold hamiltonianPermanentCountAllowance
    positivity
  refine And.intro hp ?_
  exact le_trans hScalar (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num))

universe u

theorem stochastic_weighted_cycle_comparison_linear_uniform
    (delta c : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hc : 0 <= c) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          a <= c * Real.log (2 * (Fintype.card J : Real)) ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          abs (hamiltonianBipartiteCountRatio T - 1) <=
            4 * hamiltonianSignedCountAllowance T q a delta +
              3 * hamiltonianPermanentCountAllowance (Fintype.card J) a delta := by
  have hCountRange := stochastic_weighted_cycle_comparison_logarithmic_uniform.{u}
    delta c hDelta hDelta1 hc
  have hScalarRange := hamiltonian_permanent_count_allowance_unit_uniform delta c hDelta hc
  have hRelativeRange := stochastic_relative_bipartite_comparison_logarithmic_uniform.{u}
    delta c hDelta hDelta1 hc
  refine hCountRange.elim ?_
  intro NC hNC
  refine hScalarRange.elim ?_
  intro NP hNP
  refine hRelativeRange.elim ?_
  intro NR hNR
  let N0 := max NC (max NP NR)
  refine Exists.intro N0 (And.intro (le_trans hNC.1 (le_max_left _ _)) ?_)
  intro J instF instD instN hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hnC : NC <= Fintype.card J := le_trans (le_max_left _ _) hn
  have hnP : NP <= Fintype.card J :=
    le_trans (le_trans (le_max_left NP _) (le_max_right NC _)) hn
  have hnR : NR <= Fintype.card J :=
    le_trans (le_trans (le_max_right NP _) (le_max_right NC _)) hn
  have hCount := hNC.2 J hnC T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hP := hNP.2 (Fintype.card J) hnP a ha hA
  have hRelative := hNR.2 J hnR T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hE : 0 <= hamiltonianSignedCountAllowance T q a delta :=
    le_trans (abs_nonneg _) hRelative.2.2
  exact le_trans hCount
    (hamiltonian_cycle_error_allowances_linear _ _ hP.1 hP.2 hE)


theorem hamiltonian_divided_tail_logarithmic_uniform
    (delta c : Real) (hDelta : 0 < delta) (hc : 0 <= c) :
    exists N0 : Nat, 256 <= N0 /\
      forall n : Nat, N0 <= n -> forall a : Real,
        a <= c * Real.log (2 * (n : Real)) ->
        Real.exp (-((Real.log (2 * (n : Real))) ^ 3 *
          Real.log (Real.log (2 * (n : Real)))) / 4 + (a - 1) / delta) <=
            1 / (n : Real) ^ 2 := by
  let x0 := 2 + Real.exp 1 + 4 * (c / delta + 2)
  let N0 := max 256 (Nat.ceil (Real.exp x0))
  refine Exists.intro N0 (And.intro (le_max_left _ _) ?_)
  intro n hn a hA
  have hn256 : (256 : Real) <= n := by exact_mod_cast le_trans (le_max_left 256 _) hn
  have hn1 : (1 : Real) <= n := by linarith only [hn256]
  have hn0 : 0 < (n : Real) := by linarith only [hn256]
  have hnCeil : Nat.ceil (Real.exp x0) <= n := le_trans (le_max_right _ _) hn
  have hExp : Real.exp x0 <= (n : Real) := le_trans (Nat.le_ceil _) (by exact_mod_cast hnCeil)
  have hLogN : x0 <= Real.log (n : Real) := by
    have h := Real.log_le_log (Real.exp_pos x0) hExp
    simpa only [Real.log_exp] using h
  have hRatio : 0 <= c / delta := div_nonneg hc (le_of_lt hDelta)
  have hExp1 : 0 < Real.exp 1 := Real.exp_pos 1
  have hLog2 : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
  have hLogMul : Real.log (2 * (n : Real)) = Real.log 2 + Real.log (n : Real) :=
    Real.log_mul (by norm_num) (ne_of_gt hn0)
  have hNLog : Real.log (n : Real) <= Real.log (2 * (n : Real)) := by
    linarith only [hLogMul, hLog2]
  have hL : 1 <= Real.log (2 * (n : Real)) := by
    dsimp only [x0] at hLogN
    linarith only [hLogN, hNLog, hRatio, hExp1]
  have hLExp : Real.exp 1 <= Real.log (2 * (n : Real)) := by
    dsimp only [x0] at hLogN
    linarith only [hLogN, hNLog, hRatio]
  have hLog : 1 <= Real.log (Real.log (2 * (n : Real))) := by
    have h := Real.log_le_log (Real.exp_pos 1) hLExp
    simpa only [Real.log_exp] using h
  have hLarge : 4 * (c / delta + 2) <= Real.log (2 * (n : Real)) := by
    dsimp only [x0] at hLogN
    linarith only [hLogN, hNLog, hExp1]
  exact hamiltonian_divided_tail_inverse_square (n : Real) a c delta
    (Real.log (2 * (n : Real))) hn1 hDelta hc hL hLog hNLog hA hLarge

theorem stochastic_weighted_cycle_comparison_inverse_square_tail_uniform
    (delta c : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hc : 0 <= c) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          a <= c * Real.log (2 * (Fintype.card J : Real)) ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          abs (hamiltonianBipartiteCountRatio T - 1) <=
            4 * (900 * (a / delta) ^ 3 * q +
              2 * a * (hamiltonianMinorUniformConstant delta *
                (Real.log (2 * (Fintype.card J : Real))) ^ hamiltonianMinorUniformExponent 2 /
                  (Fintype.card J : Real) ^ 2) * hamiltonianGramAmplification T q +
              1 / (Fintype.card J : Real) ^ 2) +
              3 * hamiltonianPermanentCountAllowance (Fintype.card J) a delta := by
  have hCountRange := stochastic_weighted_cycle_comparison_linear_uniform.{u}
    delta c hDelta hDelta1 hc
  have hTailRange := hamiltonian_divided_tail_logarithmic_uniform delta c hDelta hc
  refine hCountRange.elim ?_
  intro NC hNC
  refine hTailRange.elim ?_
  intro NT hNT
  let N0 := max NC NT
  refine Exists.intro N0 (And.intro (le_trans hNC.1 (le_max_left _ _)) ?_)
  intro J instF instD instN hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hnC : NC <= Fintype.card J := le_trans (le_max_left _ _) hn
  have hnT : NT <= Fintype.card J := le_trans (le_max_right _ _) hn
  have hCount := hNC.2 J hnC T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hTail := hNT.2 (Fintype.card J) hnT a hA
  unfold hamiltonianSignedCountAllowance at hCount
  linarith only [hCount, hTail]

end PrimeFactorOscillations
