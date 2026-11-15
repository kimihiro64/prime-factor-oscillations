/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianSpectralAmplification
import PrimeFactorOscillations.Helpers.HamiltonianWeightedCycleAsymptotics

/-! # One common logarithmic envelope for the actual weighted count

Every allowance in the complete signed count is bounded on the same
domain. The amplified two-power term is retained explicitly.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianCountLogExponent : Nat := hamiltonianMinorUniformExponent 2 + 25

def hamiltonianCountPermanentLogConstant (c delta : Real) : Real :=
  21 * c ^ 2 / delta ^ 3 +
    abs (hamiltonianPermanentUniformBudget delta) * (1 + c) ^ 24

def hamiltonianCountFirstLogConstant (c delta : Real) : Real :=
  3600 * (c / delta) ^ 3 + 4 + 3 * hamiltonianCountPermanentLogConstant c delta

def hamiltonianCountSecondLogConstant (c delta : Real) : Real :=
  8 * c * abs (hamiltonianMinorUniformConstant delta)

def hamiltonianCountLogConstant (c delta : Real) : Real :=
  1 + hamiltonianCountFirstLogConstant c delta + hamiltonianCountSecondLogConstant c delta

theorem hamiltonian_log_power_exponent_mono (L : Real) (hL : 1 <= L)
    (m n : Nat) (hmn : m <= n) : L ^ m <= L ^ n := by
  have hL0 : 0 <= L := le_trans (by norm_num) hL
  have hOne : 1 <= L ^ (n - m) := by
    simpa only [one_pow] using wick_nonnegative_power_le 1 L (by norm_num) hL (n - m)
  have h := mul_le_mul_of_nonneg_left hOne (pow_nonneg hL0 m)
  have hSplit : n = m + (n - m) := by omega
  rw [hSplit, pow_add]
  simpa only [mul_one] using h

theorem hamiltonian_inverse_square_le_inverse (n : Real) (hn : 1 <= n) :
    1 / n ^ 2 <= 1 / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hSquare : n <= n ^ 2 := by nlinarith only [hn]
  have hLeft : (1 / n ^ 2) * (n ^ 2 * n) = n := by field_simp [ne_of_gt hn0]
  have hRight : (1 / n) * (n ^ 2 * n) = n ^ 2 := by field_simp [ne_of_gt hn0]
  apply le_of_mul_le_mul_right _ (mul_pos (pow_pos hn0 2) hn0)
  rw [hLeft, hRight]
  exact hSquare

theorem hamiltonian_count_log_constant_positive (c delta : Real)
    (hc : 0 <= c) (hDelta : 0 < delta) :
    0 < hamiltonianCountLogConstant c delta := by
  unfold hamiltonianCountLogConstant hamiltonianCountFirstLogConstant
    hamiltonianCountSecondLogConstant hamiltonianCountPermanentLogConstant
  positivity

theorem hamiltonian_permanent_allowance_log_envelope
    (n : Nat) (a delta c L : Real) (hn : (1 : Real) <= n)
    (ha : 1 <= a) (hDelta : 0 < delta) (hc : 0 <= c) (hL : 1 <= L)
    (hA : a <= c * L) :
    hamiltonianPermanentCountAllowance n a delta <=
      hamiltonianCountPermanentLogConstant c delta * L ^ hamiltonianCountLogExponent / (n : Real) := by
  let H := hamiltonianCountLogExponent
  have hH2 : 2 <= H := by dsimp only [H, hamiltonianCountLogExponent]; omega
  have hH24 : 24 <= H := by dsimp only [H, hamiltonianCountLogExponent]; omega
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hL0 : 0 <= L := le_trans (by norm_num) hL
  have hn0 : 0 < (n : Real) := lt_of_lt_of_le (by norm_num) hn
  have hPower2 := hamiltonian_log_power_exponent_mono L hL 2 H hH2
  have hPower24 := hamiltonian_log_power_exponent_mono L hL 24 H hH24
  have hA2 : a ^ 2 <= c ^ 2 * L ^ H := by
    have h := wick_nonnegative_power_le a (c * L) ha0 hA 2
    have h2 := mul_le_mul_of_nonneg_left hPower2 (sq_nonneg c)
    nlinarith only [h, h2]
  have hOneA : 1 + a <= (1 + c) * L := by nlinarith only [hA, hL]
  have hA24 : (1 + a) ^ 24 <= (1 + c) ^ 24 * L ^ H := by
    have h := wick_nonnegative_power_le (1 + a) ((1 + c) * L)
      (by linarith only [ha0]) hOneA 24
    rw [mul_pow] at h
    exact le_trans h (mul_le_mul_of_nonneg_left hPower24 (by positivity))
  have hFirst :
      21 * a ^ 2 / (delta ^ 3 * (n : Real)) <=
        (21 * c ^ 2 / delta ^ 3) * L ^ H / (n : Real) := by
    calc
      _ <= (21 * (c ^ 2 * L ^ H)) / (delta ^ 3 * (n : Real)) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA2 (by norm_num)) (by positivity)
      _ = _ := by field_simp [ne_of_gt hDelta, ne_of_gt hn0] <;> ring
  have hSecond :
      abs (hamiltonianPermanentUniformBudget delta) * (1 + a) ^ 24 / (n : Real) ^ 2 <=
        (abs (hamiltonianPermanentUniformBudget delta) * (1 + c) ^ 24) *
          L ^ H / (n : Real) := by
    let C := abs (hamiltonianPermanentUniformBudget delta)
    have hC : 0 <= C := abs_nonneg _
    have hNumerator := mul_le_mul_of_nonneg_left hA24 hC
    have hWeight : 0 <= C * (1 + c) ^ 24 * L ^ H := by positivity
    have hInverse := mul_le_mul_of_nonneg_left
      (hamiltonian_inverse_square_le_inverse (n : Real) hn) hWeight
    calc
      _ <= (C * ((1 + c) ^ 24 * L ^ H)) / (n : Real) ^ 2 :=
        div_le_div_of_nonneg_right hNumerator (sq_nonneg _)
      _ = (C * (1 + c) ^ 24 * L ^ H) * (1 / (n : Real) ^ 2) := by ring
      _ <= (C * (1 + c) ^ 24 * L ^ H) * (1 / (n : Real)) := hInverse
      _ = _ := by ring
  unfold hamiltonianPermanentCountAllowance hamiltonianCountPermanentLogConstant
  change _ <= (21 * c ^ 2 / delta ^ 3 +
    abs (hamiltonianPermanentUniformBudget delta) * (1 + c) ^ 24) * L ^ H / (n : Real)
  simp only [div_eq_mul_inv] at hFirst hSecond
  simp only [div_eq_mul_inv]
  nlinarith only [hFirst, hSecond]

theorem hamiltonian_count_allowances_log_envelope
    (n : Nat) (q a delta c L gamma : Real) (hn : (1 : Real) <= n)
    (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hDelta : 0 < delta) (hc : 0 <= c) (hL : 1 <= L)
    (hA : a <= c * L) (hGamma : 0 <= gamma) :
    4 * (900 * (a / delta) ^ 3 * q +
      2 * a * (hamiltonianMinorUniformConstant delta *
        L ^ hamiltonianMinorUniformExponent 2 / (n : Real) ^ 2) * gamma +
      1 / (n : Real) ^ 2) +
      3 * hamiltonianPermanentCountAllowance n a delta <=
    hamiltonianCountLogConstant c delta * L ^ hamiltonianCountLogExponent / (n : Real) +
      hamiltonianCountLogConstant c delta * L ^ hamiltonianCountLogExponent * gamma /
        (n : Real) ^ 2 := by
  let H := hamiltonianCountLogExponent
  let M := hamiltonianMinorUniformExponent 2
  let C := hamiltonianMinorUniformConstant delta
  have hn0 : 0 < (n : Real) := lt_of_lt_of_le (by norm_num) hn
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hL0 : 0 <= L := le_trans (by norm_num) hL
  have hCap0 : 0 <= c * L := mul_nonneg hc hL0
  have hH3 : 3 <= H := by dsimp only [H, hamiltonianCountLogExponent]; omega
  have hHM : M + 1 <= H := by dsimp only [H, M, hamiltonianCountLogExponent]; omega
  have hPower3 := hamiltonian_log_power_exponent_mono L hL 3 H hH3
  have hPowerM := hamiltonian_log_power_exponent_mono L hL (M + 1) H hHM
  have hPowerOne : 1 <= L ^ H := by
    simpa only [one_pow] using wick_nonnegative_power_le 1 L (by norm_num) hL H
  have hQ : q = 1 / (n : Real) := by
    calc
      _ = ((n : Real) * q) / (n : Real) := by field_simp [ne_of_gt hn0]
      _ = _ := by rw [hq]
  have hDiv : a / delta <= (c / delta) * L := by
    have h := div_le_div_of_nonneg_right hA (le_of_lt hDelta)
    convert h using 1 <;> ring
  have hDivPower := wick_nonnegative_power_le _ _
    (div_nonneg ha0 (le_of_lt hDelta)) hDiv 3
  have hRatio0 : 0 <= c / delta := div_nonneg hc (le_of_lt hDelta)
  have hFirst :
      900 * (a / delta) ^ 3 * q <=
        900 * (c / delta) ^ 3 * L ^ H / (n : Real) := by
    have hPowerBound : (a / delta) ^ 3 <= (c / delta) ^ 3 * L ^ H := by
      rw [mul_pow] at hDivPower
      exact le_trans hDivPower (mul_le_mul_of_nonneg_left hPower3 (pow_nonneg hRatio0 3))
    rw [hQ]
    have h := mul_le_mul_of_nonneg_left hPowerBound (by norm_num : (0 : Real) <= 900)
    have h2 := div_le_div_of_nonneg_right h (le_of_lt hn0)
    convert h2 using 1 <;> ring
  have hAC : a * C <= c * L * abs C := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self C) ha0
    have h2 := mul_le_mul_of_nonneg_right hA (abs_nonneg C)
    exact le_trans h1 h2
  have hMinorNumerator : 2 * a * C * L ^ M <= 2 * c * abs C * L ^ H := by
    have h1 := mul_le_mul_of_nonneg_right hAC (pow_nonneg hL0 M)
    have hCoeff : (0 : Real) <= 2 * c * abs C := by positivity
    have h2 := mul_le_mul_of_nonneg_left hPowerM hCoeff
    rw [pow_succ] at h2
    nlinarith only [h1, h2]
  have hMinor :
      2 * a * (C * L ^ M / (n : Real) ^ 2) * gamma <=
        2 * c * abs C * L ^ H * gamma / (n : Real) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hMinorNumerator hGamma
    have h2 := div_le_div_of_nonneg_right h1 (sq_nonneg (n : Real))
    convert h2 using 1 <;> ring
  have hTail : 1 / (n : Real) ^ 2 <= L ^ H / (n : Real) := by
    have h := mul_le_mul_of_nonneg_right hPowerOne
      (div_nonneg (by norm_num : (0 : Real) <= 1) (le_of_lt hn0))
    calc
      _ <= 1 / (n : Real) := hamiltonian_inverse_square_le_inverse (n : Real) hn
      _ <= L ^ H * (1 / (n : Real)) := by simpa only [one_mul] using h
      _ = _ := by ring
  have hPer := hamiltonian_permanent_allowance_log_envelope n a delta c L hn ha hDelta hc hL hA
  change hamiltonianPermanentCountAllowance n a delta <=
    hamiltonianCountPermanentLogConstant c delta * L ^ H / (n : Real) at hPer
  let F := hamiltonianCountFirstLogConstant c delta
  let G := hamiltonianCountSecondLogConstant c delta
  have hRaw :
      4 * (900 * (a / delta) ^ 3 * q + 2 * a * (C * L ^ M / (n : Real) ^ 2) * gamma +
        1 / (n : Real) ^ 2) + 3 * hamiltonianPermanentCountAllowance n a delta <=
      F * L ^ H / (n : Real) + G * L ^ H * gamma / (n : Real) ^ 2 := by
    dsimp only [F, G, hamiltonianCountFirstLogConstant, hamiltonianCountSecondLogConstant]
    change _ <= (3600 * (c / delta) ^ 3 + 4 + 3 * hamiltonianCountPermanentLogConstant c delta) *
      L ^ H / (n : Real) + (8 * c * abs C) * L ^ H * gamma / (n : Real) ^ 2
    simp only [div_eq_mul_inv] at hFirst hMinor hTail hPer
    simp only [div_eq_mul_inv]
    nlinarith only [hFirst, hMinor, hTail, hPer]
  have hF0 : 0 <= F := by
    dsimp only [F, hamiltonianCountFirstLogConstant, hamiltonianCountPermanentLogConstant]
    positivity
  have hG0 : 0 <= G := by
    dsimp only [G, hamiltonianCountSecondLogConstant]
    positivity
  have hF : F <= hamiltonianCountLogConstant c delta := by
    change F <= 1 + F + G
    linarith only [hG0]
  have hG : G <= hamiltonianCountLogConstant c delta := by
    change G <= 1 + F + G
    linarith only [hF0]
  have hWeight1 : 0 <= L ^ H / (n : Real) := div_nonneg (pow_nonneg hL0 H) (le_of_lt hn0)
  have hWeight2 : 0 <= L ^ H * gamma / (n : Real) ^ 2 := by positivity
  have hFirstFinal := mul_le_mul_of_nonneg_right hF hWeight1
  have hSecondFinal := mul_le_mul_of_nonneg_right hG hWeight2
  change 4 * (900 * (a / delta) ^ 3 * q +
    2 * a * (C * L ^ M / (n : Real) ^ 2) * gamma + 1 / (n : Real) ^ 2) +
    3 * hamiltonianPermanentCountAllowance n a delta <=
    hamiltonianCountLogConstant c delta * L ^ H / (n : Real) +
    hamiltonianCountLogConstant c delta * L ^ H * gamma / (n : Real) ^ 2
  simp only [div_eq_mul_inv] at hRaw hFirstFinal hSecondFinal
  simp only [div_eq_mul_inv]
  nlinarith only [hRaw, hFirstFinal, hSecondFinal]


universe u

theorem stochastic_weighted_cycle_log_envelope_uniform
    (delta c : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hc : 0 <= c) :
    exists C : Real, 0 < C /\
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
              C * (Real.log (2 * (Fintype.card J : Real))) ^ hamiltonianCountLogExponent /
                (Fintype.card J : Real) +
              C * (Real.log (2 * (Fintype.card J : Real))) ^ hamiltonianCountLogExponent *
                hamiltonianGramAmplification T q / (Fintype.card J : Real) ^ 2 := by
  let C := hamiltonianCountLogConstant c delta
  refine Exists.intro C (And.intro (hamiltonian_count_log_constant_positive c delta hc hDelta) ?_)
  have hRange := stochastic_weighted_cycle_comparison_inverse_square_tail_uniform.{u}
    delta c hDelta hDelta1 hc
  refine hRange.elim ?_
  intro NC hNC
  let N0 := max NC (Nat.ceil (Real.exp 1))
  refine Exists.intro N0 (And.intro (le_trans hNC.1 (le_max_left _ _)) ?_)
  intro J instF instD instN hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hnC : NC <= Fintype.card J := le_trans (le_max_left _ _) hn
  have hnCeil : Nat.ceil (Real.exp 1) <= Fintype.card J := le_trans (le_max_right _ _) hn
  have hN256 : (256 : Real) <= Fintype.card J := by exact_mod_cast le_trans hNC.1 hnC
  have hN1 : (1 : Real) <= Fintype.card J := by linarith only [hN256]
  have hN : 0 < (Fintype.card J : Real) := by linarith only [hN256]
  have hExp : Real.exp 1 <= (Fintype.card J : Real) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hnCeil)
  have hLogN : 1 <= Real.log (Fintype.card J : Real) := by
    have h := Real.log_le_log (Real.exp_pos 1) hExp
    simpa only [Real.log_exp] using h
  have hLog2 : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
  have hLogMul : Real.log (2 * (Fintype.card J : Real)) =
      Real.log 2 + Real.log (Fintype.card J : Real) :=
    Real.log_mul (by norm_num) (ne_of_gt hN)
  have hL : 1 <= Real.log (2 * (Fintype.card J : Real)) := by
    linarith only [hLogN, hLog2, hLogMul]
  let B := centeredKernel T q
  have hPlus := (hamiltonian_hermitian_euler_positive_bound_at
    (B.transpose * B) (realGramHermitian B)
    (fun i => realGramEigenvalues_nonnegative B i) 1 (by norm_num)).1
  have hPlusPositive : 0 < Matrix.det ((1 : Matrix J J Real) + B.transpose * B) := by
    simpa only [one_smul] using hPlus
  have hMinusPositive := stochastic_centered_determinant_positive T q a delta
    hq hDelta hDelta1 hRow hNonneg hUpper hNorm
  have hAmp : 0 <= hamiltonianGramAmplification T q :=
    div_nonneg (le_of_lt hPlusPositive) (le_of_lt hMinusPositive)
  have hCount := hNC.2 J hnC T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  exact le_trans hCount
    (hamiltonian_count_allowances_log_envelope (Fintype.card J) q a delta c
      (Real.log (2 * (Fintype.card J : Real))) (hamiltonianGramAmplification T q)
      hN1 hq ha hDelta hc hL hA hAmp)


theorem hamiltonian_unoriented_cycle_ratio_identity
    {J : Type*} [Fintype J] [DecidableEq J] (T : Matrix J J Real) :
    hamiltonianBipartiteCountRatio T =
      (2 * (Fintype.card J : Real) *
        (Fintype.card J : Real) ^ (2 * Fintype.card J) /
        ((Fintype.card J).factorial : Real) ^ 2) *
        (hamiltonianCycleSum (bipartiteLift T) / 2) := by
  let n := Fintype.card J
  let N : Real := n
  have hPower : N ^ (2 * n) = (N ^ n) ^ 2 := by rw [Nat.mul_comm 2 n, pow_mul]
  unfold hamiltonianBipartiteCountRatio
  change (N ^ n / (n.factorial : Real)) ^ 2 *
    (N * hamiltonianCycleSum (bipartiteLift T)) =
    (2 * N * N ^ (2 * n) / (n.factorial : Real) ^ 2) *
      (hamiltonianCycleSum (bipartiteLift T) / 2)
  rw [div_pow, hPower]
  ring

theorem stochastic_unoriented_bipartite_log_envelope_uniform
    (rho c : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1) (hc : 0 <= c) :
    exists C : Real, 0 < C /\
      exists N0 : Nat, 256 <= N0 /\
        forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
          N0 <= Fintype.card J ->
          forall (T : Matrix J J Real) (q a : Real),
            (Fintype.card J : Real) * q = 1 -> 1 <= a ->
            a <= c * Real.log (2 * (Fintype.card J : Real)) ->
            (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
            (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
            (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
            norm (centeredKernel T q) <= rho ->
            abs ((2 * (Fintype.card J : Real) *
              (Fintype.card J : Real) ^ (2 * Fintype.card J) /
              ((Fintype.card J).factorial : Real) ^ 2) *
              (hamiltonianCycleSum (bipartiteLift T) / 2) - 1) <=
              C * (Real.log (2 * (Fintype.card J : Real))) ^ hamiltonianCountLogExponent /
                (Fintype.card J : Real) +
              C * (Real.log (2 * (Fintype.card J : Real))) ^ hamiltonianCountLogExponent *
                (Matrix.det ((1 : Matrix J J Real) +
                    centeredKernel T q * (centeredKernel T q).transpose) /
                  Matrix.det ((1 : Matrix J J Real) -
                    centeredKernel T q * (centeredKernel T q).transpose)) /
                (Fintype.card J : Real) ^ 2 := by
  have hDelta : 0 < 1 - rho := sub_pos.mpr hRho1
  have hDelta1 : 1 - rho <= 1 := by linarith only [hRho0]
  have hRange := stochastic_weighted_cycle_log_envelope_uniform.{u}
    (1 - rho) c hDelta hDelta1 hc
  refine hRange.elim ?_
  intro C hC
  refine Exists.intro C (And.intro hC.1 ?_)
  refine hC.2.elim ?_
  intro N0 hN0
  refine Exists.intro N0 (And.intro hN0.1 ?_)
  intro J instF instD instN hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hGap : 1 - (1 - rho) = rho := by ring
  have hNormDelta : norm (centeredKernel T q) <= 1 - (1 - rho) := by rw [hGap]; exact hNorm
  have hCount := hN0.2 J hn T q a hq ha hA hRow hCol hNonneg hUpper hNormDelta
  rw [hamiltonian_unoriented_cycle_ratio_identity] at hCount
  unfold hamiltonianGramAmplification at hCount
  rw [hamiltonian_gram_amplification_swap (centeredKernel T q)] at hCount
  exact hCount

end PrimeFactorOscillations
