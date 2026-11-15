/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermanentPositivity
import PrimeFactorOscillations.Helpers.HamiltonianRectangularPermanentUpper

/-! # The full normalized complementary-permanent upper bound

The existing normalized positivity theorem supplies the denominator.
The factorial exponential lower bound is derived from the positive
exponential series. Every complementary rank, both independent
supports and the scalar factor two are retained.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_factorial_exponential_lower (n : Nat) (hn : 1 <= n) :
    Real.exp (-(n : Real)) <= (n.factorial : Real) / (n : Real) ^ n := by
  have hN : 0 < (n : Real) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  have hPower : 0 < (n : Real) ^ n := pow_pos hN n
  have hFact : 0 < (n.factorial : Real) := by exact_mod_cast Nat.factorial_pos n
  have h := Real.pow_div_factorial_le_exp (n : Real) (le_of_lt hN) n
  have hScaled := mul_le_mul_of_nonneg_right h (le_of_lt hFact)
  have hClear : ((n : Real) ^ n / (n.factorial : Real)) * (n.factorial : Real) =
      (n : Real) ^ n := by field_simp [ne_of_gt hFact]
  rw [hClear] at hScaled
  have hExp : Real.exp (-(n : Real)) * Real.exp (n : Real) = 1 := by
    rw [<- Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hProduct : Real.exp (-(n : Real)) * (n : Real) ^ n <= (n.factorial : Real) := by
    calc
      _ <= Real.exp (-(n : Real)) * (Real.exp (n : Real) * (n.factorial : Real)) :=
        mul_le_mul_of_nonneg_left hScaled (le_of_lt (Real.exp_pos _))
      _ = _ := by rw [<- mul_assoc, hExp, one_mul]
  have hRatioClear : ((n.factorial : Real) / (n : Real) ^ n) * (n : Real) ^ n =
      (n.factorial : Real) := by field_simp [ne_of_gt hPower]
  apply le_of_mul_le_mul_right _ hPower
  rw [hRatioClear]
  exact hProduct

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_rectangular_permanent_nonnegative
    (T : Matrix Iota Iota Real) (S U : Finset Iota)
    (hNonneg : forall i j, 0 <= T i j) :
    0 <= rectangularMinorPermanent T S U := by
  unfold rectangularMinorPermanent
  split
  next h =>
    unfold finitePermutationSum
    exact Finset.sum_nonneg (fun sigma _ => Finset.prod_nonneg (fun i _ => hNonneg _ _))
  next h => exact le_refl 0

variable [Nonempty Iota]

theorem hamiltonian_positive_permanent_exponential_lower
    (T : Matrix Iota Iota Real) (q : Real) (hData : hamiltonianPermanentPositiveData T q) :
    (1 / 2 : Real) * Real.exp (-(Fintype.card Iota : Real)) <= weightedPermutationSum T := by
  let n := Fintype.card Iota
  let P := weightedPermutationSum T
  let D := realGramDeterminantFactor (centeredKernel T q) 1
  let C := (n : Real) ^ n / (n.factorial : Real)
  let R := (n.factorial : Real) / (n : Real) ^ n
  have hn : 1 <= n :=
    Nat.succ_le_of_lt (show 0 < Fintype.card Iota from Fintype.card_pos)
  have hN : 0 < (n : Real) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hPower : 0 < (n : Real) ^ n := pow_pos hN n
  have hFact : 0 < (n.factorial : Real) := by exact_mod_cast Nat.factorial_pos n
  have hD : 1 <= D := hData.2.1
  have hDPos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hHalf : (1 / 2 : Real) <= C * P / D := hData.1
  have hMult := mul_le_mul_of_nonneg_right hHalf (le_of_lt hDPos)
  have hClear : (C * P / D) * D = C * P := by field_simp [ne_of_gt hDPos]
  rw [hClear] at hMult
  have hCP : (1 / 2 : Real) <= C * P := by nlinarith only [hMult, hD]
  have hR : 0 <= R := div_nonneg (le_of_lt hFact) (le_of_lt hPower)
  have hRC : R * C = 1 := by
    dsimp only [R, C]
    field_simp [ne_of_gt hFact, ne_of_gt hPower]
  have hMulR := mul_le_mul_of_nonneg_left hCP hR
  have hRCProduct : R * (C * P) = P := by rw [<- mul_assoc, hRC, one_mul]
  rw [hRCProduct] at hMulR
  calc
    _ <= (1 / 2 : Real) * R :=
      mul_le_mul_of_nonneg_left (hamiltonian_factorial_exponential_lower n hn) (by norm_num)
    _ = R * (1 / 2 : Real) := by ring
    _ <= _ := hMulR

theorem stochastic_complementary_permanent_ratio_upper
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (q a : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hNonneg : forall i j, 0 <= T i j)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hCap : forall i j, T i j <= a * q)
    (hData : hamiltonianPermanentPositiveData T q) :
    0 <= rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) / weightedPermutationSum T /\
    rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) / weightedPermutationSum T <=
      2 * Real.exp ((U.card : Real) + 16 * a * Real.log (2 * (Fintype.card Iota : Real))) := by
  let N : Real := Fintype.card Iota
  let r : Real := U.card
  let P := weightedPermutationSum T
  let M := rectangularMinorPermanent T (Compl.compl S) (Compl.compl U)
  let L := 16 * a * Real.log (2 * N)
  have hP : 0 < P := hData.2.2
  have hMinor : 0 <= M :=
    hamiltonian_rectangular_permanent_nonnegative T _ _ hNonneg
  have hLower : (1 / 2 : Real) * Real.exp (-N) <= P :=
    hamiltonian_positive_permanent_exponential_lower T q hData
  have hUpper : M <= Real.exp (r - N + L) :=
    stochastic_complementary_permanent_upper T S U q a hq ha hNonneg hCol hCap
  have hFactor : 0 <= 2 * Real.exp (r + L) :=
    mul_nonneg (by norm_num) (le_of_lt (Real.exp_pos _))
  have hScaled := mul_le_mul_of_nonneg_left hLower hFactor
  have hExp : 2 * Real.exp (r + L) * ((1 / 2 : Real) * Real.exp (-N)) =
      Real.exp (r - N + L) := by
    calc
      _ = Real.exp (r + L) * Real.exp (-N) := by ring
      _ = Real.exp ((r + L) + (-N)) := (Real.exp_add _ _).symm
      _ = _ := congrArg Real.exp (by ring)
  rw [hExp] at hScaled
  have hProduct : M <= 2 * Real.exp (r + L) * P := le_trans hUpper hScaled
  have hClear : (M / P) * P = M := by field_simp [ne_of_gt hP]
  refine And.intro (div_nonneg hMinor (le_of_lt hP)) ?_
  apply le_of_mul_le_mul_right _ hP
  change (M / P) * P <= (2 * Real.exp (r + L)) * P
  rw [hClear]
  exact hProduct

universe u

theorem stochastic_complementary_ratio_polylog_uniform (delta K : Real)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hK : 0 <= K) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          a <= (Real.log (Fintype.card J : Real)) ^ K ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          forall S U : Finset J,
            0 <= rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) / weightedPermutationSum T /\
            rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) / weightedPermutationSum T <=
              2 * Real.exp ((U.card : Real) + 16 * a * Real.log (2 * (Fintype.card J : Real))) := by
  have hRange := stochastic_permanent_positive_polylog_uniform.{u} delta K hDelta hDelta1 hK
  refine hRange.elim ?_
  intro N0 hN0
  refine Exists.intro N0 (And.intro hN0.1 ?_)
  intro J instF instD instN hn T q a hq ha hA hRow hCol hNonneg hCap hNorm S U
  have hData := hN0.2 J hn T q a hq ha hA hRow hCol hNonneg hCap hNorm
  exact stochastic_complementary_permanent_ratio_upper T S U q a hq ha hNonneg hCol hCap hData

end PrimeFactorOscillations
