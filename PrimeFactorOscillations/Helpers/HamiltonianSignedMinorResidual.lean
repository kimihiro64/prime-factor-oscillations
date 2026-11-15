/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAbsoluteMinorMass
import PrimeFactorOscillations.Helpers.HamiltonianMinorUniformExpansion

/-! # The actual small-minor residual in the signed Hamiltonian formula

The full first-order term is evaluated separately with its signs.
Only the retained pointwise error is charged to absolute Gram mass.
Both independent deleted supports and the exact rank weight remain.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

universe u

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianMinorResidualPacket (T : Matrix Iota Iota Real)
    (E : Finset Iota -> Finset Iota -> Real) : Real :=
  -Finset.univ.sum (fun U : Finset Iota =>
    (-1 : Real) ^ U.card * (U.card : Real) *
      (Finset.univ.powersetCard U.card).sum
        (fun S => rectangularMinorDet T S U ^ 2 * E S U))

theorem hamiltonian_minor_residual_absolute_mass
    (T : Matrix Iota Iota Real) (E : Finset Iota -> Finset Iota -> Real)
    (eps : Real)
    (hError : forall S U, Membership.mem (Finset.univ.powersetCard U.card) S ->
      abs (E S U) <= eps) :
    abs (hamiltonianMinorResidualPacket T E) <= eps * hamiltonianAbsoluteMinorMass T := by
  have hInner (U : Finset Iota) :
      abs ((Finset.univ.powersetCard U.card).sum
        (fun S => rectangularMinorDet T S U ^ 2 * E S U)) <=
      eps * (Finset.univ.powersetCard U.card).sum (fun S => rectangularMinorDet T S U ^ 2) := by
    calc
      _ <= (Finset.univ.powersetCard U.card).sum
          (fun S => abs (rectangularMinorDet T S U ^ 2 * E S U)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= (Finset.univ.powersetCard U.card).sum
          (fun S => eps * rectangularMinorDet T S U ^ 2) := by
        apply Finset.sum_le_sum
        intro S hS
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        have h := mul_le_mul_of_nonneg_left (hError S U hS) (sq_nonneg (rectangularMinorDet T S U))
        nlinarith only [h]
      _ = _ := (Finset.mul_sum _ _ _).symm
  unfold hamiltonianMinorResidualPacket
  rw [abs_neg]
  calc
    _ <= Finset.univ.sum (fun U : Finset Iota => abs
        ((-1 : Real) ^ U.card * (U.card : Real) *
          (Finset.univ.powersetCard U.card).sum
            (fun S => rectangularMinorDet T S U ^ 2 * E S U))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.univ.sum (fun U : Finset Iota => (U.card : Real) *
        (eps * (Finset.univ.powersetCard U.card).sum (fun S => rectangularMinorDet T S U ^ 2))) := by
      apply Finset.sum_le_sum
      intro U hU
      have hCardNonneg : (0 : Real) <= (U.card : Real) := Nat.cast_nonneg U.card
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg hCardNonneg]
      exact mul_le_mul_of_nonneg_left (hInner U) hCardNonneg
    _ = _ := by
      unfold hamiltonianAbsoluteMinorMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      ring

theorem stochastic_minor_residual_bound
    (T : Matrix Iota Iota Real) (E : Finset Iota -> Finset Iota -> Real)
    (q a eps : Real) (hEps : 0 <= eps)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hError : forall S U, Membership.mem (Finset.univ.powersetCard U.card) S ->
      abs (E S U) <= eps) :
    abs (hamiltonianMinorResidualPacket T E) <=
      2 * a * eps * Matrix.det ((1 : Matrix Iota Iota Real) +
        (centeredKernel T q).transpose * centeredKernel T q) := by
  calc
    _ <= eps * hamiltonianAbsoluteMinorMass T :=
      hamiltonian_minor_residual_absolute_mass T E eps hError
    _ <= eps * (2 * a * Matrix.det ((1 : Matrix Iota Iota Real) +
        (centeredKernel T q).transpose * centeredKernel T q)) :=
      mul_le_mul_of_nonneg_left
        (stochastic_absolute_minor_mass_bound T q a hq hRow hCol hNonneg hUpper) hEps
    _ = _ := by ring

def hamiltonianSmallMinorError (T : Matrix Iota Iota Real) (q R : Real)
    (S U : Finset Iota) : Real :=
  if (U.card : Real) <= R then
    (rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
      weightedPermutationSum T) ^ 2 - (1 + hamiltonianMinorFirstOrder T S U q)
  else 0

theorem stochastic_small_minor_residual_polylog_uniform (delta K : Real)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hK : 0 <= K) :
    exists N0 : Nat, 32 <= N0 /\
      forall (Iota : Type u) [Fintype Iota] [DecidableEq Iota] [Nonempty Iota],
        N0 <= Fintype.card Iota ->
        forall (T : Matrix Iota Iota Real) (q a : Real),
          (Fintype.card Iota : Real) * q = 1 -> 1 <= a ->
          a <= (Real.log (Fintype.card Iota : Real)) ^ K ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          0 < weightedPermutationSum T /\
          abs (hamiltonianMinorResidualPacket T
            (hamiltonianSmallMinorError T q ((Real.log (2 * (Fintype.card Iota : Real))) ^ 3))) <=
              2 * a * (hamiltonianMinorUniformConstant delta *
                (Real.log (2 * (Fintype.card Iota : Real))) ^ hamiltonianMinorUniformExponent K /
                  (Fintype.card Iota : Real) ^ 2) *
              Matrix.det ((1 : Matrix Iota Iota Real) +
                (centeredKernel T q).transpose * centeredKernel T q) := by
  have hData := stochastic_minor_two_power_polylog_uniform.{u} delta K hDelta hDelta1 hK
  have hConstant : 0 < hamiltonianMinorUniformConstant delta := hData.1
  refine hData.2.elim ?_
  intro N0 hN0
  refine Exists.intro N0 (And.intro hN0.1 ?_)
  intro Iota instF instD instN hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  let eps := hamiltonianMinorUniformConstant delta *
    (Real.log (2 * (Fintype.card Iota : Real))) ^ hamiltonianMinorUniformExponent K /
      (Fintype.card Iota : Real) ^ 2
  have hN : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hN32 : (32 : Real) <= Fintype.card Iota := by exact_mod_cast le_trans hN0.1 hn
  have hLog : 0 <= Real.log (2 * (Fintype.card Iota : Real)) :=
    Real.log_nonneg (by linarith only [hN32])
  have hEps : 0 <= eps :=
    div_nonneg (mul_nonneg (le_of_lt hConstant) (pow_nonneg hLog _)) (sq_nonneg _)
  have hPos := hN0.2 Iota hn T Finset.empty Finset.empty rfl q a hq ha hA
    (by simpa [Finset.empty] using pow_nonneg hLog 3)
    hRow hCol hNonneg hUpper hNorm
  refine And.intro hPos.1 ?_
  apply stochastic_minor_residual_bound T _ q a eps hEps hq hRow hCol hNonneg hUpper
  intro S U hS
  unfold hamiltonianSmallMinorError
  by_cases hSize : (U.card : Real) <= (Real.log (2 * (Fintype.card Iota : Real))) ^ 3
  case pos =>
    rw [if_pos hSize]
    exact (hN0.2 Iota hn T S U (Finset.mem_powersetCard.mp hS).2 q a hq ha hA
      hSize hRow hCol hNonneg hUpper hNorm).2
  case neg =>
    rw [if_neg hSize, abs_zero]
    exact hEps

end PrimeFactorOscillations
