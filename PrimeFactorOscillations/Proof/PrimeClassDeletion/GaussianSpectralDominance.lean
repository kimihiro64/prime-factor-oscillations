/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianSpectralGap
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianSpectralMajorant

/-!
# A uniquely exposed residue dominates the full infinite zero sum

The signed sum is split exactly at its principal zero. One fixed,
absolutely summable base-scale series bounds every remaining zero at
every larger real scale, with a uniform positive exponent gap.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianZetaResidue_split
    (X V tau : Real) (w : ZetaDistinctZero) (hX : 0 < X) (hV : 1 <= V) :
    tsum (logGaussianZetaResidue X V tau) =
      logGaussianZetaResidue X V tau w +
        tsum (fun z : {z : ZetaDistinctZero | Not (z = w)} =>
          logGaussianZetaResidue X V tau z.val) := by
  classical
  let F := {z : ZetaDistinctZero //
    Not (Membership.mem (Singleton.singleton w : Finset ZetaDistinctZero) z)}
  let S : Set ZetaDistinctZero := {z | Not (z = w)}
  let e : Equiv F S := {
    toFun := fun z => Subtype.mk z.val
      (fun hEq => z.property (Finset.mem_singleton.mpr hEq))
    invFun := fun z => Subtype.mk z.val
      (fun hMem => z.property (Finset.mem_singleton.mp hMem))
    left_inv := fun z => by cases z; rfl
    right_inv := fun z => by cases z; rfl }
  have hTail : tsum (fun z : F => logGaussianZetaResidue X V tau z.val) =
      tsum (fun z : S => logGaussianZetaResidue X V tau z.val) := by
    simpa only [e] using! e.tsum_eq (fun z : S => logGaussianZetaResidue X V tau z.val)
  have h := (logGaussian_zeta_zero_residue_hasSum X V tau hX hV).summable
    |>.sum_add_tsum_subtype_compl (Singleton.singleton w : Finset ZetaDistinctZero)
  have hSum : logGaussianZetaResidue X V tau w +
      tsum (fun z : F => logGaussianZetaResidue X V tau z.val) =
      tsum (logGaussianZetaResidue X V tau) := by
    simpa only [Finset.sum_singleton] using h
  rw [hTail] at hSum
  exact hSum.symm

theorem logGaussianZetaResidue_uniform_dominance
    (c tau : Real) (hc : 0 < c) (w : ZetaDistinctZero)
    (hUnique : forall z : ZetaDistinctZero, Not (z = w) ->
      gaussianZeroExponent c z.val.re z.val.im tau <
        gaussianZeroExponent c w.val.re w.val.im tau) :
    Exists fun delta : Real => And (0 < delta) (And (delta <= 1)
      (Exists fun C : Real => And (0 <= C) (forall X : Real, Real.exp (1 / c) <= X ->
        And
          (norm (tsum (logGaussianZetaResidue X (c * Real.log X) tau) -
            logGaussianZetaResidue X (c * Real.log X) tau w) <=
            C * X ^ (gaussianZeroExponent c w.val.re w.val.im tau - delta))
          (gaussianZetaAmplitude w * X ^ (gaussianZeroExponent c w.val.re w.val.im tau) -
            C * X ^ (gaussianZeroExponent c w.val.re w.val.im tau - delta) <=
            norm (tsum (logGaussianZetaResidue X (c * Real.log X) tau)))))) := by
  classical
  cases gaussianZeroExponent_uniform_gap c tau hc w hUnique with
  | intro delta hDelta =>
    let a : Real := gaussianZeroExponent c w.val.re w.val.im tau - delta
    let X1 : Real := Real.exp (1 / c)
    let S : Set ZetaDistinctZero := {z | Not (z = w)}
    let Q : Real := tsum (fun z : S =>
      norm (logGaussianZetaResidue X1 (c * Real.log X1) tau z.val))
    let C : Real := Q / X1 ^ a
    have hX1 : 0 < X1 := Real.exp_pos _
    have hV1 : c * Real.log X1 = 1 := by
      dsimp only [X1]
      rw [Real.log_exp]
      field_simp [hc.ne']
    have hC : 0 <= C :=
      div_nonneg (tsum_nonneg (fun z => norm_nonneg _))
        (Real.rpow_pos_of_pos hX1 a).le
    refine Exists.intro delta (And.intro hDelta.1 (And.intro hDelta.2.1
      (Exists.intro C (And.intro hC ?_))))
    intro X hScale
    have hX : 0 < X := lt_of_lt_of_le hX1 hScale
    have hLog := Real.log_le_log hX1 hScale
    have hVX : 1 <= c * Real.log X := by
      have hMul := mul_le_mul_of_nonneg_left hLog hc.le
      rw [hV1] at hMul
      exact hMul
    have hTail := (logGaussianZetaResidue_subset_sum_norm_bound X X1 c tau a S
      hX1 hScale (by rw [hV1]) (fun z hz => hDelta.2.2 z hz)).2
    have hTailFinal : norm (tsum (fun z : S =>
        logGaussianZetaResidue X (c * Real.log X) tau z.val)) <= C * X ^ a := by
      calc
        _ <= (X ^ a / X1 ^ a) * Q := hTail
        _ = _ := by dsimp only [C]; ring
    have hSplit := logGaussianZetaResidue_split X (c * Real.log X) tau w hX hVX
    have hDifference :
        tsum (logGaussianZetaResidue X (c * Real.log X) tau) -
          logGaussianZetaResidue X (c * Real.log X) tau w =
        tsum (fun z : S => logGaussianZetaResidue X (c * Real.log X) tau z.val) := by
      rw [hSplit]
      dsimp only [S]
      ring
    have hDifferenceBound :
        norm (tsum (logGaussianZetaResidue X (c * Real.log X) tau) -
          logGaussianZetaResidue X (c * Real.log X) tau w) <= C * X ^ a := by
      rw [hDifference]
      exact hTailFinal
    refine And.intro hDifferenceBound ?_
    have hReverse :
        norm (logGaussianZetaResidue X (c * Real.log X) tau w) <=
        norm (tsum (logGaussianZetaResidue X (c * Real.log X) tau)) +
          norm (tsum (logGaussianZetaResidue X (c * Real.log X) tau) -
            logGaussianZetaResidue X (c * Real.log X) tau w) := by
      calc
        _ = norm (tsum (logGaussianZetaResidue X (c * Real.log X) tau) -
            (tsum (logGaussianZetaResidue X (c * Real.log X) tau) -
              logGaussianZetaResidue X (c * Real.log X) tau w)) := by congr 1; ring
        _ <= _ := norm_sub_le _ _
    rw [logGaussianZetaResidue_log_scale_norm X c tau w hX] at hReverse
    change gaussianZetaAmplitude w * X ^ (gaussianZeroExponent c w.val.re w.val.im tau) -
      C * X ^ a <= _
    linarith only [hReverse, hDifferenceBound]

end PrimeFactorOscillations.PrimeClassDeletion
