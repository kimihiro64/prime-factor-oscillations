/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteLiu
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedTailDecay
import PrimeFactorOscillations.Helpers.HamiltonianJointSignedCorrection

/-! # The complete signed bipartite comparison

The actual normalized Liu packet is split exactly into its signed
constant, full first-order correction, small residual and full
compensated large tail. The real and integer cutoffs are matched.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_minor_residual_add
    (T : Matrix Iota Iota Real)
    (E F : Finset Iota -> Finset Iota -> Real) :
    hamiltonianMinorResidualPacket T (fun S U => E S U + F S U) =
      hamiltonianMinorResidualPacket T E + hamiltonianMinorResidualPacket T F := by
  unfold hamiltonianMinorResidualPacket
  simp only [mul_add, Finset.sum_add_distrib]
  ring

def hamiltonianNormalizedBipartitePacket (T : Matrix Iota Iota Real) : Real :=
  hamiltonianBipartiteLiuPacket T / weightedPermutationSum T ^ 2

theorem hamiltonian_normalized_bipartite_packet_as_residual
    (T : Matrix Iota Iota Real) :
    hamiltonianNormalizedBipartitePacket T =
      hamiltonianMinorResidualPacket T (fun S U =>
        (rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
          weightedPermutationSum T) ^ 2) := by
  let P := weightedPermutationSum T
  have hOuter (U : Finset Iota) :
      ((-1 : Real) ^ U.card * (U.card : Real) *
        (Finset.univ.powersetCard U.card).sum (fun S =>
          rectangularMinorDet T S U ^ 2 *
            rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) ^ 2)) / P ^ 2 =
      (-1 : Real) ^ U.card * (U.card : Real) *
        (Finset.univ.powersetCard U.card).sum (fun S =>
          rectangularMinorDet T S U ^ 2 *
            (rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) / P) ^ 2) := by
    rw [mul_div_assoc, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro S hS
    rw [mul_div_assoc, div_pow]
  unfold hamiltonianNormalizedBipartitePacket hamiltonianBipartiteLiuPacket
    hamiltonianMinorResidualPacket
  rw [neg_div, Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl (fun U _ => hOuter U)

theorem stochastic_minor_residual_one
    (T : Matrix Iota Iota Real) (q : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) :
    hamiltonianMinorResidualPacket T (fun _ _ => (1 : Real)) =
      Matrix.det ((1 : Matrix Iota Iota Real) -
        (centeredKernel T q).transpose * centeredKernel T q) := by
  have h := hamiltonian_signed_minor_one_eq_centeredDet T q hq hRow hCol
  rw [hamiltonian_signed_minor_bipartite] at h
  simpa only [hamiltonianSignedBipartiteFunctional, hamiltonianMinorResidualPacket] using h

variable [Nonempty Iota]

theorem hamiltonian_compensated_error_cutoff_identity
    (T : Matrix Iota Iota Real) (q Q : Real) (hQ : 0 <= Q) (S U : Finset Iota) :
    (rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
      weightedPermutationSum T) ^ 2 =
      1 + hamiltonianMinorFirstOrder T S U q + hamiltonianSmallMinorError T q Q S U +
        (if Nat.floor Q < U.card then hamiltonianCompensatedMinorError T q S U else 0) := by
  by_cases hSmall : (U.card : Real) <= Q
  case pos =>
    have hRank : U.card <= Nat.floor Q := (Nat.le_floor_iff hQ).mpr hSmall
    have hNotTail : Not (Nat.floor Q < U.card) := Nat.not_lt_of_ge hRank
    rw [hamiltonianSmallMinorError, if_pos hSmall, if_neg hNotTail]
    ring
  case neg =>
    have hTail : Nat.floor Q < U.card := by
      apply Nat.lt_of_not_ge
      intro hRank
      exact hSmall ((Nat.le_floor_iff hQ).mp hRank)
    rw [hamiltonianSmallMinorError, if_neg hSmall, if_pos hTail,
      hamiltonianCompensatedMinorError]
    ring

theorem stochastic_normalized_bipartite_packet_decomposition
    (T : Matrix Iota Iota Real) (q Q : Real) (hQ : 0 <= Q)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) :
    hamiltonianNormalizedBipartitePacket T =
      Matrix.det ((1 : Matrix Iota Iota Real) -
        (centeredKernel T q).transpose * centeredKernel T q) +
      hamiltonianSignedMinorFirstOrderSum T q +
      hamiltonianMinorResidualPacket T (hamiltonianSmallMinorError T q Q) +
      hamiltonianMinorTailPacket T (hamiltonianCompensatedMinorError T q) (Nat.floor Q) := by
  rw [hamiltonian_normalized_bipartite_packet_as_residual]
  have hFunctions :
      (fun S U => (rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
        weightedPermutationSum T) ^ 2) =
      (fun S U => (1 + hamiltonianMinorFirstOrder T S U q +
        hamiltonianSmallMinorError T q Q S U) +
        (if Nat.floor Q < U.card then hamiltonianCompensatedMinorError T q S U else 0)) := by
    funext S U
    exact hamiltonian_compensated_error_cutoff_identity T q Q hQ S U
  rw [hFunctions, hamiltonian_minor_residual_add, hamiltonian_minor_residual_add,
    hamiltonian_minor_residual_add, stochastic_minor_residual_one T q hq hRow hCol]
  rfl

theorem stochastic_normalized_bipartite_comparison_bound
    (T : Matrix Iota Iota Real) (q a delta Q eps eta : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hDelta : 0 < delta) (hQ : 0 <= Q)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hSmall : abs (hamiltonianMinorResidualPacket T (hamiltonianSmallMinorError T q Q)) <= eps)
    (hTail : abs (hamiltonianMinorTailPacket T (hamiltonianCompensatedMinorError T q)
      (Nat.floor Q)) <= eta) :
    abs (hamiltonianNormalizedBipartitePacket T -
      Matrix.det ((1 : Matrix Iota Iota Real) -
        (centeredKernel T q).transpose * centeredKernel T q)) <=
      900 * abs (Matrix.det ((1 : Matrix Iota Iota Real) -
        (centeredKernel T q).transpose * centeredKernel T q)) *
          (a / delta) ^ 3 * q + eps + eta := by
  have hFirst := stochastic_signed_minor_first_order_sum_bound T q a (1 - delta)
    hq ha hRow hCol hNonneg hUpper hNorm (by linarith only [hDelta])
  have hGap : 1 - (1 - delta) = delta := by ring
  rw [hGap] at hFirst
  rw [stochastic_normalized_bipartite_packet_decomposition T q Q hQ hq hRow hCol]
  let d := Matrix.det ((1 : Matrix Iota Iota Real) -
    (centeredKernel T q).transpose * centeredKernel T q)
  let f := hamiltonianSignedMinorFirstOrderSum T q
  let s := hamiltonianMinorResidualPacket T (hamiltonianSmallMinorError T q Q)
  let t := hamiltonianMinorTailPacket T (hamiltonianCompensatedMinorError T q) (Nat.floor Q)
  change abs (d + f + s + t - d) <= _
  have h1 := abs_add_le f s
  have h2 := abs_add_le (f + s) t
  have hRing : d + f + s + t - d = f + s + t := by ring
  rw [hRing]
  linarith only [h1, h2, hFirst, hSmall, hTail]

theorem hamiltonian_normalized_packet_cycle_readout
    (T : Matrix Iota Iota Real) :
    hamiltonianNormalizedBipartitePacket T =
      (Fintype.card Iota : Real) * hamiltonianCycleSum (bipartiteLift T) /
        weightedPermutationSum T ^ 2 := by
  unfold hamiltonianNormalizedBipartitePacket
  rw [hamiltonianBipartiteCycleIdentity]


theorem hamiltonian_logarithmic_cap_square
    (n a c : Real) (hn : 2 <= n) (hc : 0 <= c)
    (hLog : 2 * c <= Real.log n) (hA : a <= c * Real.log (2 * n)) :
    a <= Real.log n ^ (2 : Nat) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hLog0 : 0 <= Real.log n := Real.log_nonneg (le_trans (by norm_num) hn)
  have hTwo : Real.log 2 <= Real.log n := Real.log_le_log (by norm_num) hn
  have hSplit : Real.log (2 * n) = Real.log 2 + Real.log n :=
    Real.log_mul (by norm_num) (ne_of_gt hn0)
  have hDouble : Real.log (2 * n) <= 2 * Real.log n := by linarith only [hSplit, hTwo]
  have h1 := mul_le_mul_of_nonneg_left hDouble hc
  have h2 := mul_le_mul_of_nonneg_right hLog hLog0
  nlinarith only [hA, h1, h2]

universe u

theorem stochastic_signed_bipartite_comparison_logarithmic_uniform
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
          0 < weightedPermutationSum T /\
          abs (hamiltonianNormalizedBipartitePacket T -
            Matrix.det ((1 : Matrix J J Real) -
              (centeredKernel T q).transpose * centeredKernel T q)) <=
            900 * abs (Matrix.det ((1 : Matrix J J Real) -
              (centeredKernel T q).transpose * centeredKernel T q)) *
                (a / delta) ^ 3 * q +
            2 * a * (hamiltonianMinorUniformConstant delta *
              (Real.log (2 * (Fintype.card J : Real))) ^ hamiltonianMinorUniformExponent 2 /
                (Fintype.card J : Real) ^ 2) *
              Matrix.det ((1 : Matrix J J Real) +
                (centeredKernel T q).transpose * centeredKernel T q) +
            Real.exp (-((Real.log (2 * (Fintype.card J : Real))) ^ 3 *
              Real.log (Real.log (2 * (Fintype.card J : Real)))) / 4) := by
  have hSmallRange := stochastic_small_minor_residual_polylog_uniform.{u}
    delta 2 hDelta hDelta1 (by norm_num)
  have hTailRange := stochastic_compensated_minor_tail_logarithmic_uniform.{u}
    delta c hDelta hDelta1 hc
  refine hSmallRange.elim ?_
  intro NS hNS
  refine hTailRange.elim ?_
  intro NT hNT
  let N0 := max NT (max NS (Nat.ceil (Real.exp (2 * c))))
  refine Exists.intro N0 (And.intro (le_trans hNT.1 (le_max_left _ _)) ?_)
  intro J instF instD instN hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hnT : NT <= Fintype.card J := le_trans (le_max_left _ _) hn
  have hnS : NS <= Fintype.card J :=
    le_trans (le_trans (le_max_left NS _) (le_max_right NT _)) hn
  have hnCeil : Nat.ceil (Real.exp (2 * c)) <= Fintype.card J :=
    le_trans (le_trans (le_max_right NS _) (le_max_right NT _)) hn
  have hN256 : (256 : Real) <= Fintype.card J := by exact_mod_cast le_trans hNT.1 hnT
  have hN2 : (2 : Real) <= Fintype.card J := by linarith only [hN256]
  have hN : 0 < (Fintype.card J : Real) := by linarith only [hN256]
  have hExpN : Real.exp (2 * c) <= (Fintype.card J : Real) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hnCeil)
  have hLogNC : 2 * c <= Real.log (Fintype.card J : Real) := by
    have h := Real.log_le_log (Real.exp_pos _) hExpN
    simpa only [Real.log_exp] using h
  have hAPolyNat := hamiltonian_logarithmic_cap_square
    (Fintype.card J : Real) a c hN2 hc hLogNC hA
  have hRealTwo : (Real.log (Fintype.card J : Real)) ^ (2 : Real) =
      (Real.log (Fintype.card J : Real)) ^ (2 : Nat) := by
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log (Fintype.card J : Real)) 2
  have hAPoly : a <= (Real.log (Fintype.card J : Real)) ^ (2 : Real) := by
    rw [hRealTwo]
    exact hAPolyNat
  have hSmall := hNS.2 J hnS T q a hq ha hAPoly hRow hCol hNonneg hUpper hNorm
  have hTail := hNT.2 J hnT T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hLog : 0 <= Real.log (2 * (Fintype.card J : Real)) :=
    Real.log_nonneg (by linarith only [hN256])
  exact And.intro hSmall.1
    (stochastic_normalized_bipartite_comparison_bound T q a delta
      ((Real.log (2 * (Fintype.card J : Real))) ^ 3) _ _ hq ha hDelta
      (pow_nonneg hLog 3) hRow hCol hNonneg hUpper hNorm hSmall.2 hTail)

end PrimeFactorOscillations
