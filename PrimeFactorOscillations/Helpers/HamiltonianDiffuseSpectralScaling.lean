/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianNormalizedSpectralScaling

/-! # Native spectral repair with logarithmic cost in the entry cap

The existing scalar budget is applied with its free scale equal to a,
rather than to the matrix dimension. The matrix, weighted mode and full
nonlinear remainder are retained in the same positive scaling witness.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_centered_gap_diffuse_scaling
    (T : Matrix Iota Iota Real) (a delta eps : Real)
    (ha : 1 <= a)
    (hd0 : 0 < delta) (hd1 : delta < 1) (he0 : 0 <= eps) (he1 : eps <= 1 / 2)
    (hT : forall i j, 0 <= T i j)
    (hUpper : forall i j, T i j <= a * (1 / (Fintype.card Iota : Real)))
    (hRow : forall i, abs (hamiltonianCrossRowDegrees T i - 1) <= eps)
    (hCol : forall j, abs (hamiltonianCrossColumnDegrees T j - 1) <= eps)
    (hRaw : norm (centeredKernel T (1 / (Fintype.card Iota : Real))) <= 1 - delta + 8 * eps)
    (hSmall : eps * Real.log (4 * a) ^ 2 <=
      hamiltonianNormalizedScalingSmall delta) :
    exists z : Sum Iota Iota -> Real,
      norm z <= hamiltonianNormalizedScalingCost delta * eps *
        Real.log (4 * a) /\
      (forall i, 0 < 1 + z i) /\
      (forall i j, 0 <= hamiltonianScaledCross T z i j) /\
      (forall i, Finset.univ.sum (fun j => hamiltonianScaledCross T z i j) = 1) /\
      (forall j, Finset.univ.sum (fun i => hamiltonianScaledCross T z i j) = 1) /\
      (forall i j, hamiltonianScaledCross T z i j = 0 <-> T i j = 0) /\
      (forall i j, hamiltonianScaledCross T z i j <= 2 * T i j) /\
      norm (hamiltonianScaledCross T z - T) <=
        hamiltonianNormalizedScalingCost delta * eps *
          Real.log (4 * a) := by
  by_cases hZero : eps = 0
  case pos =>
    subst eps
    have hScaled : hamiltonianScaledCross T (fun _ => 0) = T := by
      ext i j
      simp [hamiltonianScaledCross]
    refine Exists.intro (fun _ => 0) (And.intro ?_ (And.intro ?_ (And.intro ?_
      (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))))))
    next => simp
    next => intro i; norm_num
    next => intro i j; rw [hScaled]; exact hT i j
    next =>
      intro i
      rw [hScaled]
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (hRow i) (abs_nonneg _)))
    next =>
      intro j
      rw [hScaled]
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (hCol j) (abs_nonneg _)))
    next => intro i j; rw [hScaled]
    next => intro i j; rw [hScaled]; linarith only [hT i j]
    next => rw [hScaled, sub_self, norm_zero]; simp
  case neg =>
    have hePos : 0 < eps := lt_of_le_of_ne he0 (Ne.symm hZero)
    let n : Real := Fintype.card Iota
    let q := 1 / n
    let rho := 1 - delta / 2
    let G := hamiltonianScalingOrderCost rho
    let g := hamiltonianDiffuseInverseBudget (a + 9 * eps) rho
    let R := 4 * g * eps
    let L := Real.log (4 * a)
    have hn : 1 <= n := by
      change (1 : Real) <= (Fintype.card Iota : Real)
      have hCard : 0 < Fintype.card Iota := Fintype.card_pos
      exact_mod_cast (show 1 <= Fintype.card Iota by omega)
    have hnPos : 0 < n := by linarith only [hn]
    have hq : (Fintype.card Iota : Real) * q = 1 := by
      change n * (1 / n) = 1
      field_simp [ne_of_gt hnPos]
    have hr0 : 0 < rho := by dsimp [rho]; linarith only [hd1]
    have hr1 : rho < 1 := by dsimp [rho]; linarith only [hd0]
    have hL0 : 0 <= L := Real.log_nonneg (by linarith only [ha])
    have hG : 0 < G := hamiltonian_scaling_order_cost_positive rho hr0 hr1
    have hSelfCap : a <= (1 + eps) * a := by
      have hProduct := mul_nonneg he0 (by linarith only [ha] : 0 <= a)
      nlinarith only [hProduct]
    have hBudgets := hamiltonian_scaling_order_all_budgets a a eps rho ha ha he0 he1
      hSelfCap hr0 hr1 hSmall
    have hMargin : 28 * eps <= delta := by
      have h := hBudgets.1
      dsimp [rho] at h
      linarith only [h]
    have hRowPos (i : Iota) : 0 < hamiltonianCrossRowDegrees T i := by
      have h := (abs_le.mp (hRow i)).1
      linarith only [h, he1]
    have hColPos (j : Iota) : 0 < hamiltonianCrossColumnDegrees T j := by
      have h := (abs_le.mp (hCol j)).1
      linarith only [h, he1]
    have hAvail : norm (centeredKernel T q) <= rho - 6 * eps := by
      change norm (centeredKernel T q) <= 1 - delta + 8 * eps at hRaw
      dsimp only [rho]
      linarith only [hRaw, hMargin]
    choose z hz hPos hNonneg hRows hCols hSupport hCap hError using
      hamiltonian_actual_diffuse_stochastic_repair T q a eps rho
        hq ha hePos he1 hT hRow hCol hUpper hAvail hr0 hr1 hBudgets.2.1
    have hR0 : 0 <= R := by
      have hG0 := hamiltonian_diffuse_inverse_budget_positive (a + 9 * eps) rho
        (by linarith only [ha, he0]) hr0 hr1
      dsimp [R]
      positivity
    have hScaleCost : 4 * G * eps * L <= hamiltonianNormalizedScalingCost delta * eps * L := by
      have hPositive := mul_nonneg (mul_nonneg hG.le he0) hL0
      change 4 * G * eps * L <= 20 * G * eps * L
      nlinarith only [hPositive]
    have hZ : norm z <= hamiltonianNormalizedScalingCost delta * eps * L :=
      hz.trans (hBudgets.2.2.1.trans hScaleCost)
    have hg : 1 <= g := hamiltonian_diffuse_inverse_budget_positive (a + 9 * eps) rho
      (by linarith only [ha, he0]) hr0 hr1
    have hgSquare : g <= g ^ 2 := by nlinarith only [hg]
    have hEG : eps * g <= 1 / 256 :=
      (mul_le_mul_of_nonneg_left hgSquare he0).trans hBudgets.2.1
    have hR1 : R <= 1 / 64 := by dsimp [R]; nlinarith only [hEG]
    have hZPoint (i : Sum Iota Iota) : abs (z i) <= R :=
      (pi_norm_le_iff_of_nonneg hR0).mp hz i
    have hR2 := mul_le_mul hR1 hR1 hR0 (by norm_num : (0 : Real) <= 1 / 64)
    have hCoeff : (1 + R) ^ 2 <= 2 := by nlinarith only [hR1, hR2]
    have hPointCap (i j : Iota) : hamiltonianScaledCross T z i j <= 2 * T i j := by
      have hLeft : 1 + z (Sum.inl i) <= 1 + R := by
        linarith only [(abs_le.mp (hZPoint (Sum.inl i))).2]
      have hRight : 1 + z (Sum.inr j) <= 1 + R := by
        linarith only [(abs_le.mp (hZPoint (Sum.inr j))).2]
      have hCoeff' := mul_le_mul hLeft hRight (hPos (Sum.inr j)).le
        (by linarith only [hR0] : 0 <= 1 + R)
      have hCoeff2 : (1 + z (Sum.inl i)) * (1 + z (Sum.inr j)) <= 2 := by
        nlinarith only [hCoeff', hCoeff]
      have hWeighted := mul_le_mul_of_nonneg_right hCoeff2 (hT i j)
      change (1 + z (Sum.inl i)) * T i j * (1 + z (Sum.inr j)) <= 2 * T i j
      nlinarith only [hWeighted]
    refine Exists.intro z (And.intro hZ (And.intro hPos (And.intro hNonneg
      (And.intro hRows (And.intro hCols (And.intro hSupport (And.intro hPointCap ?_)))))))
    exact hError.trans hBudgets.2.2.2

theorem hamiltonian_normalized_spectral_diffuse_scaling
    (T : Matrix Iota Iota Real) (a delta eps : Real)
    (ha : 1 <= a)
    (hd0 : 0 < delta) (hd1 : delta < 1) (he0 : 0 <= eps)
    (hT : forall i j, 0 <= T i j)
    (hUpper : forall i j, T i j <= a * (1 / (Fintype.card Iota : Real)))
    (hRow : forall i, abs (hamiltonianCrossRowDegrees T i - 1) <= eps)
    (hCol : forall j, abs (hamiltonianCrossColumnDegrees T j - 1) <= eps)
    (hSpectrum : HamiltonianNormalizedSpectralPacket T (1 - delta))
    (hSmall : eps * Real.log (4 * a) ^ 2 <=
      hamiltonianNormalizedScalingSmall delta) :
    exists z : Sum Iota Iota -> Real,
      norm z <= hamiltonianNormalizedScalingCost delta * eps *
        Real.log (4 * a) /\
      (forall i, 0 < 1 + z i) /\
      (forall i j, 0 <= hamiltonianScaledCross T z i j) /\
      (forall i, Finset.univ.sum (fun j => hamiltonianScaledCross T z i j) = 1) /\
      (forall j, Finset.univ.sum (fun i => hamiltonianScaledCross T z i j) = 1) /\
      (forall i j, hamiltonianScaledCross T z i j = 0 <-> T i j = 0) /\
      (forall i j, hamiltonianScaledCross T z i j <= 2 * T i j) /\
      norm (hamiltonianScaledCross T z - T) <=
        hamiltonianNormalizedScalingCost delta * eps *
          Real.log (4 * a) := by
  let L := Real.log (4 * a)
  have hFour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hL : Real.log 4 <= L :=
    Real.log_le_log (by norm_num) (by linarith only [ha])
  have hL2 : (Real.log 4) ^ 2 <= L ^ 2 := by
    nlinarith only [hL, hFour]
  have hScale := mul_le_mul_of_nonneg_left hL2 he0
  have hBase := hSmall.trans (min_le_left _ _)
  change eps * L ^ 2 <=
    ((1 - (1 - delta / 2)) / 14) * (Real.log 4) ^ 2 at hBase
  have hGap : eps * (Real.log 4) ^ 2 <= (delta / 28) * (Real.log 4) ^ 2 := by
    nlinarith only [hScale, hBase]
  have hEps : eps <= delta / 28 := by
    by_contra h
    exact (not_lt_of_ge hGap)
      (mul_lt_mul_of_pos_right (lt_of_not_ge h) (sq_pos_of_pos hFour))
  have he1 : eps <= 1 / 2 := by linarith only [hEps, hd1]
  let q : Real := 1 / (Fintype.card Iota : Real)
  have hn : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq : (Fintype.card Iota : Real) * q = 1 := by
    dsimp [q]
    field_simp [ne_of_gt hn]
  have hRowPos (i : Iota) : 0 < hamiltonianCrossRowDegrees T i := by
    have h := (abs_le.mp (hRow i)).1
    linarith only [h, he1]
  have hColPos (j : Iota) : 0 < hamiltonianCrossColumnDegrees T j := by
    have h := (abs_le.mp (hCol j)).1
    linarith only [h, he1]
  have hNorm := hamiltonian_actual_normalized_native_gap T q (1 - delta) hq
    (by linarith only [hd1]) hRowPos hColPos hSpectrum.plus_simple
    hSpectrum.minus_simple hSpectrum.nontrivial
  have hRaw := hamiltonian_actual_normalized_degree_gap T q eps (1 - delta)
    hq he0 he1 (by linarith only [hd1]) (by linarith only [hd0]) hRow hCol hNorm
  exact hamiltonian_centered_gap_diffuse_scaling T a delta eps ha hd0 hd1 he0 he1
    hT hUpper hRow hCol hRaw hSmall

theorem hamiltonian_normalized_spectral_physical_cap_scaling
    (T : Matrix Iota Iota Real) (A delta eps : Real) (hA : 2 <= A)
    (hd0 : 0 < delta) (hd1 : delta < 1) (he0 : 0 <= eps)
    (hT : forall i j, 0 <= T i j)
    (hUpper : forall i j, T i j <= A / (2 * (Fintype.card Iota : Real)))
    (hRow : forall i, abs (hamiltonianCrossRowDegrees T i - 1) <= eps)
    (hCol : forall j, abs (hamiltonianCrossColumnDegrees T j - 1) <= eps)
    (hSpectrum : HamiltonianNormalizedSpectralPacket T (1 - delta))
    (hSmall : eps * Real.log (2 * A) ^ 2 <= hamiltonianNormalizedScalingSmall delta) :
    exists z : Sum Iota Iota -> Real,
      norm z <= hamiltonianNormalizedScalingCost delta * eps * Real.log (2 * A) /\
      (forall i, 0 < 1 + z i) /\
      (forall i j, 0 <= hamiltonianScaledCross T z i j) /\
      (forall i, Finset.univ.sum (fun j => hamiltonianScaledCross T z i j) = 1) /\
      (forall j, Finset.univ.sum (fun i => hamiltonianScaledCross T z i j) = 1) /\
      (forall i j, hamiltonianScaledCross T z i j = 0 <-> T i j = 0) /\
      (forall i j, hamiltonianScaledCross T z i j <= 2 * T i j) /\
      norm (hamiltonianScaledCross T z - T) <=
        hamiltonianNormalizedScalingCost delta * eps * Real.log (2 * A) := by
  have ha : 1 <= A / 2 := by linarith only [hA]
  have hLogArg : 4 * (A / 2) = 2 * A := by ring
  have hCap (i j : Iota) :
      T i j <= (A / 2) * (1 / (Fintype.card Iota : Real)) := by
    have hId : A / (2 * (Fintype.card Iota : Real)) =
        (A / 2) * (1 / (Fintype.card Iota : Real)) := by ring
    rw [<- hId]
    exact hUpper i j
  have hSmall' : eps * Real.log (4 * (A / 2)) ^ 2 <=
      hamiltonianNormalizedScalingSmall delta := by rwa [hLogArg]
  have h := hamiltonian_normalized_spectral_diffuse_scaling T (A / 2) delta eps
    ha hd0 hd1 he0 hT hCap hRow hCol hSpectrum hSmall'
  simpa only [hLogArg] using h

end PrimeFactorOscillations
