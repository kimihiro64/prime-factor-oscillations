/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianGammaFubini

/-! # The original rook inverse-Gamma tail with explicit stochastic constants

The exact Gaussian rook identity and full product-integrability theorem
transfer the joint bound back to the maintained rook polynomial.
The cutoffs remain N/(1+delta/4) and N/(1-delta/4) in the Euler variable.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem realGaussianAffineProductKernel_integrable_all
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (c : Complex) :
    Integrable (realGaussianAffineProductKernel M hM c) gaussianTensorMeasure := by
  have h := (standardGaussianPolynomialKernel_integrable
    (realGaussianEigenVariances M hM) (realGaussianAffinePolynomial M hM c)).norm
  apply h.congr
  exact Filter.Eventually.of_forall
    (standardGaussianPolynomialKernel_affine_norm M hM c)

theorem hamiltonianRookPolynomial_abs_le_gaussian {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (s : Real) (hs : 0 <= s) :
    abs (hamiltonianRookPolynomial B s) <=
      realGaussianAffineProductAverage (bipartiteLift B) (bipartiteLift_hermitian B)
        (Real.sqrt s : Complex) := by
  have hId := realGaussianAffinePolynomial_rook B (Real.sqrt s : Complex)
  have hSquare : (Real.sqrt s : Complex) ^ 2 = (s : Complex) := by
    exact_mod_cast Real.sq_sqrt hs
  rw [hSquare, hamiltonianComplexRookPolynomial_ofReal] at hId
  have h := realGaussianAffinePolynomial_state_norm_le (bipartiteLift B)
    (bipartiteLift_hermitian B) (Real.sqrt s : Complex)
  rw [hId] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

def hamiltonianRookGammaOutsideIntegrand {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (delta t : Real) : Real :=
  Set.indicator (Set.compl (Set.Icc
    ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4))))
    (fun u : Real => Real.exp (-u) * u ^ n *
      abs (hamiltonianRookPolynomial B ((n : Real) / u))) t

def hamiltonianRookGammaOutsideMass {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (delta : Real) : Real :=
  Inv.inv (n.factorial : Real) *
    MeasureTheory.integral gammaHalfLine (hamiltonianRookGammaOutsideIntegrand B delta)

theorem hamiltonianRookGammaOutsideIntegrand_integrable {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (delta : Real) :
    Integrable (hamiltonianRookGammaOutsideIntegrand B delta) gammaHalfLine := by
  have hRaw : Integrable (fun t : Real => Real.exp (-t) * t ^ n *
      hamiltonianRookPolynomial B ((n : Real) / t)) gammaHalfLine := by
    simpa only [Fintype.card_fin] using hamiltonianRookPolynomial_integrable B
  have hAbs : Integrable (fun t : Real => Real.exp (-t) * t ^ n *
      abs (hamiltonianRookPolynomial B ((n : Real) / t))) gammaHalfLine := by
    apply hRaw.norm.congr
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t ht
    dsimp only
    rw [norm_mul, norm_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (pow_nonneg (show 0 <= t from le_of_lt ht) _),
      Real.norm_eq_abs]
  exact hAbs.indicator (measurableSet_Icc.compl)

theorem hamiltonianRookGammaOutsideIntegrand_le_profile {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (delta t : Real) (ht : 0 < t) :
    Inv.inv (n.factorial : Real) * hamiltonianRookGammaOutsideIntegrand B delta t <=
      MeasureTheory.integral gaussianTensorMeasure (fun x =>
        realGaussianGammaJointProfile (bipartiteLift B) (bipartiteLift_hermitian B)
          delta (x, t)) /
        realStandardGaussianNormalizer ^ Fintype.card (Sum (Fin n) (Fin n)) := by
  let M := bipartiteLift B
  let hM := bipartiteLift_hermitian B
  let c : Complex := (Real.sqrt ((n : Real) / t) : Complex)
  let k := Inv.inv (n.factorial : Real) * Real.exp (-t) * t ^ n
  have hK : 0 <= k :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Real.exp_pos _).le)
      (pow_nonneg ht.le _)
  have hRook := hamiltonianRookPolynomial_abs_le_gaussian B ((n : Real) / t)
    (div_nonneg (Nat.cast_nonneg _) ht.le)
  by_cases hE : Membership.mem (Set.compl (Set.Icc
    ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4)))) t
  case neg =>
    simp [hamiltonianRookGammaOutsideIntegrand, realGaussianGammaJointProfile,
      Set.indicator, hE]
  case pos =>
    have hFun :
        (fun x => realGaussianGammaJointProfile M hM delta (x, t)) =
          fun x => k * realGaussianAffineProductKernel M hM c x := by
      funext x
      unfold realGaussianGammaJointProfile realGaussianAffineProductKernel
        realStandardGaussianDensity
      simp only [Prod.fst, Prod.snd, Set.indicator_of_mem hE]
      dsimp only [k, c]
      ring
    calc
      _ = k * abs (hamiltonianRookPolynomial B ((n : Real) / t)) := by
        unfold hamiltonianRookGammaOutsideIntegrand
        rw [Set.indicator_of_mem hE]
        dsimp only [k]
        ring
      _ <= k * realGaussianAffineProductAverage M hM c :=
        mul_le_mul_of_nonneg_left hRook hK
      _ = _ := by
        change k * realGaussianAffineProductAverage M hM c =
          MeasureTheory.integral gaussianTensorMeasure
            (fun x => realGaussianGammaJointProfile M hM delta (x, t)) /
              realStandardGaussianNormalizer ^ Fintype.card (Sum (Fin n) (Fin n))
        rw [hFun, integral_const_mul]
        unfold realGaussianAffineProductAverage
        ring

theorem hamiltonianRookGammaOutsideMass_le_gaussian {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (delta rho : Real) (hN : 0 < n)
    (hCol : forall j, Finset.sum Finset.univ (fun i => bipartiteLift B i j) = 0)
    (hNorm : norm (bipartiteLift B) <= rho) (hGap : 0 < 1 - rho) :
    hamiltonianRookGammaOutsideMass B delta <=
      realGaussianGammaOutsideAverage (bipartiteLift B)
        (bipartiteLift_hermitian B) n delta := by
  let M := bipartiteLift B
  let hM := bipartiteLift_hermitian B
  let Z := realStandardGaussianNormalizer ^ Fintype.card (Sum (Fin n) (Fin n))
  have hZ : 0 <= Z := (pow_pos realStandardGaussianNormalizer_positive _).le
  have hProfile := realGaussianGammaJointProfile_integrable M hM delta rho hN hCol hNorm hGap
  have hLeft := (hamiltonianRookGammaOutsideIntegrand_integrable B delta).const_mul
    (Inv.inv (n.factorial : Real))
  have hRight := hProfile.integral_prod_right.div_const Z
  have hDom : Filter.Eventually (fun t : Real =>
      Inv.inv (n.factorial : Real) * hamiltonianRookGammaOutsideIntegrand B delta t <=
        MeasureTheory.integral gaussianTensorMeasure
          (fun x => realGaussianGammaJointProfile M hM delta (x, t)) / Z)
      (ae gammaHalfLine) := by
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t ht
    exact hamiltonianRookGammaOutsideIntegrand_le_profile B delta t ht
  have hIntegral := integral_mono_ae hLeft hRight hDom
  unfold hamiltonianRookGammaOutsideMass
  calc
    _ = MeasureTheory.integral gammaHalfLine (fun t =>
        Inv.inv (n.factorial : Real) * hamiltonianRookGammaOutsideIntegrand B delta t) :=
      (integral_const_mul _ _).symm
    _ <= MeasureTheory.integral gammaHalfLine (fun t =>
        MeasureTheory.integral gaussianTensorMeasure
          (fun x => realGaussianGammaJointProfile M hM delta (x, t)) / Z) := hIntegral
    _ = (MeasureTheory.integral gammaHalfLine (fun t =>
        MeasureTheory.integral gaussianTensorMeasure
          (fun x => realGaussianGammaJointProfile M hM delta (x, t)))) / Z := by
      calc
        _ = MeasureTheory.integral gammaHalfLine (fun t => Inv.inv Z *
            MeasureTheory.integral gaussianTensorMeasure
              (fun x => realGaussianGammaJointProfile M hM delta (x, t))) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun _ => by ring)
        _ = Inv.inv Z * MeasureTheory.integral gammaHalfLine (fun t =>
            MeasureTheory.integral gaussianTensorMeasure
              (fun x => realGaussianGammaJointProfile M hM delta (x, t))) :=
          integral_const_mul _ _
        _ = _ := by ring
    _ <= MeasureTheory.integral gaussianTensorMeasure
          (realGaussianGammaOutsideKernel M hM n delta) / Z :=
      div_le_div_of_nonneg_right
        (realGaussianGammaJointProfile_total_le M hM delta rho hN hCol hNorm hGap) hZ
    _ = _ := rfl

theorem hamiltonianRookGammaOutsideMass_stochastic_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta : Real)
    (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hN : 8 <= (n : Real) * delta) :
    hamiltonianRookGammaOutsideMass (centeredKernel T q) delta <=
      3 * Real.exp (-(n : Real) * delta ^ 2 / 2304 +
        10 / (3 * delta) * Real.sqrt ((n : Real) * (a - 1))) := by
  have hNpos : 0 < n := by
    by_contra h
    have hZero : n = 0 := Nat.eq_zero_of_not_pos h
    norm_num [hZero] at hq
  apply le_trans (hamiltonianRookGammaOutsideMass_le_gaussian (centeredKernel T q)
    delta (1 - delta) hNpos
    (centered_bipartite_column_sum_zero T q
      (by simpa only [Fintype.card_fin] using hq) hRow hCol)
    (le_trans (bipartiteLift_l2_norm_le _) hNorm) (by linarith))
  exact stochasticGaussianGammaOutsideAverage_bound T q a delta hq ha hRow
    hNonneg hUpper hNorm hDelta0 hDelta1 hN

private theorem positive_left_div_iff (a b c : Real) (hc : 0 < c) :
    Iff (a <= b / c) (a * c <= b) := by
  have hCancel : (b / c) * c = b := by field_simp
  constructor
  case mp =>
    intro h
    have hMul := mul_le_mul_of_nonneg_right h hc.le
    rwa [hCancel] at hMul
  case mpr =>
    intro h
    by_contra hNot
    have hMul := mul_lt_mul_of_pos_right (lt_of_not_ge hNot) hc
    rw [hCancel] at hMul
    linarith

private theorem positive_div_right_iff (a b c : Real) (hb : 0 < b) :
    Iff (a / b <= c) (a <= c * b) := by
  have hCancel : (a / b) * b = a := by field_simp
  constructor
  case mp =>
    intro h
    have hMul := mul_le_mul_of_nonneg_right h hb.le
    rwa [hCancel] at hMul
  case mpr =>
    intro h
    by_contra hNot
    have hMul := mul_lt_mul_of_pos_right (lt_of_not_ge hNot) hb
    rw [hCancel] at hMul
    linarith

theorem positive_divisor_interval (u t a b : Real)
    (ht : 0 < t) (ha : 0 < a) (hb : 0 < b) :
    Iff (Membership.mem (Set.Icc a b) (u / t))
      (Membership.mem (Set.Icc (u / b) (u / a)) t) := by
  change Iff (And (a <= u / t) (u / t <= b)) (And (u / b <= t) (t <= u / a))
  rw [positive_left_div_iff a u t ht, positive_div_right_iff u t b ht,
    positive_div_right_iff u b t hb, positive_left_div_iff t u a ha]
  constructor
  case mp => intro h; exact And.intro (by nlinarith [h.2]) (by nlinarith [h.1])
  case mpr => intro h; exact And.intro (by nlinarith [h.2]) (by nlinarith [h.1])

theorem hamiltonianRookGammaOutsideMass_eq_inverse {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (delta : Real)
    (hDelta0 : 0 <= delta) (hDelta1 : delta <= 1) :
    hamiltonianRookGammaOutsideMass B delta =
      gammaInverseAverage n
        (Set.indicator (Set.compl (Set.Icc (1 - delta / 4) (1 + delta / 4)))
          (fun s => abs (hamiltonianRookPolynomial B s))) := by
  unfold hamiltonianRookGammaOutsideMass gammaInverseAverage
  congr 1
  apply integral_congr_ae
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  unfold hamiltonianRookGammaOutsideIntegrand
  dsimp only
  have hIff := positive_divisor_interval (n : Real) t (1 - delta / 4) (1 + delta / 4)
    ht (by linarith) (by linarith)
  by_cases hT : Membership.mem (Set.Icc ((n : Real) / (1 + delta / 4))
    ((n : Real) / (1 - delta / 4))) t
  case pos =>
    have hS := hIff.mpr hT
    have hTc : Not (Membership.mem (Set.compl (Set.Icc
        ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4)))) t) :=
      fun h => h hT
    have hSc : Not (Membership.mem
        (Set.compl (Set.Icc (1 - delta / 4) (1 + delta / 4))) ((n : Real) / t)) :=
      fun h => h hS
    rw [Set.indicator_of_notMem hTc, Set.indicator_of_notMem hSc, mul_zero]
  case neg =>
    have hS : Not (Membership.mem (Set.Icc (1 - delta / 4) (1 + delta / 4))
        ((n : Real) / t)) := fun h => hT (hIff.mp h)
    have hTc : Membership.mem (Set.compl (Set.Icc
        ((n : Real) / (1 + delta / 4)) ((n : Real) / (1 - delta / 4)))) t := hT
    have hSc : Membership.mem (Set.compl (Set.Icc (1 - delta / 4) (1 + delta / 4)))
        ((n : Real) / t) := hS
    rw [Set.indicator_of_mem hTc, Set.indicator_of_mem hSc]

theorem hamiltonianRookInverseGammaOutside_stochastic_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta : Real)
    (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hN : 8 <= (n : Real) * delta) :
    gammaInverseAverage n
        (Set.indicator (Set.compl (Set.Icc (1 - delta / 4) (1 + delta / 4)))
          (fun s => abs (hamiltonianRookPolynomial (centeredKernel T q) s))) <=
      3 * Real.exp (-(n : Real) * delta ^ 2 / 2304 +
        10 / (3 * delta) * Real.sqrt ((n : Real) * (a - 1))) := by
  rw [<- hamiltonianRookGammaOutsideMass_eq_inverse _ delta hDelta0.le hDelta1]
  exact hamiltonianRookGammaOutsideMass_stochastic_bound T q a delta hq ha hRow hCol
    hNonneg hUpper hNorm hDelta0 hDelta1 hN

end PrimeFactorOscillations
