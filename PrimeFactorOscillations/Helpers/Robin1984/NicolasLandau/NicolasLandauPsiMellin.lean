/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandau.lean
Original source lines 26-438. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import Mathlib.NumberTheory.LSeries.SumCoeff
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasOscillation

/-!
# The psi Mellin transform in the Nicolas-Landau argument

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Asymptotics Filter MeasureTheory Set

noncomputable section

theorem riemannZeta_one_sub_eq_zero_of_nontrivial_zero
    {s : Complex} (hz : riemannZeta s = 0)
    (hNontrivial : Not (Exists fun n : Nat => s = -2 * (n + 1)))
    (hOne : Not (s = 1)) :
    riemannZeta (1 - s) = 0 := by
  have hsZero : Not (s = 0) := by
    intro hs
    subst s
    norm_num [riemannZeta_zero] at hz
  have hCompleted : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hsZero] at hz
    rcases div_eq_zero_iff.mp hz with hCompleted | hGammaFactor
    . exact hCompleted
    . change
        (Real.pi : Complex) ^ (-s / 2) * Complex.Gamma (s / 2) = 0 at hGammaFactor
      rcases mul_eq_zero.mp hGammaFactor with hPiPower | hGamma
      . have hPi : Not ((Real.pi : Complex) = 0) :=
          Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        exact (Complex.cpow_ne_zero_iff.mpr (Or.inl hPi) hPiPower).elim
      . choose m hm using (Complex.Gamma_eq_zero_iff (s / 2)).mp hGamma
        have hsEq : s = -2 * (m : Complex) := by
          calc
            s = 2 * (s / 2) := by ring
            _ = 2 * (-(m : Complex)) := by rw [hm]
            _ = -2 * (m : Complex) := by ring
        cases m with
        | zero => exact (hsZero (by simpa using hsEq)).elim
        | succ n =>
            exact (hNontrivial (Exists.intro n (by
              simpa [Nat.cast_add, Nat.cast_one] using hsEq))).elim
  have hMirrorCompleted : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact hCompleted
  have hMirrorNeZero : Not (1 - s = 0) :=
    sub_ne_zero.mpr (Ne.symm hOne)
  rw [riemannZeta_def_of_ne_zero hMirrorNeZero, hMirrorCompleted, zero_div]

/-- Failure of RH supplies a zeta zero strictly to the right of the critical
line and strictly inside the critical strip. -/
theorem exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis
    (hNotRH : Not RiemannHypothesis) :
    Exists fun rho : Complex =>
      And (riemannZeta rho = 0)
        (And ((1 / 2 : Real) < rho.re) (rho.re < 1)) := by
  unfold RiemannHypothesis at hNotRH
  push_neg at hNotRH
  choose z hz hNontrivial hzOne hzOff using hNotRH
  have hNontrivialExists :
      Not (Exists fun n : Nat => z = -2 * (n + 1)) := by
    intro hExists
    choose n hn using hExists
    exact hNontrivial n hn
  have hzLt : z.re < 1 := by
    by_contra hNotLt
    exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hNotLt) hz
  have hMirrorZero : riemannZeta (1 - z) = 0 :=
    riemannZeta_one_sub_eq_zero_of_nontrivial_zero hz hNontrivialExists hzOne
  have hzPos : 0 < z.re := by
    by_contra hNotPos
    have hMirrorRe : 1 <= (1 - z).re := by
      change 1 <= 1 - z.re
      linarith
    exact riemannZeta_ne_zero_of_one_le_re hMirrorRe hMirrorZero
  by_cases hRight : (1 / 2 : Real) < z.re
  . exact Exists.intro z (And.intro hz (And.intro hRight hzLt))
  . have hzLeft : z.re < (1 / 2 : Real) :=
      lt_of_le_of_ne (le_of_not_gt hRight) hzOff
    refine Exists.intro (1 - z) (And.intro hMirrorZero (And.intro ?_ ?_))
    . change (1 / 2 : Real) < 1 - z.re
      linarith
    . change 1 - z.re < (1 : Real)
      linarith


/-- The complete von Mangoldt partial sums have the exact linear growth
needed for Abel's integral representation of their Dirichlet series. -/
theorem nicolasVonMangoldtPartialSums_isBigO :
    (fun n : Nat =>
      Finset.sum (Finset.Icc 1 n)
        (fun k => ArithmeticFunction.vonMangoldt k)) =O[atTop]
      (fun n : Nat => (n : Real) ^ (1 : Real)) := by
  apply (IsBigOWith.of_bound
    (c := Real.log 4 + 4) (Eventually.of_forall fun n => ?_)).isBigO
  have hSum :
      Finset.sum (Finset.Icc 1 n)
          (fun k => ArithmeticFunction.vonMangoldt k) =
        Chebyshev.psi (n : Real) := by
    rw [Chebyshev.psi_eq_sum_Icc]
    rw [Nat.floor_natCast]
    symm
    rw [<- Finset.insert_Icc_add_one_left_eq_Icc n.zero_le,
      Finset.sum_insert (by aesop)]
    simp
  rw [hSum, Real.norm_eq_abs,
    abs_of_nonneg (Chebyshev.psi_nonneg (n : Real)), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) 1), Real.rpow_one]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)

/-- Abel's exact Mellin representation of the logarithmic derivative of
zeta, with the complete Chebyshev psi partial sum retained. -/
theorem nicolasLogDeriv_eq_psiMellin
    {s : Complex} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      s * integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (Chebyshev.psi t : Complex) *
          (t : Complex) ^ (-(s + 1))) := by
  have hAbel := LSeries_eq_mul_integral_of_nonneg
    (fun n : Nat => ArithmeticFunction.vonMangoldt n)
    (r := (1 : Real)) (by norm_num) hs
    nicolasVonMangoldtPartialSums_isBigO
    (fun n => ArithmeticFunction.vonMangoldt_nonneg)
  calc
    -deriv riemannZeta s / riemannZeta s =
        LSeries (fun n : Nat =>
          (ArithmeticFunction.vonMangoldt n : Complex)) s := by
      symm
      exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
    _ = s * integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (Finset.sum (Finset.Icc 1 (Nat.floor t))
          (fun k => (ArithmeticFunction.vonMangoldt k : Complex))) *
          (t : Complex) ^ (-(s + 1))) := hAbel
    _ = s * integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (Chebyshev.psi t : Complex) *
          (t : Complex) ^ (-(s + 1))) := by
      have hIntegral :
          integral (volume.restrict (Ioi (1 : Real)))
              (fun t => (Finset.sum (Finset.Icc 1 (Nat.floor t))
                (fun k => (ArithmeticFunction.vonMangoldt k : Complex))) *
                (t : Complex) ^ (-(s + 1))) =
            integral (volume.restrict (Ioi (1 : Real)))
              (fun t => (Chebyshev.psi t : Complex) *
                (t : Complex) ^ (-(s + 1))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change
          (Finset.sum (Finset.Icc 1 (Nat.floor t))
              (fun k => (ArithmeticFunction.vonMangoldt k : Complex))) *
              (t : Complex) ^ (-(s + 1)) =
            (Chebyshev.psi t : Complex) *
              (t : Complex) ^ (-(s + 1))
        congr 1
        rw [Chebyshev.psi_eq_sum_Icc]
        push_cast
        symm
        rw [<- Finset.insert_Icc_add_one_left_eq_Icc
            (Nat.zero_le (Nat.floor t)),
          Finset.sum_insert (by aesop)]
        simp
      rw [hIntegral]

theorem nicolasPsiMellin_integrable
    {s : Complex} (hs : 1 < s.re) :
    IntegrableOn
      (fun t : Real => (Chebyshev.psi t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi 1) := by
  let c : Real := Real.log 4 + 4
  have hcPos : 0 < c := by
    dsimp [c]
    positivity
  have hPower : IntegrableOn
      (fun t : Real => (c : Complex) * (t : Complex) ^ (-s)) (Ioi 1) := by
    exact (integrableOn_Ioi_cpow_of_lt
      (by simp only [Complex.neg_re]; linarith) (by norm_num)).const_mul (c : Complex)
  apply Integrable.mono
    (g := fun t : Real => (c : Complex) * (t : Complex) ^ (-s)) hPower
  . have hCpow : ContinuousOn
        (fun t : Real => (t : Complex) ^ (-(s + 1))) (Ioi 1) :=
      continuousOn_of_forall_continuousAt fun t ht =>
        Complex.continuousAt_ofReal_cpow_const t (-(s + 1))
          (Or.inr (ne_of_gt (lt_trans (by norm_num) ht)))
    exact ((Complex.measurable_ofReal.comp
      Chebyshev.psi_mono.measurable).aestronglyMeasurable.mul
        (hCpow.aestronglyMeasurable measurableSet_Ioi))
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htPos : 0 < t := lt_trans (by norm_num) ht
    have hPsi := Chebyshev.psi_le_const_mul_self htPos.le
    have hPowNonneg : 0 <= t ^ (-(s + 1)).re :=
      Real.rpow_nonneg htPos.le _
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Chebyshev.psi_nonneg t), abs_of_pos hcPos,
      Complex.norm_cpow_eq_rpow_re_of_pos htPos]
    calc
      Chebyshev.psi t * t ^ (-(s + 1)).re <=
          (c * t) * t ^ (-(s + 1)).re :=
        mul_le_mul_of_nonneg_right hPsi hPowNonneg
      _ = c * t ^ (-s).re := by
        calc
          (c * t) * t ^ (-(s + 1)).re =
              c * (t ^ (1 : Real) * t ^ (-(s + 1)).re) := by
            rw [Real.rpow_one]
            ring
          _ = c * t ^ ((1 : Real) + (-(s + 1)).re) := by
            rw [Real.rpow_add htPos]
          _ = c * t ^ (-s).re := by
            congr 2
            simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
            ring

theorem nicolasLinearMellin_integrable
    {s : Complex} (hs : 1 < s.re) :
    IntegrableOn
      (fun t : Real => (t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi 1) := by
  have hPower : IntegrableOn
      (fun t : Real => (t : Complex) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt
      (by simp only [Complex.neg_re]; linarith) (by norm_num)
  apply hPower.congr_fun
  . intro t ht
    have htZero : Not ((t : Complex) = 0) := by
      exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_trans (by norm_num) ht))
    change (t : Complex) ^ (-s) =
      (t : Complex) * (t : Complex) ^ (-(s + 1))
    symm
    calc
      (t : Complex) * (t : Complex) ^ (-(s + 1)) =
          (t : Complex) ^ (1 : Complex) *
            (t : Complex) ^ (-(s + 1)) := by
        rw [Complex.cpow_one]
      _ = (t : Complex) ^ ((1 : Complex) + -(s + 1)) := by
        rw [Complex.cpow_add _ _ htZero]
      _ = (t : Complex) ^ (-s) := by
        congr 1
        ring
  . exact measurableSet_Ioi

/-- The exact Mellin transform of Nicolas's psi error on its initial
half-plane of convergence.  This is the expression whose continuation
inherits the nonreal singularities of the logarithmic derivative of zeta. -/
theorem nicolasPsiErrorMellin_eq_logDeriv
    {s : Complex} (hs : 1 < s.re) :
    integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) =
      (-deriv riemannZeta s / riemannZeta s) / s -
        1 / (s - 1) := by
  have hsZero : Not (s = 0) := by
    intro hZero
    subst s
    norm_num at hs
  have hsOne : Not (s = 1) := by
    intro hOne
    subst s
    norm_num at hs
  have hLinear :
      integral (volume.restrict (Ioi (1 : Real)))
          (fun t => (t : Complex) * (t : Complex) ^ (-(s + 1))) =
        1 / (s - 1) := by
    calc
      integral (volume.restrict (Ioi (1 : Real)))
          (fun t => (t : Complex) * (t : Complex) ^ (-(s + 1))) =
          integral (volume.restrict (Ioi (1 : Real)))
            (fun t => (t : Complex) ^ (-s)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have htZero : Not ((t : Complex) = 0) := by
          exact Complex.ofReal_ne_zero.mpr
            (ne_of_gt (lt_trans (by norm_num) ht))
        change (t : Complex) * (t : Complex) ^ (-(s + 1)) =
          (t : Complex) ^ (-s)
        calc
          (t : Complex) * (t : Complex) ^ (-(s + 1)) =
              (t : Complex) ^ (1 : Complex) *
                (t : Complex) ^ (-(s + 1)) := by
            rw [Complex.cpow_one]
          _ = (t : Complex) ^ ((1 : Complex) + -(s + 1)) := by
            rw [Complex.cpow_add _ _ htZero]
          _ = (t : Complex) ^ (-s) := by
            congr 1
            ring
      _ = 1 / (s - 1) := by
        rw [integral_Ioi_cpow_of_lt
          (by simp only [Complex.neg_re]; linarith) (by norm_num)]
        rw [Complex.ofReal_one, Complex.one_cpow]
        rw [show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
  rw [show (fun t : Real => (nicolasPsiError t : Complex) *
      (t : Complex) ^ (-(s + 1))) =
      (fun t : Real =>
        (Chebyshev.psi t : Complex) * (t : Complex) ^ (-(s + 1)) -
        (t : Complex) * (t : Complex) ^ (-(s + 1))) by
      funext t
      unfold nicolasPsiError
      push_cast
      ring]
  rw [integral_sub (nicolasPsiMellin_integrable hs)
    (nicolasLinearMellin_integrable hs), hLinear]
  have hLog := nicolasLogDeriv_eq_psiMellin hs
  congr 1
  symm
  apply (div_eq_iff hsZero).2
  rw [hLog]
  ring

theorem nicolasPsiErrorMellin_integrable
    {s : Complex} (hs : 1 < s.re) :
    IntegrableOn
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi 1) := by
  have hSub := (nicolasPsiMellin_integrable hs).sub
    (nicolasLinearMellin_integrable hs)
  apply hSub.congr_fun
  . intro t ht
    change
      (Chebyshev.psi t : Complex) * (t : Complex) ^ (-(s + 1)) -
          (t : Complex) * (t : Complex) ^ (-(s + 1)) =
        (nicolasPsiError t : Complex) * (t : Complex) ^ (-(s + 1))
    unfold nicolasPsiError
    push_cast
    ring
  . exact measurableSet_Ioi

/-- The meromorphic expression agreeing with the complete psi-error Mellin
transform on `re s > 1`. -/
def nicolasPsiMellinContinuation (s : Complex) : Complex :=
  (-deriv riemannZeta s / riemannZeta s) / s - 1 / (s - 1)

/-- The finite startup interval removed when the psi-error Mellin tail begins
from `x` instead of from one. -/
def nicolasPsiMellinStartup (x : Real) (s : Complex) : Complex :=
  integral (volume.restrict (Ioc (1 : Real) x))
    (fun t : Real => (nicolasPsiError t : Complex) *
      (t : Complex) ^ (-(s + 1)))

/-- Analytic continuation candidate for the psi-error Mellin tail beginning
from `x`: complete meromorphic transform minus its finite startup interval. -/
def nicolasPsiMellinTailContinuation (x : Real) (s : Complex) : Complex :=
  nicolasPsiMellinContinuation s - nicolasPsiMellinStartup x s

theorem nicolasPsiErrorTailMellin_eq_continuation
    {x : Real} (hx : 1 <= x) {s : Complex} (hs : 1 < s.re) :
    integral (volume.restrict (Ioi x))
        (fun t : Real => (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) =
      nicolasPsiMellinTailContinuation x s := by
  have hFull := nicolasPsiErrorMellin_integrable hs
  have hStartup : IntegrableOn
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioc 1 x) :=
    hFull.mono_set Ioc_subset_Ioi_self
  have hTail : IntegrableOn
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi x) :=
    hFull.mono_set (Ioi_subset_Ioi hx)
  have hSplit :
      integral (volume.restrict (Ioi (1 : Real)))
          (fun t : Real => (nicolasPsiError t : Complex) *
            (t : Complex) ^ (-(s + 1))) =
        integral (volume.restrict (Ioc (1 : Real) x))
            (fun t : Real => (nicolasPsiError t : Complex) *
              (t : Complex) ^ (-(s + 1))) +
          integral (volume.restrict (Ioi x))
            (fun t : Real => (nicolasPsiError t : Complex) *
              (t : Complex) ^ (-(s + 1))) := by
    rw [<- Ioc_union_Ioi_eq_Ioi hx,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
    . exact hStartup
    . exact hTail
  unfold nicolasPsiMellinTailContinuation nicolasPsiMellinContinuation
    nicolasPsiMellinStartup
  rw [<- nicolasPsiErrorMellin_eq_logDeriv hs]
  rw [hSplit]
  ring

theorem integrableOn_mul_exp_neg_mul_Ioi_zero
    {r : Real} (hr : 0 < r) :
    IntegrableOn (fun u : Real => u * Real.exp (-(r * u))) (Ioi 0) := by
  have hGamma : IntegrableOn
      (fun u : Real => Real.exp (-u) * u ^ ((2 : Real) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by norm_num)
  have hScaled : IntegrableOn
      (fun u : Real =>
        Real.exp (-(r * u)) * (r * u) ^ ((2 : Real) - 1)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun u : Real => Real.exp (-u) * u ^ ((2 : Real) - 1)) 0 hr).2
    simpa using hGamma
  have hDiv := hScaled.const_mul (1 / r)
  change Integrable (fun u : Real => u * Real.exp (-(r * u)))
    (volume.restrict (Ioi 0))
  apply hDiv.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  calc
    (1 / r) *
        (Real.exp (-(r * u)) * (r * u) ^ ((2 : Real) - 1)) =
        (1 / r) * (Real.exp (-(r * u)) * (r * u)) := by
      rw [show (2 : Real) - 1 = 1 by norm_num, Real.rpow_one]
    _ = u * Real.exp (-(r * u)) := by
      field_simp [hr.ne']

theorem integral_exp_neg_mul_Ioi_zero
    {r : Real} (hr : 0 < r) :
    integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => Real.exp (-(r * u))) =
      1 / r := by
  have hValue := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1 : Real)) (r := r) (by norm_num) hr
  simpa using hValue

theorem integral_mul_exp_neg_mul_Ioi_zero
    {r : Real} (hr : 0 < r) :
    integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => u * Real.exp (-(r * u))) =
      1 / r ^ 2 := by
  have hValue := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : Real)) (r := r) (by norm_num) hr
  convert hValue using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change u * Real.exp (-(r * u)) =
    u ^ ((2 : Real) - 1) * Real.exp (-(r * u))
  rw [show (2 : Real) - 1 = 1 by norm_num, Real.rpow_one]
  norm_num [Real.Gamma_ofNat_eq_factorial, div_pow]

end

end Robin1984

