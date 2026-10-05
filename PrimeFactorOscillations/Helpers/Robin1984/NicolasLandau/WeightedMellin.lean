/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/WeightedMellin.lean
Original source lines 426-708. Apache-2.0.
Statements and proof bodies retained; only the required declaration block is selected.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedMellinKernel

/-!
# Prime-power sum and resolvent pairing for the cutoff test

Part of the written RH negative-envelope argument.
-/

namespace Robin1984

noncomputable section

open Complex MeasureTheory Set

theorem robin_summable_vonMangoldt_cpow
    {s : Complex} (hs : 1 < s.re) :
    Summable (fun m : Nat =>
      (ArithmeticFunction.vonMangoldt m : Complex) / (m : Complex) ^ s) := by
  refine (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).congr ?_
  intro m
  by_cases hm : m = 0
  case pos => simp [hm]
  case neg => rw [LSeries.term_of_ne_zero hm]

theorem robin_tsum_vonMangoldt_eq_neg_logDeriv
    {s : Complex} (hs : 1 < s.re) :
    tsum (fun m : Nat =>
      (ArithmeticFunction.vonMangoldt m : Complex) / (m : Complex) ^ s) =
      -deriv riemannZeta s / riemannZeta s := by
  rw [<- ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, LSeries]
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  case pos => simp [hm]
  case neg => rw [LSeries.term_of_ne_zero hm]

theorem norm_vonMangoldt_vertical_eq
    (c t : Real) (m : Nat) :
    norm ((ArithmeticFunction.vonMangoldt m : Complex) /
        (m : Complex) ^ ((c : Complex) + (t : Complex) * Complex.I)) =
      norm ((ArithmeticFunction.vonMangoldt m : Complex) /
        (m : Complex) ^ (c : Complex)) := by
  cases m with
  | zero => simp
  | succ m =>
      rw [norm_div, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.succ_pos m),
        Complex.norm_natCast_cpow_of_pos (Nat.succ_pos m)]
      simp

/-- On a safe line, the von Mangoldt series can be exchanged with any
integrable vertical test.  The proof supplies the summable integrated norm. -/
theorem integral_vonMangoldt_series_mul
    {c : Real} (hc : 1 < c) {H : Real -> Complex} (hH : Integrable H) :
    tsum (fun m : Nat => integral volume (fun t : Real =>
        ((ArithmeticFunction.vonMangoldt m : Complex) /
          (m : Complex) ^ ((c : Complex) + (t : Complex) * Complex.I)) * H t)) =
      integral volume (fun t : Real =>
        (-deriv riemannZeta ((c : Complex) + (t : Complex) * Complex.I) /
          riemannZeta ((c : Complex) + (t : Complex) * Complex.I)) * H t) := by
  let F : Nat -> Real -> Complex := fun m t =>
    ((ArithmeticFunction.vonMangoldt m : Complex) /
      (m : Complex) ^ ((c : Complex) + (t : Complex) * Complex.I)) * H t
  let A : Nat -> Real := fun m =>
    norm ((ArithmeticFunction.vonMangoldt m : Complex) /
      (m : Complex) ^ (c : Complex))
  have hNorm : forall m : Nat, forall t : Real, norm (F m t) = A m * norm (H t) := by
    intro m t
    dsimp [F, A]
    rw [norm_mul, norm_vonMangoldt_vertical_eq]
  have hFInt : forall m : Nat, Integrable (F m) := by
    intro m
    have hCoeffMeas : Measurable (fun t : Real =>
        (ArithmeticFunction.vonMangoldt m : Complex) /
          (m : Complex) ^ ((c : Complex) + (t : Complex) * Complex.I)) := by
      fun_prop
    have hFMeas : AEStronglyMeasurable (F m) volume :=
      hCoeffMeas.aestronglyMeasurable.mul hH.aestronglyMeasurable
    apply (hH.norm.const_mul (A m)).mono' hFMeas
    filter_upwards with t
    rw [hNorm]
  have hNormIntegral : forall m : Nat,
      integral volume (fun t : Real => norm (F m t)) =
        A m * integral volume (fun t : Real => norm (H t)) := by
    intro m
    have hFunction : (fun t : Real => norm (F m t)) =
        (fun t : Real => A m * norm (H t)) := by
      funext t
      exact hNorm m t
    rw [hFunction, integral_const_mul]
  have hASum : Summable A := by
    exact (robin_summable_vonMangoldt_cpow (s := (c : Complex)) (by simpa using hc)).norm
  have hNormSum : Summable (fun m : Nat => integral volume (fun t : Real => norm (F m t))) := by
    have h := hASum.mul_right (integral volume (fun t : Real => norm (H t)))
    exact h.congr (fun m => (hNormIntegral m).symm)
  calc
    tsum (fun m : Nat => integral volume (F m)) =
        integral volume (fun t : Real => tsum (fun m : Nat => F m t)) :=
      integral_tsum_of_summable_integral_norm hFInt hNormSum
    _ = integral volume (fun t : Real =>
        (-deriv riemannZeta ((c : Complex) + (t : Complex) * Complex.I) /
          riemannZeta ((c : Complex) + (t : Complex) * Complex.I)) * H t) := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp [F]
      rw [tsum_mul_right, robin_tsum_vonMangoldt_eq_neg_logDeriv (by simpa using hc)]

theorem vonMangoldt_mul_robinCutoffMellinTest_eq_integral
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x)
    {c : Real} (hcPos : 0 < c) (hcLt : c < n) (m : Nat) :
    (ArithmeticFunction.vonMangoldt m : Complex) *
        robinCutoffMellinTest n x (m : Real) =
      (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          ((ArithmeticFunction.vonMangoldt m : Complex) /
            (m : Complex) ^ ((c : Complex) + (t : Complex) * Complex.I)) *
            mellin (robinCutoffMellinTest n x)
              ((c : Complex) + (t : Complex) * Complex.I)) := by
  by_cases hm : m = 0
  case pos => simp [hm]
  case neg =>
    have hmPos : 0 < (m : Real) := by
      exact_mod_cast (Nat.pos_of_ne_zero hm)
    have hInv := mellinInv_mellin_robinCutoffMellinTest hn hx hcPos hcLt hmPos
    simp only [mellinInv, RCLike.real_smul_eq_coe_mul, smul_eq_mul,
      Complex.ofReal_natCast] at hInv
    rw [<- hInv]
    calc
      (ArithmeticFunction.vonMangoldt m : Complex) *
          ((((1 / (2 * Real.pi) : Real) : Complex)) *
            integral volume (fun t : Real =>
              (m : Complex) ^ (-((c : Complex) + (t : Complex) * Complex.I)) *
                mellin (robinCutoffMellinTest n x)
                  ((c : Complex) + (t : Complex) * Complex.I))) =
          (((1 / (2 * Real.pi) : Real) : Complex)) *
            ((ArithmeticFunction.vonMangoldt m : Complex) *
              integral volume (fun t : Real =>
                (m : Complex) ^ (-((c : Complex) + (t : Complex) * Complex.I)) *
                  mellin (robinCutoffMellinTest n x)
                    ((c : Complex) + (t : Complex) * Complex.I))) := by ring
      _ = (((1 / (2 * Real.pi) : Real) : Complex)) *
          integral volume (fun t : Real =>
            (ArithmeticFunction.vonMangoldt m : Complex) *
              ((m : Complex) ^ (-((c : Complex) + (t : Complex) * Complex.I)) *
                mellin (robinCutoffMellinTest n x)
                  ((c : Complex) + (t : Complex) * Complex.I))) := by
        rw [integral_const_mul]
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards with t
        rw [Complex.cpow_neg, div_eq_mul_inv]
        ring

/-- The arithmetic prime-power sum is the absolutely convergent safe-line
zeta integral for the exact Robin cutoff test. -/
theorem robinPrimePowerSum_eq_safeLineIntegral
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x)
    {c : Real} (hc : 1 < c) (hcLt : c < n) :
    tsum (fun m : Nat =>
        (ArithmeticFunction.vonMangoldt m : Complex) *
          robinCutoffMellinTest n x (m : Real)) =
      (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          (-deriv riemannZeta ((c : Complex) + (t : Complex) * Complex.I) /
            riemannZeta ((c : Complex) + (t : Complex) * Complex.I)) *
            mellin (robinCutoffMellinTest n x)
              ((c : Complex) + (t : Complex) * Complex.I)) := by
  have hcPos : 0 < c := lt_trans Real.zero_lt_one hc
  have hVertical := verticalIntegrable_mellin_robinCutoffMellinTest hn hx hcPos hcLt
  have hSwap := integral_vonMangoldt_series_mul hc hVertical
  calc
    tsum (fun m : Nat =>
        (ArithmeticFunction.vonMangoldt m : Complex) *
          robinCutoffMellinTest n x (m : Real)) =
        tsum (fun m : Nat =>
          (((1 / (2 * Real.pi) : Real) : Complex)) *
            integral volume (fun t : Real =>
              ((ArithmeticFunction.vonMangoldt m : Complex) /
                (m : Complex) ^ ((c : Complex) + (t : Complex) * Complex.I)) *
                mellin (robinCutoffMellinTest n x)
                  ((c : Complex) + (t : Complex) * Complex.I))) := by
      apply tsum_congr
      intro m
      exact vonMangoldt_mul_robinCutoffMellinTest_eq_integral hn hx hcPos hcLt m
    _ = (((1 / (2 * Real.pi) : Real) : Complex)) *
        tsum (fun m : Nat => integral volume (fun t : Real =>
          ((ArithmeticFunction.vonMangoldt m : Complex) /
            (m : Complex) ^ ((c : Complex) + (t : Complex) * Complex.I)) *
            mellin (robinCutoffMellinTest n x)
              ((c : Complex) + (t : Complex) * Complex.I))) := by
      rw [tsum_mul_left]
    _ = _ := by rw [hSwap]

/-- Absolute Fubini for the resolvent of a vertical Mellin test. -/
theorem integrable_vertical_resolvent_joint
    {H : Real -> Complex} (hH : Integrable H) {c : Real} {rho : Complex}
    (hRho : rho.re < c) :
    Integrable (fun z : Prod Real Real => H z.1 *
      (z.2 : Complex) ^ (rho - ((c : Complex) + (z.1 : Complex) * Complex.I) - 1))
      (volume.prod (volume.restrict (Ioi (1 : Real)))) := by
  have hPower : IntegrableOn (fun u : Real => u ^ (rho.re - c - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) Real.zero_lt_one
  have hMajor := hH.norm.mul_prod hPower
  have hPowerMeas : Measurable (fun z : Prod Real Real =>
      (z.2 : Complex) ^ (rho - ((c : Complex) + (z.1 : Complex) * Complex.I) - 1)) := by
    fun_prop
  have hMeas : AEStronglyMeasurable (fun z : Prod Real Real => H z.1 *
      (z.2 : Complex) ^ (rho - ((c : Complex) + (z.1 : Complex) * Complex.I) - 1))
      (volume.prod (volume.restrict (Ioi (1 : Real)))) :=
    hH.aestronglyMeasurable.comp_fst.mul hPowerMeas.aestronglyMeasurable
  apply hMajor.mono' hMeas
  have hMem : Filter.Eventually (fun z : Prod Real Real => 1 < z.2)
      (ae (volume.prod (volume.restrict (Ioi (1 : Real))))) := by
    apply (MeasureTheory.Measure.ae_prod_iff_ae_ae
      (measurableSet_Ioi.preimage measurable_snd)).mpr
    exact Filter.Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hMem] with z hz
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < z.2)]
  simp

/-- Evaluate the resolvent by an absolutely convergent tail integral, without
moving the vertical contour. -/
theorem integral_vertical_resolvent_eq_inverse_tail
    {H : Real -> Complex} (hH : Integrable H) {c : Real} {rho : Complex}
    (hRho : rho.re < c) :
    integral volume (fun t : Real =>
        H t / ((c : Complex) + (t : Complex) * Complex.I - rho)) =
      integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
        (u : Complex) ^ (rho - 1) * integral volume (fun t : Real =>
          (u : Complex) ^ (-((c : Complex) + (t : Complex) * Complex.I)) * H t)) := by
  have hJoint := integrable_vertical_resolvent_joint hH hRho
  have hInner : forall t : Real,
      integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
        H t * (u : Complex) ^ (rho - ((c : Complex) + (t : Complex) * Complex.I) - 1)) =
      H t / ((c : Complex) + (t : Complex) * Complex.I - rho) := by
    intro t
    rw [integral_const_mul, integral_Ioi_cpow_of_lt (by
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re,
        Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im]
      linarith : (rho - ((c : Complex) + (t : Complex) * Complex.I) - 1).re < -1)
        Real.zero_lt_one]
    simp only [Complex.ofReal_one, Complex.one_cpow, sub_add_cancel]
    have hDen : rho - ((c : Complex) + (t : Complex) * Complex.I) =
        -((c : Complex) + (t : Complex) * Complex.I - rho) := by ring
    rw [hDen]
    simp only [div_eq_mul_inv, inv_neg, neg_mul, one_mul, neg_neg]
  calc
    integral volume (fun t : Real =>
        H t / ((c : Complex) + (t : Complex) * Complex.I - rho)) =
      integral volume (fun t : Real =>
        integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
          H t * (u : Complex) ^ (rho - ((c : Complex) + (t : Complex) * Complex.I) - 1))) := by
        apply integral_congr_ae
        filter_upwards with t
        exact (hInner t).symm
    _ = integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
        integral volume (fun t : Real =>
          H t * (u : Complex) ^ (rho - ((c : Complex) + (t : Complex) * Complex.I) - 1))) :=
      integral_integral_swap hJoint
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      have huZero : Not ((u : Complex) = 0) :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans Real.zero_lt_one hu))
      rw [<- integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      rw [show rho - ((c : Complex) + (t : Complex) * Complex.I) - 1 =
          (rho - 1) + (-((c : Complex) + (t : Complex) * Complex.I)) by ring,
        Complex.cpow_add _ _ huZero]
      ring

/-- The resolvent of the exact cutoff transform is its multiplicative tail. -/
theorem robinCutoffMellin_resolvent_pairing
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x)
    {c : Real} (hcPos : 0 < c) (hcLt : c < n)
    {rho : Complex} (hRho : rho.re < c) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          mellin (robinCutoffMellinTest n x) ((c : Complex) + (t : Complex) * Complex.I) /
            ((c : Complex) + (t : Complex) * Complex.I - rho)) =
      integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
        (u : Complex) ^ (rho - 1) * robinCutoffMellinTest n x u) := by
  rw [integral_vertical_resolvent_eq_inverse_tail
    (verticalIntegrable_mellin_robinCutoffMellinTest hn hx hcPos hcLt) hRho,
    <- integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  have hInv := mellinInv_mellin_robinCutoffMellinTest hn hx hcPos hcLt
    (lt_trans Real.zero_lt_one hu)
  simp only [mellinInv, RCLike.real_smul_eq_coe_mul, smul_eq_mul] at hInv
  have hScaled := congrArg (fun v : Complex => (u : Complex) ^ (rho - 1) * v) hInv
  simpa only [mul_left_comm, mul_assoc, mul_comm] using! hScaled

end

end Robin1984
