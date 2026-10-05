/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauRightmostRay.lean
Original source lines 856-1126. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauRayKernel

/-!
# The logarithmic singular contribution and its bounded complement

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

theorem exists_nicolasRightmostRayScaledKernel_log_interval_estimate
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps : Real, 0 < eps -> eps < r ->
            norm (intervalIntegral (fun v : Real =>
                HSMul.hSMul (Inv.inv v)
                  (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v))
                eps r volume -
              HSMul.hSMul (Real.log (r / eps)) d) <=
              (norm d / 4) * abs (Real.log (r / eps))))) := by
  choose d r hd hrPos hrHalf hUniform using
    exists_nicolasRightmostRayScaledKernelFilled_uniform
      hZero hHalf hOneRe hRay
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps hEps hEpsR
  have hInt :=
    nicolasJRightmostRayTranslatedScaledKernelFilled_intervalIntegrable
      hZero hHalf hOneRe hRay hEps hEpsR (by linarith)
  apply norm_intervalIntegral_inv_smul_sub_le_of_intervalIntegrable
    hInt hEps hrPos (by positivity)
  intro v hv
  have hvIoc : Membership.mem (Ioc eps r) v := by
    simpa [uIoc, min_eq_left hEpsR.le, max_eq_right hEpsR.le] using hv
  exact hUniform eps v hEps hvIoc.1 hvIoc.2

theorem nicolasRightmostRay_weighted_scaledKernelFilled_interval_eq
    {rho : Complex} {eps r : Real} (hEps : 0 < eps) (hEpsR : eps < r) :
    intervalIntegral (fun v : Real =>
        HSMul.hSMul (Inv.inv v)
          (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v))
        eps r volume =
      intervalIntegral
        (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps))
        0 (r - eps) volume := by
  calc
    intervalIntegral (fun v : Real =>
        HSMul.hSMul (Inv.inv v)
          (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v))
        eps r volume =
        intervalIntegral (fun v : Real =>
          nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps) (v - eps))
          eps r volume := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hvIcc : Membership.mem (Icc eps r) v := by
        simpa [uIcc, min_eq_left hEpsR.le,
          max_eq_right hEpsR.le] using hv
      have hvPos : 0 < v := hEps.trans_le hvIcc.1
      unfold nicolasJRightmostRayTranslatedScaledKernelFilled
      change ((Inv.inv v : Real) : Complex) *
          ((v : Complex) *
            nicolasJMellinShiftIntegrandFilled
              (nicolasRightmostRayPoint rho eps) (v - eps)) =
        nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps) (v - eps)
      rw [Complex.ofReal_inv]
      field_simp [Complex.ofReal_ne_zero.mpr hvPos.ne']
    _ = intervalIntegral
        (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps))
        (eps - eps) (r - eps) volume := by
      exact intervalIntegral.integral_comp_sub_right
        (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps)) eps
    _ = intervalIntegral
        (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps))
        0 (r - eps) volume := by ring_nf

theorem exists_nicolasRightmostRayCompactSingularIntegral_lowerBound
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps : Real, 0 < eps -> eps < r ->
            (3 / 4 : Real) * norm d * Real.log (r / eps) <=
              norm (intervalIntegral
                (nicolasJMellinShiftIntegrandFilled
                  (nicolasRightmostRayPoint rho eps))
                0 (r - eps) volume)))) := by
  choose d r hd hrPos hrHalf hEstimate using
    exists_nicolasRightmostRayScaledKernel_log_interval_estimate
      hZero hHalf hOneRe hRay
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps hEps hEpsR
  let I : Complex := intervalIntegral (fun v : Real =>
      HSMul.hSMul (Inv.inv v)
        (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v))
      eps r volume
  let A : Complex := HSMul.hSMul (Real.log (r / eps)) d
  have hRatio : 1 < r / eps := (one_lt_div hEps).mpr hEpsR
  have hLogPos : 0 < Real.log (r / eps) := Real.log_pos hRatio
  have hErr : norm (I - A) <=
      (norm d / 4) * Real.log (r / eps) := by
    dsimp [I, A]
    simpa [abs_of_pos hLogPos] using hEstimate eps hEps hEpsR
  have hReverse : norm A - norm I <= norm (I - A) := by
    have hBasic := (le_abs_self (norm A - norm I)).trans
      (abs_norm_sub_norm_le A I)
    simpa [norm_sub_rev] using hBasic
  have hANorm : norm A = Real.log (r / eps) * norm d := by
    dsimp [A]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hLogPos]
  have hLowerI : (3 / 4 : Real) * norm d * Real.log (r / eps) <=
      norm I := by
    rw [hANorm] at hReverse
    have hdNorm : 0 <= norm d := norm_nonneg d
    nlinarith [hReverse.trans hErr]
  dsimp [I] at hLowerI
  have hIntegralEq :
      intervalIntegral (fun v : Real =>
          ((Inv.inv v : Real) : Complex) *
            nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v)
          eps r volume =
        intervalIntegral
          (nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps))
          0 (r - eps) volume := by
    simpa [smul_eq_mul] using
      (nicolasRightmostRay_weighted_scaledKernelFilled_interval_eq
        (rho := rho) hEps hEpsR)
  rw [hIntegralEq] at hLowerI
  exact hLowerI

theorem exists_nicolasRightmostRayCompactAwayKernel_bound
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {r : Real} (hrPos : 0 < r) (hrHalf : r < 1 / 2) :
    Exists fun M : Real => And (0 <= M)
      (forall eps u : Real,
        Membership.mem (Icc (0 : Real) (r / 2)) eps ->
        Membership.mem (Icc (r / 2) (1 : Real)) u ->
        norm (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps) u) <= M) := by
  let K : Set (Prod Real Real) := fun p =>
    And (Membership.mem (Icc (0 : Real) (r / 2)) p.1)
      (Membership.mem (Icc (r / 2) (1 : Real)) p.2)
  let F : Prod Real Real -> Complex := fun p =>
    nicolasJMellinShiftIntegrandFilled
      (nicolasRightmostRayPoint rho p.1) p.2
  have hKCompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_Icc : IsCompact (Icc (0 : Real) (r / 2))).prod
      (isCompact_Icc : IsCompact (Icc (r / 2) (1 : Real)))
  have hKNonempty : K.Nonempty := by
    refine Exists.intro ((0 : Real), r / 2) ?_
    dsimp [K]
    exact And.intro (And.intro le_rfl (by positivity))
      (And.intro le_rfl (by linarith))
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOneRe
  have hContinuous : ContinuousOn F K := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    change And (Membership.mem (Icc (0 : Real) (r / 2)) p.1)
      (Membership.mem (Icc (r / 2) (1 : Real)) p.2) at hp
    have hzZero : Not (nicolasRightmostRayPoint rho p.1 = 0) := by
      intro hEq
      have hEqIm := congrArg Complex.im hEq
      unfold nicolasRightmostRayPoint at hEqIm
      simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im,
        Complex.zero_im] at hEqIm
      apply hIm
      linarith
    let s : Complex := rho + ((p.1 + p.2 : Real) : Complex)
    have hsIm : s.im = rho.im := by
      dsimp [s]
      simp
    have hsZero : Not (s = 0) := by
      intro hEq
      have hEqIm := congrArg Complex.im hEq
      rw [hsIm, Complex.zero_im] at hEqIm
      exact hIm hEqIm
    have hsOne : Not (s = 1) := by
      intro hEq
      have hEqIm := congrArg Complex.im hEq
      rw [hsIm, Complex.one_im] at hEqIm
      exact hIm hEqIm
    have hSumPos : 0 < p.1 + p.2 := by
      linarith [hp.1.1, hp.2.1, hrPos]
    have hZeta : Not (riemannZeta s = 0) := by
      dsimp [s]
      exact hRay (p.1 + p.2) hSumPos
    have hFactor : Not (nicolasZetaPoleFactor s = 0) :=
      nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta
    have hShift :
        ((((p.2 + 1 : Real) : Complex) -
            nicolasRightmostRayPoint rho p.1)) = s := by
      dsimp [s, nicolasRightmostRayPoint]
      push_cast
      ring
    have hShiftZero : Not
        ((((p.2 + 1 : Real) : Complex) -
            nicolasRightmostRayPoint rho p.1) = 0) := by
      rw [hShift]
      exact hsZero
    have hShiftFactor : Not
        (nicolasZetaPoleFactor
          (((p.2 + 1 : Real) : Complex) -
            nicolasRightmostRayPoint rho p.1) = 0) := by
      rw [hShift]
      exact hFactor
    have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      (u := p.2) (z := nicolasRightmostRayPoint rho p.1)
      (by linarith [hp.2.1, hrPos]) hzZero hShiftZero hShiftFactor
    have hEmbed : ContinuousAt (fun q : Prod Real Real =>
        (q.2, nicolasRightmostRayPoint rho q.1)) p := by
      unfold nicolasRightmostRayPoint
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    simpa [F, Function.comp_def] using hComp
  choose p hpK hpMax using
    hKCompact.exists_isMaxOn hKNonempty hContinuous.norm
  let M : Real := norm (F p)
  refine Exists.intro M (And.intro (norm_nonneg _) ?_)
  intro eps u hEps hU
  have hPair : K (eps, u) := by
    dsimp [K]
    exact And.intro hEps hU
  simpa [M, F] using hpMax hPair

theorem exists_nicolasRightmostRayCompactAwayIntegral_bound
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {r : Real} (hrPos : 0 < r) (hrHalf : r < 1 / 2) :
    Exists fun M : Real => And (0 <= M)
      (forall eps : Real, 0 <= eps -> eps <= r / 2 ->
        norm (intervalIntegral
          (nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps))
          (r - eps) 1 volume) <= M) := by
  choose M hMNonneg hKernel using
    exists_nicolasRightmostRayCompactAwayKernel_bound
      hZero hHalf hOneRe hRay hrPos hrHalf
  refine Exists.intro M (And.intro hMNonneg ?_)
  intro eps hEps hEpsLe
  have hLowerNonneg : 0 <= r - eps := by linarith
  have hLowerOne : r - eps <= 1 := by linarith
  have hPointwise : forall u : Real,
      Membership.mem (uIoc (r - eps) (1 : Real)) u ->
      norm (nicolasJMellinShiftIntegrandFilled
        (nicolasRightmostRayPoint rho eps) u) <= M := by
    intro u hu
    have huIoc : Membership.mem (Ioc (r - eps) (1 : Real)) u := by
      simpa [uIoc, min_eq_left hLowerOne,
        max_eq_right hLowerOne] using hu
    apply hKernel eps u
    . exact And.intro hEps hEpsLe
    . exact And.intro (by linarith [huIoc.1]) huIoc.2
  have hNorm := intervalIntegral.norm_integral_le_of_norm_le_const hPointwise
  rw [abs_of_nonneg (by linarith : 0 <= (1 : Real) - (r - eps))] at hNorm
  nlinarith

end

end Robin1984
