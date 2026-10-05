/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauRightmostRay.lean
Original source lines 1127-1505. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauRaySingular

/-!
# Unbounded growth of the continued transform at the zero

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

theorem exists_nicolasRightmostRayCompactIntegral_log_lowerBound
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real => Exists fun M : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2) (And (0 <= M)
          (forall eps : Real, 0 < eps -> eps <= r / 2 ->
            (3 / 4 : Real) * norm d * Real.log (r / eps) - M <=
              norm (intervalIntegral
                (nicolasJMellinShiftIntegrandFilled
                  (nicolasRightmostRayPoint rho eps))
                0 1 volume))))) := by
  choose d r hd hrPos hrHalf hSingular using
    exists_nicolasRightmostRayCompactSingularIntegral_lowerBound
      hZero hHalf hOneRe hRay
  choose M hMNonneg hAway using
    exists_nicolasRightmostRayCompactAwayIntegral_bound
      hZero hHalf hOneRe hRay hrPos hrHalf
  refine Exists.intro d (Exists.intro r (Exists.intro M
    (And.intro hd (And.intro hrPos (And.intro hrHalf
      (And.intro hMNonneg ?_))))))
  intro eps hEps hEpsLe
  have hEpsR : eps < r := by linarith [hrPos]
  have hLowerNonneg : 0 <= r - eps := by linarith [hEpsLe, hrPos]
  have hLowerOne : r - eps <= 1 := by linarith [hrHalf]
  let f : Real -> Complex :=
    nicolasJMellinShiftIntegrandFilled
      (nicolasRightmostRayPoint rho eps)
  have hIntegrableOn : IntegrableOn f (Ioc (0 : Real) 1) := by
    have hEventually :=
      eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_compact_rightmostRay
        hZero hHalf hOneRe hRay hEps
    have hAt := hEventually.self_of_nhds
    simpa [f, nicolasRightmostRayPoint] using hAt
  have hFullIntegrable : IntervalIntegrable f volume 0 1 := by
    rw [intervalIntegrable_iff]
    simpa [uIoc, min_eq_left zero_le_one,
      max_eq_right zero_le_one] using hIntegrableOn
  have hLeftIntegrable : IntervalIntegrable f volume 0 (r - eps) := by
    apply hFullIntegrable.mono_set
    intro u hu
    have huSmall : Membership.mem (Icc (0 : Real) (r - eps)) u := by
      simpa [uIcc, min_eq_left hLowerNonneg,
        max_eq_right hLowerNonneg] using hu
    have huFull : Membership.mem (Icc (0 : Real) 1) u :=
      And.intro huSmall.1 (huSmall.2.trans hLowerOne)
    simpa [uIcc, min_eq_left zero_le_one,
      max_eq_right zero_le_one] using huFull
  have hRightIntegrable : IntervalIntegrable f volume (r - eps) 1 := by
    apply hFullIntegrable.mono_set
    intro u hu
    have huSmall : Membership.mem (Icc (r - eps) (1 : Real)) u := by
      simpa [uIcc, min_eq_left hLowerOne,
        max_eq_right hLowerOne] using hu
    have huFull : Membership.mem (Icc (0 : Real) 1) u :=
      And.intro (hLowerNonneg.trans huSmall.1) huSmall.2
    simpa [uIcc, min_eq_left zero_le_one,
      max_eq_right zero_le_one] using huFull
  let L : Complex := intervalIntegral f 0 (r - eps) volume
  let R : Complex := intervalIntegral f (r - eps) 1 volume
  let T : Complex := intervalIntegral f 0 1 volume
  have hDecomp : L + R = T := by
    dsimp [L, R, T]
    exact intervalIntegral.integral_add_adjacent_intervals
      hLeftIntegrable hRightIntegrable
  have hTriangle : norm L <= norm T + norm R := by
    calc
      norm L = norm ((L + R) - R) := by ring_nf
      _ <= norm (L + R) + norm R := norm_sub_le _ _
      _ = norm T + norm R := by rw [hDecomp]
  have hSing : (3 / 4 : Real) * norm d * Real.log (r / eps) <=
      norm L := by
    dsimp [L, f]
    exact hSingular eps hEps hEpsR
  have hAwayBound : norm R <= M := by
    dsimp [R, f]
    exact hAway eps hEps.le hEpsLe
  have hFinal : (3 / 4 : Real) * norm d * Real.log (r / eps) - M <=
      norm T := by
    linarith
  simpa [T, f] using hFinal

theorem nicolasRightmostRayCompactIntegral_norm_tendsto_atTop
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Tendsto (fun eps : Real =>
        norm (intervalIntegral
          (nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps))
          0 1 volume))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
  choose d r M hd hrPos hrHalf hMNonneg hLower using
    exists_nicolasRightmostRayCompactIntegral_log_lowerBound
      hZero hHalf hOneRe hRay
  have hInv : Tendsto (fun eps : Real => Inv.inv eps)
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
    simpa using (tendsto_inv_nhdsGT_zero :
      Tendsto (fun eps : Real => Inv.inv eps)
        (nhdsWithin 0 (Ioi (0 : Real))) atTop)
  have hRatio : Tendsto (fun eps : Real => r / eps)
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
    have hMul := Tendsto.const_mul_atTop hrPos hInv
    simpa [div_eq_mul_inv] using hMul
  have hLog : Tendsto (fun eps : Real => Real.log (r / eps))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop :=
    Real.tendsto_log_atTop.comp hRatio
  have hCoefficient : 0 < (3 / 4 : Real) * norm d :=
    mul_pos (by norm_num) (norm_pos_iff.mpr hd)
  have hScaled : Tendsto (fun eps : Real =>
      ((3 / 4 : Real) * norm d) * Real.log (r / eps))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop :=
    Tendsto.const_mul_atTop hCoefficient hLog
  have hLowerTendsto : Tendsto (fun eps : Real =>
      (3 / 4 : Real) * norm d * Real.log (r / eps) - M)
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
    simpa [mul_assoc, sub_eq_add_neg] using
      (tendsto_atTop_add_const_right
        (nhdsWithin 0 (Ioi (0 : Real))) (-M) hScaled)
  have hSmall : Filter.Eventually (fun eps : Real => eps <= r / 2)
      (nhdsWithin 0 (Ioi (0 : Real))) := by
    have hNhd : Membership.mem (nhds (0 : Real)) (Iio (r / 2)) :=
      Iio_mem_nhds (by positivity)
    have hNhdWithin : Filter.Eventually (fun eps : Real => eps < r / 2)
        (nhdsWithin 0 (Ioi (0 : Real))) :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hNhd
    filter_upwards [hNhdWithin] with eps hEps
    exact hEps.le
  have hEventualLower : Filter.Eventually (fun eps : Real =>
      (3 / 4 : Real) * norm d * Real.log (r / eps) - M <=
        norm (intervalIntegral
          (nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps))
          0 1 volume))
      (nhdsWithin 0 (Ioi (0 : Real))) := by
    filter_upwards [self_mem_nhdsWithin, hSmall] with eps hEps hEpsLe
    exact hLower eps (mem_Ioi.mp hEps) hEpsLe
  exact tendsto_atTop_mono'
    (nhdsWithin 0 (Ioi (0 : Real))) hEventualLower hLowerTendsto

theorem nicolasJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRayEndpoint
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledLarge
      (nicolasRightmostRayPoint rho 0) := by
  let center : Complex := nicolasRightmostRayPoint rho 0
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOneRe
  have hCenterIm : center.im = -rho.im := by
    dsimp [center, nicolasRightmostRayPoint]
    simp
  have hCenterNe : Not (center = 0) := by
    intro hEq
    have hZeroIm : center.im = 0 := by rw [hEq]; simp
    apply hIm
    linarith [hCenterIm, hZeroIm]
  have hCenterNorm : 0 < norm center := norm_pos_iff.mpr hCenterNe
  have hCenterRe : center.re = 1 - rho.re := by
    dsimp [center, nicolasRightmostRayPoint]
    simp
  have hReMargin : 0 < (3 / 4 : Real) - center.re := by
    rw [hCenterRe]
    linarith
  let d : Real := norm center / 2
  let R : Real := min (norm center / 2)
    (((3 / 4 : Real) - center.re) / 2)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hRPos : 0 < R := by
    dsimp [R]
    exact lt_min (by positivity) (by positivity)
  have hGeometry : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (z.re <= (3 / 4 : Real)) (d <= norm z) := by
    intro z hz
    have hzDist : dist z center < R := by
      simpa [Metric.mem_ball] using hz
    have hDistNorm : dist z center < norm center / 2 :=
      lt_of_lt_of_le hzDist (by
        dsimp [R]
        exact min_le_left _ _)
    have hDistRe : dist z center <
        ((3 / 4 : Real) - center.re) / 2 :=
      lt_of_lt_of_le hzDist (by
        dsimp [R]
        exact min_le_right _ _)
    have hReDiff : z.re - center.re <= dist z center := by
      calc
        z.re - center.re <= abs (z.re - center.re) := le_abs_self _
        _ = abs ((z - center).re) :=
          congrArg abs (Complex.sub_re z center).symm
        _ <= norm (z - center) := Complex.abs_re_le_norm _
        _ = dist z center := by rw [dist_eq_norm]
    have hTriangle : norm center <= dist center z + norm z := by
      have h := dist_triangle center z 0
      simpa [dist_zero_right] using h
    have hNorm : d <= norm z := by
      dsimp [d]
      rw [dist_comm center z] at hTriangle
      linarith
    exact And.intro (by linarith) hNorm
  apply nicolasJShiftedComplexContinuationFilledLarge_analyticAt_of_ball
    hRPos hd
  intro z hz
  exact hGeometry z (by simpa [center] using hz)

theorem nicolasJShiftedComplexContinuationFilledLarge_rightmostRay_tendsto
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    Tendsto (fun eps : Real =>
        nicolasJShiftedComplexContinuationFilledLarge
          (nicolasRightmostRayPoint rho eps))
      (nhdsWithin 0 (Ioi (0 : Real)))
      (nhds (nicolasJShiftedComplexContinuationFilledLarge
        (nicolasRightmostRayPoint rho 0))) := by
  have hOuter :=
    (nicolasJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRayEndpoint
      hZero hHalf hOneRe).continuousAt.tendsto
  have hInner : Tendsto (nicolasRightmostRayPoint rho)
      (nhdsWithin 0 (Ioi (0 : Real)))
      (nhds (nicolasRightmostRayPoint rho 0)) := by
    have hContinuous : ContinuousAt (nicolasRightmostRayPoint rho) 0 := by
      unfold nicolasRightmostRayPoint
      fun_prop
    exact hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  exact hOuter.comp hInner

theorem nicolasJShiftedComplexContinuationFilled_rightmostRay_norm_tendsto_atTop
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Tendsto (fun eps : Real =>
        norm (nicolasJShiftedComplexContinuationFilled
          (nicolasRightmostRayPoint rho eps)))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  let C : Real -> Complex := fun eps =>
    nicolasJShiftedComplexContinuationFilledCompact
      (nicolasRightmostRayPoint rho eps)
  let G : Real -> Complex := fun eps =>
    nicolasJShiftedComplexContinuationFilledLarge
      (nicolasRightmostRayPoint rho eps)
  let H : Real -> Complex := fun eps =>
    nicolasJShiftedComplexContinuationFilled
      (nicolasRightmostRayPoint rho eps)
  have hCompact : Tendsto (fun eps : Real => norm (C eps)) l atTop := by
    have hBase := nicolasRightmostRayCompactIntegral_norm_tendsto_atTop
      hZero hHalf hOneRe hRay
    simpa [l, C, nicolasJShiftedComplexContinuationFilledCompact,
      intervalIntegral.integral_of_le zero_le_one] using hBase
  let G0 : Complex := nicolasJShiftedComplexContinuationFilledLarge
    (nicolasRightmostRayPoint rho 0)
  have hLarge : Tendsto G l (nhds G0) := by
    simpa [l, G, G0] using
      nicolasJShiftedComplexContinuationFilledLarge_rightmostRay_tendsto
        hZero hHalf hOneRe
  have hLargeBound : Filter.Eventually (fun eps : Real =>
      norm (G eps) <= norm G0 + 1) l := by
    have hBall := hLarge.eventually
      (Metric.ball_mem_nhds G0 (by norm_num : (0 : Real) < 1))
    filter_upwards [hBall] with eps hEps
    have hDist : norm (G eps - G0) < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hEps
    calc
      norm (G eps) = norm ((G eps - G0) + G0) := by ring_nf
      _ <= norm (G eps - G0) + norm G0 := norm_add_le _ _
      _ <= norm G0 + 1 := by linarith
  have hEq : Filter.Eventually (fun eps : Real => H eps = C eps + G eps) l := by
    filter_upwards [self_mem_nhdsWithin] with eps hEps
    have hAt :=
      (eventually_nicolasJShiftedComplexContinuationFilled_eq_compact_add_large_rightmostRay
        hZero hHalf hOneRe hRay (mem_Ioi.mp hEps)).self_of_nhds
    simpa [H, C, G, nicolasRightmostRayPoint] using hAt
  have hLowerTendsto : Tendsto (fun eps : Real =>
      norm (C eps) - (norm G0 + 1)) l atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right l (-(norm G0 + 1)) hCompact)
  have hEventualLower : Filter.Eventually (fun eps : Real =>
      norm (C eps) - (norm G0 + 1) <= norm (H eps)) l := by
    filter_upwards [hLargeBound, hEq] with eps hGBound hAt
    have hTriangle : norm (C eps) <= norm (H eps) + norm (G eps) := by
      calc
        norm (C eps) = norm ((C eps + G eps) - G eps) := by ring_nf
        _ = norm (H eps - G eps) := by rw [hAt]
        _ <= norm (H eps) + norm (G eps) := norm_sub_le _ _
    linarith
  exact tendsto_atTop_mono' l hEventualLower hLowerTendsto

theorem nicolasLandauPositiveComplexContinuationFilled_rightmostRay_norm_tendsto_atTop
    {X b : Real} (hX : 3 <= X)
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Tendsto (fun eps : Real =>
        norm (nicolasLandauPositiveComplexContinuationFilled X b
          (nicolasRightmostRayPoint rho eps)))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  let J : Real -> Complex := fun eps =>
    nicolasJShiftedComplexContinuationFilled
      (nicolasRightmostRayPoint rho eps)
  let D : Real -> Complex := fun eps =>
    -nicolasJComplexMellinStartup X (nicolasRightmostRayPoint rho eps) +
      nicolasLandauRpowComplexContinuation X b
        (nicolasRightmostRayPoint rho eps)
  let P : Real -> Complex := fun eps =>
    nicolasLandauPositiveComplexContinuationFilled X b
      (nicolasRightmostRayPoint rho eps)
  have hJ : Tendsto (fun eps : Real => norm (J eps)) l atTop := by
    simpa [l, J] using
      nicolasJShiftedComplexContinuationFilled_rightmostRay_norm_tendsto_atTop
        hZero hHalf hOneRe hRay
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOneRe
  have hPointNeB : Not (nicolasRightmostRayPoint rho 0 = (b : Complex)) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    unfold nicolasRightmostRayPoint at hEqIm
    simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im] at hEqIm
    apply hIm
    linarith
  have hCorrectionAnalytic : AnalyticAt Complex (fun z : Complex =>
      -nicolasJComplexMellinStartup X z +
        nicolasLandauRpowComplexContinuation X b z)
      (nicolasRightmostRayPoint rho 0) := by
    exact (nicolasJComplexMellinStartup_analyticAt hX _).neg.add
      (nicolasLandauRpowComplexContinuation_analyticAt
        (lt_of_lt_of_le (by norm_num) hX) hPointNeB)
  let D0 : Complex :=
    -nicolasJComplexMellinStartup X (nicolasRightmostRayPoint rho 0) +
      nicolasLandauRpowComplexContinuation X b
        (nicolasRightmostRayPoint rho 0)
  have hInner : Tendsto (nicolasRightmostRayPoint rho) l
      (nhds (nicolasRightmostRayPoint rho 0)) := by
    have hContinuous : ContinuousAt (nicolasRightmostRayPoint rho) 0 := by
      unfold nicolasRightmostRayPoint
      fun_prop
    exact hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hD : Tendsto D l (nhds D0) := by
    have hComp := hCorrectionAnalytic.continuousAt.tendsto.comp hInner
    simpa [D, D0, Function.comp_def] using hComp
  have hDBound : Filter.Eventually (fun eps : Real =>
      norm (D eps) <= norm D0 + 1) l := by
    have hBall := hD.eventually
      (Metric.ball_mem_nhds D0 (by norm_num : (0 : Real) < 1))
    filter_upwards [hBall] with eps hEps
    have hDist : norm (D eps - D0) < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hEps
    calc
      norm (D eps) = norm ((D eps - D0) + D0) := by ring_nf
      _ <= norm (D eps - D0) + norm D0 := norm_add_le _ _
      _ <= norm D0 + 1 := by linarith
  have hEq : forall eps : Real, P eps = J eps + D eps := by
    intro eps
    unfold P J D nicolasLandauPositiveComplexContinuationFilled
    ring
  have hLowerTendsto : Tendsto (fun eps : Real =>
      norm (J eps) - (norm D0 + 1)) l atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right l (-(norm D0 + 1)) hJ)
  have hEventualLower : Filter.Eventually (fun eps : Real =>
      norm (J eps) - (norm D0 + 1) <= norm (P eps)) l := by
    filter_upwards [hDBound] with eps hBound
    have hTriangle : norm (J eps) <= norm (P eps) + norm (D eps) := by
      calc
        norm (J eps) = norm ((J eps + D eps) - D eps) := by ring_nf
        _ = norm (P eps - D eps) := by rw [hEq]
        _ <= norm (P eps) + norm (D eps) := norm_sub_le _ _
    linarith
  exact tendsto_atTop_mono' l hEventualLower hLowerTendsto

end

end Robin1984
