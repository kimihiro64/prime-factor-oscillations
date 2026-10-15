/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMajorCenteredKernel
import PrimeFactorOscillations.Helpers.LPFMajorPerronNumeric

/-!
# Numerical character Chebyshev prefixes after the complete contour shift

The centered contour coefficient is 54912, the optimized Perron error is 87,
and the principal pole contributes an error at most 3. Including the half-sum
endpoint gives coefficient 65536 at exponent fifteen sixteenths. This consumes
the audited seven-eighths nonvanishing theorem, includes all characters and
moduli, and makes no equidistribution claim about generated LPF states.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

theorem lpf_character_centered_contour_numeric
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 4 <= x) :
    norm (VIntegral' (lpfCenteredContourIntegrand chi (x : Real))
      (BombieriVinogradov.SiegelWalfisz.optimizedPerronLine x)
      (-(x : Real)) (x : Real)) <=
      54912 * (x : Real) ^ (15 / 16 : Real) *
        (1 + Real.log (N : Real) + Real.log ((x : Real) + 2)) ^ 2 := by
  let X : Real := x
  let c : Real := BombieriVinogradov.SiegelWalfisz.optimizedPerronLine x
  let B : Real := 1 + Real.log (N : Real) + Real.log (X + 2)
  let g : Complex -> Complex :=
    -(deriv (lpfCharacterPoleFill chi) / lpfCharacterPoleFill chi)
  have hX : 4 <= X := by
    change 4 <= (x : Real)
    exact_mod_cast hx
  have hX0 : 0 < X := by linarith
  have hx2 : 2 < x := by omega
  have hN : 1 <= (N : Real) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hLogN := Real.log_nonneg hN
  have hLogX : 0 <= Real.log (X + 2) := Real.log_nonneg (by linarith)
  have hB : 1 <= B := by dsimp [B]; linarith
  have hc : 1 < c :=
    BombieriVinogradov.SiegelWalfisz.optimizedPerronLine_gt_one hx2
  have hc2 : c <= 2 :=
    BombieriVinogradov.SiegelWalfisz.optimizedPerronLine_le_two hx2
  have hLog : Real.log (1 + X) <= B := by
    have hm := Real.log_le_log (by linarith : 0 < 1 + X)
      (show 1 + X <= X + 2 by linarith)
    dsimp [B]
    linarith
  have hPower : X ^ c <= 3 * X := by
    change (x : Real) ^ BombieriVinogradov.SiegelWalfisz.optimizedPerronLine x <=
      3 * (x : Real)
    rw [BombieriVinogradov.SiegelWalfisz.rpow_optimizedPerronLine_eq hx2]
    calc
      _ <= (x : Real) * 3 :=
        mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le (Nat.cast_nonneg x)
      _ = _ := by ring
  have ho : IsOpen {s : Complex | 7 / 8 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hAnalytic := (lpf_centered_contour_integrand_differentiableOn chi X hX0).analyticOnNhd ho
  have hDiff : forall s : Complex, 7 / 8 < s.re ->
      DifferentiableAt Complex (lpfMellinKernel g X) s := by
    intro s hs
    change DifferentiableAt Complex (lpfCenteredContourIntegrand chi X) s
    exact (hAnalytic s hs).differentiableAt
  have hGrowth : forall sigma t : Real, 15 / 16 <= sigma -> sigma <= 2 ->
      abs t <= X -> norm (g ((sigma : Complex) + (t : Complex) * Complex.I)) <=
        26624 * B := by
    intro sigma t hSigma hTwo ht
    let s : Complex := (sigma : Complex) + (t : Complex) * Complex.I
    have hDist : dist s (2 + Complex.I * (t : Complex)) <= 17 / 16 := by
      dsimp [s]
      rw [mul_comm (t : Complex) Complex.I]
      exact lpf_contour_point_distance sigma t hSigma hTwo
    have hRaw := lpf_character_poleFill_log_deriv_numeric chi t s hDist
    have hHeight := lpf_height_log_numeric (N : Real) X t hN (by linarith) ht
    change norm (-(deriv (lpfCharacterPoleFill chi) s / lpfCharacterPoleFill chi s)) <=
      26624 * B
    rw [norm_neg]
    calc
      _ <= 13312 * (1 + Real.log (N : Real) + Real.log (abs t + 8)) := hRaw
      _ <= 13312 * (2 * B) :=
        mul_le_mul_of_nonneg_left hHeight (by norm_num)
      _ = _ := by ring
  have h := lpf_mellin_contour_numeric g X c B hX hB hc hc2 hLog hPower hDiff hGrowth
  change norm (VIntegral' (lpfCenteredContourIntegrand chi X) c (-X) X) <=
    54912 * X ^ (15 / 16 : Real) * B ^ 2
  simpa only [VIntegral', VIntegral, smul_eq_mul, lpfCenteredContourIntegrand, g, mul_assoc] using h

theorem lpf_perron_kernel_intervalIntegrable
    {X a T : Real} (hX : 0 < X) (ha : 0 < a) :
    IntervalIntegrable (fun t : Real =>
      BombieriVinogradov.SiegelWalfisz.perronKernelIntegrand X
        ((a : Complex) + (t : Complex) * Complex.I))
      MeasureTheory.volume (-T) T := by
  have hc : Continuous (fun t : Real =>
      (a : Complex) + (t : Complex) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hXc : Not ((X : Complex) = 0) := by
    exact_mod_cast (ne_of_gt hX)
  have hn : forall t : Real,
      Not ((a : Complex) + (t : Complex) * Complex.I = 0) := by
    intro t h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, sub_self, add_zero, Complex.zero_re] at hr
    linarith
  exact ((hc.const_cpow (Or.inl hXc)).div hc hn).intervalIntegrable _ _

theorem lpf_principal_perron_pole_numeric
    {X c : Real} (hX : 4 <= X) (hc : 1 < c)
    (hPower : X ^ c <= 3 * X) :
    norm ((X : Complex) *
      BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel X (c - 1) X -
      BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel X c X -
      (X : Complex)) <= 3 := by
  have hX0 : 0 < X := by linarith
  have hX1 : 1 < X := by linarith
  have hLog : 1 <= Real.log X := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ <= Real.log X := Real.log_le_log (Real.exp_pos 1)
        (by linarith [Real.exp_one_lt_three])
  have hPi : 3 <= Real.pi := Real.pi_gt_three.le
  have hDenom : 3 * X <= Real.pi * X * abs (Real.log X) := by
    rw [abs_of_nonneg (by linarith : 0 <= Real.log X)]
    calc
      3 * X <= Real.pi * X := mul_le_mul_of_nonneg_right hPi hX0.le
      _ <= Real.pi * X * Real.log X := by
        nlinarith [mul_pos Real.pi_pos hX0]
  have hDenom0 : 0 < Real.pi * X * abs (Real.log X) := by
    nlinarith
  have hUnit : X ^ c / (Real.pi * X * abs (Real.log X)) <= 1 :=
    (div_le_one hDenom0).mpr (hPower.trans hDenom)
  have hK0 :=
    (BombieriVinogradov.SiegelWalfisz.norm_truncatedPerronKernel_sub_one_lt_log_bound
      hX1 (show 0 < c by linarith) hX0).le
  have hK1 :=
    (BombieriVinogradov.SiegelWalfisz.norm_truncatedPerronKernel_sub_one_lt_log_bound
      hX1 (show 0 < c - 1 by linarith) hX0).le
  have hProd : X * X ^ (c - 1) = X ^ c := by
    rw [Real.rpow_sub hX0, Real.rpow_one]
    field_simp
  have hWeighted :
      norm ((X : Complex) *
        (BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel X (c - 1) X - 1)) <= 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0]
    calc
      _ <= X * (X ^ (c - 1) / (Real.pi * X * abs (Real.log X))) :=
        mul_le_mul_of_nonneg_left hK1 hX0.le
      _ = X ^ c / (Real.pi * X * abs (Real.log X)) := by
        rw [<- mul_div_assoc, hProd]
      _ <= 1 := hUnit
  have hPlain :
      norm (BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel X c X - 1) <= 1 :=
    hK0.trans hUnit
  calc
    _ = norm (((X : Complex) *
        (BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel X (c - 1) X - 1) -
        (BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel X c X - 1)) - 1) := by
          congr 1
          ring
    _ <= norm ((X : Complex) *
        (BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel X (c - 1) X - 1)) +
        norm (BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel X c X - 1) + 1 := by
          have hFirst := norm_sub_le
            ((X : Complex) *
              (BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel X (c - 1) X - 1))
            (BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel X c X - 1)
          have hLast := norm_sub_le
            ((X : Complex) *
              (BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel X (c - 1) X - 1) -
              (BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel X c X - 1))
            (1 : Complex)
          simp only [norm_one] at hLast
          linarith only [hFirst, hLast]
    _ <= 3 := by linarith

theorem lpf_character_explicit_integral_split
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) :
    BombieriVinogradov.SiegelWalfisz.explicitFormulaVerticalIntegral chi x c T =
      VIntegral' (lpfCenteredContourIntegrand chi (x : Real)) c (-T) T +
        (@ite Complex (chi = 1) (Classical.propDecidable _)
          ((x : Complex) *
            BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel (x : Real) (c - 1) T -
            BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel (x : Real) c T) 0) := by
  classical
  have hxR : 0 < (x : Real) := by exact_mod_cast hx
  have hCurve : Continuous (fun t : Real =>
      (c : Complex) + (t : Complex) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have ho : IsOpen {s : Complex | 7 / 8 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hAnalytic :=
    (lpf_centered_contour_integrand_differentiableOn chi (x : Real) hxR).analyticOnNhd ho
  have hCore : IntervalIntegrable (fun t : Real =>
      lpfCenteredContourIntegrand chi (x : Real)
        ((c : Complex) + (t : Complex) * Complex.I))
      MeasureTheory.volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    intro t _
    have hs : 7 / 8 < ((c : Complex) + (t : Complex) * Complex.I).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        zero_mul, sub_self, add_zero]
      linarith
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun u : Real => (c : Complex) + (u : Complex) * Complex.I)
      (g := lpfCenteredContourIntegrand chi (x : Real))
      (hAnalytic _ hs).differentiableAt.continuousAt hCurve.continuousWithinAt
  have hK0 := lpf_perron_kernel_intervalIntegrable (T := T) hxR
    (show 0 < c by linarith)
  have hK1 := lpf_perron_kernel_intervalIntegrable (T := T) hxR
    (show 0 < c - 1 by linarith)
  have hPoint : forall t : Real,
      BombieriVinogradov.SiegelWalfisz.explicitFormulaIntegrand chi x
        ((c : Complex) + (t : Complex) * Complex.I) =
      lpfCenteredContourIntegrand chi (x : Real)
        ((c : Complex) + (t : Complex) * Complex.I) +
        (if chi = 1 then
          (x : Complex) * BombieriVinogradov.SiegelWalfisz.perronKernelIntegrand (x : Real)
            (((c - 1 : Real) : Complex) + (t : Complex) * Complex.I) -
          BombieriVinogradov.SiegelWalfisz.perronKernelIntegrand (x : Real)
            ((c : Complex) + (t : Complex) * Complex.I) else 0) := by
    intro t
    let z : Complex := (c : Complex) + (t : Complex) * Complex.I
    have hz : z.re = c := by simp [z]
    have hs : 7 / 8 < z.re := by rw [hz]; linarith
    have hz0 : Not (z = 0) := by intro h; have hr := congrArg Complex.re h; simp [hz] at hr; linarith
    have hz1 : Not (z = 1) := by intro h; have hr := congrArg Complex.re h; simp [hz] at hr; linarith
    have hD := lpf_character_poleFill_log_deriv_identity chi z hs
      (fun h => hz1 h.2)
    have hShift : z - 1 = (((c - 1 : Real) : Complex) + (t : Complex) * Complex.I) := by
      dsimp [z]
      push_cast
      ring
    change BombieriVinogradov.SiegelWalfisz.explicitFormulaIntegrand chi x z =
      lpfCenteredContourIntegrand chi (x : Real) z + _
    by_cases hchi : chi = 1
    next =>
      rw [if_pos hchi] at hD
      rw [if_pos hchi, <- hShift]
      have hp := lpf_principal_pole_kernel_identity (x : Real) hxR z hz0 hz1
      dsimp only [BombieriVinogradov.SiegelWalfisz.explicitFormulaIntegrand,
        logDeriv, lpfCenteredContourIntegrand, lpfMellinKernel,
        Pi.div_apply, Pi.neg_apply, Pi.mul_apply, id_eq,
        BombieriVinogradov.SiegelWalfisz.perronKernelIntegrand]
      simp only [Complex.ofReal_natCast] at hp
      simp only [Complex.ofReal_natCast]
      rw [hD, <- hp]
      field_simp [hz0, sub_ne_zero.mpr hz1]
      <;> ring
    next =>
      rw [if_neg hchi] at hD
      rw [if_neg hchi]
      dsimp only [BombieriVinogradov.SiegelWalfisz.explicitFormulaIntegrand,
        logDeriv, lpfCenteredContourIntegrand, lpfMellinKernel,
        Pi.div_apply, Pi.neg_apply, Pi.mul_apply, id_eq]
      rw [hD]
      simp only [sub_zero, Complex.ofReal_natCast]
      ring
  by_cases hchi : chi = 1
  next =>
    simp only [if_pos hchi] at hPoint
    have hInt : intervalIntegral (fun t : Real =>
        BombieriVinogradov.SiegelWalfisz.explicitFormulaIntegrand chi x
          ((c : Complex) + (t : Complex) * Complex.I)) (-T) T MeasureTheory.volume =
        intervalIntegral (fun t : Real => lpfCenteredContourIntegrand chi (x : Real)
          ((c : Complex) + (t : Complex) * Complex.I)) (-T) T MeasureTheory.volume +
        ((x : Complex) * intervalIntegral (fun t : Real =>
          BombieriVinogradov.SiegelWalfisz.perronKernelIntegrand (x : Real)
            (((c - 1 : Real) : Complex) + (t : Complex) * Complex.I)) (-T) T MeasureTheory.volume -
          intervalIntegral (fun t : Real =>
          BombieriVinogradov.SiegelWalfisz.perronKernelIntegrand (x : Real)
            ((c : Complex) + (t : Complex) * Complex.I)) (-T) T MeasureTheory.volume) := by
      simp_rw [hPoint]
      rw [intervalIntegral.integral_add hCore ((hK1.const_mul (x : Complex)).sub hK0),
        intervalIntegral.integral_sub (hK1.const_mul (x : Complex)) hK0,
        intervalIntegral.integral_const_mul]
    simp only [if_pos hchi]
    unfold BombieriVinogradov.SiegelWalfisz.explicitFormulaVerticalIntegral
      BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel VIntegral' VIntegral
    simp only [smul_eq_mul]
    rw [hInt]
    ring
  next =>
    simp only [if_neg hchi, add_zero] at hPoint
    simp only [if_neg hchi, add_zero]
    unfold BombieriVinogradov.SiegelWalfisz.explicitFormulaVerticalIntegral VIntegral' VIntegral
    simp_rw [hPoint]

theorem lpf_character_chebyshev_numeric
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 4 <= x) :
    norm (BombieriVinogradov.SiegelWalfisz.characterChebyshevSum x chi -
      (@ite Complex (chi = 1) (Classical.propDecidable _) (x : Complex) 0)) <=
      65536 * (x : Real) ^ (15 / 16 : Real) *
        (1 + Real.log (N : Real) + Real.log ((x : Real) + 2)) ^ 2 := by
  classical
  let X : Real := x
  let c := BombieriVinogradov.SiegelWalfisz.optimizedPerronLine x
  let B := 1 + Real.log (N : Real) + Real.log (X + 2)
  let R := X ^ (15 / 16 : Real)
  let I := BombieriVinogradov.SiegelWalfisz.explicitFormulaVerticalIntegral chi x c X
  let H := BombieriVinogradov.SiegelWalfisz.characterChebyshevHalfSum x chi
  let F := BombieriVinogradov.SiegelWalfisz.characterChebyshevSum x chi
  let A := VIntegral' (lpfCenteredContourIntegrand chi X) c (-X) X
  let D : Complex := if chi = 1 then (x : Complex) else 0
  let P : Complex := if chi = 1 then
    (x : Complex) * BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel X (c - 1) X -
      BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel X c X else 0
  have hx2 : 2 < x := by omega
  have hx0 : 0 < x := by omega
  have hX : 4 <= X := by change 4 <= (x : Real); exact_mod_cast hx
  have hX0 : 0 < X := by linarith
  have hN : 1 <= (N : Real) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hNLog := Real.log_nonneg hN
  have hXLog := Real.log_nonneg (show 1 <= X + 2 by linarith)
  have hB : 1 <= B := by dsimp [B]; linarith
  have hR : 1 <= R := Real.one_le_rpow (by linarith) (by norm_num)
  have hc : 1 < c := BombieriVinogradov.SiegelWalfisz.optimizedPerronLine_gt_one hx2
  have hPower : X ^ c <= 3 * X := by
    change (x : Real) ^ BombieriVinogradov.SiegelWalfisz.optimizedPerronLine x <= 3 * (x : Real)
    rw [BombieriVinogradov.SiegelWalfisz.rpow_optimizedPerronLine_eq hx2]
    nlinarith [Real.exp_one_lt_three]
  have hP : norm (P - D) <= 3 := by
    dsimp [P, D]
    split_ifs with hchi
    next =>
      simpa only [X, Complex.ofReal_natCast] using lpf_principal_perron_pole_numeric hX hc hPower
    next => norm_num
  have hA : norm A <= 54912 * R * B ^ 2 :=
    lpf_character_centered_contour_numeric chi hx
  have hSplit : I = A + P := lpf_character_explicit_integral_split chi hx0 hc
  have hE := lpf_Perron_approx_numeric chi hx2 X hX0
  have hLog2 : Real.log (2 * X) <= B := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have hTwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    have hMon := Real.log_le_log hX0 (show X <= X + 2 by linarith)
    dsimp [B]
    linarith
  have hLog2Pos : 0 <= Real.log (2 * X) := Real.log_nonneg (by linarith)
  have hE' : norm (I - H) <= 87 * B ^ 2 := by
    have hCancel : (x : Real) * Real.log (2 * (x : Real)) ^ 2 / X =
        Real.log (2 * X) ^ 2 := by change X * Real.log (2 * X) ^ 2 / X = _; field_simp
    rw [hCancel] at hE
    exact hE.trans (by nlinarith)
  have hEnd : norm (F - H) <= B ^ 2 := by
    have hHalf := BombieriVinogradov.SiegelWalfisz.characterChebyshevHalfSum_eq_characterChebyshevSum_sub chi hx0
    have hEq : F - H = (1 / 2 : Complex) *
        BombieriVinogradov.SiegelWalfisz.twistedMangoldtSequence chi x := by
      dsimp [F, H]
      rw [hHalf]
      ring
    rw [hEq, norm_mul, show norm (1 / 2 : Complex) = (1 / 2 : Real) by norm_num]
    have hV := (BombieriVinogradov.SiegelWalfisz.norm_twistedMangoldtSequence_le_vonMangoldt chi x).trans
      (ArithmeticFunction.vonMangoldt_le_log (n := x))
    have hLog : Real.log (x : Real) <= B := by
      have h := Real.log_le_log hX0 (show X <= X + 2 by linarith)
      dsimp [B]
      change Real.log X <= _
      linarith
    nlinarith [sq_nonneg (B - 1)]
  have hRaw : norm (F - D) <= norm A + (norm (I - H) + norm (F - H)) + norm (P - D) := by
    have h1 := norm_add_le A (P - D)
    have h2 := norm_sub_le (A + (P - D)) (I - H)
    have h3 := norm_add_le ((A + (P - D)) - (I - H)) (F - H)
    have hEq : F - D = ((A + (P - D)) - (I - H)) + (F - H) := by rw [hSplit]; ring
    rw [hEq]
    linarith only [h1, h2, h3]
  have hBudget := lpf_chebyshev_numeric_budget B R (norm A)
    (norm (I - H) + norm (F - H)) (norm (P - D))
    hB hR hA (by linarith) hP
  exact hRaw.trans hBudget

end PrimeFactorOscillations.QRH

