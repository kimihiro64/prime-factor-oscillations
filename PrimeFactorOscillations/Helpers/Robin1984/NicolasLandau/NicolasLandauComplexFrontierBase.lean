/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauComplexFrontier.lean
Original source lines 26-185. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauPositiveStrip

/-!
# Complex convergence and the rightmost zero at a fixed height

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

theorem nicolasLandauComplexMGF_analyticAt_of_positive
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= nicolasLandauPositiveTail b x)
    {z : Complex} (hz : z.re < b) :
    AnalyticAt Complex
      (complexMGF (fun x : Real => Real.log x)
        (nicolasLandauPositiveMeasure X b)) z := by
  apply analyticAt_complexMGF
  exact Iio_subset_interior_integrableExpSet_nicolasLandau_of_positive
    hX hb hbHalf hPos hz


theorem exists_nicolasLandauComplexMGF_analytic_halfPlane_of_not_omegaMinus
    {b : Real} (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hNot : Not (AtTopOmegaMinus nicolasJ
      (fun x : Real => x ^ (-b)))) :
    Exists fun X : Real => And (3 <= X)
      (And (forall x : Real, X < x ->
        0 <= nicolasLandauPositiveTail b x)
        (forall z : Complex, z.re < b ->
          AnalyticAt Complex
            (complexMGF (fun x : Real => Real.log x)
              (nicolasLandauPositiveMeasure X b)) z)) := by
  choose X hX hPos using exists_nicolasLandauPositiveTail_start hNot
  exact Exists.intro X (And.intro hX (And.intro hPos (fun z hz =>
    nicolasLandauComplexMGF_analyticAt_of_positive
      hX hb hbHalf hPos hz)))

theorem riemannZeta_zero_im_ne_zero_of_re_mem_Ioo
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hRePos : 0 < rho.re) (hReLt : rho.re < 1) :
    Not (rho.im = 0) := by
  intro hIm
  have hEq : rho = (rho.re : Complex) := by
    apply Complex.ext
    . simp
    . simpa using hIm
  rw [hEq] at hZero
  exact (riemannZeta_real_ne_zero_of_mem_Ioo_zero_one
    (And.intro hRePos hReLt)) hZero

theorem exists_rightmost_horizontal_riemannZeta_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1) :
    Exists fun rhoMax : Complex =>
      And (riemannZeta rhoMax = 0)
        (And ((1 / 2 : Real) < rhoMax.re)
          (And (rhoMax.re < 1)
            (And (rhoMax.im = rho.im)
              (forall v : Real, 0 < v ->
                Not (riemannZeta (rhoMax + (v : Complex)) = 0))))) := by
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOne
  let linePoint : Real -> Complex := fun r : Real =>
    (r : Complex) + (rho.im : Complex) * Complex.I
  let S : Set Real := Set.inter (Icc rho.re 1)
    {r : Real | nicolasZetaPoleFactor (linePoint r) = 0}
  have hLineContinuous : Continuous linePoint := by
    dsimp [linePoint]
    fun_prop
  have hFactorContinuous : Continuous
      (fun r : Real => nicolasZetaPoleFactor (linePoint r)) :=
    nicolasZetaPoleFactor_differentiable.continuous.comp hLineContinuous
  have hZeroClosed : IsClosed
      {r : Real | nicolasZetaPoleFactor (linePoint r) = 0} :=
    isClosed_eq hFactorContinuous continuous_const
  have hCompact : IsCompact S := by
    dsimp [S]
    exact isCompact_Icc.inter_right hZeroClosed
  have hRhoLine : linePoint rho.re = rho := by
    dsimp [linePoint]
    apply Complex.ext
    . simp
    . simp
  have hRhoNeOne : Not (rho = 1) := by
    intro hEq
    rw [hEq] at hOne
    norm_num at hOne
  have hFactorRho : nicolasZetaPoleFactor rho = 0 := by
    have hIdentity := riemannZeta_eq_nicolasZetaPoleFactor_div hRhoNeOne
    rw [hZero] at hIdentity
    have hDen : Not (rho - 1 = 0) := sub_ne_zero.mpr hRhoNeOne
    simpa [hDen] using hIdentity.symm
  have hNonempty : S.Nonempty := by
    refine Exists.intro rho.re ?_
    dsimp [S]
    refine And.intro (And.intro le_rfl hOne.le) ?_
    change nicolasZetaPoleFactor (linePoint rho.re) = 0
    rw [hRhoLine]
    exact hFactorRho
  choose rMax hrMax using hCompact.exists_isGreatest hNonempty
  let rhoMax : Complex := linePoint rMax
  have hrMem : Membership.mem S rMax := hrMax.1
  have hrBounds : Membership.mem (Icc rho.re 1) rMax := by
    exact hrMem.1
  have hrFactor : nicolasZetaPoleFactor rhoMax = 0 := by
    exact hrMem.2
  have hMaxIm : rhoMax.im = rho.im := by
    dsimp [rhoMax, linePoint]
    simp
  have hMaxRe : rhoMax.re = rMax := by
    dsimp [rhoMax, linePoint]
    simp
  have hMaxNeOne : Not (rhoMax = 1) := by
    intro hEq
    have hZeroIm : rhoMax.im = 0 := by rw [hEq]; simp
    exact hIm (hMaxIm.symm.trans hZeroIm)
  have hMaxZero : riemannZeta rhoMax = 0 := by
    rw [riemannZeta_eq_nicolasZetaPoleFactor_div hMaxNeOne, hrFactor,
      zero_div]
  have hMaxHalf : (1 / 2 : Real) < rhoMax.re := by
    rw [hMaxRe]
    exact hHalf.trans_le hrBounds.1
  have hMaxLtOne : rhoMax.re < 1 := by
    rw [hMaxRe]
    apply lt_of_le_of_ne hrBounds.2
    intro hrEq
    have hReOne : (1 : Real) <= rhoMax.re := by rw [hMaxRe, hrEq]
    exact (riemannZeta_ne_zero_of_one_le_re hReOne) hMaxZero
  refine Exists.intro rhoMax (And.intro hMaxZero
    (And.intro hMaxHalf (And.intro hMaxLtOne
      (And.intro hMaxIm ?_))))
  intro v hv
  by_cases hRight : 1 <= (rhoMax + (v : Complex)).re
  . exact riemannZeta_ne_zero_of_one_le_re hRight
  . intro hShiftZero
    have hShiftNeOne : Not (rhoMax + (v : Complex) = 1) := by
      intro hEq
      have hZeroIm : (rhoMax + (v : Complex)).im = 0 := by rw [hEq]; simp
      have hShiftIm : (rhoMax + (v : Complex)).im = rho.im := by
        simp [hMaxIm]
      exact hIm (hShiftIm.symm.trans hZeroIm)
    have hShiftFactor :
        nicolasZetaPoleFactor (rhoMax + (v : Complex)) = 0 := by
      have hIdentity :=
        riemannZeta_eq_nicolasZetaPoleFactor_div hShiftNeOne
      rw [hShiftZero] at hIdentity
      have hDen : Not (rhoMax + (v : Complex) - 1 = 0) :=
        sub_ne_zero.mpr hShiftNeOne
      simpa [hDen] using hIdentity.symm
    have hShiftLine : linePoint (rMax + v) = rhoMax + (v : Complex) := by
      dsimp [linePoint, rhoMax]
      push_cast
      ring
    have hShiftMem : S (rMax + v) := by
      dsimp [S]
      refine And.intro ?_ ?_
      . constructor
        . linarith [hrBounds.1]
        . rw [Complex.add_re, Complex.ofReal_re, hMaxRe] at hRight
          exact (lt_of_not_ge hRight).le
      . change nicolasZetaPoleFactor (linePoint (rMax + v)) = 0
        rw [hShiftLine]
        exact hShiftFactor
    have hMaximal : rMax + v <= rMax := hrMax.2 hShiftMem
    linarith

end

end Robin1984

