/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/Analytic/RiemannZetaRealNonzero.lean
Original source lines 27-471. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauFrontier
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauPositiveTail

/-!
# The Euler remainder and nonvanishing on the positive real axis

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory Set

noncomputable section

def nicolasEulerSaw (x : Real) : Real :=
  x + 1 - (Int.ceil x : Real)

theorem nicolasEulerSaw_pos (x : Real) :
    0 < nicolasEulerSaw x := by
  unfold nicolasEulerSaw
  have h := Int.ceil_lt_add_one x
  linarith

theorem nicolasEulerSaw_le_one (x : Real) :
    nicolasEulerSaw x <= 1 := by
  unfold nicolasEulerSaw
  have h := Int.le_ceil x
  linarith

theorem nicolasEulerSaw_eq_sub_nat_on_cell
    (n : Nat) {x : Real}
    (hx : Membership.mem (Ioc ((n : Real) + 1) ((n : Real) + 2)) x) :
    nicolasEulerSaw x = x - ((n : Real) + 1) := by
  have hCeil : Int.ceil x = (n : Int) + 2 := by
    apply Int.ceil_eq_iff.mpr
    constructor
    case left =>
      push_cast
      linarith [hx.1]
    case right =>
      push_cast
      linarith [hx.2]
  unfold nicolasEulerSaw
  rw [hCeil]
  push_cast
  ring

theorem iUnion_nicolasEulerCells :
    (iUnion fun n : Nat =>
      Ioc ((n : Real) + 1) ((n : Real) + 2)) = Ioi (1 : Real) := by
  apply Set.ext
  intro x
  constructor
  case mp =>
    intro hx
    rw [mem_iUnion] at hx
    choose n hn using hx
    have hnNonneg : (0 : Real) <= (n : Real) := Nat.cast_nonneg n
    have hOneLe : (1 : Real) <= (n : Real) + 1 := by linarith
    exact hOneLe.trans_lt hn.1
  case mpr =>
    intro hx
    change 1 < x at hx
    have hxNonneg : 0 <= x := le_trans (by norm_num) hx.le
    let m : Nat := Nat.ceil x
    have hUpper : x <= (m : Real) := by
      exact Nat.le_ceil x
    have hLower : (m : Real) - 1 < x := by
      have h := Nat.ceil_lt_add_one hxNonneg
      dsimp [m] at hUpper h
      linarith
    have hmTwo : 2 <= m := by
      by_contra hm
      have hmLe : m <= 1 := by omega
      have hmCast : (m : Real) <= 1 := by exact_mod_cast hmLe
      exact (not_lt_of_ge (hUpper.trans hmCast)) hx
    let n : Nat := m - 2
    rw [mem_iUnion]
    refine Exists.intro n ?_
    have hnOne : n + 1 = m - 1 := by
      dsimp [n]
      omega
    have hnTwo : n + 2 = m := by
      dsimp [n]
      omega
    have hmOne : 1 <= m := le_trans (by norm_num) hmTwo
    constructor
    case left =>
      calc
        (n : Real) + 1 = ((n + 1 : Nat) : Real) := by push_cast; rfl
        _ = ((m - 1 : Nat) : Real) := congrArg Nat.cast hnOne
        _ = (m : Real) - 1 := by rw [Nat.cast_sub hmOne]; norm_num
        _ < x := hLower
    case right =>
      calc
        x <= (m : Real) := hUpper
        _ = ((n + 2 : Nat) : Real) := congrArg Nat.cast hnTwo.symm
        _ = (n : Real) + 2 := by push_cast; rfl

theorem pairwise_disjoint_nicolasEulerCells :
    Pairwise (Function.onFun Disjoint fun n : Nat =>
      Ioc ((n : Real) + 1) ((n : Real) + 2)) := by
  intro i j hij
  obtain hijLt | hjiLt := lt_or_gt_of_ne hij
  case inl =>
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hCast : (i : Real) + 2 <= (j : Real) + 1 := by
      have hNat : i + 2 <= j + 1 := by omega
      exact_mod_cast hNat
    linarith [hxi.2, hxj.1]
  case inr =>
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hCast : (j : Real) + 2 <= (i : Real) + 1 := by
      have hNat : j + 2 <= i + 1 := by omega
      exact_mod_cast hNat
    linarith [hxj.2, hxi.1]

def nicolasEulerRemainderIntegrand (s x : Real) : Real :=
  nicolasEulerSaw x / x ^ (s + 1)

def nicolasEulerRemainder (s : Real) : Real :=
  integral (volume.restrict (Ioi 1))
    (fun x : Real => nicolasEulerRemainderIntegrand s x)

theorem nicolasEulerRemainderIntegrable
    {s : Real} (hs : 0 < s) :
    IntegrableOn (nicolasEulerRemainderIntegrand s) (Ioi 1) := by
  have hMajorant : IntegrableOn (fun x : Real => x ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  apply hMajorant.mono'
  case hf =>
    apply Measurable.aestronglyMeasurable
    unfold nicolasEulerRemainderIntegrand nicolasEulerSaw
    measurability
  case h =>
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxPos : 0 < x := lt_trans (by norm_num) hx
    have hDenomNonneg : 0 <= x ^ (s + 1) :=
      Real.rpow_nonneg hxPos.le _
    have hValueNonneg : 0 <= nicolasEulerRemainderIntegrand s x := by
      unfold nicolasEulerRemainderIntegrand
      exact div_nonneg (nicolasEulerSaw_pos x).le hDenomNonneg
    calc
      norm (nicolasEulerRemainderIntegrand s x) =
          nicolasEulerRemainderIntegrand s x := abs_of_nonneg hValueNonneg
      _ <= 1 / x ^ (s + 1) := by
        unfold nicolasEulerRemainderIntegrand
        exact div_le_div_of_nonneg_right (nicolasEulerSaw_le_one x) hDenomNonneg
      _ = x ^ (-(s + 1)) := by
        rw [Real.rpow_neg hxPos.le]
        simp only [one_div]

theorem integral_nicolasEulerCell_eq_term
    (n : Nat) (s : Real) :
    integral (volume.restrict (Ioc ((n : Real) + 1) ((n : Real) + 2)))
        (fun x : Real => nicolasEulerRemainderIntegrand s x) =
      ZetaAsymptotics.term (n + 1) s := by
  unfold ZetaAsymptotics.term
  rw [intervalIntegral.integral_of_le (by linarith :
    ((n + 1 : Nat) : Real) <= ((n + 1 : Nat) : Real) + 1)]
  push_cast
  ring_nf
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hxCell : Membership.mem
      (Ioc ((n : Real) + 1) ((n : Real) + 2)) x := by
    simpa [add_comm] using hx
  unfold nicolasEulerRemainderIntegrand
  rw [nicolasEulerSaw_eq_sub_nat_on_cell n hxCell]
  push_cast
  ring

theorem nicolasEulerRemainder_eq_termTSum
    {s : Real} (hs : 0 < s) :
    nicolasEulerRemainder s = ZetaAsymptotics.termTSum s := by
  unfold nicolasEulerRemainder ZetaAsymptotics.termTSum
  rw [iUnion_nicolasEulerCells.symm]
  rw [MeasureTheory.integral_iUnion
    (fun _ => measurableSet_Ioc)
    pairwise_disjoint_nicolasEulerCells
    (by simpa [iUnion_nicolasEulerCells] using
      nicolasEulerRemainderIntegrable hs)]
  apply tsum_congr
  intro n
  exact integral_nicolasEulerCell_eq_term n s

def nicolasEulerDensity (x : Real) : NNReal :=
  Real.toNNReal (nicolasEulerSaw x / x)

theorem measurable_nicolasEulerDensity :
    Measurable nicolasEulerDensity := by
  unfold nicolasEulerDensity nicolasEulerSaw
  measurability

def nicolasEulerMeasure : Measure Real :=
  (volume.restrict (Ioi 1)).withDensity
    (fun x : Real => nicolasEulerDensity x)

theorem nicolasEulerDensity_coe
    {x : Real} (hx : 1 < x) :
    (nicolasEulerDensity x : Real) = nicolasEulerSaw x / x := by
  unfold nicolasEulerDensity
  rw [Real.coe_toNNReal]
  exact div_nonneg (nicolasEulerSaw_pos x).le (le_trans (by norm_num) hx.le)

theorem nicolasEulerDensity_mul_exp_eq_integrand
    {t x : Real} (hx : 1 < x) :
    (nicolasEulerDensity x : Real) * Real.exp (t * Real.log x) =
      nicolasEulerRemainderIntegrand (-t) x := by
  have hxPos : 0 < x := lt_trans (by norm_num) hx
  rw [nicolasEulerDensity_coe hx]
  unfold nicolasEulerRemainderIntegrand
  rw [Real.rpow_def_of_pos hxPos]
  have hExp : Real.exp (t * Real.log x) *
      Real.exp (Real.log x * (-t + 1)) = x := by
    calc
      Real.exp (t * Real.log x) * Real.exp (Real.log x * (-t + 1)) =
          Real.exp (t * Real.log x + Real.log x * (-t + 1)) :=
        (Real.exp_add _ _).symm
      _ = Real.exp (Real.log x) := by congr 1; ring
      _ = x := Real.exp_log hxPos
  field_simp [Real.exp_ne_zero, hxPos.ne']
  calc
    nicolasEulerSaw x * Real.exp (t * Real.log x) *
        Real.exp (Real.log x * (-t + 1)) =
      nicolasEulerSaw x *
        (Real.exp (t * Real.log x) *
          Real.exp (Real.log x * (-t + 1))) := by ring
    _ = nicolasEulerSaw x * x := by rw [hExp]

theorem mgf_nicolasEulerMeasure_neg_eq_remainder
    {s : Real} (hs : 0 < s) :
    ProbabilityTheory.mgf Real.log nicolasEulerMeasure (-s) =
      nicolasEulerRemainder s := by
  unfold ProbabilityTheory.mgf nicolasEulerMeasure nicolasEulerRemainder
  rw [integral_withDensity_eq_integral_smul measurable_nicolasEulerDensity]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  change (nicolasEulerDensity x : Real) * Real.exp (-s * Real.log x) =
    nicolasEulerRemainderIntegrand s x
  simpa using nicolasEulerDensity_mul_exp_eq_integrand (t := -s) hx

theorem integrable_exp_log_nicolasEulerMeasure_of_neg
    {t : Real} (ht : t < 0) :
    Integrable (fun x : Real => Real.exp (t * Real.log x))
      nicolasEulerMeasure := by
  unfold nicolasEulerMeasure
  rw [integrable_withDensity_iff_integrable_smul measurable_nicolasEulerDensity]
  apply (nicolasEulerRemainderIntegrable (neg_pos.mpr ht)).congr_fun
  case hst =>
    intro x hx
    change nicolasEulerRemainderIntegrand (-t) x =
      (nicolasEulerDensity x : Real) * Real.exp (t * Real.log x)
    exact (nicolasEulerDensity_mul_exp_eq_integrand (t := t) hx).symm
  case hs =>
    exact measurableSet_Ioi

theorem neg_mem_nicolasEulerIntegrableExpSet
    {t : Real} (ht : t < 0) :
    Membership.mem
      (ProbabilityTheory.integrableExpSet Real.log nicolasEulerMeasure) t :=
  integrable_exp_log_nicolasEulerMeasure_of_neg ht

theorem zetaAsymptoticsTermTSum_analyticAt_of_pos
    {s : Real} (hs : 0 < s) :
    AnalyticAt Real ZetaAsymptotics.termTSum s := by
  have hLeft := neg_mem_nicolasEulerIntegrableExpSet
    (t := -2 * s) (by linarith)
  have hRight := neg_mem_nicolasEulerIntegrableExpSet
    (t := -s / 2) (by linarith)
  have hInterior := mem_interior_integrableExpSet_of_two_sided
    hLeft hRight (by linarith : -2 * s < -s) (by linarith : -s < -s / 2)
  have hMgf : AnalyticAt Real
      (ProbabilityTheory.mgf Real.log nicolasEulerMeasure) (-s) :=
    ProbabilityTheory.analyticAt_mgf hInterior
  have hComp : AnalyticAt Real
      (fun u : Real =>
        ProbabilityTheory.mgf Real.log nicolasEulerMeasure (-u)) s := by
    simpa [Function.comp_def] using hMgf.comp (analyticAt_id.neg)
  have hEq : Filter.EventuallyEq (nhds s)
      (fun u : Real =>
        ProbabilityTheory.mgf Real.log nicolasEulerMeasure (-u))
      ZetaAsymptotics.termTSum := by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    rw [mgf_nicolasEulerMeasure_neg_eq_remainder hu]
    exact nicolasEulerRemainder_eq_termTSum hu
  exact (analyticAt_congr hEq).mp hComp


theorem zetaAsymptoticsTermTSum_nonneg
    {s : Real} (hs : 0 < s) :
    0 <= ZetaAsymptotics.termTSum s := by
  unfold ZetaAsymptotics.termTSum
  exact tsum_nonneg (fun n => ZetaAsymptotics.term_nonneg (n + 1) s)

set_option maxHeartbeats 300000 in
theorem nicolasZetaPoleFactor_eq_termTSum_of_one_lt
    {s : Real} (hs : 1 < s) :
    nicolasZetaPoleFactor (s : Complex) =
      (s * (1 - (s - 1) * ZetaAsymptotics.termTSum s) : Real) := by
  let Z : Real := tsum fun n : Nat =>
    1 / ((n : Real) + 1) ^ s
  let T : Real := ZetaAsymptotics.termTSum s
  change nicolasZetaPoleFactor (s : Complex) =
    ((s * (1 - (s - 1) * T) : Real) : Complex)
  have hRealSummable : Summable (fun n : Nat =>
      1 / ((n : Real) + 1) ^ s) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_rpow.mpr hs))
  have hCast : (Z : Complex) = tsum fun n : Nat =>
      1 / ((n : Complex) + 1) ^ (s : Complex) := by
    dsimp [Z]
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [Complex.ofReal_div, Complex.ofReal_one]
    rw [Complex.ofReal_cpow (by positivity : 0 <= (n : Real) + 1) s]
    push_cast
    rfl
  have hZeta : riemannZeta (s : Complex) = (Z : Complex) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
    exact hCast.symm
  have hLimit := ZetaAsymptotics.zeta_limit_aux1 hs
  change Z - 1 / (s - 1) =
    1 - s * T at hLimit
  have hsOne : Not ((s : Complex) = 1) := by
    exact Complex.ofReal_ne_one.mpr (ne_of_gt hs)
  have hPole := riemannZeta_eq_nicolasZetaPoleFactor_div hsOne
  rw [hZeta] at hPole
  have hsSub : Not (s - 1 = 0) := sub_ne_zero.mpr (ne_of_gt hs)
  have hPoleMul : nicolasZetaPoleFactor (s : Complex) =
      (Z : Complex) * ((s : Complex) - 1) := by
    exact (div_eq_iff (sub_ne_zero.mpr hsOne)).mp hPole.symm
  have hReal : Z * (s - 1) =
      s * (1 - (s - 1) * T) := by
    have hZ : Z = 1 / (s - 1) +
        (1 - s * T) := by
      linarith [hLimit]
    calc
      Z * (s - 1) =
          (1 / (s - 1) +
            (1 - s * T)) * (s - 1) := by
        rw [hZ]
      _ = 1 + (1 - s * T) * (s - 1) := by
        rw [add_mul]
        simp [hsSub]
      _ = s * (1 - (s - 1) * T) := by
        ring
  calc
    nicolasZetaPoleFactor (s : Complex) =
        (Z : Complex) * ((s : Complex) - 1) := hPoleMul
    _ = ((Z * (s - 1) : Real) : Complex) := by push_cast; rfl
    _ = ((s * (1 - (s - 1) * T) : Real) : Complex) :=
      congrArg Complex.ofReal hReal

theorem nicolasZetaPoleFactor_re_eq_termTSum_of_pos
    {s : Real} (hs : 0 < s) :
    (nicolasZetaPoleFactor (s : Complex)).re =
      s * (1 - (s - 1) * ZetaAsymptotics.termTSum s) := by
  let F : Real -> Real := fun u => (nicolasZetaPoleFactor (u : Complex)).re
  let G : Real -> Real := fun u =>
    u * (1 - (u - 1) * ZetaAsymptotics.termTSum u)
  have hF : AnalyticOnNhd Real F (Ioi 0) := by
    intro u hu
    exact nicolasZetaPoleFactor_differentiable.analyticAt (u : Complex) |>.re_ofReal
  have hG : AnalyticOnNhd Real G (Ioi 0) := by
    intro u hu
    have hTerm := zetaAsymptoticsTermTSum_analyticAt_of_pos hu
    have hSub : AnalyticAt Real (fun v : Real => v - 1) u :=
      analyticAt_id.sub analyticAt_const
    have hProduct : AnalyticAt Real
        (fun v : Real => (v - 1) * ZetaAsymptotics.termTSum v) u :=
      hSub.mul hTerm
    have hBracket : AnalyticAt Real
        (fun v : Real => 1 -
          (v - 1) * ZetaAsymptotics.termTSum v) u :=
      analyticAt_const.sub hProduct
    have hReal : AnalyticAt Real
        (fun v : Real => v *
          (1 - (v - 1) * ZetaAsymptotics.termTSum v)) u :=
      analyticAt_id.mul hBracket
    exact hReal
  have hEqNhd : Filter.EventuallyEq (nhds (2 : Real)) F G := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (1 : Real) < 2)] with u hu
    have hIdentity := nicolasZetaPoleFactor_eq_termTSum_of_one_lt hu
    simpa [F, G] using congrArg Complex.re hIdentity
  have hEqOn : EqOn F G (Ioi 0) :=
    hF.eqOn_of_preconnected_of_eventuallyEq
      hG (convex_Ioi (0 : Real)).isPreconnected (by norm_num) hEqNhd
  exact hEqOn hs

theorem nicolasZetaPoleFactor_ne_zero_of_mem_Ioo_zero_one
    {s : Real} (hs : Membership.mem (Ioo (0 : Real) 1) s) :
    Not (nicolasZetaPoleFactor (s : Complex) = 0) := by
  have hIdentity := nicolasZetaPoleFactor_re_eq_termTSum_of_pos hs.1
  have hTermNonneg := zetaAsymptoticsTermTSum_nonneg hs.1
  have hCoefficientNonpos :
      (s - 1) * ZetaAsymptotics.termTSum s <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs.2.le) hTermNonneg
  have hRealPos :
      0 < s * (1 - (s - 1) * ZetaAsymptotics.termTSum s) := by
    apply mul_pos hs.1
    linarith
  intro hZero
  have hReZero : (nicolasZetaPoleFactor (s : Complex)).re = 0 := by
    rw [hZero]
    exact Complex.zero_re
  rw [hIdentity] at hReZero
  linarith

theorem riemannZeta_real_ne_zero_of_mem_Ioo_zero_one
    {s : Real} (hs : Membership.mem (Ioo (0 : Real) 1) s) :
    Not (riemannZeta (s : Complex) = 0) := by
  have hsOne : Not ((s : Complex) = 1) := by
    exact Complex.ofReal_ne_one.mpr (ne_of_lt hs.2)
  rw [riemannZeta_eq_nicolasZetaPoleFactor_div hsOne]
  exact div_ne_zero
    (nicolasZetaPoleFactor_ne_zero_of_mem_Ioo_zero_one hs)
    (sub_ne_zero.mpr hsOne)

theorem nicolasZetaPoleFactor_ne_zero_of_pos_real
    {s : Real} (hs : 0 < s) :
    Not (nicolasZetaPoleFactor (s : Complex) = 0) := by
  by_cases hsLt : s < 1
  case pos =>
    exact nicolasZetaPoleFactor_ne_zero_of_mem_Ioo_zero_one
      (And.intro hs hsLt)
  case neg =>
    by_cases hsEq : s = 1
    case pos =>
      subst s
      simp
    case neg =>
      have hsGt : 1 < s := lt_of_le_of_ne (not_lt.mp hsLt) (Ne.symm hsEq)
      have hsOne : Not ((s : Complex) = 1) :=
        Complex.ofReal_ne_one.mpr (ne_of_gt hsGt)
      have hZeta : Not (riemannZeta (s : Complex) = 0) :=
        riemannZeta_ne_zero_of_one_lt_re (by simpa using hsGt)
      exact nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_pos_real
    {s : Real} (hs : 0 < s) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled (s : Complex) := by
  by_cases hsOne : s = 1
  case pos =>
    subst s
    exact nicolasPsiMellinTailContinuationFilled_analyticAt_one
  case neg =>
    have hsZero : Not ((s : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr hs.ne'
    have hFactor := nicolasZetaPoleFactor_ne_zero_of_pos_real hs
    unfold nicolasPsiMellinTailContinuationFilled
    exact (nicolasPsiMellinContinuationFilled_analyticAt hsZero hFactor).sub
      (nicolasPsiMellinStartup_three_analyticAt (s : Complex))

end

end Robin1984

