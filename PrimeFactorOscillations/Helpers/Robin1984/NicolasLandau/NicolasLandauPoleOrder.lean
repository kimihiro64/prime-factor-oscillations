/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandau.lean
Original source lines 1137-1259. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauMellinSwap

/-!
# The genuine pole order of the zeta Mellin continuation

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Asymptotics Filter MeasureTheory Set

noncomputable section

/-- Every critical-strip zero of zeta gives a genuine simple pole of its
logarithmic derivative, without assuming that the zero itself is simple. -/
theorem nicolasRiemannZetaLogDeriv_order_eq_neg_one
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hOne : Not (rho = 1)) :
    meromorphicOrderAt (logDeriv riemannZeta) rho = -1 := by
  have hAnalyticRho : AnalyticAt Complex riemannZeta rho :=
    analyticOn_riemannZeta rho (by simpa using hOne)
  have hMeromorphicRho : MeromorphicAt riemannZeta rho :=
    hAnalyticRho.meromorphicAt
  have hTendstoZero : Tendsto riemannZeta
      (nhdsWithin rho (Set.compl {rho})) (nhds 0) := by
    have hCont : Tendsto riemannZeta
        (nhdsWithin rho (Set.compl {rho})) (nhds (riemannZeta rho)) :=
      hAnalyticRho.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [hZero] using hCont
  have hOrderPos : 0 < meromorphicOrderAt riemannZeta rho :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hMeromorphicRho).1 hTendstoZero
  have hAnalyticTwo : AnalyticAt Complex riemannZeta 2 :=
    analyticOn_riemannZeta 2 (by norm_num)
  have hMeromorphicTwo : MeromorphicAt riemannZeta 2 :=
    hAnalyticTwo.meromorphicAt
  have hZetaTwo : Not (riemannZeta 2 = 0) :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hTendstoTwo : Tendsto riemannZeta
      (nhdsWithin (2 : Complex) (Set.compl {(2 : Complex)}))
      (nhds (riemannZeta 2)) :=
    hAnalyticTwo.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hOrderTwo : meromorphicOrderAt riemannZeta 2 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hMeromorphicTwo).1
      (Exists.intro (riemannZeta 2)
        (And.intro hZetaTwo hTendstoTwo))
  have hMeromorphicOn : MeromorphicOn riemannZeta (Set.compl {1}) :=
    analyticOn_riemannZeta.meromorphicOn
  apply meromorphicOrderAt_logDeriv_eq_neg_one hMeromorphicRho
    (ne_of_gt hOrderPos)
  apply hMeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (x := (2 : Complex))
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  . exact Set.mem_compl_singleton_iff.mpr (by norm_num)
  . exact Set.mem_compl_singleton_iff.mpr hOne
  . rw [hOrderTwo]
    simp

theorem nicolasPsiMellinContinuation_order_eq_neg_one
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hRhoZero : Not (rho = 0)) (hOne : Not (rho = 1)) :
    meromorphicOrderAt nicolasPsiMellinContinuation rho = -1 := by
  let logF : Complex -> Complex := fun w => logDeriv riemannZeta w
  let negLogF : Complex -> Complex := fun w => -logF w
  let idF : Complex -> Complex := fun w => w
  let first : Complex -> Complex := fun w => negLogF w / idF w
  let regular : Complex -> Complex := fun w => -(Inv.inv (w - 1))
  have hZetaMeromorphic : MeromorphicAt riemannZeta rho :=
    (analyticOn_riemannZeta rho
      (Set.mem_compl_singleton_iff.mpr hOne)).meromorphicAt
  have hLogMeromorphic : MeromorphicAt logF rho := by
    dsimp [logF]
    exact hZetaMeromorphic.logDeriv
  have hNegLogMeromorphic : MeromorphicAt negLogF rho := by
    dsimp [negLogF]
    exact hLogMeromorphic.neg
  have hIdMeromorphic : MeromorphicAt idF rho := by
    dsimp [idF]
    fun_prop
  have hFirstMeromorphic : MeromorphicAt first rho := by
    dsimp [first]
    exact hNegLogMeromorphic.div hIdMeromorphic
  have hDen : Not (rho - 1 = 0) := sub_ne_zero.mpr hOne
  have hRegularAnalytic : AnalyticAt Complex regular rho := by
    dsimp [regular]
    have hOneAnalytic : AnalyticAt Complex
        (fun _ : Complex => (1 : Complex)) rho := analyticAt_const
    exact ((analyticAt_id.sub hOneAnalytic).inv hDen).neg
  have hRegularMeromorphic : MeromorphicAt regular rho :=
    hRegularAnalytic.meromorphicAt
  have hLogOrder : meromorphicOrderAt logF rho = -1 := by
    dsimp [logF]
    exact nicolasRiemannZetaLogDeriv_order_eq_neg_one hZero hOne
  have hNegLogOrder : meromorphicOrderAt negLogF rho = -1 := by
    dsimp [negLogF]
    rw [<- meromorphicOrderAt_fun_neg]
    exact hLogOrder
  have hIdTendsto : Tendsto idF
      (nhdsWithin rho (Set.compl {rho})) (nhds rho) := by
    dsimp [idF]
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  have hIdOrder : meromorphicOrderAt idF rho = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hIdMeromorphic).1
      (Exists.intro rho (And.intro hRhoZero hIdTendsto))
  have hFirstOrder : meromorphicOrderAt first rho = -1 := by
    change meromorphicOrderAt (negLogF / idF) rho = -1
    rw [meromorphicOrderAt_div hNegLogMeromorphic hIdMeromorphic,
      hNegLogOrder, hIdOrder]
    norm_num
  have hRegularNonneg : 0 <= meromorphicOrderAt regular rho :=
    hRegularAnalytic.meromorphicOrderAt_nonneg
  have hOrdersNe : Not (meromorphicOrderAt first rho =
      meromorphicOrderAt regular rho) := by
    intro hEq
    rw [hFirstOrder] at hEq
    rw [<- hEq] at hRegularNonneg
    have hNegOne : ((-1 : Int) : WithTop Int) <
        ((0 : Int) : WithTop Int) := WithTop.coe_lt_coe.mpr (by norm_num)
    exact (not_lt_of_ge hRegularNonneg) hNegOne
  have hSumOrder : meromorphicOrderAt (first + regular) rho = -1 := by
    rw [meromorphicOrderAt_add_of_ne hFirstMeromorphic
      hRegularMeromorphic hOrdersNe, hFirstOrder]
    rw [min_eq_left]
    have hNegOne : ((-1 : Int) : WithTop Int) <
        ((0 : Int) : WithTop Int) := WithTop.coe_lt_coe.mpr (by norm_num)
    exact le_of_lt (lt_of_lt_of_le hNegOne hRegularNonneg)
  have hOrderCongr :
      meromorphicOrderAt nicolasPsiMellinContinuation rho =
        meromorphicOrderAt (first + regular) rho := by
    apply meromorphicOrderAt_congr
    exact Filter.Eventually.of_forall fun w => by
      unfold nicolasPsiMellinContinuation
      dsimp [first, regular, negLogF, logF, idF]
      rw [logDeriv_apply]
      ring
  exact hOrderCongr.trans hSumOrder

end

end Robin1984

