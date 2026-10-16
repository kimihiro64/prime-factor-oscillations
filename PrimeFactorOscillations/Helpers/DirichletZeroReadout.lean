/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import PrimeFactorOscillations.Helpers.DetectorMellin
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauPoleOrder

/-!
# Dirichlet Zero Readout

Unconditional Dirichlet zero detection by logarithmic derivatives plus analytic reconstruction errors.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.DirichletZeroReadout

open Filter

theorem analyticOnNhd_LFunction_off_one {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) :
    AnalyticOnNhd Complex (DirichletCharacter.LFunction chi) (Set.compl {1}) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro s hs
  exact (DirichletCharacter.differentiableAt_LFunction chi s
    (Or.inl (Set.mem_compl_singleton_iff.mp hs))).differentiableWithinAt

theorem LFunction_logDeriv_order {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex)
    (hZero : DirichletCharacter.LFunction chi rho = 0)
    (hOne : Not (rho = 1)) :
    meromorphicOrderAt (logDeriv (DirichletCharacter.LFunction chi)) rho = -1 := by
  let L := DirichletCharacter.LFunction chi
  have ha := analyticOnNhd_LFunction_off_one chi
  have har : AnalyticAt Complex L rho := ha rho (Set.mem_compl_singleton_iff.mpr hOne)
  have hmr : MeromorphicAt L rho := har.meromorphicAt
  have ht0 : Tendsto L (nhdsWithin rho (Set.compl {rho})) (nhds 0) := by
    simpa only [L, hZero] using har.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have horder : 0 < meromorphicOrderAt L rho :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hmr).mp ht0
  have ha2 : AnalyticAt Complex L 2 :=
    ha 2 (Set.mem_compl_singleton_iff.mpr (by norm_num))
  have hn2 : Not (L 2 = 0) :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inr (by norm_num)) (by norm_num)
  have ht2 : Tendsto L (nhdsWithin (2 : Complex) (Set.compl {2})) (nhds (L 2)) :=
    ha2.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ho2 : meromorphicOrderAt L 2 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero ha2.meromorphicAt).mp
      (Exists.intro (L 2) (And.intro hn2 ht2))
  apply meromorphicOrderAt_logDeriv_eq_neg_one hmr (ne_of_gt horder)
  have hMon : MeromorphicOn L (Set.compl {1}) := fun z hz => (ha z hz).meromorphicAt
  apply hMon.meromorphicOrderAt_ne_top_of_isPreconnected
    (x := (2 : Complex))
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  . exact Set.mem_compl_singleton_iff.mpr (by norm_num)
  . exact Set.mem_compl_singleton_iff.mpr hOne
  . rw [ho2]
    simp

def readout {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (G : Complex -> Complex) (s : Complex) : Complex :=
  -logDeriv (DirichletCharacter.LFunction chi) s + G s

/-- An analytic reconstruction error cannot conceal any Dirichlet zero. -/
theorem readout_order_iff_zero {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex)
    (hOne : Not (rho = 1)) (G : Complex -> Complex)
    (hG : AnalyticAt Complex G rho) :
    meromorphicOrderAt (readout chi G) rho = -1 <->
      DirichletCharacter.LFunction chi rho = 0 := by
  have ha := (analyticOnNhd_LFunction_off_one chi) rho
    (Set.mem_compl_singleton_iff.mpr hOne)
  let negLog : Complex -> Complex := fun s => -logDeriv (DirichletCharacter.LFunction chi) s
  have hlog := ha.meromorphicAt.logDeriv
  have hneg : MeromorphicAt negLog rho := by
    dsimp [negLog]
    exact hlog.neg
  constructor
  . intro hOrder
    by_contra hNonzero
    have hreg : AnalyticAt Complex (readout chi G) rho := by
      have hFun : readout chi G = fun s =>
          -(deriv (DirichletCharacter.LFunction chi) s / DirichletCharacter.LFunction chi s) + G s := by
        funext s
        rw [readout, logDeriv_apply]
      rw [hFun]
      exact (ha.deriv.div ha hNonzero).neg.add hG
    have hnonneg := hreg.meromorphicOrderAt_nonneg
    rw [hOrder] at hnonneg
    have hlt : ((-1 : Int) : WithTop Int) < ((0 : Int) : WithTop Int) :=
      WithTop.coe_lt_coe.mpr (by norm_num)
    exact (not_lt_of_ge hnonneg) hlt
  . intro hZero
    have horder := LFunction_logDeriv_order chi rho hZero hOne
    have hnegOrder : meromorphicOrderAt negLog rho = -1 := by
      dsimp [negLog]
      rw [<- meromorphicOrderAt_fun_neg]
      exact horder
    have hGOrder := hG.meromorphicOrderAt_nonneg
    have hne : Not (meromorphicOrderAt negLog rho = meromorphicOrderAt G rho) := by
      intro he
      rw [hnegOrder] at he
      rw [<- he] at hGOrder
      have hlt : ((-1 : Int) : WithTop Int) < ((0 : Int) : WithTop Int) :=
        WithTop.coe_lt_coe.mpr (by norm_num)
      exact (not_lt_of_ge hGOrder) hlt
    change meromorphicOrderAt (negLog + G) rho = -1
    rw [meromorphicOrderAt_add_of_ne hneg hG.meromorphicAt hne, hnegOrder, min_eq_left]
    exact le_of_lt (lt_of_lt_of_le
      (show ((-1 : Int) : WithTop Int) < ((0 : Int) : WithTop Int) from
        WithTop.coe_lt_coe.mpr (by norm_num)) hGOrder)

end PrimeFactorOscillations.DirichletZeroReadout
