/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandau.lean
Original source lines 1455-1663. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauPoleStartup

/-!
# The removable value of the zeta Mellin continuation at one

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Asymptotics Filter MeasureTheory Set

noncomputable section

/-- The removable regular part of zeta at one.  Away from one this is exactly
`zeta(s) - 1 / (s - 1)`; at one it is assigned its punctured limit. -/
def nicolasZetaRegularPart (s : Complex) : Complex :=
  Function.update
    (fun w : Complex => riemannZeta w - 1 / (w - 1)) 1
    (limUnder (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (fun w : Complex => riemannZeta w - 1 / (w - 1))) s

theorem nicolasZetaRegularPart_eq_of_ne_one
    {s : Complex} (hs : Not (s = 1)) :
    nicolasZetaRegularPart s = riemannZeta s - 1 / (s - 1) := by
  simp [nicolasZetaRegularPart, hs]

/-- The regular part is entire after filling the removable singularity. -/
theorem nicolasZetaRegularPart_differentiable :
    Differentiable Complex nicolasZetaRegularPart := by
  intro s
  let f : Complex -> Complex := fun w => riemannZeta w - 1 / (w - 1)
  by_cases hs : s = 1
  . subst s
    have hDiffAway : DifferentiableOn Complex f
        (Set.univ \ {1}) := by
      intro w hw
      have hwOne : Not (w = 1) := by
        exact Set.mem_compl_singleton_iff.mp hw.2
      have hNumerator : DifferentiableAt Complex
          (fun _ : Complex => (1 : Complex)) w := by fun_prop
      have hDenominator : DifferentiableAt Complex
          (fun z : Complex => z - 1) w := by fun_prop
      dsimp [f]
      exact ((differentiableAt_riemannZeta hwOne).sub
        (hNumerator.div hDenominator (sub_ne_zero.mpr hwOne))).differentiableWithinAt
    have hLittleO : (fun w : Complex => f w - f 1) =o[
        nhdsWithin 1 (Set.compl {(1 : Complex)})]
        (fun w : Complex => Inv.inv (w - 1)) := by
      refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
      . filter_upwards [self_mem_nhdsWithin] with w hw hwInv
        rw [inv_eq_zero, sub_eq_zero] at hwInv
        tauto
      . simp_rw [div_eq_mul_inv, inv_inv, sub_mul,
          (by ring_nf : nhds (0 : Complex) =
            nhds ((1 - 1) - f 1 * (1 - 1)))]
        apply Tendsto.sub
        . simp_rw [mul_comm (f _), f, mul_sub]
          apply riemannZeta_residue_one.sub
          refine Tendsto.congr' ?_
            (tendsto_const_nhds.mono_left nhdsWithin_le_nhds)
          filter_upwards [self_mem_nhdsWithin] with w hw
          field_simp [sub_ne_zero.mpr
            (Set.mem_compl_singleton_iff.mp hw)]
        . exact ((tendsto_id.sub tendsto_const_nhds).mono_left
            nhdsWithin_le_nhds).const_mul _
    have hFilled := Complex.differentiableOn_update_limUnder_of_isLittleO
      (s := Set.univ) (c := (1 : Complex)) univ_mem hDiffAway hLittleO
    change DifferentiableAt Complex
      (Function.update f 1
        (limUnder (nhdsWithin 1 (Set.compl {(1 : Complex)})) f)) 1
    exact (hFilled 1 (Set.mem_univ 1)).differentiableAt Filter.univ_mem
  . have hBase : DifferentiableAt Complex f s := by
      have hNumerator : DifferentiableAt Complex
          (fun _ : Complex => (1 : Complex)) s := by fun_prop
      have hDenominator : DifferentiableAt Complex
          (fun z : Complex => z - 1) s := by fun_prop
      dsimp [f]
      exact (differentiableAt_riemannZeta hs).sub
        (hNumerator.div hDenominator (sub_ne_zero.mpr hs))
    change DifferentiableAt Complex
      (Function.update f 1
        (limUnder (nhdsWithin 1 (Set.compl {(1 : Complex)})) f)) s
    apply hBase.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
    simp [Function.update_of_ne
      (Set.mem_compl_singleton_iff.mp hw)]

/-- The entire factor left after extracting zeta's simple pole at one. -/
def nicolasZetaPoleFactor (s : Complex) : Complex :=
  1 + (s - 1) * nicolasZetaRegularPart s

theorem nicolasZetaPoleFactor_differentiable :
    Differentiable Complex nicolasZetaPoleFactor := by
  intro s
  unfold nicolasZetaPoleFactor
  have hConst : DifferentiableAt Complex
      (fun _ : Complex => (1 : Complex)) s := by fun_prop
  have hDifference : DifferentiableAt Complex
      (fun w : Complex => w - 1) s := by fun_prop
  exact hConst.add
    (hDifference.mul (nicolasZetaRegularPart_differentiable s))

@[simp] theorem nicolasZetaPoleFactor_one :
    nicolasZetaPoleFactor 1 = 1 := by
  unfold nicolasZetaPoleFactor
  ring

theorem riemannZeta_eq_nicolasZetaPoleFactor_div
    {s : Complex} (hs : Not (s = 1)) :
    riemannZeta s = nicolasZetaPoleFactor s / (s - 1) := by
  unfold nicolasZetaPoleFactor
  rw [nicolasZetaRegularPart_eq_of_ne_one hs]
  field_simp [sub_ne_zero.mpr hs]
  ring

theorem logDeriv_riemannZeta_eq_poleFactor_sub
    {s : Complex} (hs : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    logDeriv riemannZeta s =
      logDeriv nicolasZetaPoleFactor s - 1 / (s - 1) := by
  have hLocal : Filter.EventuallyEq (nhds s) riemannZeta
      (fun w : Complex => nicolasZetaPoleFactor w / (w - 1)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
    exact riemannZeta_eq_nicolasZetaPoleFactor_div
      (Set.mem_compl_singleton_iff.mp hw)
  have hLogCongr := logDeriv_congr_nhds hLocal
  have hLogAt : logDeriv riemannZeta s =
      logDeriv (fun w : Complex => nicolasZetaPoleFactor w / (w - 1)) s :=
    hLogCongr.self_of_nhds
  have hFactor : Not (nicolasZetaPoleFactor s = 0) := by
    intro hFactorZero
    have hIdentity := riemannZeta_eq_nicolasZetaPoleFactor_div hs
    rw [hFactorZero, zero_div] at hIdentity
    exact hZeta hIdentity
  calc
    logDeriv riemannZeta s =
        logDeriv (fun w : Complex =>
          nicolasZetaPoleFactor w / (w - 1)) s := hLogAt
    _ = logDeriv nicolasZetaPoleFactor s -
        logDeriv (fun w : Complex => w - 1) s :=
      logDeriv_div s hFactor (sub_ne_zero.mpr hs)
        (nicolasZetaPoleFactor_differentiable s) (by fun_prop)
    _ = logDeriv nicolasZetaPoleFactor s - 1 / (s - 1) := by
      congr 1
      simp [logDeriv_apply]

/-- After the pole at one is extracted, the complete psi Mellin continuation
is the regular logarithmic derivative of the pole factor. -/
theorem nicolasPsiMellinContinuation_eq_poleFactor
    {s : Complex} (hsZero : Not (s = 0)) (hsOne : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    nicolasPsiMellinContinuation s =
      -(logDeriv nicolasZetaPoleFactor s + 1) / s := by
  unfold nicolasPsiMellinContinuation
  have hLog := logDeriv_riemannZeta_eq_poleFactor_sub hsOne hZeta
  rw [show -deriv riemannZeta s / riemannZeta s =
      -(logDeriv riemannZeta s) by
        rw [logDeriv_apply]
        ring,
    hLog]
  field_simp [hsZero, sub_ne_zero.mpr hsOne]
  ring

theorem logDeriv_nicolasZetaPoleFactor_continuousAt_one :
    ContinuousAt (logDeriv nicolasZetaPoleFactor) 1 := by
  rw [show logDeriv nicolasZetaPoleFactor =
      (fun s : Complex => deriv nicolasZetaPoleFactor s /
        nicolasZetaPoleFactor s) by rfl]
  exact (nicolasZetaPoleFactor_differentiable.deriv 1).continuousAt.div
    (nicolasZetaPoleFactor_differentiable 1).continuousAt (by simp)

/-- The complete psi Mellin continuation has a finite punctured limit at one.
This is the endpoint cancellation complementary to the genuine pole at a
nontrivial zeta zero. -/
theorem nicolasPsiMellinContinuation_tendsto_one :
    Tendsto nicolasPsiMellinContinuation
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (-(logDeriv nicolasZetaPoleFactor 1 + 1))) := by
  have hRegular : Tendsto
      (fun s : Complex => -(logDeriv nicolasZetaPoleFactor s + 1) / s)
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (-(logDeriv nicolasZetaPoleFactor 1 + 1))) := by
    have hContinuous : ContinuousAt
        (fun s : Complex => -(logDeriv nicolasZetaPoleFactor s + 1) / s) 1 :=
      (logDeriv_nicolasZetaPoleFactor_continuousAt_one.add
        continuousAt_const).neg.div continuousAt_id (by norm_num)
    simpa using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hZeroNeighborhood :
      Membership.mem (nhds (1 : Complex)) (Set.compl {(0 : Complex)}) :=
    isOpen_compl_singleton.mem_nhds
      (Set.mem_compl_singleton_iff.mpr (by norm_num))
  have hZeroWithin : Membership.mem
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (Set.compl {(0 : Complex)}) :=
    nhdsWithin_le_nhds hZeroNeighborhood
  apply hRegular.congr'
  filter_upwards
      [riemannZeta_eventually_ne_zero_nhds_one.filter_mono
        nhdsWithin_le_nhds,
      hZeroWithin,
      self_mem_nhdsWithin] with s hZeta hsZeroMem hs
  have hsOne : Not (s = 1) := Set.mem_compl_singleton_iff.mp hs
  have hsZero : Not (s = 0) :=
    Set.mem_compl_singleton_iff.mp hsZeroMem
  exact (nicolasPsiMellinContinuation_eq_poleFactor
    hsZero hsOne hZeta).symm

theorem nicolasPsiMellinTailContinuation_three_tendsto_one :
    Tendsto (nicolasPsiMellinTailContinuation 3)
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (-(logDeriv nicolasZetaPoleFactor 1 + 1) -
        nicolasPsiMellinStartup 3 1)) := by
  have hStartup : Tendsto (nicolasPsiMellinStartup 3)
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (nicolasPsiMellinStartup 3 1)) :=
    (nicolasPsiMellinStartup_three_continuousAt 1).tendsto.mono_left
      nhdsWithin_le_nhds
  have hDifference := nicolasPsiMellinContinuation_tendsto_one.sub hStartup
  convert hDifference using 1
  . rfl

end

end Robin1984

