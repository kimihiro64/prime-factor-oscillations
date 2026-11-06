/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelFivePointSpectrum

/-!
# Complete reference rows of the five-point extremizer

The right quadratic collision is retained. Every other absent reference is
proved absent from the actual finite point set by its real coordinate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelTraceSharpness

theorem fiveSpectrum_two_order (H : Real) (hH : 0 < H) (i : Fin 5) :
    (fiveSpectrum H hH).rowOrder 2 i = if i = 0 \/ i = 2 then 1 else 0 := by
  by_cases h0 : i = 0
  . subst i
    rw [ite_eq_left (Or.inl rfl)]
    change atomicOrder (fivePoint H) fiveMultiplicity (powerMap 2 (fivePoint H 0)) = 1
    rw [fivePoint_two_center]
    simpa [fiveMultiplicity] using
      atomicOrder_at (fivePoint H) fiveMultiplicity (fivePoint_injective H) (2 : Fin 5)
  . by_cases h2 : i = 2
    . subst i
      rw [ite_eq_left (Or.inr rfl)]
      change atomicOrder (fivePoint H) fiveMultiplicity (powerMap 2 (fivePoint H 2)) = 1
      rw [fivePoint_two_right]
      simpa [fiveMultiplicity] using
        atomicOrder_at (fivePoint H) fiveMultiplicity (fivePoint_injective H) (4 : Fin 5)
    . rw [ite_eq_right (not_or_intro h0 h2)]
      change atomicOrder (fivePoint H) fiveMultiplicity (powerMap 2 (fivePoint H i)) = 0
      apply atomicOrder_zero
      intro j hj
      have he := congrArg Complex.re hj
      rw [fivePoint_power_re H 2 (by norm_num)] at he
      fin_cases i <;> fin_cases j <;>
        first | exact (h0 rfl).elim | exact (h2 rfl).elim | norm_num [fivePoint] at he

theorem fiveSpectrum_four_order (H : Real) (hH : 0 < H) (i : Fin 5) :
    (fiveSpectrum H hH).rowOrder 4 i = if i = 0 then 1 else 0 := by
  by_cases h0 : i = 0
  . subst i
    rw [ite_eq_left rfl]
    change atomicOrder (fivePoint H) fiveMultiplicity (powerMap 4 (fivePoint H 0)) = 1
    rw [fivePoint_four_center]
    simpa [fiveMultiplicity] using
      atomicOrder_at (fivePoint H) fiveMultiplicity (fivePoint_injective H) (4 : Fin 5)
  . rw [ite_eq_right h0]
    change atomicOrder (fivePoint H) fiveMultiplicity (powerMap 4 (fivePoint H i)) = 0
    apply atomicOrder_zero
    intro j hj
    have he := congrArg Complex.re hj
    rw [fivePoint_power_re H 4 (by norm_num)] at he
    fin_cases i <;> fin_cases j <;>
      first | exact (h0 rfl).elim | norm_num [fivePoint] at he

theorem fiveSpectrum_weak_iff (H : Real) (hH : 0 < H) (i : Fin 5) :
    Membership.mem (fiveSpectrum H hH).weakIndices i <-> i = 0 := by
  classical
  rw [ReflectedSpectrum.weakIndices, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [fiveSpectrum_two_order, fiveSpectrum_four_order]
  change ((fiveMultiplicity i : Real) <= 2 * ((if i = 0 \/ i = 2 then 1 else 0 : Nat) : Real) /\
    (fiveMultiplicity i : Real) <= 4 * ((if i = 0 then 1 else 0 : Nat) : Real)) <-> i = 0
  fin_cases i <;> norm_num [fiveMultiplicity]

theorem fiveSpectrum_weakIndices (H : Real) (hH : 0 < H) :
    (fiveSpectrum H hH).weakIndices = {0} := by
  classical
  apply Finset.ext
  intro i
  rw [fiveSpectrum_weak_iff, Finset.mem_singleton]

theorem fiveSpectrum_den_ne (H : Real) (hH : 0 < H) (d : Real) (i : Fin 5) :
    Not ((fiveSpectrum H hH).point i + (d : Complex) - 1 = 0) := by
  intro hz
  have he := congrArg Complex.im hz
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.one_im,
    Complex.zero_im, add_zero, sub_zero] at he
  exact (ne_of_gt ((fiveSpectrum H hH).im_pos i)) he

theorem fiveSpectrum_full_residue_ne_zero (H : Real) (hH : 0 < H)
    (d : Real) (hd : 1 < d) (i : Fin 5) :
    Not (atomicPowerResidue (fiveSpectrum H hH).point
      (fiveSpectrum H hH).mult d ((fiveSpectrum H hH).point i) = 0) := by
  apply atomicPowerResidue_ne_zero _ _ d hd _
    (ne_of_gt ((fiveSpectrum H hH).im_pos i)) (fiveSpectrum_den_ne H hH d i)
  rw [atomicOrder_at _ _ (fiveSpectrum H hH).point_injective i]
  exact (fiveSpectrum H hH).mult_pos i

theorem fiveSpectrum_readout_scaled_limit (H : Real) (hH : 0 < H)
    (d : Real) (hd : 0 < d) (i : Fin 5) :
    Filter.Tendsto
      (fun s => (s - (fiveSpectrum H hH).point i) *
        affinePowerReadout
          (atomicReadout (fiveSpectrum H hH).point (fiveSpectrum H hH).mult) d s)
      (nhdsWithin ((fiveSpectrum H hH).point i)
        (Set.compl {(fiveSpectrum H hH).point i}))
      (nhds (atomicPowerResidue (fiveSpectrum H hH).point
        (fiveSpectrum H hH).mult d ((fiveSpectrum H hH).point i))) := by
  exact atomicPower_scaled_limit _ _ d hd _ (fiveSpectrum_den_ne H hH d i)

end PrimeFactorOscillations.CarmichaelDyadicSharpness
