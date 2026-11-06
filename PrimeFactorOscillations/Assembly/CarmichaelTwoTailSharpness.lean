/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelFifthSharpness
import PrimeFactorOscillations.Assembly.CarmichaelTailMass
import PrimeFactorOscillations.Assembly.CarmichaelZetaTwoTail

/-!
# The complete sharp two-tail coefficient region

Every real coefficient pair is admissible exactly when a<=16,b<=1 and
a+4b<=4. The three finite models have every actual reference row retained.
Their complete atomic readouts have nonzero residues and actual scaled
limits, as follows from the generic reflected-spectrum readout certificates.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelTraceSharpness

theorem universal_two_tail_coefficients_iff (a b : Real) :
    (forall (I : Type) [Fintype I] (S : ReflectedSpectrum I (7 / 8)),
      39 * S.weakUnitMass + S.weakRepeatedUnitMass +
        a * S.weakFifthUnitMass + b * S.weakOffTripleUnitMass <= S.carrierMass) <->
      a <= 16 /\ b <= 1 /\ a + 4 * b <= 4 := by
  constructor
  . intro h
    have hNine := h (Fin 9) (tailNineSpectrum 1 (by norm_num : (0 : Real) < 1))
    rw [tailNineSpectrum_weakUnitMass, tailNineSpectrum_weakRepeatedUnitMass,
      tailNineSpectrum_weakFifthUnitMass, tailNineSpectrum_weakOffTripleUnitMass,
      tailNineSpectrum_carrierMass] at hNine
    norm_num at hNine
    have hThirteen := h (Fin 13) (tailThirteenSpectrum 1 (by norm_num : (0 : Real) < 1))
    rw [tailThirteenSpectrum_weakUnitMass, tailThirteenSpectrum_weakRepeatedUnitMass,
      tailThirteenSpectrum_weakFifthUnitMass, tailThirteenSpectrum_weakOffTripleUnitMass,
      tailThirteenSpectrum_carrierMass] at hThirteen
    norm_num at hThirteen
    have hSeventeen := h (Fin 17) (seventeenSpectrum 1 (by norm_num : (0 : Real) < 1))
    rw [seventeenSpectrum_weakUnitMass, seventeenSpectrum_weakRepeatedUnitMass,
      seventeenSpectrum_weakFifthUnitMass, seventeenSpectrum_weakOffTripleUnitMass,
      seventeenSpectrum_carrierMass] at hSeventeen
    norm_num at hSeventeen
    exact And.intro (by linarith) (And.intro (by linarith) (by linarith))
  . intro h I inst S
    exact S.carrier_two_tail_bound a b h.1 h.2.1 h.2.2

theorem reflectedSpectrum_affine_den_ne {I : Type*} [Fintype I] {sigma : Real}
    (S : ReflectedSpectrum I sigma) (d : Real) (i : I) :
    Not (S.point i + (d : Complex) - 1 = 0) := by
  intro hz
  have he := congrArg Complex.im hz
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.one_im,
    Complex.zero_im, add_zero, sub_zero] at he
  exact (ne_of_gt (S.im_pos i)) he

theorem reflectedSpectrum_full_residue_ne_zero {I : Type*} [Fintype I] {sigma : Real}
    (S : ReflectedSpectrum I sigma) (d : Real) (hd : 1 < d) (i : I) :
    Not (atomicPowerResidue S.point S.mult d (S.point i) = 0) := by
  apply atomicPowerResidue_ne_zero _ _ d hd _ (ne_of_gt (S.im_pos i))
    (reflectedSpectrum_affine_den_ne S d i)
  rw [atomicOrder_at _ _ S.point_injective i]
  exact S.mult_pos i

theorem reflectedSpectrum_readout_scaled_limit {I : Type*} [Fintype I] {sigma : Real}
    (S : ReflectedSpectrum I sigma) (d : Real) (hd : 0 < d) (i : I) :
    Filter.Tendsto
      (fun s => (s - S.point i) * affinePowerReadout (atomicReadout S.point S.mult) d s)
      (nhdsWithin (S.point i) (Set.compl {S.point i}))
      (nhds (atomicPowerResidue S.point S.mult d (S.point i))) := by
  exact atomicPower_scaled_limit _ _ d hd _ (reflectedSpectrum_affine_den_ne S d i)

theorem reflectedSpectrum_projection_negative_iff {I : Type*} [Fintype I] {sigma : Real}
    (S : ReflectedSpectrum I sigma) (d : Real) (i : I) :
    (atomicPowerResidue S.point S.mult d (S.point i) *
      (S.point i + (d : Complex) - 1)).im < 0 <->
        d * (S.rowOrder d i : Real) < (S.mult i : Real) := by
  have h := atomicPower_projection S.point S.mult d (S.point i)
    (reflectedSpectrum_affine_den_ne S d i)
  rw [atomicOrder_at _ _ S.point_injective i] at h
  change (atomicPowerResidue S.point S.mult d (S.point i) *
      (S.point i + (d : Complex) - 1)).im =
    (d * (S.rowOrder d i : Real) - (S.mult i : Real)) * (S.point i).im at h
  rw [h]
  constructor
  . intro hNeg
    by_contra hn
    have hNonneg := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) (S.im_pos i).le
    exact (not_lt_of_ge hNonneg) hNeg
  . intro hNeg
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hNeg) (S.im_pos i)

theorem reflectedSpectrum_joint_readout_carrier {I : Type*} [Fintype I] {sigma : Real}
    (S : ReflectedSpectrum I sigma) :
    S.carrierIndices = Finset.univ.filter (fun i =>
      (atomicPowerResidue S.point S.mult 2 (S.point i) *
        (S.point i + ((2 : Real) : Complex) - 1)).im < 0 \/
      (atomicPowerResidue S.point S.mult 4 (S.point i) *
        (S.point i + ((4 : Real) : Complex) - 1)).im < 0) := by
  classical
  apply Finset.ext
  intro i
  simp only [ReflectedSpectrum.carrierIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [reflectedSpectrum_projection_negative_iff S 2 i,
    reflectedSpectrum_projection_negative_iff S 4 i]

end PrimeFactorOscillations.CarmichaelDyadicSharpness
