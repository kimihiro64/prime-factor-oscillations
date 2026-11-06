/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelDyadicSpectrum
import PrimeFactorOscillations.Helpers.CarmichaelSimpleTreeWeights

/-!
# Finite simple spectra with the complete atomic readout

The previously proved injective reflected point geometry is retained,
and every actual atomic multiplicity is one. The full compensated residue
and local readout limit retain the reference order for every real power.
These are finite atomic models, not asserted zeta zero configurations.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelTraceSharpness

def simpleTreeSpectrum (N : Nat) (H : Real) (hH : 0 < H) :
    ReflectedSpectrum (TreeIndex N) (7 / 8) :=
  { treeSpectrum N H hH with
    mult := fun _ => 1
    mult_pos := fun _ => Nat.zero_lt_one
    mult_mirror := fun _ => rfl }

theorem simpleTreeSpectrum_inner_strip (N : Nat) (H : Real) (hH : 0 < H)
    (i : TreeIndex N) :
    (1 / 7 : Real) <= ((simpleTreeSpectrum N H hH).point i).re /\
      ((simpleTreeSpectrum N H hH).point i).re <= (6 / 7 : Real) := by
  exact treeSpectrum_inner_strip N H hH i

theorem simpleTreeSpectrum_mass (N : Nat) (H : Real) (hH : 0 < H)
    (i : TreeIndex N) :
    (simpleTreeSpectrum N H hH).mass i = rootMass 0 H * simpleWordWeight i.2.val := by
  change ((1 : Nat) : Real) / (wordHeight H i.2.val) ^ 2 =
    rootMass 0 H * simpleWordWeight i.2.val
  rw [Nat.cast_one]
  simp only [wordHeight, rootMass, Nat.mul_zero, pow_zero, simpleWordWeight]
  rw [div_pow, one_div_div]
  have hp : ((2 : Real) ^ wordScore i.2.val) ^ 2 =
      (4 : Real) ^ wordScore i.2.val := by
    rw [pow_two, <- mul_pow]
    norm_num
  rw [hp]
  ring

theorem simpleTreeSpectrum_den_ne (N : Nat) (H : Real) (hH : 0 < H)
    (d : Real) (i : TreeIndex N) :
    Not ((simpleTreeSpectrum N H hH).point i + (d : Complex) - 1 = 0) := by
  exact treeSpectrum_den_ne N H hH d i

theorem simpleTreeSpectrum_full_residue_ne_zero (N : Nat) (H : Real) (hH : 0 < H)
    (d : Real) (hd : 1 < d) (i : TreeIndex N) :
    Not (atomicPowerResidue (simpleTreeSpectrum N H hH).point
      (simpleTreeSpectrum N H hH).mult d ((simpleTreeSpectrum N H hH).point i) = 0) := by
  apply atomicPowerResidue_ne_zero _ _ d hd _
    (ne_of_gt ((simpleTreeSpectrum N H hH).im_pos i))
    (simpleTreeSpectrum_den_ne N H hH d i)
  rw [atomicOrder_at _ _ (simpleTreeSpectrum N H hH).point_injective i]
  exact (simpleTreeSpectrum N H hH).mult_pos i

theorem simpleTreeSpectrum_readout_scaled_limit (N : Nat) (H : Real) (hH : 0 < H)
    (d : Real) (hd : 0 < d) (i : TreeIndex N) :
    Filter.Tendsto
      (fun s => (s - (simpleTreeSpectrum N H hH).point i) *
        affinePowerReadout
          (atomicReadout (simpleTreeSpectrum N H hH).point
            (simpleTreeSpectrum N H hH).mult) d s)
      (nhdsWithin ((simpleTreeSpectrum N H hH).point i)
        (Set.compl {(simpleTreeSpectrum N H hH).point i}))
      (nhds (atomicPowerResidue (simpleTreeSpectrum N H hH).point
        (simpleTreeSpectrum N H hH).mult d ((simpleTreeSpectrum N H hH).point i))) := by
  exact atomicPower_scaled_limit _ _ d hd _
    (simpleTreeSpectrum_den_ne N H hH d i)

end PrimeFactorOscillations.CarmichaelDyadicSharpness
