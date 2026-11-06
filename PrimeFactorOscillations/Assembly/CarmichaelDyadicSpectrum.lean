/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelFiniteSpectrum
import PrimeFactorOscillations.Helpers.CarmichaelDyadicPoints

/-!
# Actual finite dyadic spectra with natural multiplicities

The tree is a finite reflected spectrum inside [1/7, 6/7]. Its complete
atomic logarithmic readout has the prescribed multiplicities, and every
nonreal zero retains a nonzero full complex residue for every real power
greater than one. These claims retain the actual reference atomic order.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelTraceSharpness

abbrev TreeIndex (N : Nat) :=
  Prod Bool {w : List Bool // Membership.mem (wordSupport N) w}

def treeRaw {N : Nat} (i : TreeIndex N) : Prod Bool (List Bool) :=
  Prod.mk i.1 i.2.val

def treeNode (N : Nat) (b : Bool) (w : List Bool) (hw : w.length <= N) : TreeIndex N :=
  Prod.mk b (Subtype.mk w ((mem_wordSupport N w).mpr hw))

theorem treeRaw_injective (N : Nat) : Function.Injective (treeRaw (N := N)) := by
  intro i j h
  apply Prod.ext
  . exact congrArg (fun p : Prod Bool (List Bool) => p.1) h
  . apply Subtype.ext
    exact congrArg (fun p : Prod Bool (List Bool) => p.2) h

def treeSpectrum (N : Nat) (H : Real) (hH : 0 < H) :
    ReflectedSpectrum (TreeIndex N) (7 / 8) where
  point i := wordPoint H i.1 i.2.val
  mult i := wordMultiplicity N i.2.val
  point_injective := by
    intro i j h
    exact treeRaw_injective N (wordPoint_injective H h)
  mult_pos i := wordMultiplicity_pos N i.2.val
  im_pos i := wordHeight_pos H hH i.2.val
  re_lower i := by
    have h := (wordPoint_bounds H i.1 i.2.val).1
    linarith
  re_upper i := by
    have h := (wordPoint_bounds H i.1 i.2.val).2
    linarith
  mirror i := Prod.mk (Bool.not i.1) i.2
  mirror_involutive := by
    intro i
    apply Prod.ext
    . exact Bool.not_not i.1
    . rfl
  point_mirror i := by
    simpa [zeroReflection] using wordPoint_reflection H i.1 i.2.val
  mult_mirror i := rfl

theorem treeSpectrum_inner_strip (N : Nat) (H : Real) (hH : 0 < H) (i : TreeIndex N) :
    (1 / 7 : Real) <= ((treeSpectrum N H hH).point i).re /\
      ((treeSpectrum N H hH).point i).re <= (6 / 7 : Real) :=
  wordPoint_bounds H i.1 i.2.val

theorem treeSpectrum_mass (N : Nat) (H : Real) (hH : 0 < H) (i : TreeIndex N) :
    (treeSpectrum N H hH).mass i = rootMass N H * wordWeight i.2.val := by
  change wordMass N H i.2.val = _
  exact wordMass_eq N H i.2.val i.2.property

theorem treeSpectrum_den_ne (N : Nat) (H : Real) (hH : 0 < H)
    (d : Real) (i : TreeIndex N) :
    Not ((treeSpectrum N H hH).point i + (d : Complex) - 1 = 0) := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.one_im,
    Complex.zero_im, add_zero, sub_zero] at hi
  exact (ne_of_gt ((treeSpectrum N H hH).im_pos i)) hi

theorem treeSpectrum_full_residue_ne_zero (N : Nat) (H : Real) (hH : 0 < H)
    (d : Real) (hd : 1 < d) (i : TreeIndex N) :
    Not (atomicPowerResidue (treeSpectrum N H hH).point
      (treeSpectrum N H hH).mult d ((treeSpectrum N H hH).point i) = 0) := by
  apply atomicPowerResidue_ne_zero _ _ d hd _
    (ne_of_gt ((treeSpectrum N H hH).im_pos i))
    (treeSpectrum_den_ne N H hH d i)
  rw [atomicOrder_at _ _ (treeSpectrum N H hH).point_injective i]
  exact (treeSpectrum N H hH).mult_pos i

theorem treeSpectrum_readout_scaled_limit (N : Nat) (H : Real) (hH : 0 < H)
    (d : Real) (hd : 0 < d) (i : TreeIndex N) :
    Filter.Tendsto
      (fun s => (s - (treeSpectrum N H hH).point i) *
        affinePowerReadout
          (atomicReadout (treeSpectrum N H hH).point (treeSpectrum N H hH).mult) d s)
      (nhdsWithin ((treeSpectrum N H hH).point i)
        (Set.compl {(treeSpectrum N H hH).point i}))
      (nhds (atomicPowerResidue (treeSpectrum N H hH).point
        (treeSpectrum N H hH).mult d ((treeSpectrum N H hH).point i))) := by
  exact atomicPower_scaled_limit _ _ d hd _ (treeSpectrum_den_ne N H hH d i)

end PrimeFactorOscillations.CarmichaelDyadicSharpness
