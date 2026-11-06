/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResidueLattice

/-!
# Sharp noise tolerance for integer compensated residues

Below half the lattice spacing, one complex measurement identifies both
integer coordinates. The midpoint of the attaining pair proves that the
strict threshold cannot be enlarged or made non-strict.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

theorem integerResidueCode_zero (d : Nat) (z : Complex) :
    integerResidueCode d z 0 0 = 0 := by
  simp [integerResidueCode]

theorem integerResidueCode_unique_of_error_sum_lt (d : Nat) (hd : 2 <= d)
    (z : Complex) (hz : (d : Real) * ((d : Real) - 1) <= abs z.im)
    (a b a' b' : Int) (r : Complex)
    (hden : Not (z + (d : Complex) - 1 = 0))
    (hsmall :
      (norm (integerResidueCode d z a b - r) +
        norm (integerResidueCode d z a' b' - r)) * norm (z + (d : Complex) - 1) <
        (d : Real) * ((d : Real) - 1)) :
    a = a' /\ b = b' := by
  by_contra hne
  have hs := integerResidueCode_pair_separation d hd z hz a b a' b' hne hden
  have ht :
      norm (integerResidueCode d z a b - integerResidueCode d z a' b') <=
        norm (integerResidueCode d z a b - r) +
          norm (integerResidueCode d z a' b' - r) := by
    calc
      _ = norm ((integerResidueCode d z a b - r) +
          (r - integerResidueCode d z a' b')) := by congr 1; ring
      _ <= _ := by
        simpa only [norm_sub_rev r (integerResidueCode d z a' b')] using
          norm_add_le (integerResidueCode d z a b - r)
            (r - integerResidueCode d z a' b')
  have hp := mul_le_mul_of_nonneg_right ht (norm_nonneg (z + (d : Complex) - 1))
  exact (not_le_of_gt hsmall) (hs.trans hp)

theorem integerResidueCode_unique_of_half_error (d : Nat) (hd : 2 <= d)
    (z : Complex) (hz : (d : Real) * ((d : Real) - 1) <= abs z.im)
    (a b a' b' : Int) (r : Complex)
    (hden : Not (z + (d : Complex) - 1 = 0))
    (ha : norm (integerResidueCode d z a b - r) * norm (z + (d : Complex) - 1) <
      (d : Real) * ((d : Real) - 1) / 2)
    (hb : norm (integerResidueCode d z a' b' - r) * norm (z + (d : Complex) - 1) <
      (d : Real) * ((d : Real) - 1) / 2) :
    a = a' /\ b = b' := by
  apply integerResidueCode_unique_of_error_sum_lt d hd z hz a b a' b' r hden
  rw [add_mul]
  linarith

theorem integerResidueCode_midpoint_distances (d : Nat) (hd : 2 <= d)
    (z : Complex) (hden : Not (z + (d : Complex) - 1 = 0)) :
    let r := integerResidueCode d z (d : Int) 1 / 2
    norm (integerResidueCode d z (d : Int) 1 - r) *
        norm (z + (d : Complex) - 1) = (d : Real) * ((d : Real) - 1) / 2 /\
      norm (integerResidueCode d z 0 0 - r) *
        norm (z + (d : Complex) - 1) = (d : Real) * ((d : Real) - 1) / 2 := by
  dsimp only
  have hh :
      norm (integerResidueCode d z (d : Int) 1 / 2) *
        norm (z + (d : Complex) - 1) = (d : Real) * ((d : Real) - 1) / 2 := by
    calc
      _ = (norm (integerResidueCode d z (d : Int) 1) / 2) *
          norm (z + (d : Complex) - 1) := by
        congr 1
        rw [norm_div]
        norm_num
      _ = (norm (integerResidueCode d z (d : Int) 1) *
          norm (z + (d : Complex) - 1)) / 2 := by ring
      _ = _ := by rw [integerResidueCode_attains d hd z hden]
  constructor
  . have he : integerResidueCode d z (d : Int) 1 -
        integerResidueCode d z (d : Int) 1 / 2 =
        integerResidueCode d z (d : Int) 1 / 2 := by ring
    rw [he]
    exact hh
  . rw [integerResidueCode_zero, zero_sub, norm_neg]
    exact hh

/-- Every larger radius admits one measurement compatible with distinct pairs. -/
theorem integerResidueCode_radius_sharp (d : Nat) (hd : 2 <= d)
    (z : Complex) (hden : Not (z + (d : Complex) - 1 = 0))
    (R : Real) (hR : (d : Real) * ((d : Real) - 1) / 2 < R) :
    exists r : Complex,
      norm (integerResidueCode d z (d : Int) 1 - r) * norm (z + (d : Complex) - 1) < R /\
      norm (integerResidueCode d z 0 0 - r) * norm (z + (d : Complex) - 1) < R /\
      Not ((d : Int) = 0 /\ (1 : Int) = 0) := by
  refine Exists.intro (integerResidueCode d z (d : Int) 1 / 2) ?_
  have h := integerResidueCode_midpoint_distances d hd z hden
  dsimp only at h
  exact And.intro (h.1.trans_lt hR)
    (And.intro (h.2.trans_lt hR) (by intro hc; norm_num at hc))

theorem integerResidueCode_sharp_separation (d : Nat) (hd : 2 <= d)
    (z : Complex) (hden : Not (z + (d : Complex) - 1 = 0))
    (K : Real)
    (hK : forall a b : Int, Not (a = 0 /\ b = 0) ->
      K <= norm (integerResidueCode d z a b) * norm (z + (d : Complex) - 1)) :
    K <= (d : Real) * ((d : Real) - 1) := by
  have h := hK (d : Int) 1 (by intro hc; norm_num at hc)
  rwa [integerResidueCode_attains d hd z hden] at h

theorem integerResidueCode_small_forces_relation
    (d : Nat) (z : Complex) (a b : Int)
    (hden : Not (z + (d : Complex) - 1 = 0))
    (hsmall : norm (integerResidueCode d z a b) * norm (z + (d : Complex) - 1) <
      abs z.im) :
    a = (d : Int) * b := by
  by_contra hne
  have hk : Not ((d : Int) * b - a = 0) := by
    intro hk
    apply hne
    omega
  exact (not_le_of_gt hsmall)
    (integerResidueCode_nonresonant_separation d z a b hden hk)

end Complex

end
