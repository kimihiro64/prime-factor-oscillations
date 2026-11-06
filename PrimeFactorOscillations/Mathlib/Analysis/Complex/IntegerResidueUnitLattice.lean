/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResidueDecoding

/-!
# Unit spacing and the optimal absolute noise threshold

A reference coefficient with imaginary part of absolute value at least one
gives exact unit spacing for the full integer residue lattice. Horizontal
adjacent positive pairs force a universal half-unit ambiguity threshold.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

private theorem int_real_abs_one_le (a : Int) (ha : Not (a = 0)) :
    (1 : Real) <= abs (a : Real) := by
  have hi : (1 : Int) <= abs a := by
    rcases lt_or_gt_of_ne ha with hn | hp
    . rw [abs_of_neg hn]
      omega
    . rw [abs_of_pos hp]
      omega
  exact_mod_cast hi

theorem integerResidueCode_im (d : Nat) (z : Complex) (a b : Int) :
    (integerResidueCode d z a b).im =
      ((d : Complex) * z / (z + (d : Complex) - 1)).im * (b : Real) := by
  simp [integerResidueCode, Complex.mul_im]

theorem integerResidueCode_unit_separation (d : Nat) (z : Complex)
    (hVertical : 1 <= abs (((d : Complex) * z / (z + (d : Complex) - 1)).im))
    (a b : Int) (hab : Not (a = 0 /\ b = 0)) :
    1 <= norm (integerResidueCode d z a b) := by
  by_cases hb : b = 0
  . have ha : Not (a = 0) := by
      intro ha
      exact hab (And.intro ha hb)
    have h := Complex.abs_re_le_norm (integerResidueCode d z a b)
    have he : (integerResidueCode d z a b).re = -(a : Real) := by
      simp [integerResidueCode, hb]
    rw [he, abs_neg] at h
    exact (int_real_abs_one_le a ha).trans h
  . have hi := int_real_abs_one_le b hb
    have h := Complex.abs_im_le_norm (integerResidueCode d z a b)
    rw [integerResidueCode_im, abs_mul] at h
    have hp := mul_le_mul hVertical hi (by norm_num : (0 : Real) <= 1)
      (abs_nonneg (((d : Complex) * z / (z + (d : Complex) - 1)).im))
    simpa only [one_mul] using hp.trans h

theorem integerResidueCode_unit_pair_separation (d : Nat) (z : Complex)
    (hVertical : 1 <= abs (((d : Complex) * z / (z + (d : Complex) - 1)).im))
    (a b a' b' : Int) (hab : Not (a = a' /\ b = b')) :
    1 <= norm (integerResidueCode d z a b - integerResidueCode d z a' b') := by
  rw [integerResidueCode_sub]
  apply integerResidueCode_unit_separation d z hVertical (a - a') (b - b')
  intro h
  apply hab
  exact And.intro (by omega) (by omega)

theorem integerResidueCode_unit_attains (d : Nat) (z : Complex) :
    norm (integerResidueCode d z 1 0) = 1 := by
  norm_num [integerResidueCode]

theorem integerResidueCode_unit_unique (d : Nat) (z : Complex)
    (hVertical : 1 <= abs (((d : Complex) * z / (z + (d : Complex) - 1)).im))
    (a b a' b' : Int) (r : Complex)
    (ha : norm (integerResidueCode d z a b - r) < 1 / 2)
    (hb : norm (integerResidueCode d z a' b' - r) < 1 / 2) :
    a = a' /\ b = b' := by
  by_contra hne
  have hs := integerResidueCode_unit_pair_separation d z hVertical a b a' b' hne
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
  linarith

/-- Even two strictly positive order pairs are ambiguous at half-unit error. -/
theorem integerResidueCode_unit_midpoint (d : Nat) (z : Complex) :
    let r := integerResidueCode d z 1 1 - 1 / 2
    norm (integerResidueCode d z 1 1 - r) = 1 / 2 /\
      norm (integerResidueCode d z 2 1 - r) = 1 / 2 := by
  dsimp only
  have h1 : integerResidueCode d z 1 1 -
      (integerResidueCode d z 1 1 - 1 / 2) = (1 / 2 : Complex) := by ring
  have h2 : integerResidueCode d z 2 1 -
      (integerResidueCode d z 1 1 - 1 / 2) = (-1 / 2 : Complex) := by
    unfold integerResidueCode
    norm_num
    ring
  constructor
  . rw [h1]
    norm_num
  . rw [h2]
    norm_num

theorem integerResidueCode_unit_radius_sharp (d : Nat) (z : Complex)
    (R : Real) (hR : 1 / 2 < R) :
    exists r : Complex,
      norm (integerResidueCode d z 1 1 - r) < R /\
      norm (integerResidueCode d z 2 1 - r) < R /\
      Not ((1 : Int) = 2 /\ (1 : Int) = 1) := by
  refine Exists.intro (integerResidueCode d z 1 1 - 1 / 2) ?_
  have h := integerResidueCode_unit_midpoint d z
  dsimp only at h
  exact And.intro (h.1.trans_lt hR)
    (And.intro (h.2.trans_lt hR) (by norm_num))

theorem integerResidueCode_spacing_le_one (d : Nat) (z : Complex)
    (K : Real)
    (hK : forall a b : Int, Not (a = 0 /\ b = 0) ->
      K <= norm (integerResidueCode d z a b)) :
    K <= 1 := by
  have h := hK 1 0 (by norm_num)
  rwa [integerResidueCode_unit_attains] at h

end Complex

end
