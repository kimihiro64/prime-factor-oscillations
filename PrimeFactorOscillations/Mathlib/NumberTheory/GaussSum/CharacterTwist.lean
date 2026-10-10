/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.QuadraticEnergy

/-!
# Additive indices and character orientation at a fixed cusp

A positive quartic twist and a quadratic twist correspond to a cube-square
additive index in the complete Gauss sum. The identity retains zero indices.
For a nonquadratic character value, a linear index provably gives a different
answer when both characters are nontrivial. These finite identities do not
assert a functional equation or a conductor bound for an analytic series.

Over arbitrary finite commutative rings, combining the input Gauss transform
with the fixed-cusp multiplier gives a Gauss transform of omega / chi.
After evaluating that transform, the frequency character is chi / omega.
Inverse quartic input yields a quadratic transform; positive input yields a
Ramanujan sum. All unit residues and all output frequencies remain.
-/

set_option autoImplicit false
set_option Elab.async false

namespace MulChar

variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
/-- A positive quartic twist uses a cube index and a quadratic twist uses a square index. -/
theorem quartic_inverse_cube_square (chi : MulChar F Complex) (hfour : chi ^ 4 = 1)
    (k f : F) :
    (Inv.inv chi) (k ^ 3 * f ^ 2) = chi k * (chi ^ 2) f := by
  have hcube : (Inv.inv chi) ^ 3 = chi := by
    rw [inv_pow]
    apply inv_eq_of_mul_eq_one_right
    calc
      chi ^ 3 * chi = chi ^ 4 := (pow_succ chi 3).symm
      _ = 1 := hfour
  have hsquare : (Inv.inv chi) ^ 2 = chi ^ 2 := by
    rw [inv_pow]
    apply inv_eq_of_mul_eq_one_right
    calc
      chi ^ 2 * chi ^ 2 = chi ^ (2 + 2) := (pow_add chi 2 2).symm
      _ = 1 := hfour
  rw [map_mul, map_pow, map_pow,
    <- MulChar.pow_apply' (Inv.inv chi) (by decide : Not ((3 : Nat) = 0)),
    <- MulChar.pow_apply' (Inv.inv chi) (by decide : Not ((2 : Nat) = 0)),
    hcube, hsquare]

/-- The complete Gauss transform retains both twists, including zero indices. -/
theorem quarticGaussShift_cube_square (chi : MulChar F Complex)
    (hfour : chi ^ 4 = 1) (hchi : Not (chi = 1))
    (psi : AddChar F Complex) (k f : F) :
    gaussSum chi (psi.mulShift (k ^ 3 * f ^ 2)) =
      chi k * (chi ^ 2) f * gaussSum chi psi := by
  classical
  by_cases hzero : k ^ 3 * f ^ 2 = 0
  . have hcoef : chi k * (chi ^ 2) f = 0 := by
      rw [<- quartic_inverse_cube_square chi hfour k f, hzero, MulChar.map_zero]
    rw [hcoef, zero_mul, hzero]
    simpa [gaussSum] using MulChar.sum_eq_zero_of_ne_one hchi
  . have hs := gaussSum_mulShift_eq chi psi (Units.mk0 (k ^ 3 * f ^ 2) hzero)
    simpa only [Units.val_mk0, quartic_inverse_cube_square chi hfour k f] using hs

/-- A linear index cannot replace the cube for a nonquadratic character value. -/
theorem gaussSum_linear_ne_positive_twist (chi : MulChar F Complex)
    (hchi : Not (chi = 1)) (psi : AddChar F Complex) (hpsi : Not (psi = 1))
    (k : F) (hk : Not (k = 0)) (hvalue : Not (chi k ^ 2 = 1)) :
    Not (gaussSum chi (psi.mulShift k) = chi k * gaussSum chi psi) := by
  have hG : Not (gaussSum chi psi = 0) := by
    intro hz
    have hn := normSq_gaussSum_eq_card chi hchi psi hpsi
    rw [hz, map_zero] at hn
    have hc : Not ((Fintype.card F : Real) = 0) := by exact_mod_cast Fintype.card_ne_zero
    exact hc hn.symm
  intro heq
  have hs := gaussSum_mulShift_eq chi psi (Units.mk0 k hk)
  simp only [Units.val_mk0] at hs
  have hsame := hs.symm.trans heq
  have hprodzero : ((Inv.inv chi) k - chi k) * gaussSum chi psi = 0 := by
    rw [sub_mul, hsame, sub_self]
  have hi : (Inv.inv chi) k = chi k :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprodzero).resolve_right hG)
  have hprod : (Inv.inv chi) k * chi k = 1 := by
    rw [<- MulChar.mul_apply]
    simp [MulChar.one_apply (isUnit_iff_ne_zero.mpr hk)]
  apply hvalue
  rw [hi, <- pow_two] at hprod
  exact hprod

variable {R : Type*} [CommRing R] [Fintype R] [Fintype (Units R)]

omit [Fintype R] [Fintype (Units R)] in
/-- Inverting the unit argument inverts the multiplicative character. -/
theorem apply_inv_unit_eq_inverse (chi : MulChar R Complex) (u : Units R) :
    chi ((Inv.inv u : Units R) : R) = (Inv.inv chi) (u : R) := by
  have hleft : chi ((Inv.inv u : Units R) : R) * chi (u : R) = 1 := by
    rw [<- map_mul]
    simp
  have hright : chi (u : R) * (Inv.inv chi) (u : R) = 1 := by
    rw [<- MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
  calc
    chi ((Inv.inv u : Units R) : R) =
        chi ((Inv.inv u : Units R) : R) * 1 := (mul_one _).symm
    _ = chi ((Inv.inv u : Units R) : R) *
        (chi (u : R) * (Inv.inv chi) (u : R)) := by rw [hright]
    _ = (chi ((Inv.inv u : Units R) : R) * chi (u : R)) *
        (Inv.inv chi) (u : R) := (mul_assoc _ _ _).symm
    _ = (Inv.inv chi) (u : R) := by rw [hleft, one_mul]

omit [Fintype (Units R)] in
/-- The input Fourier coefficient, with its negative additive sign retained. -/
theorem gaussSum_neg_unit_shift (omega : MulChar R Complex)
    (psi : AddChar R Complex) (h : Units R) :
    gaussSum omega (psi.mulShift (-(h : R))) =
      (Inv.inv omega) (h : R) * gaussSum omega (psi.mulShift (-1)) := by
  have hshift : psi.mulShift (-(h : R)) = (psi.mulShift (-1)).mulShift (h : R) := by
    ext x
    simp only [AddChar.mulShift_apply]
    congr 1
    ring
  rw [hshift]
  exact gaussSum_mulShift_eq omega (psi.mulShift (-1)) h

/-- Combining the input transform with automorphy gives the Gauss transform
of omega/chi. Its evaluated frequency character is the inverse, chi/omega.
All unit residues are included and the output frequency is unrestricted. -/
theorem fixedCuspTransform (omega chi : MulChar R Complex)
    (psi : AddChar R Complex) (a : R) :
    Finset.sum Finset.univ (fun h : Units R =>
      gaussSum omega (psi.mulShift (-(h : R))) * chi (h : R) *
        psi (a * ((Inv.inv h : Units R) : R))) =
      gaussSum omega (psi.mulShift (-1)) *
        Finset.sum Finset.univ (fun t : Units R =>
          (omega * Inv.inv chi) (t : R) * psi (a * (t : R))) := by
  classical
  simp_rw [gaussSum_neg_unit_shift]
  rw [Finset.mul_sum]
  apply (Fintype.sum_equiv (Equiv.inv (Units R)) _ _ ?_)
  intro h
  simp only [Equiv.inv_apply, apply_inv_unit_eq_inverse, MulChar.mul_apply, inv_inv]
  ring

/-- For quartic input inverse to the automorphy character, the output is quadratic. -/
theorem fixedCuspTransform_inverse_quartic (chi : MulChar R Complex)
    (hfour : chi ^ 4 = 1) (psi : AddChar R Complex) (a : R) :
    Finset.sum Finset.univ (fun h : Units R =>
      gaussSum (Inv.inv chi) (psi.mulShift (-(h : R))) * chi (h : R) *
        psi (a * ((Inv.inv h : Units R) : R))) =
      gaussSum (Inv.inv chi) (psi.mulShift (-1)) *
        Finset.sum Finset.univ (fun t : Units R =>
          (chi ^ 2) (t : R) * psi (a * (t : R))) := by
  have hsquare : Inv.inv chi * Inv.inv chi = chi ^ 2 := by
    rw [<- pow_two, inv_pow]
    apply inv_eq_of_mul_eq_one_right
    calc
      chi ^ 2 * chi ^ 2 = chi ^ (2 + 2) := (pow_add chi 2 2).symm
      _ = 1 := hfour
  rw [fixedCuspTransform, hsquare]

/-- The opposite orientation produces the full Ramanujan sum, not a quadratic twist. -/
theorem fixedCuspTransform_positive (chi : MulChar R Complex)
    (psi : AddChar R Complex) (a : R) :
    Finset.sum Finset.univ (fun h : Units R =>
      gaussSum chi (psi.mulShift (-(h : R))) * chi (h : R) *
        psi (a * ((Inv.inv h : Units R) : R))) =
      gaussSum chi (psi.mulShift (-1)) *
        Finset.sum Finset.univ (fun t : Units R => psi (a * (t : R))) := by
  rw [fixedCuspTransform, mul_inv_cancel]
  simp only [MulChar.one_apply_coe, one_mul]


omit [Fintype R] [Fintype (Units R)] in
/-- A completion power killing the automorphy multiplier also identifies the
input character power with the reflected Gauss character power. -/
theorem fixedCusp_completion_pow (omega chi : MulChar R Complex) (m : Nat)
    (hchi : chi ^ m = 1) :
    omega ^ m = (omega * Inv.inv chi) ^ m := by
  rw [mul_pow, inv_pow, hchi, inv_one, mul_one]

omit [Fintype R] [Fintype (Units R)] in
/-- An even completion has principal character when the reflected character
is quadratic. The principal multiplicative character retains nonunit zeros. -/
theorem fixedCusp_completion_even (omega chi : MulChar R Complex) (r : Nat)
    (hchi : chi ^ (2 * r) = 1)
    (hquadratic : (omega * Inv.inv chi) ^ 2 = 1) :
    omega ^ (2 * r) = 1 := by
  rw [fixedCusp_completion_pow omega chi (2 * r) hchi,
    pow_mul, hquadratic, one_pow]

omit [Fintype R] [Fintype (Units R)] in
/-- An odd completion retains the quadratic reflected character. This uses
the multiplier's actual order relation, not a chosen residue-field label. -/
theorem fixedCusp_completion_odd (omega chi : MulChar R Complex) (r : Nat)
    (hchi : chi ^ (2 * r + 1) = 1)
    (hquadratic : (omega * Inv.inv chi) ^ 2 = 1) :
    omega ^ (2 * r + 1) = omega * Inv.inv chi := by
  rw [fixedCusp_completion_pow omega chi (2 * r + 1) hchi,
    pow_succ, pow_mul, hquadratic, one_pow, one_mul]

omit [Fintype R] [Fintype (Units R)] in
/-- On the overlap k=a*b, f=b the quartic canonical character becomes an
opposite pair. The identity includes every nonunit of the finite ring. -/
theorem quartic_overlap_opposite (chi : MulChar R Complex)
    (hfour : chi ^ 4 = 1) (a b : R) :
    chi (a * b) * (chi ^ 2) b = chi a * (Inv.inv chi) b := by
  have hthree : Inv.inv chi = chi ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    calc
      chi * chi ^ 3 = chi ^ 3 * chi := mul_comm _ _
      _ = chi ^ 4 := (pow_succ chi 3).symm
      _ = 1 := hfour
  have hmul : chi * chi ^ 2 = chi ^ 3 := by
    calc
      chi * chi ^ 2 = chi ^ 2 * chi := mul_comm _ _
      _ = chi ^ 3 := (pow_succ chi 2).symm
  calc
    chi (a * b) * (chi ^ 2) b = chi a * (chi b * (chi ^ 2) b) := by
      rw [map_mul, mul_assoc]
    _ = chi a * (chi * chi ^ 2) b := by rw [MulChar.mul_apply]
    _ = chi a * (Inv.inv chi) b := by rw [hmul, hthree]

/-- The decic-quintic exponent pattern gives a fifth-power Gauss character.
This is the complete finite fixed-cusp transform, not a theta functional equation. -/
theorem fixedCuspTransform_decic_quintic (chi : MulChar R Complex)
    (psi : AddChar R Complex) (a : R) :
    Finset.sum Finset.univ (fun h : Units R =>
      gaussSum (chi ^ 3) (psi.mulShift (-(h : R))) *
        ((Inv.inv chi) ^ 2) (h : R) *
        psi (a * ((Inv.inv h : Units R) : R))) =
      gaussSum (chi ^ 3) (psi.mulShift (-1)) *
        Finset.sum Finset.univ (fun t : Units R =>
          (chi ^ 5) (t : R) * psi (a * (t : R))) := by
  rw [fixedCuspTransform, inv_pow, inv_inv, <- pow_add]

omit [Fintype R] [Fintype (Units R)] in
/-- Native fifth-power completion retains the quadratic character. A cube
index changes the two-character packet back to chi; this cost cannot be erased. -/
theorem decic_quintic_index_packet (chi : MulChar R Complex)
    (hten : chi ^ 10 = 1) :
    (chi ^ 3) ^ 5 = chi ^ 5 /\
      (chi ^ 5) ^ 2 = 1 /\
      (chi ^ 3) ^ 3 * chi ^ 2 = chi := by
  have hperiod (a : Nat) : chi ^ (10 + a) = chi ^ a := by
    rw [pow_add, hten, one_mul]
  constructor
  . calc
      (chi ^ 3) ^ 5 = chi ^ (10 + 5) := by rw [<- pow_mul]
      _ = chi ^ 5 := hperiod 5
  . constructor
    . calc
        (chi ^ 5) ^ 2 = chi ^ 10 := by rw [<- pow_mul]
        _ = 1 := hten
    . calc
        (chi ^ 3) ^ 3 * chi ^ 2 = chi ^ (10 + 1) := by
          rw [<- pow_mul, <- pow_add]
        _ = chi := by rw [hperiod 1, pow_one]

end MulChar
