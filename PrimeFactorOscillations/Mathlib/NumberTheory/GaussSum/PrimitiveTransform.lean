/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.CharacterTwist
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.FiniteRingEnergy

/-!
# Primitive finite-ring Gauss transforms

A concrete unit-stabilizer condition forces nonunit-frequency vanishing and
extends Gauss scaling to every frequency. Full-ring Parseval then proves the
exact squared magnitude. Nontriviality on each individual factor verifies the
condition on products of fields, as required after squarefree CRT reduction.

The fixed-cusp inverse-quartic transform is evaluated without erasing any
frequency, and its normalized two-Gauss factor has squared modulus one.
Gaussian residue characters, reciprocity, theta automorphy and analytic moment
estimates are not constructed or assumed here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace MulChar

variable {R : Type*} [CommRing R] [Fintype R]

/-- A nontrivial character on a unit stabilizer forces the shifted Gauss sum to vanish. -/
theorem gaussSum_mulShift_zero_of_unit_stabilizer (chi : MulChar R Complex)
    (psi : AddChar R Complex) (a : R) (u : Units R)
    (hau : a * (u : R) = a) (hu : Not (chi (u : R) = 1)) :
    gaussSum chi (psi.mulShift a) = 0 := by
  have hshift : (psi.mulShift a).mulShift (u : R) = psi.mulShift a := by
    ext x
    simp only [AddChar.mulShift_apply]
    rw [<- mul_assoc, hau]
  have hs := gaussSum_mulShift_eq chi (psi.mulShift a) u
  rw [hshift] at hs
  have hprod : chi (u : R) * (Inv.inv chi) (u : R) = 1 := by
    rw [<- MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
  have hscale : chi (u : R) * gaussSum chi (psi.mulShift a) =
      gaussSum chi (psi.mulShift a) := by
    calc
      _ = chi (u : R) * ((Inv.inv chi) (u : R) *
          gaussSum chi (psi.mulShift a)) := congrArg (fun z : Complex => chi (u : R) * z) hs
      _ = _ := by rw [<- mul_assoc, hprod, one_mul]
  have hz : (chi (u : R) - 1) * gaussSum chi (psi.mulShift a) = 0 := by
    rw [sub_mul, one_mul, hscale, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (fun h => hu (sub_eq_zero.mp h))

/-- Unit scaling extends to all frequencies if each nonunit has a nontrivial
character value on its unit stabilizer. This is an explicit finite condition. -/
theorem gaussSum_mulShift_eq_of_nonunit_stabilizers (chi : MulChar R Complex)
    (hsep : forall a : R, Not (IsUnit a) ->
      Exists fun u : Units R => And (a * (u : R) = a) (Not (chi (u : R) = 1)))
    (psi : AddChar R Complex) (a : R) :
    gaussSum chi (psi.mulShift a) =
      (Inv.inv chi) a * gaussSum chi psi := by
  classical
  by_cases ha : IsUnit a
  . cases ha with
    | intro u hu =>
      rw [<- hu]
      exact gaussSum_mulShift_eq chi psi u
  . choose u hau hu using hsep a ha
    rw [gaussSum_mulShift_zero_of_unit_stabilizer chi psi a u hau hu,
      (Inv.inv chi).map_nonunit ha, zero_mul]

/-- Inversion of a finite-ring character preserves the squared magnitude at every point. -/
theorem normSq_inverse_apply (chi : MulChar R Complex) (a : R) :
    Complex.normSq ((Inv.inv chi) a) = Complex.normSq (chi a) := by
  by_cases ha : IsUnit a
  . cases ha with
    | intro u hu =>
      rw [<- hu, normSq_apply_unit, normSq_apply_unit]
  . rw [chi.map_nonunit ha, (Inv.inv chi).map_nonunit ha]

/-- The squared coefficient mass of a character is positive because its value at one is one. -/
theorem sum_normSq_apply_pos (chi : MulChar R Complex) :
    0 < Finset.sum Finset.univ (fun a : R => Complex.normSq (chi a)) := by
  have hle : Complex.normSq (chi (1 : R)) <=
      Finset.sum Finset.univ (fun a : R => Complex.normSq (chi a)) :=
    Finset.single_le_sum (fun a _ => Complex.normSq_nonneg (chi a))
      (Finset.mem_univ (1 : R))
  have hone : Complex.normSq (chi (1 : R)) = 1 := by simp
  rw [hone] at hle
  exact lt_of_lt_of_le zero_lt_one hle

/-- Full-ring Parseval yields the exact Gauss magnitude under the nonunit
stabilizer condition, without assuming a field or squarefree modulus. -/
theorem normSq_gaussSum_of_nonunit_stabilizers (chi : MulChar R Complex)
    (hsep : forall a : R, Not (IsUnit a) ->
      Exists fun u : Units R => And (a * (u : R) = a) (Not (chi (u : R) = 1)))
    (psi : AddChar R Complex) (hpsi : psi.IsPrimitive) :
    Complex.normSq (gaussSum chi psi) = (Fintype.card R : Real) := by
  have hparseval := AddChar.sum_normSq_fourier_injective psi hpsi
    (fun a : R => a) (fun _ _ h => h) (fun a : R => chi a)
  change Finset.sum Finset.univ (fun a : R =>
    Complex.normSq (gaussSum chi (psi.mulShift a))) = _ at hparseval
  simp_rw [gaussSum_mulShift_eq_of_nonunit_stabilizers chi hsep,
    map_mul, normSq_inverse_apply] at hparseval
  rw [<- Finset.sum_mul] at hparseval
  have hmass := sum_normSq_apply_pos chi
  have hz :
      (Finset.sum Finset.univ (fun a : R => Complex.normSq (chi a))) *
        (Complex.normSq (gaussSum chi psi) - (Fintype.card R : Real)) = 0 := by
    rw [mul_sub, hparseval, mul_comm (Fintype.card R : Real), sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt hmass))

omit [Fintype R] in
/-- A nonprincipal character has a nontrivial value on a unit. -/
theorem exists_unit_ne_one_of_ne_one (chi : MulChar R Complex) (hchi : Not (chi = 1)) :
    Exists fun u : Units R => Not (chi (u : R) = 1) := by
  classical
  by_contra h
  apply hchi
  apply MulChar.ext
  intro u
  rw [MulChar.one_apply_coe]
  by_contra hu
  exact h (Exists.intro u hu)

/-- Over a field a nonprincipal character satisfies the nonunit stabilizer condition. -/
theorem nonunit_stabilizers_of_field {F : Type*} [Field F]
    (chi : MulChar F Complex) (hchi : Not (chi = 1)) :
    forall a : F, Not (IsUnit a) ->
      Exists fun u : Units F => And (a * (u : F) = a) (Not (chi (u : F) = 1)) := by
  intro a ha
  have ha0 : a = 0 := by
    by_contra h
    exact ha (isUnit_iff_ne_zero.mpr h)
  choose u hu using exists_unit_ne_one_of_ne_one chi hchi
  exact Exists.intro u (And.intro (by rw [ha0, zero_mul]) hu)

/-- On a product of fields, a nontrivial character on every individual unit factor
supplies the needed witness at each nonunit. This is the squarefree CRT criterion. -/
theorem nonunit_stabilizers_of_pi_fields {I : Type*} [DecidableEq I] {F : I -> Type*}
    [forall i, Field (F i)] (chi : MulChar (forall i, F i) Complex)
    (hlocal : forall i : I, Exists fun u : Units (F i) =>
      Not (chi (Function.update (1 : forall i, F i) i (u : F i)) = 1)) :
    forall a : (forall i, F i), Not (IsUnit a) ->
      Exists fun u : Units (forall i, F i) =>
        And (a * (u : forall i, F i) = a) (Not (chi (u : forall i, F i) = 1)) := by
  classical
  intro a ha
  have hz : Exists fun i : I => a i = 0 := by
    by_contra hn
    have hnz (i : I) : Not (a i = 0) := fun hi => hn (Exists.intro i hi)
    let v : Units (forall i, F i) :=
      { val := a
        inv := fun i => Inv.inv (a i)
        val_inv := by
          funext i
          change a i * Inv.inv (a i) = 1
          field_simp [hnz i]
        inv_val := by
          funext i
          change Inv.inv (a i) * a i = 1
          field_simp [hnz i] }
    exact ha (Exists.intro v rfl)
  choose i hi using hz
  choose ui hui using hlocal i
  let u : Units (forall i, F i) :=
    { val := Function.update (1 : forall i, F i) i (ui : F i)
      inv := Function.update (1 : forall i, F i) i ((Inv.inv ui : Units (F i)) : F i)
      val_inv := by
        funext j
        by_cases hj : j = i
        . subst j; simp
        . simp [Function.update, hj]
      inv_val := by
        funext j
        by_cases hj : j = i
        . subst j; simp
        . simp [Function.update, hj] }
  refine Exists.intro u (And.intro ?_ hui)
  funext j
  by_cases hj : j = i
  . subst j; simp [u, hi]
  . simp [u, Function.update, hj]

/-- Multiplicative characters vanish off the units, so the complete Gauss sum
can be reindexed by units without a primitivity assumption. -/
theorem gaussSum_eq_unit_sum [Fintype (Units R)] (chi : MulChar R Complex)
    (psi : AddChar R Complex) :
    gaussSum chi psi = Finset.sum Finset.univ
      (fun u : Units R => chi (u : R) * psi (u : R)) := by
  classical
  have hfull :
      Finset.sum (Finset.univ.filter (fun a : R => IsUnit a)) (fun a => chi a * psi a) =
        Finset.sum Finset.univ (fun a : R => chi a * psi a) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a ha hn
    have hnu : Not (IsUnit a) := fun hu => hn (Finset.mem_filter.mpr (And.intro ha hu))
    rw [chi.map_nonunit hnu, zero_mul]
  unfold gaussSum
  rw [<- hfull]
  symm
  refine Finset.sum_bij (fun u _ => (u : R)) ?_ ?_ ?_ ?_
  . intro u _
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) u.isUnit)
  . intro u _ v _ huv
    exact Units.ext huv
  . intro a ha
    cases (Finset.mem_filter.mp ha).2 with
    | intro u hu => exact Exists.intro u (Exists.intro (Finset.mem_univ _) hu)
  . intro u _
    rfl

omit [Fintype R] in
/-- Nontriviality on stabilizers for a character power implies it for the character. -/
theorem nonunit_stabilizers_of_pow (chi : MulChar R Complex) (n : Nat)
    (hsep : forall a : R, Not (IsUnit a) ->
      Exists fun u : Units R => And (a * (u : R) = a) (Not ((chi ^ n) (u : R) = 1))) :
    forall a : R, Not (IsUnit a) ->
      Exists fun u : Units R => And (a * (u : R) = a) (Not (chi (u : R) = 1)) := by
  intro a ha
  choose u hau hu using hsep a ha
  refine Exists.intro u (And.intro hau ?_)
  intro h
  apply hu
  rw [MulChar.pow_apply_coe, h, one_pow]

omit [Fintype R] in
/-- Inverting both the unit witness and the character preserves primitivity witnesses. -/
theorem nonunit_stabilizers_inv (chi : MulChar R Complex)
    (hsep : forall a : R, Not (IsUnit a) ->
      Exists fun u : Units R => And (a * (u : R) = a) (Not (chi (u : R) = 1))) :
    forall a : R, Not (IsUnit a) ->
      Exists fun u : Units R => And (a * (u : R) = a) (Not ((Inv.inv chi) (u : R) = 1)) := by
  intro a ha
  choose u hau hu using hsep a ha
  refine Exists.intro (Inv.inv u) (And.intro ?_ ?_)
  . calc
      a * ((Inv.inv u : Units R) : R) =
          (a * (u : R)) * ((Inv.inv u : Units R) : R) := by rw [hau]
      _ = a := by rw [mul_assoc]; simp
  . simpa only [apply_inv_unit_eq_inverse, inv_inv] using hu

/-- Under the explicit composite primitivity condition, the fixed-cusp transform
is evaluated at every frequency, including zero and nonunits. -/
theorem fixedCuspTransform_inverse_quartic_eval [Fintype (Units R)]
    (chi : MulChar R Complex) (hfour : chi ^ 4 = 1)
    (hsep : forall a : R, Not (IsUnit a) ->
      Exists fun u : Units R => And (a * (u : R) = a) (Not ((chi ^ 2) (u : R) = 1)))
    (psi : AddChar R Complex) (a : R) :
    Finset.sum Finset.univ (fun h : Units R =>
      gaussSum (Inv.inv chi) (psi.mulShift (-(h : R))) * chi (h : R) *
        psi (a * ((Inv.inv h : Units R) : R))) =
      gaussSum (Inv.inv chi) (psi.mulShift (-1)) *
        gaussSum (chi ^ 2) psi * (chi ^ 2) a := by
  have hinv : Inv.inv (chi ^ 2) = chi ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    calc
      chi ^ 2 * chi ^ 2 = chi ^ (2 + 2) := (pow_add chi 2 2).symm
      _ = 1 := hfour
  have hsum := gaussSum_eq_unit_sum (chi ^ 2) (psi.mulShift a)
  change gaussSum (chi ^ 2) (psi.mulShift a) =
    Finset.sum Finset.univ (fun t : Units R => (chi ^ 2) (t : R) * psi (a * (t : R))) at hsum
  rw [fixedCuspTransform_inverse_quartic chi hfour, <- hsum,
    gaussSum_mulShift_eq_of_nonunit_stabilizers (chi ^ 2) hsep, hinv]
  ring

/-- The normalized two-Gauss reflection factor has exact squared modulus one. -/
theorem normSq_fixedCuspReflectionFactor (chi : MulChar R Complex)
    (hsep : forall a : R, Not (IsUnit a) ->
      Exists fun u : Units R => And (a * (u : R) = a) (Not ((chi ^ 2) (u : R) = 1)))
    (psi : AddChar R Complex) (hpsi : psi.IsPrimitive) :
    Complex.normSq ((gaussSum (Inv.inv chi) (psi.mulShift (-1)) *
      gaussSum (chi ^ 2) psi) / (Fintype.card R : Complex)) = 1 := by
  have hi := nonunit_stabilizers_inv chi (nonunit_stabilizers_of_pow chi 2 hsep)
  have hneg : Complex.normSq (gaussSum (Inv.inv chi) (psi.mulShift (-1))) =
      (Fintype.card R : Real) := by
    rw [gaussSum_mulShift_eq_of_nonunit_stabilizers (Inv.inv chi) hi, inv_inv, map_mul,
      normSq_gaussSum_of_nonunit_stabilizers (Inv.inv chi) hi psi hpsi]
    have hu := normSq_apply_unit chi (-1 : Units R)
    simpa using congrArg (fun z : Real => z * (Fintype.card R : Real)) hu
  have hc : Not ((Fintype.card R : Real) = 0) := by exact_mod_cast Fintype.card_ne_zero
  rw [Complex.normSq_div, map_mul, hneg,
    normSq_gaussSum_of_nonunit_stabilizers (chi ^ 2) hsep psi hpsi,
    Complex.normSq_natCast]
  field_simp [hc]

section

variable [Fintype (Units R)]

/-- The character of the evaluated frequency is chi / omega; omega / chi
is the character inside the intermediate Gauss transform. -/
theorem fixedCuspTransform_eval (omega chi : MulChar R Complex)
    (hsep : forall a : R, Not (IsUnit a) ->
      Exists fun u : Units R => And (a * (u : R) = a)
        (Not ((omega * Inv.inv chi) (u : R) = 1)))
    (psi : AddChar R Complex) (a : R) :
    Finset.sum Finset.univ (fun h : Units R =>
      gaussSum omega (psi.mulShift (-(h : R))) * chi (h : R) *
        psi (a * ((Inv.inv h : Units R) : R))) =
      gaussSum omega (psi.mulShift (-1)) * gaussSum (omega * Inv.inv chi) psi *
        (chi * Inv.inv omega) a := by
  have hinv : Inv.inv (omega * Inv.inv chi) = chi * Inv.inv omega := by
    apply inv_eq_of_mul_eq_one_right
    simp [mul_assoc, mul_left_comm, mul_comm]
  have hsum := gaussSum_eq_unit_sum (omega * Inv.inv chi) (psi.mulShift a)
  change gaussSum (omega * Inv.inv chi) (psi.mulShift a) =
    Finset.sum Finset.univ (fun t : Units R =>
      (omega * Inv.inv chi) (t : R) * psi (a * (t : R))) at hsum
  rw [fixedCuspTransform, <- hsum,
    gaussSum_mulShift_eq_of_nonunit_stabilizers (omega * Inv.inv chi) hsep, hinv]
  ring

/-- Quadratic input under the quartic cusp multiplier gives an inverse-quartic
frequency character, as occurs on the square rows of the zero detector. -/
theorem fixedCuspTransform_quadratic_input_eval (chi : MulChar R Complex)
    (hsep : forall a : R, Not (IsUnit a) ->
      Exists fun u : Units R => And (a * (u : R) = a) (Not (chi (u : R) = 1)))
    (psi : AddChar R Complex) (a : R) :
    Finset.sum Finset.univ (fun h : Units R =>
      gaussSum (chi ^ 2) (psi.mulShift (-(h : R))) * chi (h : R) *
        psi (a * ((Inv.inv h : Units R) : R))) =
      gaussSum (chi ^ 2) (psi.mulShift (-1)) * gaussSum chi psi * (Inv.inv chi) a := by
  have hdelta : chi ^ 2 * Inv.inv chi = chi := by simp [pow_two, mul_assoc]
  have hfreq : chi * Inv.inv (chi ^ 2) = Inv.inv chi := by
    rw [<- inv_pow, pow_two, <- mul_assoc, mul_inv_cancel, one_mul]
  have hsep' : forall x : R, Not (IsUnit x) ->
      Exists fun u : Units R => And (x * (u : R) = x)
        (Not ((chi ^ 2 * Inv.inv chi) (u : R) = 1)) := by
    simpa only [hdelta] using hsep
  rw [fixedCuspTransform_eval (chi ^ 2) chi hsep', hdelta, hfreq]

omit [Fintype R] [Fintype (Units R)] in
/-- A genuinely nonquadratic input character stays nonquadratic after inversion. -/
theorem inverse_not_quadratic (chi : MulChar R Complex) (htwo : Not (chi ^ 2 = 1)) :
    Not ((Inv.inv chi) ^ 2 = 1) := by
  intro h
  apply htwo
  rw [inv_pow] at h
  simpa only [inv_eq_one] using h

omit [Fintype R] [Fintype (Units R)] in
/-- No fixed scalar multiplier can make both inverse-quartic and quadratic
inputs have quadratic evaluated frequency characters. This does not rule out
a coupled multi-component argument or separate estimates for the two sectors. -/
theorem not_both_quadratic_reflected_inputs (chi kappa : MulChar R Complex)
    (hfour : chi ^ 4 = 1) (htwo : Not (chi ^ 2 = 1)) :
    Not (And ((kappa * Inv.inv (Inv.inv chi)) ^ 2 = 1)
      ((kappa * Inv.inv (chi ^ 2)) ^ 2 = 1)) := by
  intro h
  have hc : (Inv.inv (chi ^ 2)) ^ 2 = 1 := by
    rw [inv_pow, <- pow_mul]
    change Inv.inv (chi ^ 4) = 1
    rw [hfour, inv_one]
  have hk : kappa ^ 2 = 1 := by
    simpa only [mul_pow, hc, mul_one] using h.2
  apply htwo
  simpa only [inv_inv, mul_pow, hk, one_mul] using h.1


end

end MulChar
