import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Definitions.ReciprocalSmoothLaw
import PrimeFactorOscillations.Helpers.AffineLocalResidues

/-! # The actual affine local residue law is reciprocal-smooth -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.AffineSumFamily

/-- Exact finite exceptions and the rational residue formula give the required
o(1) reciprocal remainder, uniformly over every later prime. -/
theorem localProbability_reciprocal_control (F : AffineSumFamily)
    (epsilon : Real) (he : 0 < epsilon) :
    exists P : Nat, forall p : Nat, P <= p -> Nat.Prime p ->
      abs (1 / F.localProbability p - (p : Real) / F.arity +
        (if (exists i : Fin F.arity, F.shift i = 0) then (1 : Real) else 0) /
          (F.arity : Real) ^ 2) <= epsilon := by
  classical
  choose P0 hP0 using F.eventually_localProbability_formula
  let m : Real := F.arity
  let z : Real := if (exists i : Fin F.arity, F.shift i = 0) then 1 else 0
  let a : Real := (1 - z / m) ^ 2
  have hm : 0 < m := by dsimp only [m]; exact_mod_cast F.arity_pos
  have ha : 0 <= a := sq_nonneg _
  choose P1 hP1 using exists_nat_gt (max 3 (2 + (a / epsilon - z) / m))
  refine Exists.intro (max P0 P1) ?_
  intro p hp hprime
  have hpR : (P1 : Real) <= p := by exact_mod_cast (le_max_right P0 P1).trans hp
  have hp3 : (3 : Real) < p := ((le_max_left _ _).trans_lt hP1).trans_le hpR
  have hlarge : 2 + (a / epsilon - z) / m < (p : Real) :=
    ((le_max_right _ _).trans_lt hP1).trans_le hpR
  have hscaled := mul_lt_mul_of_pos_left hlarge hm
  have hcancel : m * (2 + (a / epsilon - z) / m) = 2 * m + a / epsilon - z := by
    field_simp [ne_of_gt hm, ne_of_gt he]
    ring
  rw [hcancel] at hscaled
  let D : Real := m * p - 2 * m + z
  have hmargin : a / epsilon < D := by dsimp only [D]; linarith only [hscaled]
  have hD : 0 < D := (div_nonneg ha he.le).trans_lt hmargin
  have hnum : m * ((p : Real) - 2) + z = D := by dsimp only [D]; ring
  have hEta : F.localProbability p =
      (m * ((p : Real) - 2) + z) / ((p : Real) - 1) ^ 2 :=
    hP0 p ((le_max_left P0 P1).trans hp) hprime
  have hid : 1 / ((m * ((p : Real) - 2) + z) / ((p : Real) - 1) ^ 2) -
      (p : Real) / m + z / m ^ 2 = a / D := by
    have hpn : Not ((p : Real) - 1 = 0) := by linarith only [hp3]
    have hn : Not (m * ((p : Real) - 2) + z = 0) := by rw [hnum]; exact ne_of_gt hD
    dsimp only [a, D]
    field_simp [ne_of_gt hm, hpn, hn]
    ring
  change abs (1 / F.localProbability p - (p : Real) / m + z / m ^ 2) <= epsilon
  rw [hEta, hid, abs_of_nonneg (div_nonneg ha hD.le)]
  have hscaledE := mul_lt_mul_of_pos_right hmargin he
  have hcancelE : (a / epsilon) * epsilon = a := by field_simp [ne_of_gt he]
  rw [hcancelE] at hscaledE
  have hcancelD : (a / D) * D = a := by field_simp [ne_of_gt hD]
  by_contra hn
  have hbad := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hD
  rw [hcancelD] at hbad
  nlinarith only [hscaledE, hbad]

/-- The reciprocal-smooth law is constructed from the actual all-prime
residue counts. Its dimension is the number of distinct affine forms. -/
noncomputable def reciprocalSmoothLaw (F : AffineSumFamily) : ReciprocalSmoothLaw where
  eta := F.localProbability
  nu := F.arity
  offset := -((if (exists i : Fin F.arity, F.shift i = 0) then (1 : Real) else 0) /
    (F.arity : Real) ^ 2)
  nu_pos := by exact_mod_cast F.arity_pos
  probability := F.localProbability_bounds
  reciprocal_control := by
    intro epsilon he
    simpa only [sub_neg_eq_add] using F.localProbability_reciprocal_control epsilon he

end PrimeFactorOscillations.AffineSumFamily
