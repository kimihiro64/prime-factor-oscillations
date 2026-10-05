import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A countermodel to the scalar low-owner closure

The four labels are prime, cube-rough semiprime, low composite and high
composite. This real matrix is a countermodel to specified scalar
inequalities, not a model of actual primes or of full progression estimates.
-/

set_option autoImplicit false

noncomputable section

namespace PrimeFactorOscillations.LowOwnerMarginal

/-- The four class masses in the scalar low-owner comparison. -/
def mass (c l u : Real) (i : Fin 4) : Real :=
  if i = 0 then 1 else if i = 1 then c else if i = 2 then l else u

/-- A perturbation preserving every row sum. -/
def shift (i : Fin 4) : Real :=
  if i = 0 then 1 else if i = 2 then -1 else 0

/-- A symmetric nonnegative pair matrix with a zero prime-prime entry. -/
def model (k c l u : Real) (i j : Fin 4) : Real :=
  k * (mass c l u i * mass c l u j - shift i * shift j)

/-- Signed prime-minus-semiprime pairing with one class. -/
def signedRow (k c l u : Real) (i : Fin 4) : Real :=
  model k c l u i 0 - model k c l u i 1

/-- The rough signed supply, including all four classes. -/
def roughSigned (k c l u : Real) : Real :=
  signedRow k c l u 0 + signedRow k c l u 1 +
    signedRow k c l u 2 + signedRow k c l u 3

theorem model_symmetric (k c l u : Real) (i j : Fin 4) :
    model k c l u i j = model k c l u j i := by
  unfold model
  ring

theorem mass_nonneg (c l u : Real) (hc : 0 <= c) (hl : 1 <= l)
    (hu : 0 <= u) (i : Fin 4) : 0 <= mass c l u i := by
  fin_cases i <;> norm_num [mass] <;> linarith

theorem model_nonneg (k c l u : Real) (hk : 0 <= k) (hc : 0 <= c)
    (hl : 1 <= l) (hu : 0 <= u) (i j : Fin 4) :
    0 <= model k c l u i j := by
  have hl0 : 0 <= l := by linarith
  have hll : 0 <= l * l - 1 := by nlinarith [sq_nonneg (l - 1)]
  apply mul_nonneg hk
  fin_cases i <;> fin_cases j <;> norm_num [mass, shift]
  all_goals first | positivity | nlinarith [hll]

theorem model_row (k c l u : Real) (i : Fin 4) :
    model k c l u i 0 + model k c l u i 1 +
      model k c l u i 2 + model k c l u i 3 =
        k * (1 + c + l + u) * mass c l u i := by
  fin_cases i <;> norm_num [model, mass, shift] <;> ring

theorem model_zero_target (k c l u : Real) :
    model k c l u 0 0 = 0 := by
  norm_num [model, mass, shift]

private theorem column_inside (c l u : Real) (hc : 0 <= c)
    (hc1 : c <= 7 / 10) (hl : 39 / 10 <= l) (hu : 0 <= u)
    (i : Fin 4) :
    mass c l u i * (1 + c) - shift i <= 2 * mass c l u i := by
  have hl0 : 0 <= l := by linarith
  have hc2 : c <= 1 := by linarith
  have hcc := mul_nonneg hc (sub_nonneg.mpr hc2)
  have hcl := mul_le_mul_of_nonneg_right hc1 hl0
  have hcu := mul_le_mul_of_nonneg_right hc2 hu
  fin_cases i <;> norm_num [mass, shift] <;> nlinarith

theorem model_joint_column_cap (k c l u : Real) (hk : 0 <= k)
    (hk1 : k <= 11 / 10) (hc : 0 <= c) (hc1 : c <= 7 / 10)
    (hl : 39 / 10 <= l) (hu : 0 <= u) (i : Fin 4) :
    model k c l u i 0 + model k c l u i 1 <= 4 * mass c l u i := by
  have hm : 0 <= mass c l u i := mass_nonneg c l u hc (by linarith) hu i
  have hi := column_inside c l u hc hc1 hl hu i
  calc
    model k c l u i 0 + model k c l u i 1 =
        k * (mass c l u i * (1 + c) - shift i) := by
          fin_cases i <;> norm_num [model, mass, shift] <;> ring
    _ <= k * (2 * mass c l u i) := mul_le_mul_of_nonneg_left hi hk
    _ <= (11 / 10) * (2 * mass c l u i) :=
      mul_le_mul_of_nonneg_right hk1 (by positivity)
    _ <= 4 * mass c l u i := by nlinarith

theorem low_signed_gt_threshold (k c l u : Real) (hk : 19 / 20 <= k)
    (hc1 : c <= 7 / 10) (hl : 39 / 10 <= l) :
    5 / 3 < signedRow k c l u 2 := by
  have hp : 0 <= (l - 39 / 10) * (1 - c) :=
    mul_nonneg (sub_nonneg.mpr hl) (by linarith)
  have hi : 217 / 100 <= l * (1 - c) + 1 := by nlinarith
  have hs : 0 <= (k - 19 / 20) * (l * (1 - c) + 1) :=
    mul_nonneg (sub_nonneg.mpr hk) (by linarith)
  have he : signedRow k c l u 2 = k * (l * (1 - c) + 1) := by
    norm_num [signedRow, model, mass, shift]
    ring
  rw [he]
  nlinarith

theorem rough_signed_value (k c l u : Real) :
    roughSigned k c l u = k * (1 + c + l + u) * (1 - c) := by
  norm_num [roughSigned, signedRow, model, mass, shift]
  ring

theorem complete_signed_net_zero (k c l u : Real) :
    roughSigned k c l u + model k c l u 1 1 -
      signedRow k c l u 2 - signedRow k c l u 3 = 0 := by
  norm_num [roughSigned, signedRow, model, mass, shift]
  ring

/-- All scalar conditions coexist with zero target and a low correction above 5/3. -/
theorem countermodel_constraints (k c l u : Real)
    (hk0 : 19 / 20 <= k) (hk1 : k <= 11 / 10)
    (hc0 : 0 <= c) (hc1 : c <= 7 / 10)
    (hl : 39 / 10 <= l) (hu : 0 <= u) :
    (forall i j : Fin 4, 0 <= model k c l u i j) /\
    (forall i j : Fin 4, model k c l u i j = model k c l u j i) /\
    (forall i : Fin 4, model k c l u i 0 + model k c l u i 1 +
      model k c l u i 2 + model k c l u i 3 =
        k * (1 + c + l + u) * mass c l u i) /\
    (forall i : Fin 4, model k c l u i 0 + model k c l u i 1 <=
        4 * mass c l u i) /\
    model k c l u 0 0 = 0 /\
    5 / 3 < signedRow k c l u 2 /\
    roughSigned k c l u + model k c l u 1 1 -
      signedRow k c l u 2 - signedRow k c l u 3 = 0 := by
  have hk : 0 <= k := by linarith
  refine And.intro (model_nonneg k c l u hk hc0 (by linarith) hu) ?_
  refine And.intro (model_symmetric k c l u) ?_
  refine And.intro (model_row k c l u) ?_
  refine And.intro (model_joint_column_cap k c l u hk hk1 hc0 hc1 hl hu) ?_
  refine And.intro (model_zero_target k c l u) ?_
  exact And.intro (low_signed_gt_threshold k c l u hk0 hc1 hl)
    (complete_signed_net_zero k c l u)

end PrimeFactorOscillations.LowOwnerMarginal
