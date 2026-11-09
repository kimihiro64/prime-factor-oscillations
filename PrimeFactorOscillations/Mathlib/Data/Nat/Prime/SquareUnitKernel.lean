/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.FinitePiProduct
import PrimeFactorOscillations.Mathlib.Data.Nat.Prime.SquareResidues

/-! # The signed kernel on odd prime-square unit coordinates

The binary coordinate retains the modulus-four mode. Every odd coordinate
has exactly p*(p-1) units, and its actual residue-inequality kernel is
identified pointwise with the finite dependent-product model.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace Nat

def primeSquareUnitDensity {I : Type} [Fintype I] (p : I -> Nat) : Real :=
  Finset.univ.prod (fun i => 1 - 1 / (((p i) * (p i - 1) : Nat) : Real)) / 2

def primeSquareUnitKernel {I : Type} (p : I -> Nat)
    (x y : Prod Bool ((i : I) -> Units (ZMod ((p i) ^ 2)))) : Real := by
  classical
  exact if x.1 = y.1 then 0 else
    if forall i, Not ((x.2 i).val = (y.2 i).val) then 1 else 0

private theorem primeSquare_unit_card (q : Nat) [NeZero (q ^ 2)] (hq : Nat.Prime q) :
    Fintype.card (Units (ZMod (q ^ 2))) = q * (q - 1) := by
  rw [ZMod.card_units_eq_totient]
  simpa using Nat.totient_prime_pow hq (show 0 < 2 from by decide)

private theorem primeSquare_unit_card_ge_six (q : Nat) [NeZero (q ^ 2)]
    (hq : Nat.Prime q) (h3 : 3 <= q) :
    6 <= Fintype.card (Units (ZMod (q ^ 2))) := by
  rw [primeSquare_unit_card q hq]
  exact Nat.mul_le_mul h3 (Nat.sub_le_sub_right h3 1)

private theorem primeSquare_unit_density_eq {I : Type} [Fintype I] (p : I -> Nat)
    [forall i, NeZero ((p i) ^ 2)] (hp : forall i, Nat.Prime (p i))
    (h3 : forall i, 3 <= p i) :
    primeSquareUnitDensity p =
      Finset.completePiDensity (fun i => Units (ZMod ((p i) ^ 2))) / 2 := by
  classical
  unfold primeSquareUnitDensity Finset.completePiDensity
  apply congrArg (fun x : Real => x / 2)
  apply Finset.prod_congr rfl
  intro i hi
  rw [primeSquare_unit_card (p i) (hp i)]
  have hPosNat : 0 < p i * (p i - 1) :=
    lt_of_lt_of_le (show 0 < 6 from by decide)
      (Nat.mul_le_mul (h3 i) (Nat.sub_le_sub_right (h3 i) 1))
  have hPos : (0 : Real) < ((p i * (p i - 1) : Nat) : Real) := by
    exact_mod_cast hPosNat
  rw [_root_.sub_div, _root_.div_self (_root_.ne_of_gt hPos)]

open scoped Classical in
theorem prime_square_unit_density_bounds {I : Type} [Fintype I] (p : I -> Nat)
    [forall i, NeZero ((p i) ^ 2)] (hp : forall i, Nat.Prime (p i))
    (h3 : forall i, 3 <= p i) :
    0 < primeSquareUnitDensity p /\ primeSquareUnitDensity p <= 1 / 2 := by
  have h := Finset.completePiDensity_bounds
    (fun i => Units (ZMod ((p i) ^ 2)))
    (fun i => primeSquare_unit_card_ge_six (p i) (hp i) (h3 i))
  rw [primeSquare_unit_density_eq p hp h3]
  constructor
  { exact _root_.div_pos h.1 _root_.zero_lt_two }
  { exact _root_.div_le_div_of_nonneg_right h.2 (_root_.le_of_lt _root_.zero_lt_two) }

open scoped Classical in
theorem prime_square_unit_binary_gap {I : Type} [Fintype I] (p : I -> Nat)
    [forall i, NeZero ((p i) ^ 2)] (hp : forall i, Nat.Prime (p i))
    (h3 : forall i, 3 <= p i)
    (f : Prod Bool ((i : I) -> Units (ZMod ((p i) ^ 2))) -> Real) :
    abs (Finset.kernelBilinear Finset.univ (primeSquareUnitKernel p) f f -
      primeSquareUnitDensity p *
        ((Finset.univ.sum f) ^ 2 -
          (Finset.univ.sum (fun x => Finset.binaryProductSign x * f x)) ^ 2)) <=
      primeSquareUnitDensity p / 5 *
        (((Finset.univ : Finset (Prod Bool ((i : I) -> Units (ZMod ((p i) ^ 2))))).card : Real) *
            Finset.univ.sum (fun x => (f x) ^ 2) -
          (Finset.univ.sum f) ^ 2 -
          (Finset.univ.sum (fun x => Finset.binaryProductSign x * f x)) ^ 2) := by
  classical
  have h := Finset.kernelBilinear_complete_pi_binary_gap
    (fun i => Units (ZMod ((p i) ^ 2)))
    (fun i => primeSquare_unit_card_ge_six (p i) (hp i) (h3 i)) f
  have hKernel :
      Finset.rawCompleteCoordinateKernel
        (Finset.allDifferentPiKernel (fun i => Units (ZMod ((p i) ^ 2)))) =
        primeSquareUnitKernel p := by
    funext x y
    by_cases hxy : x.1 = y.1
    { simp [Finset.rawCompleteCoordinateKernel, primeSquareUnitKernel, hxy] }
    { by_cases hc : forall i, Not (x.2 i = y.2 i)
      { have hv : forall i, Not ((x.2 i).val = (y.2 i).val) := by
          intro i hi
          exact hc i (Units.ext hi)
        simp [Finset.rawCompleteCoordinateKernel, Finset.allDifferentPiKernel,
          primeSquareUnitKernel, hxy, hc, hv] }
      { have hv : Not (forall i, Not ((x.2 i).val = (y.2 i).val)) := by
          intro hval
          apply hc
          intro i hi
          exact hval i (congrArg (fun u : Units (ZMod ((p i) ^ 2)) => u.val) hi)
        simp [Finset.rawCompleteCoordinateKernel, Finset.allDifferentPiKernel,
          primeSquareUnitKernel, hxy, hc, hv] } }
  rw [hKernel, <- primeSquare_unit_density_eq p hp h3] at h
  exact h

end Nat

namespace ZMod

private theorem unitsFour_cases (u : Units (ZMod 4)) :
    Or (u = 1) (u = -1) := by
  have h : forall v : Units (ZMod 4), Or (v = 1) (v = -1) := by decide
  exact h u

/-- The two actual reduced classes modulo four, with the negative unit
corresponding to the negative binary mode. -/
def unitsFourEquivBool : Equiv (Units (ZMod 4)) Bool where
  toFun u := decide (u = -1)
  invFun b := if b then -1 else 1
  left_inv u := by
    cases unitsFour_cases u with
    | inl h => subst u; decide
    | inr h => subst u; decide
  right_inv b := by
    cases b <;> decide

theorem unitsFourEquivBool_eq_iff (u v : Units (ZMod 4)) :
    unitsFourEquivBool u = unitsFourEquivBool v <-> u.val = v.val := by
  constructor
  { intro h
    exact congrArg (fun w : Units (ZMod 4) => w.val) (unitsFourEquivBool.injective h) }
  { intro h
    exact congrArg unitsFourEquivBool (Units.ext h) }

def unitsFourSign (u : Units (ZMod 4)) : Real :=
  if u.val = 1 then 1 else -1

theorem unitsFourSign_eq_binary (u : Units (ZMod 4)) :
    unitsFourSign u = if unitsFourEquivBool u then -1 else 1 := by
  cases unitsFour_cases u with
  | inl h => subst u; rfl
  | inr h => subst u; rfl

theorem unitsFourEquivBool_symm_val (b : Bool) :
    (unitsFourEquivBool.symm b).val = if b then (3 : ZMod 4) else 1 := by
  cases b <;> rfl

end ZMod
