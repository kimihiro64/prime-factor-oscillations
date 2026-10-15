/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Residue counts with their exact principal-character center

The finite indexing set may contain repeated output values. Nonunit outputs
are retained, and the principal mass counts precisely the unit outputs.
A common bound for nonprincipal character sums bounds every reduced-residue
discrepancy by the same error.
-/

set_option autoImplicit false
set_option Elab.async false

namespace DirichletCharacter

theorem abs_residue_count_sub_unit_mean_le
    {I : Type*} {N : Nat} [NeZero N] (S : Finset I) (f : I -> ZMod N)
    (a : Units (ZMod N)) (E : Real) (hE : 0 <= E)
    (hBound : forall chi : DirichletCharacter Complex N, Not (chi = 1) ->
      norm (Finset.sum S (fun i => chi (f i))) <= E) :
    abs (((S.filter (fun i => f i = (a : ZMod N))).card : Real) -
      ((S.filter (fun i => IsUnit (f i))).card : Real) / (N.totient : Real)) <= E := by
  classical
  let U : Finset (DirichletCharacter Complex N) := Finset.univ
  let F : DirichletCharacter Complex N -> Complex := fun chi =>
    chi (Inv.inv (a : ZMod N)) * Finset.sum S (fun i => chi (f i))
  let r : Nat := (S.filter (fun i => f i = (a : ZMod N))).card
  let u : Nat := (S.filter (fun i => IsUnit (f i))).card
  have hInvMul : Inv.inv (a : ZMod N) * (a : ZMod N) = 1 :=
    (ZMod.inv_mul_eq_one_of_isUnit a.isUnit (a : ZMod N)).mpr rfl
  have hOneInv : (1 : DirichletCharacter Complex N) (Inv.inv (a : ZMod N)) = 1 := by
    have h := congrArg (fun z => (1 : DirichletCharacter Complex N) z) hInvMul
    simpa only [map_mul, MulChar.one_apply_coe, map_one, mul_one] using h
  have hPrincipal (z : ZMod N) :
      (1 : DirichletCharacter Complex N) z = if IsUnit z then (1 : Complex) else 0 := by
    by_cases hz : IsUnit z
    next =>
      rw [if_pos hz]
      exact MulChar.one_apply_coe hz.unit
    next =>
      rw [if_neg hz]
      exact (1 : DirichletCharacter Complex N).map_nonunit hz
  have hOne : F 1 = (u : Complex) := by
    dsimp [F, u]
    rw [hOneInv, one_mul]
    simp only [hPrincipal, Finset.sum_boole]
  have hAll : Finset.sum U F = (N.totient : Complex) * (r : Complex) := by
    calc
      _ = Finset.sum S (fun i => Finset.sum Finset.univ
          (fun chi : DirichletCharacter Complex N =>
            chi (Inv.inv (a : ZMod N)) * chi (f i))) := by
        dsimp [U, F]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = Finset.sum S (fun i =>
          if (a : ZMod N) = f i then (N.totient : Complex) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact sum_char_inv_mul_char_eq Complex a.isUnit (f i)
      _ = Finset.sum S (fun i => (N.totient : Complex) *
          (if f i = (a : ZMod N) then (1 : Complex) else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases h : f i = (a : ZMod N)
        next => simp [h]
        next => simp [h, Ne.symm h]
      _ = (N.totient : Complex) * (r : Complex) := by
        rw [(Finset.mul_sum S (fun i =>
          if f i = (a : ZMod N) then (1 : Complex) else 0) (N.totient : Complex)).symm]
        simp only [Finset.sum_boole, r]
  have hSplit : Finset.sum (U.erase 1) F + F 1 = Finset.sum U F :=
    Finset.sum_erase_add U F (by simp [U])
  have hCentered : Finset.sum (U.erase 1) F = (N.totient : Complex) * (r : Complex) - (u : Complex) := by
    rw [hOne, hAll] at hSplit
    exact eq_sub_iff_add_eq.mpr hSplit
  have hCard : U.card = N.totient := by
    simpa only [U, Finset.card_univ, Nat.card_eq_fintype_card] using
      card_eq_totient_of_hasEnoughRootsOfUnity Complex N
  have hTerm : forall chi, Membership.mem (U.erase 1) chi -> norm (F chi) <= E := by
    intro chi hchi
    dsimp [F]
    rw [norm_mul]
    calc
      _ <= 1 * E := mul_le_mul (chi.norm_le_one _)
        (hBound chi (Finset.mem_erase.mp hchi).1) (norm_nonneg _) zero_le_one
      _ = E := one_mul _
  have hCount : ((U.erase 1).card : Real) <= (N.totient : Real) := by
    apply Nat.cast_le.mpr
    calc
      _ <= U.card := Finset.card_le_card (Finset.erase_subset _ _)
      _ = N.totient := hCard
  have hNorm : norm (Finset.sum (U.erase 1) F) <= (N.totient : Real) * E := by
    calc
      _ <= Finset.sum (U.erase 1) (fun chi => norm (F chi)) := norm_sum_le _ _
      _ <= Finset.sum (U.erase 1) (fun _ => E) := Finset.sum_le_sum hTerm
      _ = ((U.erase 1).card : Real) * E := by simp
      _ <= (N.totient : Real) * E := mul_le_mul_of_nonneg_right hCount hE
  have hPhiNat : 0 < N.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hPhi : 0 < (N.totient : Real) := Nat.cast_pos.mpr hPhiNat
  have hPhiC : Not ((N.totient : Complex) = 0) := by exact_mod_cast hPhiNat.ne'
  have hIdentity : (r : Complex) - (u : Complex) / (N.totient : Complex) =
      Finset.sum (U.erase 1) F / (N.totient : Complex) := by
    rw [hCentered]
    field_simp [hPhiC]
  have hDenom : norm (N.totient : Complex) = (N.totient : Real) := by simp
  have hNormalized : norm ((r : Complex) - (u : Complex) / (N.totient : Complex)) <= E := by
    rw [hIdentity, norm_div, hDenom]
    calc
      _ <= ((N.totient : Real) * E) / (N.totient : Real) :=
        div_le_div_of_nonneg_right hNorm hPhi.le
      _ = E := by field_simp [hPhi.ne']
  have hCast : (((r : Real) - (u : Real) / (N.totient : Real) : Real) : Complex) =
      (r : Complex) - (u : Complex) / (N.totient : Complex) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [hCast.symm] at hNormalized
  simpa only [Complex.norm_real, Real.norm_eq_abs, r, u] using hNormalized

end DirichletCharacter
