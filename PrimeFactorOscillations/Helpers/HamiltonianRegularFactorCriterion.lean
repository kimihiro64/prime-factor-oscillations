/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
import PrimeFactorOscillations.Helpers.HamiltonianFactorIncidence

/-!
# Regular factors from near regularity and the complete cut bound

Both orientations of the degree balance are combined with the same full cut.
No separate absolute-value estimate is applied to either crossing count.
-/

set_option autoImplicit false
set_option Elab.async false

open Finset

theorem hamiltonian_factor_coupled_scalar
    (D g eps a b x u r : Real)
    (hD : 0 < D) (hg : 0 < g) (heps : 0 <= eps) (hepsg : eps < g / 2)
    (ha : 0 <= a) (hb : 0 <= b) (hu : 0 <= u) (hr0 : 0 <= r)
    (hr : r <= (1 - 2 * eps / g) * D)
    (hcut : g * D * u <= a + b)
    (hbalance : D * x - eps * D * u <= a - b) :
    r * x <= a := by
  by_cases hx : x <= 0
  . exact (mul_nonpos_of_nonneg_of_nonpos hr0 hx).trans ha
  . have hx0 : 0 <= x := le_of_lt (lt_of_not_ge hx)
    have hg0 : 0 <= g := le_of_lt hg
    have hD0 : 0 <= D := le_of_lt hD
    have hmain : (g - 2 * eps) * D * x <= g * a := by
      by_cases hxu : x <= (g - eps) * u
      . have hxD := mul_le_mul_of_nonneg_left hxu hD0
        have hax : D * x <= a := by nlinarith only [hcut, hbalance, hxD]
        have hga := mul_le_mul_of_nonneg_left hax hg0
        have hgain : 0 <= (2 * eps) * (D * x) :=
          mul_nonneg (by linarith) (mul_nonneg hD0 hx0)
        nlinarith only [hga, hgain]
      . have hge : 0 <= g - 2 * eps := by linarith
        have hgu : g * u <= 2 * x := by
          nlinarith only [hxu, mul_nonneg hge hu]
        have hfirst : D * x - eps * D * u <= a := by
          linarith only [hbalance, hb]
        have hga := mul_le_mul_of_nonneg_left hfirst hg0
        have hsave := mul_le_mul_of_nonneg_left hgu (mul_nonneg heps hD0)
        nlinarith only [hga, hsave]
    have hratio : g * ((1 - 2 * eps / g) * D) = (g - 2 * eps) * D := by
      have hcancel : g * (2 * eps / g) = 2 * eps := by
        have hdiv : 2 * eps = (2 * eps / g) * g :=
          (div_eq_iff (ne_of_gt hg)).mp rfl
        simpa only [mul_comm] using hdiv.symm
      calc
        g * ((1 - 2 * eps / g) * D) = (g - g * (2 * eps / g)) * D := by ring
        _ = (g - 2 * eps) * D := by rw [hcancel]
    have hgr := mul_le_mul_of_nonneg_left hr hg0
    rw [hratio] at hgr
    have hgrx := mul_le_mul_of_nonneg_right hgr hx0
    have hfinal : g * (r * x) <= g * a := by nlinarith only [hgrx, hmain]
    exact le_of_not_gt (fun hax =>
      (not_lt_of_ge hfinal) (mul_lt_mul_of_pos_left hax hg))

universe u v

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]

theorem hamiltonian_regular_factor_from_cuts
    (E : Finset (Prod A B)) (r : Nat)
    (hAB : Fintype.card A = Fintype.card B)
    (D g eps : Real) (hD : 0 < D) (hg : 0 < g)
    (heps : 0 <= eps) (hepsg : eps < g / 2)
    (hr : (r : Real) <= (1 - 2 * eps / g) * D)
    (hleft : forall a,
      (1 - eps) * D <=
        hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.1) {a} /\
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.1) {a} <=
        (1 + eps) * D)
    (hright : forall b,
      (1 - eps) * D <=
        hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.2) {b} /\
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.2) {b} <=
        (1 + eps) * D)
    (hcut : forall (S : Finset A) (T : Finset B),
      g * D * min ((S.card : Real) + (T.card : Real))
        (((Compl.compl S).card : Real) + ((Compl.compl T).card : Real)) <=
      ((hamiltonianFactorCross E S T).card : Real) +
        ((hamiltonianFactorCross E (Compl.compl S) (Compl.compl T)).card : Real)) :
    Exists (fun F : Finset (Prod A B) =>
      F <= E /\
      (forall a, (F.filter (fun e => e.1 = a)).card = r) /\
      (forall b, (F.filter (fun e => e.2 = b)).card = r)) := by
  apply hamiltonian_bipartite_regular_factor E r hAB
  intro S T
  have hbal1 := hamiltonian_factor_cross_degree_difference E S T D eps hleft hright
  have hbal2 := hamiltonian_factor_cross_complement_difference E S T hAB D eps hleft hright
  have hbal :
      D * ((S.card : Real) - (T.card : Real)) -
        eps * D * min ((S.card : Real) + (T.card : Real))
          (((Compl.compl S).card : Real) + ((Compl.compl T).card : Real)) <=
      ((hamiltonianFactorCross E S T).card : Real) -
        ((hamiltonianFactorCross E (Compl.compl S) (Compl.compl T)).card : Real) := by
    rcases le_total ((S.card : Real) + (T.card : Real))
        (((Compl.compl S).card : Real) + ((Compl.compl T).card : Real)) with h | h
    . simpa only [min_eq_left h] using hbal1
    . simpa only [min_eq_right h] using hbal2
  have hu : 0 <= min ((S.card : Real) + (T.card : Real))
      (((Compl.compl S).card : Real) + ((Compl.compl T).card : Real)) :=
    le_min (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hs := hamiltonian_factor_coupled_scalar D g eps
    ((hamiltonianFactorCross E S T).card : Real)
    ((hamiltonianFactorCross E (Compl.compl S) (Compl.compl T)).card : Real)
    ((S.card : Real) - (T.card : Real))
    (min ((S.card : Real) + (T.card : Real))
      (((Compl.compl S).card : Real) + ((Compl.compl T).card : Real)))
    (r : Real) hD hg heps hepsg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hu (Nat.cast_nonneg _) hr (hcut S T) hbal
  have hcast : ((r * S.card : Nat) : Real) <=
      (((hamiltonianFactorCross E S T).card + r * T.card : Nat) : Real) := by
    simp only [Nat.cast_mul, Nat.cast_add]
    nlinarith only [hs]
  exact_mod_cast hcast
