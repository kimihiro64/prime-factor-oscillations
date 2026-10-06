/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Data.Nat.Prime.FactorialCrossing

/-!
# Strictly separated prime steps in three-window cells

In each cell of length 10h, a prime in its left window and one in its
middle window cross a fixed factorial composite barrier. The crossing
gives a long prime step before a selected pair in the right window.
Different cells give strictly separated closed witness intervals.

The theorem is finite: it retains the three prime-window hypotheses and
the exact spacing condition h >= L! + 2. No short-interval prime supply
or limiting density is assumed implicitly.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

/-- Three occupied windows in every cell force ordered long/short steps,
with strict separation between successive selected witnesses. -/
theorem separated_gap_pairs_of_three_windows
    (f : Nat -> Nat) (hprime : forall i, Nat.Prime (f i)) (hf : StrictMono f)
    (X h L m : Nat) (hspace : Nat.factorial L + 2 <= h)
    (u v a : Fin m -> Nat)
    (hleft : forall i, X + 10 * h * i.val <= f (u i) /\
      f (u i) <= X + 10 * h * i.val + h)
    (hmiddle : forall i, X + 10 * h * i.val + 3 * h <= f (v i) /\
      f (v i) <= X + 10 * h * i.val + 4 * h)
    (hright : forall i, X + 10 * h * i.val + 6 * h <= f (a i) /\
      f (a i + 1) <= X + 10 * h * i.val + 7 * h) :
    exists d : Fin m -> Nat,
      (forall i, d i < a i /\ f (d i) + L <= f (d i + 1) /\
        X + 10 * h * i.val <= f (d i) /\
        f (d i + 1) <= X + 10 * h * i.val + 4 * h) /\
      (forall i j, i < j -> a i + 1 < d j) := by
  have hh : 0 < h := by omega
  have hex : forall i : Fin m, exists d : Nat,
      u i <= d /\ d < v i /\ f d + L <= f (d + 1) := by
    intro i
    let z := X + 10 * h * i.val
    let W := Nat.factorial L
    let c := (z + 2 * h) / W + 1
    have hW : 0 < W := Nat.factorial_pos L
    have hc : 0 < c := Nat.succ_pos _
    have hmod : (z + 2 * h) % W < W := Nat.mod_lt _ hW
    have hdecomp : (z + 2 * h) % W + ((z + 2 * h) / W) * W =
        z + 2 * h := by
      simpa only [Nat.mul_comm] using Nat.mod_add_div (z + 2 * h) W
    have hcLow : z + 2 * h < c * W := by
      dsimp only [c]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hcHigh : c * W <= z + 2 * h + W := by
      dsimp only [c]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hlefti := hleft i
    have hmidi := hmiddle i
    change z <= f (u i) /\ f (u i) <= z + h at hlefti
    change z + 3 * h <= f (v i) /\ f (v i) <= z + 4 * h at hmidi
    have huv : u i <= v i := by
      by_contra hn
      have hrev := hf.monotone (show v i <= u i by omega)
      omega
    apply exists_prime_step_across_factorial_block f hprime hc huv
    next => change f (u i) <= c * W + 1; omega
    next =>
      change c * W + 1 < f (v i)
      change W + 2 <= h at hspace
      omega
  choose d hd using hex
  have hcell : forall i, d i < a i /\ f (d i) + L <= f (d i + 1) /\
      X + 10 * h * i.val <= f (d i) /\
      f (d i + 1) <= X + 10 * h * i.val + 4 * h := by
    intro i
    have hdi := hd i
    have hva : v i < a i := by
      by_contra hn
      have hrev := hf.monotone (show a i <= v i by omega)
      have hm := hmiddle i
      have hr := hright i
      omega
    refine And.intro (hdi.2.1.trans hva) (And.intro hdi.2.2
      (And.intro ((hleft i).1.trans (hf.monotone hdi.1)) ?_))
    exact (hf.monotone (Nat.succ_le_of_lt hdi.2.1)).trans (hmiddle i).2
  refine Exists.intro d (And.intro hcell ?_)
  intro i j hij
  have hijv : i.val < j.val := hij
  have hmul := Nat.mul_le_mul_left (10 * h) (Nat.succ_le_of_lt hijv)
  rw [Nat.mul_succ] at hmul
  have hphysical : f (a i + 1) < f (d j) := by
    have hi := (hright i).2
    have hj := (hcell j).2.2.1
    omega
  by_contra hn
  have hrev := hf.monotone (show d j <= a i + 1 by omega)
  omega

end Nat
