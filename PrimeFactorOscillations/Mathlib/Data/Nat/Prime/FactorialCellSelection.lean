/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Data.Nat.Prime.FactorialCrossing

/-! # Ordered disjoint long-gap and short-gap witnesses -/

namespace Nat

/-- Alternate occupied factorial cells supply strictly separated long/short gaps. -/
theorem factorial_cells_separated_gap_pairs
    (f : Nat -> Nat) (hprime : forall i, Nat.Prime (f i)) (hf : StrictMono f)
    {L H M m X Y : Nat} (hL : 1 <= L) (hm : 2 * m + 1 <= M)
    (c u : Fin M -> Nat) (hc : StrictMono c)
    (hcpos : forall j, 0 < c j)
    (hleft : forall j, c j * Nat.factorial L + L + 1 <= f (u j))
    (hright : forall j, f (u j + 1) <= (c j + 1) * Nat.factorial L + 1)
    (hshort : forall j, f (u j + 1) <= f (u j) + H)
    (hX : forall j, X <= f (u j)) (hY : forall j, f (u j + 1) <= Y) :
    exists d a : Fin m -> Nat,
      (forall i, d i < a i /\ f (d i) + L <= f (d i + 1) /\
        f (a i + 1) <= f (a i) + H /\ X <= f (d i) /\ f (a i + 1) <= Y) /\
      (forall i j, i < j -> a i + 1 < d j) := by
  have hsep : forall i j : Fin M, i < j -> u i + 1 < u j := by
    intro i j hij
    have hcells := hc hij
    have hmul := Nat.mul_le_mul_right (Nat.factorial L)
      (Nat.succ_le_of_lt hcells)
    change (c i + 1) * Nat.factorial L <= c j * Nat.factorial L at hmul
    have hi := hright i
    have hj := hleft j
    have hval : f (u i + 1) < f (u j) := by omega
    by_contra hn
    have hord := hf.monotone (show u j <= u i + 1 by omega)
    omega
  let ix : Fin m -> Fin M := fun i => Fin.mk (2 * i.val + 2) (by omega)
  let prev : Fin m -> Fin M := fun i => Fin.mk (2 * i.val + 1) (by omega)
  have hprev : forall i, prev i < ix i := by
    intro i
    change 2 * i.val + 1 < 2 * i.val + 2
    omega
  have hex : forall i : Fin m, exists d,
      u (prev i) <= d /\ d < u (ix i) /\ f d + L <= f (d + 1) := by
    intro i
    have hcells := hc (hprev i)
    have hmul := Nat.mul_le_mul_right (Nat.factorial L)
      (Nat.succ_le_of_lt hcells)
    change (c (prev i) + 1) * Nat.factorial L <=
      c (ix i) * Nat.factorial L at hmul
    have hprevval := hf.monotone (Nat.le_succ (u (prev i)))
    change f (u (prev i)) <= f (u (prev i) + 1) at hprevval
    have hrightprev := hright (prev i)
    have hleftix := hleft (ix i)
    have hus := hsep (prev i) (ix i) (hprev i)
    apply exists_prime_step_across_factorial_block f hprime (hcpos (ix i))
      (show u (prev i) <= u (ix i) by omega)
    next => omega
    next => omega
  choose d hd using hex
  refine Exists.intro d (Exists.intro (fun i => u (ix i)) (And.intro ?_ ?_))
  next =>
    intro i
    have hlow : X <= f (d i) := (hX (prev i)).trans (hf.monotone (hd i).1)
    exact And.intro (hd i).2.1 (And.intro (hd i).2.2
      (And.intro (hshort (ix i)) (And.intro hlow (hY (ix i)))))
  next =>
    intro i j hij
    have hbetween : ix i < prev j := by
      change 2 * i.val + 2 < 2 * j.val + 1
      have hval : i.val < j.val := hij
      omega
    exact (hsep (ix i) (prev j) hbetween).trans_le (hd j).1

end Nat
