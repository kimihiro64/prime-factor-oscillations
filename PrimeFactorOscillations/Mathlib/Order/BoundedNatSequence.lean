/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Find

/-!
# A largest recurrent value in an eventually bounded natural sequence

The least eventual integer ceiling is attained arbitrarily far out.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem exists_eventual_maximum_recurrent (f : Nat -> Nat)
    (hbound : exists B : Nat, exists M : Nat,
      forall n : Nat, M <= n -> f n <= B) :
    exists K : Nat,
      (exists M : Nat, forall n : Nat, M <= n -> f n <= K) /\
      (forall N : Nat, exists n : Nat, N <= n /\ f n = K) := by
  classical
  let K := Nat.find hbound
  have hK : exists M : Nat, forall n : Nat, M <= n -> f n <= K :=
    Nat.find_spec hbound
  refine Exists.intro K (And.intro hK ?_)
  intro N
  by_contra hn
  have hne : forall n : Nat, N <= n -> Not (f n = K) := by
    intro n hN he
    exact hn (Exists.intro n (And.intro hN he))
  let M := Classical.choose hK
  have hM : forall n : Nat, M <= n -> f n <= K := Classical.choose_spec hK
  by_cases hz : K = 0
  . have hb := hM (max N M) (le_max_right N M)
    have hnot := hne (max N M) (le_max_left N M)
    omega
  . have hsmaller : exists L : Nat, forall n : Nat, L <= n -> f n <= K - 1 := by
      refine Exists.intro (max N M) ?_
      intro n hn
      have hb := hM n (Nat.le_trans (le_max_right N M) hn)
      have hnot := hne n (Nat.le_trans (le_max_left N M) hn)
      omega
    have hmin : K <= K - 1 := Nat.find_min' hbound hsmaller
    omega

end Nat
