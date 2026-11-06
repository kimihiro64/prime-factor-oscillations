/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.Complex.AnchoredScalarMultiplicity

/-!
# Finite anchored scalar chains

Every successor is recovered as an exact integer before the preceding row
is decoded. Thus arbitrary real coefficients and arbitrary chain lengths
retain the same strict half-unit observation tolerance. A last positive
order gives a signed negative row without estimating rows separately.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

def scalarChainDecode (t y : Nat -> Real) : Nat -> Nat -> Int
  | 0, _ => 0
  | n + 1, j => Int.floor
      (t j * (scalarChainDecode t y n (j + 1) : Real) - y j + (1 / 2 : Real))

theorem scalarChainDecode_exact (t y : Nat -> Real) (m : Nat -> Int) (n j : Nat) :
    m (j + n) = 0 ->
    (forall i, j <= i -> i < j + n ->
      abs (-(m i : Real) + t i * (m (i + 1) : Real) - y i) < 1 / 2) ->
    scalarChainDecode t y n j = m j := by
  induction n generalizing j with
  | zero =>
    intro hAnchor _hObs
    simpa only [Nat.add_zero, scalarChainDecode] using hAnchor.symm
  | succ n ih =>
    intro hAnchor hObs
    have hTailAnchor : m ((j + 1) + n) = 0 := by
      have he : (j + 1) + n = j + (n + 1) := by omega
      simpa only [he] using hAnchor
    have hTail := ih (j + 1) hTailAnchor
      (fun i hi hi' => hObs i (by omega) (by omega))
    rw [scalarChainDecode, hTail]
    have hRow := abs_lt.mp (hObs j (le_refl j) (by omega))
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith [hRow.1, hRow.2]

theorem scalarChainDecode_all (t y : Nat -> Real) (m : Nat -> Int) (n : Nat)
    (hAnchor : m n = 0)
    (hObs : forall i, i < n ->
      abs (-(m i : Real) + t i * (m (i + 1) : Real) - y i) < 1 / 2) :
    forall j, j <= n -> scalarChainDecode t y (n - j) j = m j := by
  intro j hj
  have he : j + (n - j) = n := by omega
  apply scalarChainDecode_exact t y m (n - j) j
  . simpa only [he] using hAnchor
  . intro i _hi hi'
    exact hObs i (by omega)

private theorem scalarChain_last_positive (m : Nat -> Nat) (n : Nat) :
    m n = 0 -> (Exists (fun j => And (j < n) (0 < m j))) ->
    Exists (fun j => And (j < n) (And (0 < m j) (m (j + 1) = 0))) := by
  induction n with
  | zero =>
    intro _hAnchor hMass
    choose j hj _hp using hMass
    omega
  | succ n ih =>
    intro hAnchor hMass
    by_cases hz : m n = 0
    . have hSmall : Exists (fun j => And (j < n) (0 < m j)) := by
        choose j hj hp using hMass
        have hne : Not (j = n) := by
          intro he
          rw [he, hz] at hp
          omega
        exact Exists.intro j (And.intro (by omega) hp)
      choose j hj hp hNext using ih hz hSmall
      exact Exists.intro j (And.intro (by omega) (And.intro hp hNext))
    . exact Exists.intro n (And.intro (Nat.lt_succ_self n)
        (And.intro (Nat.pos_of_ne_zero hz) hAnchor))

theorem scalarChain_negative_iff (t : Nat -> Real) (m : Nat -> Nat) (n : Nat)
    (hAnchor : m n = 0) :
    (Exists (fun j => And (j < n) (0 < m j))) <->
    Exists (fun j => And (j < n)
      (-(m j : Real) + t j * (m (j + 1) : Real) <= -1)) := by
  constructor
  . intro hMass
    choose j hj hp hNext using scalarChain_last_positive m n hAnchor hMass
    have hm : 1 <= (m j : Real) := by exact_mod_cast (Nat.succ_le_of_lt hp)
    refine Exists.intro j (And.intro hj ?_)
    rw [hNext]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    linarith
  . intro hSignal
    choose j hj hs using hSignal
    by_contra hNo
    have hAll : forall k, k < n -> m k = 0 := by
      intro k hk
      by_contra hn
      exact hNo (Exists.intro k (And.intro hk (Nat.pos_of_ne_zero hn)))
    have ha := hAll j hj
    have hb : m (j + 1) = 0 := by
      by_cases he : j + 1 = n
      . simpa only [he] using hAnchor
      . exact hAll (j + 1) (by omega)
    norm_num [ha, hb] at hs

theorem scalarChain_noisy_negative_iff (t y : Nat -> Real) (m : Nat -> Nat) (n : Nat)
    (hAnchor : m n = 0)
    (hObs : forall i, i < n ->
      abs (-(m i : Real) + t i * (m (i + 1) : Real) - y i) < 1 / 2) :
    (Exists (fun j => And (j < n) (0 < m j))) <->
    Exists (fun j => And (j < n) (y j < -1 / 2)) := by
  constructor
  . intro hMass
    choose j hj hs using (scalarChain_negative_iff t m n hAnchor).mp hMass
    have hRow := (abs_lt.mp (hObs j hj)).1
    exact Exists.intro j (And.intro hj (by linarith))
  . intro hSignal
    choose j hj hy using hSignal
    by_contra hNo
    have hAll : forall k, k < n -> m k = 0 := by
      intro k hk
      by_contra hn
      exact hNo (Exists.intro k (And.intro hk (Nat.pos_of_ne_zero hn)))
    have ha := hAll j hj
    have hb : m (j + 1) = 0 := by
      by_cases he : j + 1 = n
      . simpa only [he] using hAnchor
      . exact hAll (j + 1) (by omega)
    have hRow := hObs j hj
    norm_num [ha, hb] at hRow
    have hh := (abs_lt.mp hRow).1
    linarith

/-- Two quadratic scalar rows can both vanish for positive integer orders.
The terminal point 7/8 is compatible with a strict seven-eighths zero-free
strip. This is a code model, not a realized Dirichlet zero pattern. -/
theorem quadraticScalar_two_channel_collision :
    And (integerResidueCode 2 (1 / 2 : Complex) 4 6 = 0)
      (integerResidueCode 2 (3 / 4 : Complex) 6 7 = 0) := by
  norm_num [integerResidueCode]

end Complex

end
