/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ReciprocalSmoothRH

/-!
# Quadratic probability errors imply the required quadratic odds error

No reciprocal-smooth offset is assumed. Every probability is retained, including
eta = 0 and eta = 1. The finite head is absorbed into an explicit finite sum.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem exists_quadratic_odds_error_of_probability_error
    (eta : Nat -> Real) (nu E : Real) (hnu : 0 < nu) (hE : 0 <= E)
    (hProb : forall p : Nat, Nat.Prime p -> 0 <= eta p /\ eta p <= 1)
    (hError : forall p : Nat, Nat.Prime p -> abs (eta p - nu / p) <= E / (p : Real) ^ 2) :
    exists D : Real, 0 < D /\ forall p : Nat, Nat.Prime p ->
      abs (eta p / (1 - eta p) - nu / p) <= D / (p : Real) ^ 2 := by
  let M := nu + E
  have hM : 0 < M := by dsimp [M]; linarith
  let D0 := E + 2 * M ^ 2
  have hD0 : 0 <= D0 := by dsimp [D0]; positivity
  choose P hP using exists_nat_gt (max (1 : Real) (2 * M))
  have hTail : forall p : Nat, P <= p -> Nat.Prime p ->
      abs (eta p / (1 - eta p) - nu / p) <= D0 / (p : Real) ^ 2 := by
    intro p hp hPrime
    have hpR : (0 : Real) < p := by exact_mod_cast hPrime.pos
    have hpOne : (1 : Real) <= p := by exact_mod_cast hPrime.one_lt.le
    have hpP : (P : Real) <= p := by exact_mod_cast hp
    have hpLarge : 2 * M <= (p : Real) := ((le_max_right _ _).trans_lt hP).le.trans hpP
    have hBase := (abs_le.mp (hError p hPrime)).2
    have hSquare : (p : Real) <= (p : Real) ^ 2 := by nlinarith
    have hErrorSmall : E / (p : Real) ^ 2 <= E / p :=
      div_le_div_of_nonneg_left hE hpR hSquare
    have hEtaUpper : eta p <= M / p := by
      have hSum : nu / (p : Real) + E / p = M / p := by dsimp [M]; ring
      linarith only [hBase, hErrorSmall, hSum]
    have hHalf : eta p <= 1 / 2 := by
      have h := div_le_div_of_nonneg_left hM.le (show 0 < 2 * M by positivity) hpLarge
      have hCancel : M / (2 * M) = (1 / 2 : Real) := by field_simp [hM.ne']
      rw [hCancel] at h
      exact hEtaUpper.trans h
    have hEta := hProb p hPrime
    have hDen : 0 < 1 - eta p := by linarith
    have hCorrection : (eta p) ^ 2 / (1 - eta p) <= 2 * M ^ 2 / (p : Real) ^ 2 := by
      calc
        (eta p) ^ 2 / (1 - eta p) <= (M / (p : Real)) ^ 2 / (1 / 2 : Real) := by
          gcongr
          . exact hEta.1
          . linarith
        _ = 2 * M ^ 2 / (p : Real) ^ 2 := by ring
    have hIdentity : eta p / (1 - eta p) - nu / p =
        (eta p - nu / p) + (eta p) ^ 2 / (1 - eta p) := by
      field_simp [hDen.ne', hpR.ne']
      <;> ring
    rw [hIdentity]
    calc
      abs ((eta p - nu / p) + (eta p) ^ 2 / (1 - eta p)) <=
          abs (eta p - nu / p) + abs ((eta p) ^ 2 / (1 - eta p)) := abs_add_le _ _
      _ = abs (eta p - nu / p) + (eta p) ^ 2 / (1 - eta p) := by
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hDen.le)]
      _ <= E / (p : Real) ^ 2 + 2 * M ^ 2 / (p : Real) ^ 2 :=
        add_le_add (hError p hPrime) hCorrection
      _ = D0 / (p : Real) ^ 2 := by dsimp [D0]; ring
  let w := fun p : Nat => eta p / (1 - eta p)
  let B := (Finset.range P).sum (fun p => (p : Real) ^ 2 * abs (w p - nu / p))
  have hB : 0 <= B := Finset.sum_nonneg (fun p _ => mul_nonneg (sq_nonneg _) (abs_nonneg _))
  let D := D0 + B + 1
  have hD : 0 < D := by dsimp [D]; linarith
  refine Exists.intro D (And.intro hD ?_)
  intro p hPrime
  have hpR : (0 : Real) < p := by exact_mod_cast hPrime.pos
  by_cases hp : P <= p
  . exact (hTail p hp hPrime).trans (div_le_div_of_nonneg_right
      (show D0 <= D by dsimp [D]; linarith) (sq_nonneg _))
  . have hpMem : Membership.mem (Finset.range P) p := Finset.mem_range.mpr (lt_of_not_ge hp)
    have hTerm : (p : Real) ^ 2 * abs (w p - nu / p) <= B :=
      Finset.single_le_sum (fun (q : Nat) _ =>
        mul_nonneg (sq_nonneg (q : Real)) (abs_nonneg (w q - nu / q))) hpMem
    have hBound : (p : Real) ^ 2 * abs (w p - nu / p) <= D := by
      dsimp [D]
      linarith only [hTerm, hD0]
    have hCancel : (D / (p : Real) ^ 2) * (p : Real) ^ 2 = D := by field_simp
    have hSq : 0 < (p : Real) ^ 2 := sq_pos_of_pos hpR
    change abs (w p - nu / p) <= D / (p : Real) ^ 2
    nlinarith only [hBound, hCancel, hSq]

noncomputable def quadraticPrimeLawOfProbability
    (eta : Nat -> Real) (nu E : Real) (hnu : 0 < nu) (hE : 0 <= E)
    (hProb : forall p : Nat, Nat.Prime p -> 0 <= eta p /\ eta p <= 1)
    (hError : forall p : Nat, Nat.Prime p -> abs (eta p - nu / p) <= E / (p : Real) ^ 2) :
    QuadraticPrimeLaw := by
  choose D hD hBound using exists_quadratic_odds_error_of_probability_error
    eta nu E hnu hE hProb hError
  refine {
    weight := fun p : Nat.Primes => eta (p : Nat) / (1 - eta (p : Nat))
    nu := nu
    error := D + nu
    nu_pos := hnu
    error_nonneg := add_nonneg hD.le hnu.le
    weight_nonneg := ?_
    quadratic_error := ?_
  }
  . intro p
    exact div_nonneg (hProb (p : Nat) p.property).1
      (sub_nonneg.mpr (hProb (p : Nat) p.property).2)
  . exact quadraticPrimeWeight_error_of_inverse_prime
      (fun p : Nat.Primes => eta (p : Nat) / (1 - eta (p : Nat))) nu D hnu.le hD.le
      (fun p => hBound (p : Nat) p.property)

/-- A prime-tail estimate suffices: the exact finite head changes only the
family error constant. This is the explicit quantified form of O(p^-2). -/
noncomputable def quadraticPrimeLawOfEventualProbability
    (eta : Nat -> Real) (nu E : Real) (hnu : 0 < nu) (hE : 0 <= E)
    (hProb : forall p : Nat, Nat.Prime p -> 0 <= eta p /\ eta p <= 1)
    (hError : exists P : Nat, forall p : Nat, P <= p -> Nat.Prime p ->
      abs (eta p - nu / p) <= E / (p : Real) ^ 2) : QuadraticPrimeLaw := by
  choose P hP using hError
  let B := (Finset.range P).sum (fun p => (p : Real) ^ 2 * abs (eta p - nu / p))
  have hB : 0 <= B := Finset.sum_nonneg (fun p _ =>
    mul_nonneg (sq_nonneg (p : Real)) (abs_nonneg _))
  have hGlobal : forall p : Nat, Nat.Prime p ->
      abs (eta p - nu / p) <= (E + B) / (p : Real) ^ 2 := by
    intro p hPrime
    have hpR : (0 : Real) < p := by exact_mod_cast hPrime.pos
    by_cases hp : P <= p
    . exact (hP p hp hPrime).trans (div_le_div_of_nonneg_right
        (show E <= E + B by linarith) (sq_nonneg _))
    . have hpMem : Membership.mem (Finset.range P) p := Finset.mem_range.mpr (lt_of_not_ge hp)
      have hTerm : (p : Real) ^ 2 * abs (eta p - nu / p) <= B :=
        Finset.single_le_sum (fun (q : Nat) _ =>
          mul_nonneg (sq_nonneg (q : Real)) (abs_nonneg (eta q - nu / q))) hpMem
      have hCancel : ((E + B) / (p : Real) ^ 2) * (p : Real) ^ 2 = E + B := by field_simp
      have hSq : 0 < (p : Real) ^ 2 := sq_pos_of_pos hpR
      nlinarith only [hTerm, hCancel, hSq, hE]
  exact quadraticPrimeLawOfProbability eta nu (E + B) hnu (add_nonneg hE hB) hProb hGlobal

end PrimeFactorOscillations
