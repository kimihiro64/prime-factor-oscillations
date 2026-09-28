import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Definitions.Reversals

set_option autoImplicit false

/-!
# Exact first difference for a local rank law

Writing A = eta p, B = eta q, F = mass(r+1), G = mass(r), the difference
is B*((1-A)*F+A*G)-A*F = A*B*F*(G/F-(1/B-1/A+1)).
This algebraic identity is the consumer needed by the prime-cluster route;
no prime-distribution or independence hypothesis is hidden in its proof.
-/

namespace PrimeFactorOscillations

/-- Exact factorization of the density change after adjoining one prime. -/
theorem localStep_difference (eta : Nat -> Rat) (ps : List Nat) (r p q : Nat)
    (hp : Not (eta p = 0)) (hq : Not (eta q = 0))
    (hF : Not (finiteLocalMass eta ps (r + 1) = 0)) :
    eta q * finiteLocalMass eta (p :: ps) (r + 1) -
        eta p * finiteLocalMass eta ps (r + 1) =
      (eta p * eta q * finiteLocalMass eta ps (r + 1)) *
        (finiteLocalMass eta ps r / finiteLocalMass eta ps (r + 1) -
          (1 / eta q - 1 / eta p + 1)) := by
  simp only [finiteLocalMass]
  field_simp
  ring

/-- A positive local law converts an ascent into an exact ratio threshold. -/
theorem localStep_gt_iff (eta : Nat -> Rat) (ps : List Nat) (r p q : Nat)
    (hp : 0 < eta p) (hq : 0 < eta q)
    (hF : 0 < finiteLocalMass eta ps (r + 1)) :
    eta p * finiteLocalMass eta ps (r + 1) <
        eta q * finiteLocalMass eta (p :: ps) (r + 1) <->
      1 / eta q - 1 / eta p + 1 <
        finiteLocalMass eta ps r / finiteLocalMass eta ps (r + 1) := by
  rw [<- sub_pos, localStep_difference eta ps r p q
    (ne_of_gt hp) (ne_of_gt hq) (ne_of_gt hF)]
  rw [mul_pos_iff_of_pos_left (mul_pos (mul_pos hp hq) hF), sub_pos]

/-- The same exact threshold controls strict descent. -/
theorem localStep_lt_iff (eta : Nat -> Rat) (ps : List Nat) (r p q : Nat)
    (hp : 0 < eta p) (hq : 0 < eta q)
    (hF : 0 < finiteLocalMass eta ps (r + 1)) :
    eta q * finiteLocalMass eta (p :: ps) (r + 1) <
        eta p * finiteLocalMass eta ps (r + 1) <->
      finiteLocalMass eta ps r / finiteLocalMass eta ps (r + 1) <
        1 / eta q - 1 / eta p + 1 := by
  rw [<- sub_neg, localStep_difference eta ps r p q
    (ne_of_gt hp) (ne_of_gt hq) (ne_of_gt hF)]
  have hscale := mul_pos (mul_pos hp hq) hF
  constructor
  next =>
    intro h
    by_contra hR
    have hz := sub_nonneg.mpr (le_of_not_gt hR)
    exact not_lt_of_ge (mul_nonneg (le_of_lt hscale) hz) h
  next =>
    intro hR
    exact mul_neg_of_pos_of_neg hscale (sub_neg.mpr hR)

/-- Every odd-prime local probability is strictly positive. -/
theorem genericOddEta_pos (p : Nat) (hp : 2 < p) : 0 < genericOddEta p := by
  have hpR : (2 : Rat) < (p : Rat) := by exact_mod_cast hp
  have h1 : Not ((p : Rat) - 1 = 0) := by linarith
  simp only [genericOddEta, ite_eq_right (ne_of_gt hp)]
  exact div_pos (by linarith) (sq_pos_of_ne_zero h1)

/-- Exact reciprocal; its small correction matters in the gap criterion. -/
theorem genericOddEta_reciprocal (p : Nat) (hp : 2 < p) :
    1 / genericOddEta p = (p : Rat) + 1 / ((p : Rat) - 2) := by
  have hpR : (2 : Rat) < (p : Rat) := by exact_mod_cast hp
  have h1 : Not ((p : Rat) - 1 = 0) := by linarith
  have h2 : Not ((p : Rat) - 2 = 0) := by linarith
  simp only [genericOddEta, ite_eq_right (ne_of_gt hp)]
  field_simp
  ring

/-- The exact generic odd threshold at any two arguments greater than two. -/
theorem genericOdd_gapThreshold (p q : Nat) (hp : 2 < p) (hq : 2 < q) :
    1 / genericOddEta q - 1 / genericOddEta p + 1 =
      ((q : Rat) - (p : Rat)) + 1 -
        ((q : Rat) - (p : Rat)) / (((p : Rat) - 2) * ((q : Rat) - 2)) := by
  rw [genericOddEta_reciprocal q hq, genericOddEta_reciprocal p hp]
  have hpR : (2 : Rat) < (p : Rat) := by exact_mod_cast hp
  have hqR : (2 : Rat) < (q : Rat) := by exact_mod_cast hq
  have h1 : Not ((p : Rat) - 2 = 0) := by linarith
  have h2 : Not ((q : Rat) - 2 = 0) := by linarith
  field_simp
  ring

/-- Exact ascent criterion used to turn a bounded prime gap into a reversal. -/
theorem genericOdd_step_gt_iff (ps : List Nat) (r p q : Nat)
    (hp : 2 < p) (hq : 2 < q) (hF : 0 < finiteLocalMass genericOddEta ps (r + 1)) :
    genericOddEta p * finiteLocalMass genericOddEta ps (r + 1) <
        genericOddEta q * finiteLocalMass genericOddEta (p :: ps) (r + 1) <->
      ((q : Rat) - (p : Rat)) + 1 -
          ((q : Rat) - (p : Rat)) / (((p : Rat) - 2) * ((q : Rat) - 2)) <
        finiteLocalMass genericOddEta ps r / finiteLocalMass genericOddEta ps (r + 1) := by
  rw [localStep_gt_iff genericOddEta ps r p q
    (genericOddEta_pos p hp) (genericOddEta_pos q hq) hF, genericOdd_gapThreshold p q hp hq]

/-- Exact descent criterion used for the composite block preceding a cluster. -/
theorem genericOdd_step_lt_iff (ps : List Nat) (r p q : Nat)
    (hp : 2 < p) (hq : 2 < q) (hF : 0 < finiteLocalMass genericOddEta ps (r + 1)) :
    genericOddEta q * finiteLocalMass genericOddEta (p :: ps) (r + 1) <
        genericOddEta p * finiteLocalMass genericOddEta ps (r + 1) <->
      finiteLocalMass genericOddEta ps r / finiteLocalMass genericOddEta ps (r + 1) <
        ((q : Rat) - (p : Rat)) + 1 -
          ((q : Rat) - (p : Rat)) / (((p : Rat) - 2) * ((q : Rat) - 2)) := by
  rw [localStep_lt_iff genericOddEta ps r p q
    (genericOddEta_pos p hp) (genericOddEta_pos q hq) hF, genericOdd_gapThreshold p q hp hq]

end PrimeFactorOscillations
