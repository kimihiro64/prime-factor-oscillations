import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Real reciprocal-smooth local laws and their exact gap thresholds -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

/-- The local input for the universality target. The control is only over
prime arguments and says exactly 1/eta_p = p/nu + offset + o(1).
It contains no density-ratio, prime-gap or reversal-count assumption. -/
structure ReciprocalSmoothLaw where
  eta : Nat -> Real
  nu : Real
  offset : Real
  nu_pos : 0 < nu
  probability : forall p : Nat, Nat.Prime p -> 0 <= eta p /\ eta p <= 1
  reciprocal_control : forall epsilon : Real, 0 < epsilon ->
    exists P : Nat, forall p : Nat, P <= p -> Nat.Prime p ->
      abs (1 / eta p - (p : Real) / nu - offset) <= epsilon

namespace ReciprocalSmoothLaw

/-- Smooth reciprocal control forces every sufficiently large prime law into
the open probability interval. Forced and excluded primes are therefore finite. -/
theorem eventually_probability_interior (law : ReciprocalSmoothLaw) :
    exists P : Nat, forall p : Nat, P <= p -> Nat.Prime p ->
      0 < law.eta p /\ law.eta p < 1 := by
  choose P0 hP0 using law.reciprocal_control 1 (by norm_num)
  choose P1 hP1 using exists_nat_gt (law.nu * (abs law.offset + 3))
  refine Exists.intro (max P0 P1) ?_
  intro p hp hprime
  have happrox := abs_le.mp (hP0 p ((le_max_left P0 P1).trans hp) hprime)
  have hpR : (P1 : Real) <= p := by exact_mod_cast (le_max_right P0 P1).trans hp
  have hlarge := hP1.trans_le hpR
  have hcancel : ((p : Real) / law.nu) * law.nu = p := by
    field_simp [ne_of_gt law.nu_pos]
  have hscale : abs law.offset + 3 < (p : Real) / law.nu := by
    nlinarith only [hlarge, hcancel, law.nu_pos]
  have hoffset := neg_abs_le law.offset
  have hinv : 1 < 1 / law.eta p := by
    linarith only [happrox.1, hscale, hoffset]
  have hprob := law.probability p hprime
  have hzero : Not (law.eta p = 0) := by
    intro hz
    rw [hz] at hinv
    norm_num at hinv
  have hone : Not (law.eta p = 1) := by
    intro hz
    rw [hz] at hinv
    norm_num at hinv
  constructor
  next =>
    by_contra hn
    exact hzero (le_antisymm (le_of_not_gt hn) hprob.1)
  next =>
    by_contra hn
    exact hone (le_antisymm hprob.2 (le_of_not_gt hn))

/-- The exceptional prime laws all occur below one explicit existential cutoff. -/
theorem exceptional_primes_bounded (law : ReciprocalSmoothLaw) :
    exists P : Nat, forall p : Nat, Nat.Prime p ->
      (law.eta p = 0 \/ law.eta p = 1) -> p < P := by
  choose P hP using law.eventually_probability_interior
  refine Exists.intro P ?_
  intro p hp hex
  by_contra hn
  have hi := hP p (le_of_not_gt hn) hp
  rcases hex with hz | ho
  next => rw [hz] at hi; linarith only [hi.1]
  next => rw [ho] at hi; linarith only [hi.2]

/-- The o(1) reciprocal remainder is uniform for every later pair of primes,
including pairs whose gap is not bounded in advance. -/
theorem eventually_gap_threshold_bounds (law : ReciprocalSmoothLaw)
    (epsilon : Real) (he : 0 < epsilon) :
    exists P : Nat, forall p q : Nat, P <= p -> p <= q ->
      Nat.Prime p -> Nat.Prime q ->
      ((q - p : Nat) : Real) / law.nu + 1 - epsilon <=
        1 / law.eta q - 1 / law.eta p + 1 /\
      1 / law.eta q - 1 / law.eta p + 1 <=
        ((q - p : Nat) : Real) / law.nu + 1 + epsilon := by
  choose P hP using law.reciprocal_control (epsilon / 2) (by linarith)
  refine Exists.intro P ?_
  intro p q hp hpq hprimep hprimeq
  have hlo := abs_le.mp (hP p hp hprimep)
  have hhi := abs_le.mp (hP q (hp.trans hpq) hprimeq)
  rw [Nat.cast_sub hpq, sub_div]
  constructor <;> linarith only [hlo.1, hlo.2, hhi.1, hhi.2]

end ReciprocalSmoothLaw

end PrimeFactorOscillations
