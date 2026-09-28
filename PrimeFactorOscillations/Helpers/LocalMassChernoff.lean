import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeFactorOscillations.Helpers.LocalMassGenerating

set_option autoImplicit false

/-! # Explicit exponential tails for the finite local-law recurrence -/

namespace PrimeFactorOscillations

/-- The exact finite product is bounded by the exponential of twice its mean. -/
theorem finiteLocalMass_three_product_le_exp (eta : Nat -> Rat) (xs : List Nat)
    (heta : forall p, List.Mem p xs -> 0 <= eta p /\ eta p <= 1) :
    (((xs.map (fun p => 1 - eta p + eta p * 3)).prod : Rat) : Real) <=
      Real.exp (2 * (((xs.map eta).sum : Rat) : Real)) := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
      have hp := heta p (List.Mem.head _)
      have ht : forall q, List.Mem q xs -> 0 <= eta q /\ eta q <= 1 :=
        fun q hq => heta q (List.Mem.tail _ hq)
      have hf : (0 : Real) <= ((1 - eta p + eta p * 3 : Rat) : Real) := by
        exact_mod_cast (show (0 : Rat) <= 1 - eta p + eta p * 3 by linarith [hp.1])
      have hfac : ((1 - eta p + eta p * 3 : Rat) : Real) <=
          Real.exp (2 * (eta p : Real)) := by
        push_cast
        linarith [Real.add_one_le_exp (2 * (eta p : Real))]
      calc
        _ = ((1 - eta p + eta p * 3 : Rat) : Real) *
            (((xs.map (fun q => 1 - eta q + eta q * 3)).prod : Rat) : Real) := by
          rw [List.map_cons, List.prod_cons, Rat.cast_mul]
        _ <= ((1 - eta p + eta p * 3 : Rat) : Real) *
            Real.exp (2 * (((xs.map eta).sum : Rat) : Real)) :=
          mul_le_mul_of_nonneg_left (ih ht) hf
        _ <= Real.exp (2 * (eta p : Real)) *
            Real.exp (2 * (((xs.map eta).sum : Rat) : Real)) :=
          mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le
        _ = _ := by
          rw [<- Real.exp_add, List.map_cons, List.sum_cons, Rat.cast_add]
          congr 1
          ring

/-- A Chernoff bound directly for the exact finite local mass recurrence. -/
theorem finiteLocalMass_tail_le_exp (eta : Nat -> Rat) (xs : List Nat)
    (heta : forall p, List.Mem p xs -> 0 <= eta p /\ eta p <= 1) (k : Nat) :
    ((((Finset.range (xs.length + 1)).filter (fun r => k <= r)).sum
      (finiteLocalMass eta xs) : Rat) : Real) <=
        Real.exp (2 * (((xs.map eta).sum : Rat) : Real) - (k : Real) * Real.log 3) := by
  have hRat := finiteLocalMass_tail_mul_pow_le eta xs heta k 3 (by norm_num)
  have hCast := (Rat.cast_le (K := Real)).mpr hRat
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] at hCast
  have hbound := hCast.trans (finiteLocalMass_three_product_le_exp eta xs heta)
  have hexp : Real.exp ((k : Real) * Real.log 3) = (3 : Real) ^ k := by
    clear hRat hCast hbound
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.cast_succ, add_mul, one_mul, Real.exp_add, ih,
          Real.exp_log (by norm_num : (0 : Real) < 3), pow_succ]
  rw [<- hexp] at hbound
  by_contra h
  have hmul := mul_lt_mul_of_pos_left (lt_of_not_ge h)
    (Real.exp_pos ((k : Real) * Real.log 3))
  have heq :
      Real.exp ((k : Real) * Real.log 3) *
        Real.exp (2 * (((xs.map eta).sum : Rat) : Real) - (k : Real) * Real.log 3) =
      Real.exp (2 * (((xs.map eta).sum : Rat) : Real)) := by
    rw [<- Real.exp_add]
    congr 1
    ring
  rw [heq] at hmul
  linarith only [hbound, hmul]

/-- A mean bound on the rank scale gives the explicit rare-region exponent. -/
theorem finiteLocalMass_tail_le_exp_of_mean (eta : Nat -> Rat) (xs : List Nat)
    (heta : forall p, List.Mem p xs -> 0 <= eta p /\ eta p <= 1)
    (k : Nat) (c C : Real)
    (hmean : (((xs.map eta).sum : Rat) : Real) <= c * k + C) :
    ((((Finset.range (xs.length + 1)).filter (fun r => k <= r)).sum
      (finiteLocalMass eta xs) : Rat) : Real) <=
        Real.exp (-(Real.log 3 - 2 * c) * k + 2 * C) := by
  apply (finiteLocalMass_tail_le_exp eta xs heta k).trans
  apply Real.exp_le_exp.mpr
  nlinarith only [hmean]

end PrimeFactorOscillations
