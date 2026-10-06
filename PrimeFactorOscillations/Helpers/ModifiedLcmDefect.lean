/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ModifiedLcmHeightCorrection
import PrimeFactorOscillations.Helpers.PrimeReciprocalSquareTail

/-!
# Exact modified-LCM defect split and a free-cutoff error bound

The upper prime band contributes its actual reciprocal-square sum.
Every remaining prime is retained, with total at most J/N + 2/J^2.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations

theorem modifiedLcm_factorization_ge_two (N : Nat) {p : Nat}
    (hp : Nat.Prime p) (hSquare : p ^ 2 <= 2 * N) :
    2 <= (modifiedLcm N).factorization p := by
  by_cases hLow : p ^ 2 <= N
  . exact (Nat.le_log_of_pow_le hp.one_lt hLow).trans
      (modifiedLcm_factorization_ge_log N hp)
  . have hpN : p <= N := by nlinarith [hp.two_le]
    have hRaised : Membership.mem (modifiedLcmRaisedPrimes N) p :=
      (mem_modifiedLcmRaisedPrimes N p).mpr
        (And.intro hp (And.intro (Nat.lt_of_not_ge hLow) hSquare))
    rw [modifiedLcm_factorization N hp, ite_eq_left hRaised]
    have hLog := Nat.log_pos hp.one_lt hpN
    omega

theorem modifiedLcm_defect_nonneg (N p : Nat) :
    0 <= lcmExponentDefect (modifiedLcm N) p :=
  Real.rpow_nonneg (Nat.cast_nonneg p) _

theorem modifiedLcm_defect_le_cube (N : Nat) {p : Nat}
    (hp : Nat.Prime p) (hSquare : p ^ 2 <= 2 * N) :
    lcmExponentDefect (modifiedLcm N) p <= 1 / (p : Real) ^ (3 : Nat) := by
  have ha := modifiedLcm_factorization_ge_two N hp hSquare
  have haReal : (2 : Real) <= (modifiedLcm N).factorization p := by exact_mod_cast ha
  have hpOne : (1 : Real) <= p := by exact_mod_cast hp.one_le
  calc
    _ <= (p : Real) ^ (-3 : Real) := by
      exact Real.rpow_le_rpow_of_exponent_le hpOne (by linarith)
    _ = _ := by norm_num [Real.rpow_neg, Real.rpow_natCast]

theorem modifiedLcm_defect_eq_square (N : Nat) {p : Nat}
    (hp : Nat.Prime p) (hpN : p <= N) (hSquare : 2 * N < p ^ 2) :
    lcmExponentDefect (modifiedLcm N) p = 1 / (p : Real) ^ (2 : Nat) := by
  unfold lcmExponentDefect
  rw [modifiedLcm_factorization_eq_one N hp hpN hSquare]
  norm_num [Real.rpow_neg, Real.rpow_natCast]

theorem finite_prime_reciprocal_sq_le_tail
    (S : Finset Nat) (J : Nat)
    (hPrime : forall p, Membership.mem S p -> Nat.Prime p)
    (hCut : forall p, Membership.mem S p -> J < p) :
    S.sum (fun p => 1 / (p : Real) ^ (2 : Nat)) <= primeReciprocalSquareTail J := by
  classical
  let T := {p : Nat.Primes // J < (p : Nat)}
  let e : Function.Embedding {p : Nat // Membership.mem S p} T :=
    { toFun := fun p => Subtype.mk (Subtype.mk p.val (hPrime p.val p.property))
        (hCut p.val p.property)
      inj' := by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun r : T => ((r.val : Nat.Primes) : Nat)) hpq }
  let f : T -> Real := fun p => 1 / (p.val.val : Real) ^ (2 : Nat)
  have hs : Summable f := summable_prime_reciprocal_sq.subtype _
  have hSum : (S.attach.map e).sum f = S.sum (fun p => 1 / (p : Real) ^ (2 : Nat)) := by
    rw [Finset.sum_map]
    change S.attach.sum (fun p => 1 / (p.val : Real) ^ (2 : Nat)) = _
    exact Finset.sum_attach S (fun p : Nat => (1 : Real) / (p : Real) ^ (2 : Nat))
  have hNonneg (p : T) : 0 <= f p := by
    change 0 <= (1 : Real) / (p.val.val : Real) ^ (2 : Nat)
    positivity
  have hBound : (S.attach.map e).sum f <= tsum f :=
    hs.sum_le_tsum (S.attach.map e) (fun p _ => hNonneg p)
  rw [hSum] at hBound
  exact hBound

theorem finite_modifiedLcm_defect_low_bound
    (S : Finset Nat) (N J : Nat) (hN : 0 < N)
    (hPrime : forall p, Membership.mem S p -> Nat.Prime p)
    (hCut : forall p, Membership.mem S p -> p <= J) :
    S.sum (lcmExponentDefect (modifiedLcm N)) <= (J : Real) / (N : Real) := by
  have hn : (0 : Real) < N := by exact_mod_cast hN
  have hSubset : S <= Finset.Icc 1 J := by
    intro p hp
    exact Finset.mem_Icc.mpr (And.intro (hPrime p hp).one_le (hCut p hp))
  have hCard : S.card <= J := by simpa using Finset.card_le_card hSubset
  have hCardReal : (S.card : Real) <= J := by exact_mod_cast hCard
  calc
    _ <= S.sum (fun _ => 1 / (N : Real)) :=
      Finset.sum_le_sum (fun p hp => (modifiedLcm_exponentDefect_lt N hN (hPrime p hp)).le)
    _ = (S.card : Real) / (N : Real) := by simp [div_eq_mul_inv]
    _ <= _ := div_le_div_of_nonneg_right hCardReal hn.le

theorem finite_modifiedLcm_defect_high_bound
    (S : Finset Nat) (N J : Nat) (hJ : 1 <= J)
    (hPrime : forall p, Membership.mem S p -> Nat.Prime p)
    (hCut : forall p, Membership.mem S p -> J < p)
    (hSquare : forall p, Membership.mem S p -> p ^ 2 <= 2 * N) :
    S.sum (lcmExponentDefect (modifiedLcm N)) <= 2 / (J : Real) ^ (2 : Nat) := by
  have hJPos : (0 : Real) < J := by exact_mod_cast (show 0 < J by omega)
  have hLocal (p : Nat) (hp : Membership.mem S p) :
      lcmExponentDefect (modifiedLcm N) p <=
        (1 / (J : Real)) * (1 / (p : Real) ^ (2 : Nat)) := by
    have hpPos : (0 : Real) < p := by exact_mod_cast (hPrime p hp).pos
    have hCast : (J : Real) <= p := by exact_mod_cast (hCut p hp).le
    have hInv := one_div_le_one_div_of_le hJPos hCast
    calc
      _ <= 1 / (p : Real) ^ (3 : Nat) :=
        modifiedLcm_defect_le_cube N (hPrime p hp) (hSquare p hp)
      _ = (1 / (p : Real)) * (1 / (p : Real) ^ (2 : Nat)) := by ring
      _ <= _ := mul_le_mul_of_nonneg_right hInv (by positivity)
  have hTail : primeReciprocalSquareTail J <= 2 / (J : Real) := by
    have hQ := (primeProfileQuadraticTail_bounds J hJ).2
    have hDiff := (primeProfileQuadraticTail_shift_bound J hJ).1
    linarith only [hQ, hDiff]
  calc
    _ <= S.sum (fun p => (1 / (J : Real)) * (1 / (p : Real) ^ (2 : Nat))) :=
      Finset.sum_le_sum hLocal
    _ = (1 / (J : Real)) * S.sum (fun p => 1 / (p : Real) ^ (2 : Nat)) :=
      (Finset.mul_sum _ _ _).symm
    _ <= (1 / (J : Real)) * primeReciprocalSquareTail J :=
      mul_le_mul_of_nonneg_left (finite_prime_reciprocal_sq_le_tail S J hPrime hCut)
        (by positivity)
    _ <= (1 / (J : Real)) * (2 / (J : Real)) :=
      mul_le_mul_of_nonneg_left hTail (by positivity)
    _ = _ := by ring

theorem finite_modifiedLcm_defect_bound
    (S : Finset Nat) (N J : Nat) (hN : 0 < N) (hJ : 1 <= J)
    (hPrime : forall p, Membership.mem S p -> Nat.Prime p)
    (hSquare : forall p, Membership.mem S p -> p ^ 2 <= 2 * N) :
    S.sum (lcmExponentDefect (modifiedLcm N)) <=
      (J : Real) / (N : Real) + 2 / (J : Real) ^ (2 : Nat) := by
  let L := S.filter (fun p => p <= J)
  let H := S.filter (fun p => Not (p <= J))
  have hL := finite_modifiedLcm_defect_low_bound L N J hN
    (fun p hp => hPrime p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2)
  have hH := finite_modifiedLcm_defect_high_bound H N J hJ
    (fun p hp => hPrime p (Finset.mem_filter.mp hp).1)
    (fun p hp => Nat.lt_of_not_ge (Finset.mem_filter.mp hp).2)
    (fun p hp => hSquare p (Finset.mem_filter.mp hp).1)
  have hSplit := Finset.sum_filter_add_sum_filter_not S (fun p => p <= J)
    (lcmExponentDefect (modifiedLcm N))
  change L.sum _ + H.sum _ = S.sum _ at hSplit
  linarith only [hL, hH, hSplit]

def modifiedLcmSmallDefect (N : Nat) : Real :=
  ((Nat.primesLE N).filter (fun p => p ^ 2 <= 2 * N)).sum
    (lcmExponentDefect (modifiedLcm N))

def modifiedLcmUpperSquareSum (N : Nat) : Real :=
  ((Nat.primesLE N).filter (fun p => 2 * N < p ^ 2)).sum
    (fun p => 1 / (p : Real) ^ (2 : Nat))

theorem modifiedLcm_defect_exact_split (N : Nat) :
    lcmDefectSum (modifiedLcm N) = modifiedLcmSmallDefect N + modifiedLcmUpperSquareSum N := by
  have hSplit := Finset.sum_filter_add_sum_filter_not (Nat.primesLE N)
    (fun p => p ^ 2 <= 2 * N) (lcmExponentDefect (modifiedLcm N))
  have hHigh :
      ((Nat.primesLE N).filter (fun p => Not (p ^ 2 <= 2 * N))).sum
        (lcmExponentDefect (modifiedLcm N)) = modifiedLcmUpperSquareSum N := by
    unfold modifiedLcmUpperSquareSum
    simp only [not_le]
    apply Finset.sum_congr rfl
    intro p hp
    have hMem := Finset.mem_filter.mp hp
    exact modifiedLcm_defect_eq_square N (Nat.prime_of_mem_primesLE hMem.1)
      (Nat.le_of_mem_primesLE hMem.1) hMem.2
  rw [hHigh] at hSplit
  unfold lcmDefectSum
  rw [modifiedLcm_primeFactors]
  exact hSplit.symm

theorem modifiedLcm_defect_error_bound (N J : Nat) (hN : 0 < N) (hJ : 1 <= J) :
    0 <= lcmDefectSum (modifiedLcm N) - modifiedLcmUpperSquareSum N /\
      lcmDefectSum (modifiedLcm N) - modifiedLcmUpperSquareSum N <=
        (J : Real) / (N : Real) + 2 / (J : Real) ^ (2 : Nat) := by
  rw [modifiedLcm_defect_exact_split, add_sub_cancel_right]
  refine And.intro ?_ ?_
  . exact Finset.sum_nonneg (fun p _ => modifiedLcm_defect_nonneg N p)
  . exact finite_modifiedLcm_defect_bound _ N J hN hJ
      (fun p hp => Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1)
      (fun p hp => (Finset.mem_filter.mp hp).2)

end PrimeFactorOscillations
