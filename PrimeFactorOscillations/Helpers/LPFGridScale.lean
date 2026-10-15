/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import PrimeFactorOscillations.Helpers.LPFGridReference

/-!
# Physical normalization of the complete major square-difference packet

The major squared error remains the inverse transform of S^2-A^2 on G.
After exact grid separation and reference Parseval, its target is
8*E^2*P*M + 6*E^4*P^3/M. With E=O(M^alpha*P^(3/2)*log^2 M),
these are the retained M^(2*alpha+1)*P^4 and M^(4*alpha-1)*P^9
terms of the COMPLETE budget, alongside M^3/P, M^(13/5) and M^2*P^2.
No minor or tail estimate is supplied here. N is an auxiliary grid;
the source prime-prefix estimate must use its small denominator q.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

theorem lpfRationalGrid_scaled_width {N : Nat} [NeZero N] (M P : Nat)
    (hM : 0 < M) (hDiv : Dvd.dvd M N) (hSmall : 2 * P ^ 3 < M) :
    2 * ((N / M) * P) * P ^ 2 < N := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hD : 0 < N / M := Nat.div_pos (Nat.le_of_dvd hN hDiv) hM
  calc
    _ = (N / M) * (2 * P ^ 3) := by ring
    _ < (N / M) * M := Nat.mul_lt_mul_of_pos_left hSmall hD
    _ = N := Nat.div_mul_cancel hDiv

theorem lpfRationalGrid_normalized_card {N : Nat} [NeZero N] (M P : Nat)
    (hM : 0 < M) (hP : 0 < P) (hDiv : Dvd.dvd M N) :
    ((lpfRationalGrid N P ((N / M) * P)).card : Real) / (N : Real) <=
      3 * (P : Real) ^ 3 / (M : Real) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNr : 0 < (N : Real) := by exact_mod_cast hN
  have hMr : 0 < (M : Real) := by exact_mod_cast hM
  have hD : 0 < N / M := Nat.div_pos (Nat.le_of_dvd hN hDiv) hM
  have hW : 1 <= (N / M) * P := by nlinarith
  have hCard : (lpfRationalGrid N P ((N / M) * P)).card <= 3 * P ^ 3 * (N / M) := by
    have h := lpfRationalGrid_card_le N P ((N / M) * P)
    have hW3 : 2 * ((N / M) * P) + 1 <= 3 * ((N / M) * P) := by omega
    have hScaled := Nat.mul_le_mul_left (P ^ 2) hW3
    nlinarith only [h, hScaled]
  have hRaw : ((lpfRationalGrid N P ((N / M) * P)).card : Real) <=
      3 * (P : Real) ^ 3 * ((N / M : Nat) : Real) := by exact_mod_cast hCard
  have hMD : ((N / M : Nat) : Real) * (M : Real) = (N : Real) := by
    exact_mod_cast (Nat.div_mul_cancel hDiv)
  apply (mul_le_mul_iff_of_pos_right (mul_pos hNr hMr)).mp
  have hLeft : (((lpfRationalGrid N P ((N / M) * P)).card : Real) / (N : Real)) *
      ((N : Real) * (M : Real)) = ((lpfRationalGrid N P ((N / M) * P)).card : Real) * M := by
    field_simp
  have hRight : (3 * (P : Real) ^ 3 / (M : Real)) * ((N : Real) * (M : Real)) =
      3 * (P : Real) ^ 3 * N := by field_simp
  rw [hLeft, hRight]
  simpa only [mul_assoc, hMD] using mul_le_mul_of_nonneg_right hRaw hMr.le

theorem lpfRationalGridReference_normalized_interval_energy {N : Nat} [NeZero N]
    (M P : Nat) (U : Finset Nat) (hM : 0 < M) (hP : 0 < P)
    (hDivM : Dvd.dvd M N) (hDiv : forall q, 0 < q -> q <= P -> Dvd.dvd q N)
    (hSmall : 2 * P ^ 3 < M) (hCard : U.card <= M)
    (hU : forall n, Membership.mem U n -> n < N) :
    (Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq
      (lpfRationalGridReference N P ((N / M) * P)
        (fun k => lpfFiniteTransform U (fun n => (n : ZMod N)) (fun _ => (1 : Complex)) (k : ZMod N)) x))) /
      (N : Real) <= (P : Real) * (M : Real) := by
  have hNr : 0 < (N : Real) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hRaw := lpfRationalGridReference_interval_energy P ((N / M) * P) U hP hDiv
    (lpfRationalGrid_scaled_width M P hM hDivM hSmall) hU
  apply (mul_le_mul_iff_of_pos_right hNr).mp
  calc
    _ = Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq
        (lpfRationalGridReference N P ((N / M) * P)
          (fun k => lpfFiniteTransform U (fun n => (n : ZMod N)) (fun _ => (1 : Complex)) (k : ZMod N)) x)) := by
      field_simp
    _ <= (P : Real) * (N : Real) * (U.card : Real) := hRaw
    _ <= (P : Real) * (N : Real) * (M : Real) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hCard) (by positivity)
    _ = _ := by ring

theorem lpfRationalGrid_complete_major_bound {N : Nat} [NeZero N]
    (M P : Nat) (U : Finset Nat) (S : ZMod N -> Complex) (T : Finset (ZMod N)) (E : Real)
    (hM : 0 < M) (hP : 0 < P) (hE : 0 <= E)
    (hDivM : Dvd.dvd M N) (hDiv : forall q, 0 < q -> q <= P -> Dvd.dvd q N)
    (hSmall : 2 * P ^ 3 < M) (hCard : U.card <= M)
    (hU : forall n, Membership.mem U n -> n < N)
    (hError : forall x, Membership.mem (lpfRationalGrid N P ((N / M) * P)) x ->
      norm (S x - lpfRationalGridReference N P ((N / M) * P)
        (fun k => lpfFiniteTransform U (fun n => (n : ZMod N)) (fun _ => (1 : Complex)) (k : ZMod N)) x) <= E) :
    Finset.sum T (fun t => Complex.normSq (lpfCyclicInverse
      (fun x => if Membership.mem (lpfRationalGrid N P ((N / M) * P)) x then
        S x ^ 2 - (lpfRationalGridReference N P ((N / M) * P)
          (fun k => lpfFiniteTransform U (fun n => (n : ZMod N)) (fun _ => (1 : Complex)) (k : ZMod N)) x) ^ 2 else 0) t)) <=
      8 * E ^ 2 * (P : Real) * (M : Real) + 6 * E ^ 4 * (P : Real) ^ 3 / (M : Real) := by
  let G := lpfRationalGrid N P ((N / M) * P)
  let A := lpfRationalGridReference N P ((N / M) * P)
    (fun k => lpfFiniteTransform U (fun n => (n : ZMod N)) (fun _ => (1 : Complex)) (k : ZMod N))
  have hNr : 0 < (N : Real) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hRef : (Finset.sum G (fun x => Complex.normSq (A x))) / (N : Real) <=
      (P : Real) * (M : Real) := by
    have hSub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
      (fun x _ _ => Complex.normSq_nonneg (A x))
    exact (div_le_div_of_nonneg_right hSub hNr.le).trans
      (lpfRationalGridReference_normalized_interval_energy M P U hM hP hDivM hDiv hSmall hCard hU)
  have hGrid := lpfRationalGrid_normalized_card M P hM hP hDivM
  have hMajor := lpfCyclicInverse_major_error_bound S A G T E hE hError
  have hAlg : (N : Real) ^ (-1 : Int) *
      (8 * E ^ 2 * Finset.sum G (fun x => Complex.normSq (A x)) + 2 * E ^ 4 * (G.card : Real)) =
      8 * E ^ 2 * (Finset.sum G (fun x => Complex.normSq (A x)) / (N : Real)) +
        2 * E ^ 4 * ((G.card : Real) / (N : Real)) := by
    simp only [zpow_neg_one, div_eq_mul_inv]
    ring
  rw [hAlg] at hMajor
  have hFinal := add_le_add (mul_le_mul_of_nonneg_left hRef (by positivity : 0 <= 8 * E ^ 2))
    (mul_le_mul_of_nonneg_left hGrid (by positivity : 0 <= 2 * E ^ 4))
  change Finset.sum T (fun t => Complex.normSq (lpfCyclicInverse
    (fun x => if Membership.mem G x then S x ^ 2 - A x ^ 2 else 0) t)) <= _
  exact hMajor.trans (by convert hFinal using 1; ring)

end PrimeFactorOscillations.LPF
