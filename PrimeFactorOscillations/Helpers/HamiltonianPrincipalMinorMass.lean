/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFactorialMinorMass

/-! # Actual principal-minor mass with a factorial envelope

Every supported principal minor is included. The estimate is used only
for the residual after the exact signed aperiodic sum is evaluated.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianPrincipalRankMass (M : Matrix Iota Iota Real) (r : Nat) : Real :=
  (Finset.univ.powersetCard r).sum (fun S => abs (principalMinorDet M S))

theorem hamiltonian_principal_rank_mass_nonnegative
    (M : Matrix Iota Iota Real) (r : Nat) :
    0 <= hamiltonianPrincipalRankMass M r :=
  Finset.sum_nonneg (fun S _ => abs_nonneg (principalMinorDet M S))

theorem hamiltonian_principal_rank_mass_local_budget
    (M : Matrix Iota Iota Real) (c : Real) (hc : 0 < c)
    (hEntry : forall i j, abs (M i j) <= c) (r : Nat) (hr : 0 < r) :
    hamiltonianPrincipalRankMass M r ^ 2 <=
      ((Fintype.card Iota).choose r : Real) ^ 2 *
        (Real.exp (r : Real) * ((r : Real) * c ^ 2) ^ r) := by
  let H : Real := Real.exp (r : Real) * ((r : Real) * c ^ 2) ^ r
  have hH : 0 <= H :=
    mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (mul_nonneg (Nat.cast_nonneg r) (sq_nonneg c)) r)
  have hEach (S : Finset Iota)
      (hS : Membership.mem (Finset.univ.powersetCard r) S) :
      abs (principalMinorDet M S) <= Real.sqrt H := by
    have hCard : S.card = r := (Finset.mem_powersetCard.mp hS).2
    have hCardType : Fintype.card S = r := by simpa only [Fintype.card_coe] using hCard
    have hLocal := hamiltonian_local_minor_hadamard_budget
      (M.submatrix (Subtype.val : S -> Iota) (Subtype.val : S -> Iota)) c hc
      (by rw [hCardType]; exact hr) (fun i j => hEntry i.val j.val)
    have hSq : principalMinorDet M S ^ 2 <= H := by
      simpa only [principalMinorDet, hCardType, H] using hLocal
    have h := Real.sqrt_le_sqrt hSq
    rw [Real.sqrt_sq_eq_abs] at h
    exact h
  have hSum : hamiltonianPrincipalRankMass M r <=
      ((Fintype.card Iota).choose r : Real) * Real.sqrt H := by
    calc
      _ <= (Finset.univ.powersetCard r).sum (fun _ => Real.sqrt H) :=
        Finset.sum_le_sum hEach
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
  have hRhs : 0 <= ((Fintype.card Iota).choose r : Real) * Real.sqrt H :=
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg H)
  have hSq := mul_le_mul hSum hSum
    (hamiltonian_principal_rank_mass_nonnegative M r) hRhs
  calc
    _ <= (((Fintype.card Iota).choose r : Real) * Real.sqrt H) ^ 2 := by
      nlinarith only [hSq]
    _ = _ := by rw [mul_pow, Real.sq_sqrt hH]

theorem hamiltonian_principal_rank_mass_factorial_bound
    (M : Matrix Iota Iota Real) (c : Real) (hc : 0 < c)
    (hEntry : forall i j, abs (M i j) <= c) (r : Nat) :
    hamiltonianPrincipalRankMass M r ^ 2 <=
      (Real.exp 2 * ((Fintype.card Iota : Real) * c) ^ 2) ^ r /
        (r.factorial : Real) := by
  by_cases hr : r = 0
  case pos =>
    subst r
    simp [hamiltonianPrincipalRankMass, principalMinorDet]
  case neg =>
    have hrPos : 0 < r := Nat.pos_of_ne_zero hr
    let b : Real := ((Fintype.card Iota).choose r : Real) * c ^ r
    let f : Real := r.factorial
    let A : Real := (Fintype.card Iota : Real) * c
    have hf : 0 < f := by dsimp [f]; exact_mod_cast Nat.factorial_pos r
    have hb : 0 <= b := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc.le r)
    have hA : 0 <= A := mul_nonneg (Nat.cast_nonneg _) hc.le
    have hChoose : ((Fintype.card Iota).choose r : Real) * f <=
        (Fintype.card Iota : Real) ^ r := by
      have hDesc : ((Fintype.card Iota).descFactorial r : Real) <=
          (Fintype.card Iota : Real) ^ r := by
        exact_mod_cast Nat.descFactorial_le_pow (Fintype.card Iota) r
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul] at hDesc
      dsimp [f]
      nlinarith only [hDesc]
    have hbScaled : b * f <= A ^ r := by
      have h := mul_le_mul_of_nonneg_right hChoose (pow_nonneg hc.le r)
      dsimp [b, A]
      rw [mul_pow]
      nlinarith only [h]
    have hbSquare : (b * f) ^ 2 <= (A ^ r) ^ 2 := by
      have h := mul_le_mul hbScaled hbScaled (mul_nonneg hb hf.le) (pow_nonneg hA r)
      nlinarith only [h]
    have hLocal : hamiltonianPrincipalRankMass M r ^ 2 <=
        Real.exp (r : Real) * (r : Real) ^ r * b ^ 2 := by
      have h := hamiltonian_principal_rank_mass_local_budget M c hc hEntry r hrPos
      have hIdentity :
          ((Fintype.card Iota).choose r : Real) ^ 2 *
            (Real.exp (r : Real) * ((r : Real) * c ^ 2) ^ r) =
          Real.exp (r : Real) * (r : Real) ^ r * b ^ 2 := by
        dsimp [b]
        rw [mul_pow, mul_pow, pow_right_comm]
        ring
      rw [hIdentity] at h
      exact h
    have hTerm := hamiltonian_exponential_term_bound (r : Real) (Nat.cast_nonneg r) r
    have hExp : Real.exp (r : Real) * Real.exp (r : Real) = (Real.exp 2) ^ r := by
      rw [<- Real.exp_add, <- hamiltonian_exp_nat_scalar 2 r]
      congr 1
      ring
    have hScaled : hamiltonianPrincipalRankMass M r ^ 2 * f ^ 2 <=
        (Real.exp 2 * A ^ 2) ^ r * f := by
      calc
        _ <= (Real.exp (r : Real) * (r : Real) ^ r * b ^ 2) * f ^ 2 :=
          mul_le_mul_of_nonneg_right hLocal (sq_nonneg f)
        _ = (Real.exp (r : Real) * (r : Real) ^ r) * (b * f) ^ 2 := by ring
        _ <= (Real.exp (r : Real) * (r : Real) ^ r) * (A ^ r) ^ 2 :=
          mul_le_mul_of_nonneg_left hbSquare
            (mul_nonneg (Real.exp_pos _).le (pow_nonneg (Nat.cast_nonneg r) r))
        _ <= (Real.exp (r : Real) * (Real.exp (r : Real) * f)) * (A ^ r) ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hTerm (Real.exp_pos _).le) (sq_nonneg (A ^ r))
        _ = (Real.exp (r : Real) * Real.exp (r : Real)) * (A ^ r) ^ 2 * f := by ring
        _ = _ := by
          rw [hExp, pow_right_comm A r 2, <- mul_pow]
    have hCancel : hamiltonianPrincipalRankMass M r ^ 2 * f <=
        (Real.exp 2 * A ^ 2) ^ r := by
      nlinarith only [hScaled, hf]
    calc
      _ = (hamiltonianPrincipalRankMass M r ^ 2 * f) / f := by field_simp
      _ <= (Real.exp 2 * A ^ 2) ^ r / f :=
        div_le_div_of_nonneg_right hCancel hf.le

theorem hamiltonian_principal_tilted_rank_mass_bound
    (M : Matrix Iota Iota Real) (c z : Real) (hc : 0 < c)
    (hEntry : forall i j, abs (M i j) <= c) (n : Nat) :
    Finset.sum (Finset.range n)
      (fun r => (r : Real) * z ^ r * hamiltonianPrincipalRankMass M r) <=
      2 * Real.exp (16 * Real.exp 2 * ((Fintype.card Iota : Real) * c) ^ 2 * z ^ 2) := by
  have hC : 0 <= Real.exp 2 * ((Fintype.card Iota : Real) * c) ^ 2 :=
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have h := hamiltonian_factorial_weighted_mass_bound
    (hamiltonianPrincipalRankMass M)
    (Real.exp 2 * ((Fintype.card Iota : Real) * c) ^ 2) z hC
    (hamiltonian_principal_rank_mass_factorial_bound M c hc hEntry) n
  simpa only [mul_assoc] using h

end PrimeFactorOscillations
