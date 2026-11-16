/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRowCapPermanent

/-! # Complete scalar evaluation of the actual matching row-cap bound

A logarithmic potential telescopes the exact reveal-order grid.
The centering term minus the full matrix order is retained explicitly.
No column hypothesis or positive lower bound on entries is imposed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianLogPotential (x : Real) : Real := x * Real.log x - x

theorem hamiltonian_log_potential_increment
    (x h : Real) (hx : 0 < x) (hh : 0 <= h) :
    h * Real.log x <= hamiltonianLogPotential (x + h) - hamiltonianLogPotential x := by
  have hy : 0 < x + h := by linarith only [hx, hh]
  have hLog := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy)] at hLog
  have hScaled := mul_le_mul_of_nonneg_right hLog hy.le
  have hCancel : (x / (x + h) - 1) * (x + h) = -h := by
    field_simp [ne_of_gt hy]
    <;> ring
  rw [hCancel] at hScaled
  unfold hamiltonianLogPotential
  nlinarith only [hScaled]

theorem hamiltonian_log_grid_step
    (d c : Real) (hd : 0 < d) (hc : 0 < c) (j : Nat) :
    Real.log (c + (j : Real) / d) <= d *
      (hamiltonianLogPotential (c + ((j + 1 : Nat) : Real) / d) -
        hamiltonianLogPotential (c + (j : Real) / d)) := by
  have hx : 0 < c + (j : Real) / d := by positivity
  have hStep := hamiltonian_log_potential_increment
    (c + (j : Real) / d) (1 / d) hx (by positivity)
  have h := mul_le_mul_of_nonneg_left hStep hd.le
  have hUnit : d * (1 / d) = 1 := by field_simp [ne_of_gt hd]
  rw [<- mul_assoc, hUnit, one_mul] at h
  have hShift : c + (j : Real) / d + 1 / d =
      c + ((j + 1 : Nat) : Real) / d := by
    rw [Nat.cast_add, Nat.cast_one]
    ring
  rwa [hShift] at h

theorem hamiltonian_log_grid_sum
    (d : Nat) (hd : 1 <= d) (c : Real) (hc : 0 < c) :
    (Finset.range d).sum (fun j => Real.log (c + (j : Real) / (d : Real))) <=
      (d : Real) * (hamiltonianLogPotential (c + 1) - hamiltonianLogPotential c) := by
  have hdPos : 0 < (d : Real) := Nat.cast_pos.mpr (by omega)
  let f : Nat -> Real := fun j => hamiltonianLogPotential (c + (j : Real) / (d : Real))
  have hSum := Finset.sum_le_sum (fun j (_ : Membership.mem (Finset.range d) j) =>
    hamiltonian_log_grid_step (d : Real) c hdPos hc j)
  rw [<- Finset.mul_sum] at hSum
  have hTel (k : Nat) :
      (Finset.range k).sum (fun j => f (j + 1) - f j) = f k - f 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  change (Finset.range d).sum (fun j => Real.log (c + (j : Real) / (d : Real))) <=
    (d : Real) * (Finset.range d).sum (fun j => f (j + 1) - f j) at hSum
  rw [hTel] at hSum
  dsimp only [f] at hSum
  simpa only [Nat.cast_zero, zero_div, add_zero, div_self (ne_of_gt hdPos)] using hSum

theorem hamiltonian_row_cap_grid_reversal (n : Nat) (c : Real) :
    hamiltonianRowCapLogBound n c =
      (Finset.range (n + 2)).sum
        (fun j => Real.log (c + (j : Real) / (n + 1 : Real))) := by
  classical
  unfold hamiltonianRowCapLogBound
  apply Finset.sum_bij (fun k _ => n + 1 - k.val)
  . intro k hk
    exact Finset.mem_range.mpr (by have h := k.isLt; omega)
  . intro a ha b hb hEq
    apply Fin.ext
    have haLt := a.isLt
    have hbLt := b.isLt
    omega
  . intro j hj
    have hjLt := Finset.mem_range.mp hj
    let k : Fin (n + 2) := Fin.mk (n + 1 - j) (by omega)
    refine Exists.intro k (Exists.intro (Finset.mem_univ _) ?_)
    dsimp only [k]
    omega
  . intro k hk
    rfl

theorem hamiltonian_row_cap_potential_bound (n : Nat) (c : Real) (hc : 0 < c) :
    hamiltonianRowCapLogBound n c <=
      (n + 1 : Real) * (hamiltonianLogPotential (c + 1) - hamiltonianLogPotential c) +
        Real.log (c + 1) := by
  rw [hamiltonian_row_cap_grid_reversal, Finset.sum_range_succ]
  have h := hamiltonian_log_grid_sum (n + 1) (by omega) c hc
  have hn : Not ((n + 1 : Real) = 0) := by positivity
  have hLast : c + ((n + 1 : Nat) : Real) / (n + 1 : Real) = c + 1 := by
    simp only [Nat.cast_add, Nat.cast_one]
    rw [div_self hn]
  rw [hLast]
  simp only [Nat.cast_add, Nat.cast_one] at h
  linarith only [h]

theorem hamiltonian_row_cap_entropy_bound
    (n : Nat) (c : Real) (hc : 0 < c) (hc1 : c <= 1) :
    hamiltonianRowCapLogBound n c <=
      -(n + 2 : Real) + 1 + (n + 2 : Real) * (2 * c - c * Real.log c) := by
  let d : Real := n + 1
  have hd : 0 <= d := by dsimp [d]; positivity
  have h := hamiltonian_row_cap_potential_bound n c hc
  have hShape : (n + 1 : Real) *
      (hamiltonianLogPotential (c + 1) - hamiltonianLogPotential c) +
        Real.log (c + 1) =
      -d + (d * (c + 1) + 1) * Real.log (c + 1) - d * c * Real.log c := by
    dsimp [hamiltonianLogPotential, d]
    ring
  rw [hShape] at h
  have hLog := Real.log_le_sub_one_of_pos (show 0 < c + 1 by linarith only [hc])
  have hLog1 : Real.log (c + 1) <= c := by linarith only [hLog]
  have hCoeff : 0 <= d * (c + 1) + 1 := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hLog1 hCoeff
  have hSquare : c ^ 2 <= c := by nlinarith only [hc, hc1]
  have hDSquare := mul_le_mul_of_nonneg_left hSquare hd
  have hLogC : Real.log c <= 0 := by
    have hMono := Real.log_le_log hc hc1
    simpa only [Real.log_one] using hMono
  have hCLog : c * Real.log c <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc.le hLogC
  have hOrder : (n + 2 : Real) = d + 1 := by dsimp [d]; ring
  rw [hOrder]
  nlinarith only [h, hScaled, hDSquare, hCLog, hc]

end PrimeFactorOscillations
