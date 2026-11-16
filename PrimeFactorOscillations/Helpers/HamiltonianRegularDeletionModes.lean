/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCenteredContraction
import PrimeFactorOscillations.Helpers.HamiltonianFiniteFactorCentering

/-! # Complete normalized regular deletions with the signed mean mode retained -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota : Type*} [Fintype Iota] [DecidableEq Iota]
variable [Fintype Jota] [DecidableEq Jota]

def hamiltonianRegularDeletionKernel (S Q : Matrix Iota Iota Real) (alpha : Real) :
    Matrix Iota Iota Real := SMul.smul (1 / (1 - alpha)) (S - Q)

theorem hamiltonian_nonnegative_matrix_smul_norm
    (c : Real) (M : Matrix Iota Iota Real) (hc : 0 <= c) :
    norm (SMul.smul c M) = c * norm M := by
  have h : norm (SMul.smul c M) = norm c * norm M := norm_smul c M
  rw [Real.norm_of_nonneg hc] at h
  exact h

theorem hamiltonian_regular_deletion_centered_identity
    (S Q : Matrix Iota Iota Real) (q alpha : Real) (hAlpha : alpha < 1) :
    centeredKernel (hamiltonianRegularDeletionKernel S Q alpha) q =
      SMul.smul (1 / (1 - alpha))
        (centeredKernel S q - (Q - SMul.smul alpha (averagingKernel q))) := by
  have hGap : Not (1 - alpha = 0) := ne_of_gt (sub_pos.mpr hAlpha)
  ext i j
  change (1 / (1 - alpha)) * (S i j - Q i j) - q =
    (1 / (1 - alpha)) * ((S i j - q) - (Q i j - alpha * q))
  field_simp [hGap]
  <;> ring

theorem hamiltonian_regular_deletion_stochastic
    (S Q : Matrix Iota Iota Real) (alpha : Real) (hAlpha : alpha < 1)
    (hSRow : forall i, Finset.univ.sum (fun j => S i j) = 1)
    (hSCol : forall j, Finset.univ.sum (fun i => S i j) = 1)
    (hQRow : forall i, Finset.univ.sum (fun j => Q i j) = alpha)
    (hQCol : forall j, Finset.univ.sum (fun i => Q i j) = alpha)
    (hSub : forall i j, Q i j <= S i j) :
    (forall i, Finset.univ.sum (fun j =>
      hamiltonianRegularDeletionKernel S Q alpha i j) = 1) /\
    (forall j, Finset.univ.sum (fun i =>
      hamiltonianRegularDeletionKernel S Q alpha i j) = 1) /\
    (forall i j, 0 <= hamiltonianRegularDeletionKernel S Q alpha i j) := by
  have hGap : 0 < 1 - alpha := sub_pos.mpr hAlpha
  have hc : 0 <= 1 / (1 - alpha) := le_of_lt (one_div_pos.mpr hGap)
  refine And.intro ?_ (And.intro ?_ ?_)
  next =>
    intro i
    change Finset.univ.sum (fun j => (1 / (1 - alpha)) * (S i j - Q i j)) = 1
    rw [<- Finset.mul_sum, Finset.sum_sub_distrib, hSRow i, hQRow i]
    field_simp
  next =>
    intro j
    change Finset.univ.sum (fun i => (1 / (1 - alpha)) * (S i j - Q i j)) = 1
    rw [<- Finset.mul_sum, Finset.sum_sub_distrib, hSCol j, hQCol j]
    field_simp
  next =>
    intro i j
    exact mul_nonneg hc (sub_nonneg.mpr (hSub i j))

theorem hamiltonian_regular_deletion_entry_cap
    (S Q : Matrix Iota Iota Real) (alpha u : Real) (hAlpha : alpha < 1)
    (hQ : forall i j, 0 <= Q i j) (hS : forall i j, S i j <= u) (i j : Iota) :
    hamiltonianRegularDeletionKernel S Q alpha i j <= (1 / (1 - alpha)) * u := by
  have hc : 0 <= 1 / (1 - alpha) := le_of_lt (one_div_pos.mpr (sub_pos.mpr hAlpha))
  change (1 / (1 - alpha)) * (S i j - Q i j) <= _
  exact mul_le_mul_of_nonneg_left (by linarith only [hQ i j, hS i j]) hc

theorem hamiltonian_regular_deletion_modes
    (S Q : Matrix Iota Iota Real) (U : Matrix Iota Jota Real)
    (V : Matrix Jota Iota Real) (q alpha eta gamma L : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (hq0 : 0 <= q)
    (ha0 : 0 <= alpha) (ha : alpha <= (1 / 4 : Real))
    (hEta : eta <= (1 / 100 : Real)) (hL : 0 <= L)
    (hQRow : forall i, Finset.univ.sum (fun j => Q i j) = alpha)
    (hQCol : forall j, Finset.univ.sum (fun i => Q i j) = alpha)
    (hQ : forall i j, 0 <= Q i j)
    (hS : norm (centeredKernel S q) <= gamma)
    (hApprox : norm (S - U * V) <= eta) (hU : norm U <= L) (hV : norm V <= L) :
    exists R : Matrix Iota Iota Real,
      exists A : Matrix Iota (Sum Jota PUnit) Real,
        exists B : Matrix (Sum Jota PUnit) Iota Real,
          centeredKernel (hamiltonianRegularDeletionKernel S Q alpha) q = R + A * B /\
            norm R <= (2 / 5 : Real) /\
            norm A <= 2 * L + 2 /\ norm B <= 2 * L + 2 /\
            norm (centeredKernel (hamiltonianRegularDeletionKernel S Q alpha) q) <=
              (gamma + alpha) / (1 - alpha) := by
  have ha1 : alpha < 1 := by linarith only [ha]
  have hGap : 0 < 1 - alpha := sub_pos.mpr ha1
  let c := 1 / (1 - alpha)
  have hc : 0 <= c := le_of_lt (one_div_pos.mpr hGap)
  have hc2 : c <= 2 := by
    calc
      _ <= 1 / (1 / 2 : Real) := div_le_div_of_nonneg_left
        (by norm_num) (by norm_num) (by linarith only [ha])
      _ = _ := by norm_num
  have hQNorm := hamiltonian_nonnegative_regular_norm Q alpha ha0 hQRow hQCol hQ
  have hQCentered := hamiltonian_regular_centered_contraction Q q alpha hq ha0 hQRow hQCol hQ
  have hGlobal : norm (centeredKernel (hamiltonianRegularDeletionKernel S Q alpha) q) <=
      (gamma + alpha) / (1 - alpha) := by
    rw [hamiltonian_regular_deletion_centered_identity S Q q alpha ha1]
    rw [hamiltonian_nonnegative_matrix_smul_norm _ _ hc]
    calc
      _ <= c * (norm (centeredKernel S q) +
          norm (Q - SMul.smul alpha (averagingKernel q))) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) hc
      _ <= c * (gamma + alpha) :=
        mul_le_mul_of_nonneg_left (add_le_add hS hQCentered) hc
      _ = _ := by dsimp [c]; ring
  let R := SMul.smul c (S - U * V - Q)
  have hR : norm R <= (2 / 5 : Real) := by
    have hSmall : eta + alpha <= (2 / 5 : Real) * (1 - alpha) := by
      linarith only [hEta, ha]
    calc
      _ = c * norm (S - U * V - Q) := hamiltonian_nonnegative_matrix_smul_norm c _ hc
      _ <= c * (norm (S - U * V) + norm Q) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) hc
      _ <= c * (eta + alpha) :=
        mul_le_mul_of_nonneg_left (add_le_add hApprox hQNorm) hc
      _ <= c * ((2 / 5 : Real) * (1 - alpha)) :=
        mul_le_mul_of_nonneg_left hSmall hc
      _ = _ := by dsimp [c]; field_simp <;> ring
  choose A B hFactor hA hB using hamiltonian_finite_factor_centering U V q c L
    hq hq0 hc hc2 hL hU hV
  refine Exists.intro R (Exists.intro A (Exists.intro B
    (And.intro ?_ (And.intro hR (And.intro hA (And.intro hB hGlobal))))))
  rw [<- hFactor]
  ext i j
  change c * (S i j - Q i j) - q =
    c * (S i j - (U * V) i j - Q i j) + (c * (U * V) i j - q)
  ring

end PrimeFactorOscillations
