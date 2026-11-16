/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCutRowIdentity
import PrimeFactorOscillations.Helpers.HamiltonianScalarRowTail

/-! # Simultaneous actual cross-cut row concentration

The union is over every row on the same full sign cube.
The exact signed row identity retains the original diagonal
mass and does not condition away the row's own sign.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

def hamiltonianCutRowBadSigns (P : Matrix I I Real) (alpha A : Real) : Finset (I -> Bool) := by
  classical
  exact Finset.univ.biUnion (fun i => hamiltonianScalarBadSigns (fun j => P i j)
    (Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real)))))

theorem hamiltonian_mem_cut_row_bad_signs
    (P : Matrix I I Real) (alpha A : Real) (e : I -> Bool)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1) :
    Membership.mem (hamiltonianCutRowBadSigns P alpha A) e <->
      Exists (fun i => Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real))) <
        abs (Finset.univ.sum (fun j => hamiltonianCrossCutKernel P e i j) - 1)) := by
  classical
  have hAbs (i : I) := hamiltonian_cross_cut_row_absolute_defect P e i (hRows i)
  simp only [hamiltonianCutRowBadSigns, Finset.mem_biUnion, Finset.mem_univ, true_and,
    hamiltonian_mem_scalar_bad_signs, hAbs]

theorem hamiltonian_all_cut_rows_polynomial_tail
    (P : Matrix I I Real) (alpha A : Real) (hA : 0 < A)
    (hNonneg : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hSize : 2 <= Fintype.card I) :
    ((hamiltonianCutRowBadSigns P alpha A).card : Real) /
      (Fintype.card (I -> Bool) : Real) <=
        (Fintype.card I : Real) ^ (-(A + 4)) := by
  classical
  let n : Real := Fintype.card I
  let t := Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * n))
  let f := fun i => hamiltonianScalarBadSigns (fun j => P i j) t
  have hn : 2 <= n := by dsimp only [n]; exact_mod_cast hSize
  have hnPos : 0 < n := by linarith only [hn]
  have hNat : (Finset.univ.biUnion f).card <=
      Finset.univ.sum (fun i => (f i).card) := Finset.card_biUnion_le
  have hCount : ((Finset.univ.biUnion f).card : Real) <=
      Finset.univ.sum (fun i => ((f i).card : Real)) := by exact_mod_cast hNat
  have hEach (i : I) :
      ((f i).card : Real) / (Fintype.card (I -> Bool) : Real) <= n ^ (-(A + 5)) :=
    hamiltonian_scalar_row_uniform_polynomial_tail (fun j => P i j) alpha A hA
      (hNonneg i) (hCap i) (hRows i) hSize
  have hPower : n * n ^ (-(A + 5)) = n ^ (-(A + 4)) := by
    calc
      _ = n ^ (1 : Real) * n ^ (-(A + 5)) := by rw [Real.rpow_one]
      _ = n ^ ((1 : Real) + (-(A + 5))) := (Real.rpow_add hnPos _ _).symm
      _ = _ := by congr 1; ring
  change ((Finset.univ.biUnion f).card : Real) / _ <= n ^ (-(A + 4))
  calc
    _ <= (Finset.univ.sum (fun i => ((f i).card : Real))) /
        (Fintype.card (I -> Bool) : Real) :=
      div_le_div_of_nonneg_right hCount (Nat.cast_nonneg _)
    _ = Finset.univ.sum (fun i => ((f i).card : Real) / (Fintype.card (I -> Bool) : Real)) := by
      rw [Finset.sum_div]
    _ <= Finset.univ.sum (fun _ : I => n ^ (-(A + 5))) :=
      Finset.sum_le_sum (fun i hi => hEach i)
    _ = n * n ^ (-(A + 5)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rfl
    _ = _ := hPower

theorem hamiltonian_good_cut_all_row_defects
    (P : Matrix I I Real) (alpha A : Real) (e : I -> Bool)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hGood : Not (Membership.mem (hamiltonianCutRowBadSigns P alpha A) e)) :
    forall i, abs (Finset.univ.sum (fun j => hamiltonianCrossCutKernel P e i j) - 1) <=
      Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real))) := by
  intro i
  by_contra hNot
  exact hGood ((hamiltonian_mem_cut_row_bad_signs P alpha A e hRows).mpr
    (Exists.intro i (lt_of_not_ge hNot)))

end PrimeFactorOscillations
