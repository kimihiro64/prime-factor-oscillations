/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRationalTailNorm

/-! # Fixed-dimensional transport of the complete retained rational modes

The moving rational index is exchanged with a fixed denominator cutoff.
All signed coefficients and character phases agree exactly, including
the inactive denominators when the moving cutoff is initially smaller.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_fin_sum_cutoff_commute (Q H : Nat) (f : Nat -> Complex) :
    Finset.univ.sum (fun q : Fin Q => if q.val < H then f q.val else 0) =
      Finset.univ.sum (fun q : Fin H => if q.val < Q then f q.val else 0) := by
  rw [Fin.sum_univ_eq_sum_range (fun q => if q < H then f q else 0) Q,
    Fin.sum_univ_eq_sum_range (fun q => if q < Q then f q else 0) H]
  rw [<- Finset.sum_filter, <- Finset.sum_filter]
  have heq : (Finset.range Q).filter (fun q => q < H) =
      (Finset.range H).filter (fun q => q < Q) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, and_comm]
  rw [heq]

def hamiltonianRationalDenominatorTerm (R : Nat) [NeZero R] (q : Nat) (t : ZMod R) : Complex :=
  Finset.univ.sum (fun a : Units (ZMod (q + 1)) =>
    lpfRationalCoefficient (q + 1) *
      ZMod.stdAddChar ((-lpfRationalGridPoint R (q + 1) (a : ZMod (q + 1)).val 0) * t))

theorem hamiltonian_rational_masked_sum (R : Nat) [NeZero R] (Q H : Nat) (t : ZMod R) :
    Finset.univ.sum (fun u : lpfRationalCenters Q =>
      (if u.1.val + 1 <= H then lpfRationalCoefficient (u.1.val + 1) else 0) *
        ZMod.stdAddChar ((-hamiltonianRationalCenter R Q u) * t)) =
    Finset.univ.sum (fun q : Fin Q =>
      if q.val < H then hamiltonianRationalDenominatorTerm R q.val t else 0) := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hLow : q.val < H
  . have hLe : q.val + 1 <= H := by omega
    simp only [hLe, hLow, ite_true]
    rfl
  . have hNot : Not (q.val + 1 <= H) := by omega
    simp only [hNot, hLow, ite_false, zero_mul, Finset.sum_const_zero]

theorem hamiltonian_rational_denominator_transport
    (n R : Nat) [NeZero R] (Q H : Nat) :
    hamiltonianRationalOperator n R Q
        (fun u => if u.1.val + 1 <= H then lpfRationalCoefficient (u.1.val + 1) else 0) =
      hamiltonianRationalOperator n R H
        (fun u => if u.1.val + 1 <= Q then lpfRationalCoefficient (u.1.val + 1) else 0) := by
  ext i j
  rw [hamiltonian_rational_operator_apply, hamiltonian_rational_operator_apply]
  congr 1
  rw [hamiltonian_rational_masked_sum R Q H, hamiltonian_rational_masked_sum R H Q]
  exact hamiltonian_fin_sum_cutoff_commute Q H
    (fun q => hamiltonianRationalDenominatorTerm R q
      (((i.val + 1) + (j.val + 1) : Nat) : ZMod R))

theorem hamiltonian_rational_fixed_denominator_model_error
    {n R : Nat} [NeZero n] [NeZero R]
    (Q K : Nat) (hQ : 0 < Q) (hK : 0 < K) (hRange : 4 * Q ^ 2 <= R)
    (hDiv : forall q, 0 < q -> q <= Q -> Dvd.dvd q R) :
    norm (hamiltonianRationalSumMatrix n R Q -
      hamiltonianRationalOperator n R (27 * K ^ 4)
        (fun u => if u.1.val + 1 <= Q then lpfRationalCoefficient (u.1.val + 1) else 0)) <=
      (1 / (K : Real)) * (1 + 4 * (Q : Real) ^ 4 / (n : Real)) := by
  have hTransport := hamiltonian_rational_denominator_transport n R Q (27 * K ^ 4)
  change hamiltonianRationalOperator n R Q (hamiltonianRationalCutoffLow Q K) =
    hamiltonianRationalOperator n R (27 * K ^ 4)
      (fun u => if u.1.val + 1 <= Q then lpfRationalCoefficient (u.1.val + 1) else 0) at hTransport
  rw [<- hTransport]
  exact hamiltonian_rational_cutoff_operator_error Q K hQ hK hRange hDiv

end PrimeFactorOscillations.LPF
