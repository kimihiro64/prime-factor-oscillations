/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.SexticMobiusDiagonal

/-!
# SexticDiagonalResidueMean

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Exact finite residue mean of the marked sextic diagonal

This uses the actual canonical sextic character, its proved order six,
and full residue sums including the nonunit zero row. A positive neutral
power has mass card(R units), whereas exponent zero has mass card(R).
The physical weighted FreeRow sum and its off-diagonal are separate.
-/

set_option maxHeartbeats 800000

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.SexticDiagonalResidueMean

open SexticMobiusDiagonal

theorem finite_moment {R : Type*} [CommMonoid R] [Fintype R] [DecidableEq R]
    (psi : MulChar R Complex)
    (horder : forall k : Nat, psi^k=1 <-> Dvd.dvd 6 k) (k : Nat) :
    (Finset.univ.sum fun a : R => (psi a)^k) =
      if k=0 then (Fintype.card R:Complex)
      else if Dvd.dvd 6 k then (Fintype.card (Units R):Complex) else 0 := by
  by_cases hk : k=0
  . simp [hk]
  rw [if_neg hk]
  have hp (a : R) : (psi a)^k = (psi^k) a := by
    by_cases ha : IsUnit a
    . choose u hu using ha
      rw [<-hu]
      exact (MulChar.pow_apply_coe psi k u).symm
    . rw [MulChar.map_nonunit psi ha, zero_pow hk,
        MulChar.map_nonunit (psi^k) ha]
  simp only [hp]
  by_cases hd : Dvd.dvd 6 k
  . rw [if_pos hd, (horder k).mpr hd]
    exact MulChar.sum_one_eq_card_units
  . rw [if_neg hd]
    exact MulChar.sum_eq_zero_of_ne_one (fun h => hd ((horder k).mp h))

local notation "O" => ActualEisensteinCubic.O

abbrev Residues (P : Ideal O) : Type := HasQuotient.Quotient O P

theorem actual_moment (P : Ideal O) [P.IsMaximal] [Fintype (Residues P)]
    (hg : Not (Membership.mem P ConcretePrimeRowBridge.goodLambda))
    (hc : Not (ringChar (Residues P)=2)) (k : Nat) :
    (Finset.univ.sum fun a : Residues P => (CompletedGauss.actualSextic P hg a)^k) =
      if k=0 then (Fintype.card (Residues P):Complex)
      else if Dvd.dvd 6 k then (Fintype.card (Units (Residues P)):Complex) else 0 := by
  exact finite_moment (CompletedGauss.actualSextic P hg)
    (ProbePrimePower.actualSextic_pow_eq_one_iff P hg hc) k

theorem positive_neutral_moment (P : Ideal O) [P.IsMaximal] [Fintype (Residues P)]
    (hg : Not (Membership.mem P ConcretePrimeRowBridge.goodLambda))
    (hc : Not (ringChar (Residues P)=2)) (j : Nat) (hj : 1 <= j) :
    (Finset.univ.sum fun a : Residues P =>
      (CompletedGauss.actualSextic P hg a)^(6*j)) =
      ((Fintype.card (Residues P)-1:Nat):Complex) := by
  have hk : Not (6*j=0) := by omega
  rw [actual_moment P hg hc, if_neg hk, if_pos (by omega : Dvd.dvd 6 (6*j)),
    Fintype.card_units]

def markedBlock (P : Ideal O) [P.IsMaximal] [Fintype (Residues P)]
    (hg : Not (Membership.mem P ConcretePrimeRowBridge.goodLambda))
    (A B : Complex) (H : Nat) : Complex :=
  (Finset.range H).sum fun h =>
    A^(3+6*h)*(Finset.univ.sum fun a : Residues P =>
      (CompletedGauss.actualSextic P hg a)^(6*(h+1))) -
    B*A^(4+6*h)*(Finset.univ.sum fun a : Residues P =>
      (CompletedGauss.actualSextic P hg a)^(6*(h+2)))

theorem marked_block_factor (P : Ideal O) [P.IsMaximal] [Fintype (Residues P)]
    (hg : Not (Membership.mem P ConcretePrimeRowBridge.goodLambda))
    (hc : Not (ringChar (Residues P)=2)) (A B : Complex) (H : Nat) :
    markedBlock P hg A B H =
      ((Fintype.card (Residues P)-1:Nat):Complex)*block A B 1 H := by
  unfold markedBlock block
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [positive_neutral_moment P hg hc (h+1) (by omega),
    positive_neutral_moment P hg hc (h+2) (by omega)]
  norm_num
  ring

theorem finite_marked_diagonal (P : Ideal O) [P.IsMaximal] [Fintype (Residues P)]
    (hg : Not (Membership.mem P ConcretePrimeRowBridge.goodLambda))
    (hc : Not (ringChar (Residues P)=2)) (A B : Complex) (H : Nat) :
    (1-A^6)*markedBlock P hg A B H =
      ((Fintype.card (Residues P)-1:Nat):Complex)*
        A^3*(1-B*A)*(1-(A^6)^H) := by
  rw [marked_block_factor P hg hc A B H]
  calc
    _ = ((Fintype.card (Residues P)-1:Nat):Complex)*
        ((1-A^6)*block A B 1 H) := by ring
    _ = _ := by rw [finite_diagonal]; norm_num; ring

end OAI.SevenEighths.SexticDiagonalResidueMean
