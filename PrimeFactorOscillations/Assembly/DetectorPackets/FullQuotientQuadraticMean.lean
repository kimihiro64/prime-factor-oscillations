/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.SexticDiagonalResidueMean
import PrimeFactorOscillations.Proof.DetectorPackets.SexticToQuadraticLocal

/-!
# FullQuotientQuadraticMean

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
# Complete Euler-coordinate leading mean

Retaining the scalar, numerator and reciprocal Euler factors changes
the enhanced leading term to -c*D^2*(1-W)^2/(1-V).
Its normalized phase is a linear combination of powers three, four and
five of the actual sextic character. Their complete residue means vanish.
This is local orthogonality, not a bound for the weighted global row sum.
-/

set_option maxHeartbeats 800000

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.FullQuotientQuadraticMean

open SexticToQuadraticLocal SexticDiagonalResidueMean

theorem full_euler_identity (V W D P B q c : Complex)
    (hV : Not (1-V=0)) (hW : Not (1-W=0)) (hD : Not (1-D=0))
    (hBD : B*D=c) (hcW : c*W=q) :
    (1-D)*enhancedReplacement V W D P B q c/((1-V)*(1-W)) =
      -c*D^2*(1-W)^2/(1-V)+retainedDefect V W D P B c/((1-V)*(1-W)) := by
  rw [selected_inverse_factor V W D P B q c hD hBD hcW]
  field_simp [hV, hW]

theorem sixth_character_cube_real {R : Type*} [CommMonoid R]
    (psi : MulChar R Complex) (hsix : psi^6=1) (a : R) :
    star (psi a)^3=(psi a)^3 := by
  rw [<-star_pow]
  by_cases ha : IsUnit a
  . choose u hu using ha
    rw [<-hu]
    have he := congrArg (fun f : MulChar R Complex => f (u:R)) hsix
    rw [MulChar.pow_apply_coe, MulChar.one_apply u.isUnit] at he
    have hcube : ((psi (u:R))^3)^2=1 := by
      rw [<-pow_mul]
      norm_num
      exact he
    cases (sq_eq_one_iff.mp hcube) with
    | inl h => rw [h]; simp
    | inr h => rw [h]; simp
  . rw [MulChar.map_nonunit psi ha]
    simp

theorem finite_leading_mean {R : Type*} [CommMonoid R] [Fintype R] [DecidableEq R]
    (psi : MulChar R Complex)
    (horder : forall k : Nat, psi^k=1 <-> Dvd.dvd 6 k)
    (A : Complex) :
    (Finset.univ.sum fun a : R => star (psi a)^3*(1-psi a*A)^2)=0 := by
  have hsix : psi^6=1 := (horder 6).mpr (by decide)
  have h3 := finite_moment psi horder 3
  have h4 := finite_moment psi horder 4
  have h5 := finite_moment psi horder 5
  norm_num at h3 h4 h5
  have ht (a : R) :
      star (psi a)^3*(1-psi a*A)^2 =
        (psi a)^3-(2*A)*(psi a)^4+A^2*(psi a)^5 := by
    rw [sixth_character_cube_real psi hsix a]
    ring
  simp only [ht, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    <-Finset.mul_sum, h3, h4, h5, mul_zero, sub_zero, add_zero]

theorem scalar_leading_mean {R : Type*} [CommMonoid R] [Fintype R] [DecidableEq R]
    (psi : MulChar R Complex)
    (horder : forall k : Nat, psi^k=1 <-> Dvd.dvd 6 k)
    (A eta V : Complex) :
    (Finset.univ.sum fun a : R =>
      -eta^2*star (psi a)^3*(1-psi a*A)^2/(1-V))=0 := by
  calc
    _ = (-eta^2/(1-V))*
        (Finset.univ.sum fun a : R => star (psi a)^3*(1-psi a*A)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = 0 := by rw [finite_leading_mean psi horder A]; ring

local notation "O" => ActualEisensteinCubic.O

theorem actual_leading_mean (P : Ideal O) [P.IsMaximal] [Fintype (Residues P)]
    (hg : Not (Membership.mem P ConcretePrimeRowBridge.goodLambda))
    (hc : Not (ringChar (Residues P)=2)) (A eta V : Complex) :
    (Finset.univ.sum fun a : Residues P =>
      -eta^2*star (CompletedGauss.actualSextic P hg a)^3*
        (1-CompletedGauss.actualSextic P hg a*A)^2/(1-V))=0 := by
  exact scalar_leading_mean (CompletedGauss.actualSextic P hg)
    (ProbePrimePower.actualSextic_pow_eq_one_iff P hg hc) A eta V

end OAI.SevenEighths.FullQuotientQuadraticMean
