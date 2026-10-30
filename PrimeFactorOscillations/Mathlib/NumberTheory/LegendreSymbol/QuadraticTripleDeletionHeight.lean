/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticTripleDeletion
/-!
# Full retained-height bounds for quadratic-triple deletions

The complete signed fibre identity keeps the retained fluctuation sum R
and every phase residual. A nonnegative retained sum forces at least
q-3+sqrt(4*(q-3)+2*R) deleted admissible parameter pairs. This improves
the centered energy envelope for q>7 without a Hasse bound.
The theorem concerns finite-field parameters, not integer prime classes.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticTripleTwist
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def retainedWave (h t : F) (D : Finset (shapeState h)) : Int :=
  ((Finset.univ : Finset (shapeState h)) \ D).sum
    (fun p => compensatedWave h p.val.1 t p.val.2)

theorem full_signed_deletion_identity (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (D : Finset (shapeState h)) :
    (Finset.univ.sum fun z : regularState (F := F) =>
      (fibreDeletionPhase h hh D z)^2) =
      ((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1) +
        2*retainedWave h t D +
        (Finset.univ.sum fun z : regularState (F := F) =>
          (fibreDeletionPhase h hh D z-splitCubicPointTrace z.val (z.val+1))^2) := by
  have hsplit := Finset.sum_sdiff
    (f := fun p : shapeState h => compensatedWave h p.val.1 t p.val.2)
    (Finset.subset_univ D)
  change retainedWave h t D +
    (D.sum fun p : shapeState h => compensatedWave h p.val.1 t p.val.2) = _ at hsplit
  rw [full_shape_first_moment hF h t hh ht hchi] at hsplit
  have hpair := sum_trace_fibreDeletionPhase hF h t hh ht hchi D
  have hsq := sum_regular_trace_square (F := F) hF
  have he (z : regularState (F := F)) :
      (fibreDeletionPhase h hh D z-splitCubicPointTrace z.val (z.val+1))^2 =
      (fibreDeletionPhase h hh D z)^2 -
        2*(splitCubicPointTrace z.val (z.val+1)*fibreDeletionPhase h hh D z) +
          (splitCubicPointTrace z.val (z.val+1))^2 := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,<- Finset.mul_sum]
  linarith only [hpair,hsplit,hsq]

theorem full_deletion_count_constraints (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (D : Finset (shapeState h)) :
    ((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1) +
        2*retainedWave h t D <= (D.card : Int)^2 /\
      4*((Fintype.card F : Int)-3)+2*retainedWave h t D <=
        ((D.card : Int)-((Fintype.card F : Int)-3))^2 := by
  have hp := full_signed_deletion_identity hF h t hh ht hchi D
  have hrem : 0 <= (Finset.univ.sum fun z : regularState (F := F) =>
      (fibreDeletionPhase h hh D z-splitCubicPointTrace z.val (z.val+1))^2) :=
    Finset.sum_nonneg (fun z _ => sq_nonneg _)
  have hdom : (Finset.univ.sum fun z : regularState (F := F) =>
      (fibreDeletionPhase h hh D z)^2) <=
        (Finset.univ.sum fun z : regularState (F := F) =>
          (fibreDeletionCount h hh D z)^2) := by
    apply Finset.sum_le_sum
    intro z _
    exact fibreDeletionPhase_square_le h hh D z
  have hlow : ((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1) +
      2*retainedWave h t D <=
      (Finset.univ.sum fun z : regularState (F := F) =>
        (fibreDeletionCount h hh D z)^2) := by linarith only [hp,hrem,hdom]
  have hc0 (z : regularState (F := F))
      (_ : Membership.mem (Finset.univ : Finset (regularState (F := F))) z) :
      0 <= fibreDeletionCount h hh D z := (fibreDeletionCount_bounds h hh D z).1
  have hca (z : regularState (F := F))
      (_ : Membership.mem (Finset.univ : Finset (regularState (F := F))) z) :
      fibreDeletionCount h hh D z <= (Fintype.card F : Int)-3 :=
    (fibreDeletionCount_bounds h hh D z).2
  have htotal := count_squares_le_total_square Finset.univ (fibreDeletionCount h hh D) hc0
  have hcap := capped_count_squares Finset.univ (fibreDeletionCount h hh D)
    ((Fintype.card F : Int)-3) hc0 hca
  rw [sum_fibreDeletionCount h hh D] at htotal hcap
  constructor
  . exact le_trans hlow htotal
  . nlinarith only [hlow,hcap]

theorem deletion_height_sqrt_bound (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F)
    (D : Finset (shapeState h)) (hR : 0 <= retainedWave h t D) :
    ((Fintype.card F : Real)-3)+
      Real.sqrt (4*((Fintype.card F : Real)-3)+2*(retainedWave h t D : Real)) <=
        (D.card : Real) := by
  have hi := full_deletion_count_constraints hF h t hh ht hchi D
  have hsCast : ((Fintype.card F : Real)-3)*((Fintype.card F : Real)+1) +
      2*(retainedWave h t D : Real) <= (D.card : Real)^2 := by exact_mod_cast hi.1
  have htCast : 4*((Fintype.card F : Real)-3)+2*(retainedWave h t D : Real) <=
      ((D.card : Real)-((Fintype.card F : Real)-3))^2 := by exact_mod_cast hi.2
  let a : Real := (Fintype.card F : Real)-3
  let m : Real := D.card
  let r : Real := retainedWave h t D
  change a+Real.sqrt (4*a+2*r) <= m
  have hqr : (5 : Real) < Fintype.card F := by exact_mod_cast hq
  have ha : 0 < a := by dsimp only [a]; linarith only [hqr]
  have hm : 0 <= m := by dsimp only [m]; positivity
  have hr : 0 <= r := by
    change (0 : Real) <= (retainedWave h t D : Real)
    exact_mod_cast hR
  have hs : a*(a+4)+2*r <= m^2 := by
    dsimp only [a,m,r]
    nlinarith only [hsCast]
  have ht : 4*a+2*r <= (m-a)^2 := htCast
  have hma : 0 <= m-a := by
    by_contra hn
    have hfactor := mul_nonneg (show 0 <= a-m from by linarith only [hn])
      (add_nonneg ha.le hm)
    nlinarith only [hfactor,hs,ha,hr]
  have hrad : 0 < 4*a+2*r := by linarith only [ha,hr]
  have hroot := Real.sqrt_nonneg (4*a+2*r)
  have hsqrt := Real.sq_sqrt hrad.le
  have hrootpos : 0 < Real.sqrt (4*a+2*r) := by nlinarith only [hroot,hsqrt,hrad]
  by_contra hn
  have hlt : m-a < Real.sqrt (4*a+2*r) := by linarith only [hn]
  have hfactor := mul_pos (sub_pos.mpr hlt)
    (show 0 < Real.sqrt (4*a+2*r)+(m-a) from by linarith only [hrootpos,hma])
  nlinarith only [hfactor,ht,hsqrt]

theorem nonnegative_retained_deletion_bound (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F)
    (D : Finset (shapeState h)) (hR : 0 <= retainedWave h t D) :
    ((Fintype.card F : Real)-3)+2*Real.sqrt ((Fintype.card F : Real)-3) <=
      (D.card : Real) := by
  have hb := deletion_height_sqrt_bound hF h t hh ht hchi hq D hR
  have hr : (0 : Real) <= retainedWave h t D := by exact_mod_cast hR
  have hm := Real.sqrt_le_sqrt (show 4*((Fintype.card F : Real)-3) <=
      4*((Fintype.card F : Real)-3)+2*(retainedWave h t D : Real) from by linarith only [hr])
  have he : Real.sqrt (4*((Fintype.card F : Real)-3)) =
      2*Real.sqrt ((Fintype.card F : Real)-3) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : Real) <= 4)
    have hn := Real.sqrt_nonneg (4 : Real)
    have hf : (Real.sqrt (4 : Real)-2)*(Real.sqrt (4 : Real)+2)=0 := by
      nlinarith only [hs]
    have hne : Not (Real.sqrt (4 : Real)+2=0) := by linarith only [hn]
    have hfour : Real.sqrt (4 : Real)=2 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hne)
    rw [Real.sqrt_mul (by norm_num : (0 : Real) <= 4),hfour]
  linarith only [hb,hm,he]

theorem deletion_at_least_q_add_two (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 7 < Fintype.card F)
    (D : Finset (shapeState h)) (hR : 0 <= retainedWave h t D) :
    Fintype.card F+2 <= D.card := by
  have hq5 : 5 < Fintype.card F := by omega
  have hb := nonnegative_retained_deletion_bound hF h t hh ht hchi hq5 D hR
  have hqr : (7 : Real) < Fintype.card F := by exact_mod_cast hq
  have ha : (0 : Real) <= (Fintype.card F : Real)-3 := by linarith only [hqr]
  have hs := Real.sq_sqrt ha
  have hn := Real.sqrt_nonneg ((Fintype.card F : Real)-3)
  have hr : (2 : Real) < Real.sqrt ((Fintype.card F : Real)-3) := by
    nlinarith only [hs,hn,hqr]
  have hi : (Fintype.card F : Real)+1 < (D.card : Real) := by linarith only [hb,hr]
  have hz : Fintype.card F+1 < D.card := by exact_mod_cast hi
  omega

end FiniteField.QuadraticTripleTwist
