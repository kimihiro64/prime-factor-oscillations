/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticTripleCentering
/-!
# Signed fibre deletion bounds for quadratic triples

The complete rational fibres retain every deleted character phase.
An exact trace/deletion pairing and its squared residual force more
deletions than the global centering-energy envelope. The capped count
bound gives a square-root correction without a Hasse estimate.
No integer-prime or RH transfer is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticTripleTwist
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem count_squares_le_total_square {J : Type*} [DecidableEq J]
    (s : Finset J) (c : J -> Int)
    (hc : forall j, Membership.mem s j -> 0 <= c j) :
    (s.sum fun j => (c j)^2) <= (s.sum c)^2 := by
  calc
    _ <= s.sum (fun j => c j*s.sum c) := by
      apply Finset.sum_le_sum
      intro j hj
      have hb := Finset.single_le_sum hc hj
      have hp := mul_nonneg (hc j hj) (sub_nonneg.mpr hb)
      nlinarith only [hp]
    _ = _ := by rw [<- Finset.sum_mul]; ring

theorem capped_count_squares {J : Type*} [DecidableEq J]
    (s : Finset J) (c : J -> Int) (a : Int)
    (hc0 : forall j, Membership.mem s j -> 0 <= c j)
    (hca : forall j, Membership.mem s j -> c j <= a) :
    (s.sum fun j => (c j)^2) <= a^2+(s.sum c-a)^2 := by
  revert hc0 hca
  refine Finset.induction_on s ?_ ?_
  . intro _ _
    simp
    nlinarith only [sq_nonneg a]
  . intro j s hjs ih hc0 hca
    have hj0 := hc0 j (Finset.mem_insert_self j s)
    have hja := hca j (Finset.mem_insert_self j s)
    have hs0 : forall i, Membership.mem s i -> 0 <= c i :=
      fun i hi => hc0 i (Finset.mem_insert_of_mem hi)
    have hsa : forall i, Membership.mem s i -> c i <= a :=
      fun i hi => hca i (Finset.mem_insert_of_mem hi)
    have hold := ih hs0 hsa
    rw [Finset.sum_insert hjs,Finset.sum_insert hjs]
    by_cases hm : a <= s.sum c
    . have hp := mul_nonneg hj0 (sub_nonneg.mpr hm)
      nlinarith only [hold,hp]
    . have hsmall := count_squares_le_total_square s c hs0
      have hp := mul_nonneg (show 0 <= a-s.sum c from by omega)
        (sub_nonneg.mpr hja)
      nlinarith only [hsmall,hp]

def deletionFibreEquiv (h : F) (hh : Not (h=0)) :
    Equiv (shapeState h) (Sigma (fun z : regularState (F := F) => fibreAt z)) :=
  (fullShapeEquiv h hh).trans fibreSigmaEquiv

def deletionFibreShape (h : F) (hh : Not (h=0))
    (z : regularState (F := F)) (y : fibreAt z) : shapeState h :=
  (deletionFibreEquiv h hh).symm (Sigma.mk z y)

theorem sum_deletionFibre_transport (h : F) (hh : Not (h=0))
    (g : shapeState h -> Int) :
    (Finset.univ.sum fun z : regularState (F := F) =>
      Finset.univ.sum fun y : fibreAt z => g (deletionFibreShape h hh z y)) =
        Finset.univ.sum g := by
  calc
    _ = Finset.univ.sum (fun p : Sigma (fun z : regularState (F := F) => fibreAt z) =>
        g ((deletionFibreEquiv h hh).symm p)) :=
      (Fintype.sum_sigma (fun p : Sigma (fun z : regularState (F := F) => fibreAt z) =>
        g ((deletionFibreEquiv h hh).symm p))).symm
    _ = _ := Equiv.sum_comp (deletionFibreEquiv h hh).symm g

theorem deletionFibreShape_wave (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (z : regularState (F := F)) (y : fibreAt z) :
    compensatedWave h (deletionFibreShape h hh z y).val.1 t
      (deletionFibreShape h hh z y).val.2 =
      fibrePhase z.val y.val*splitCubicPointTrace z.val (z.val+1) := by
  change compensatedWave h (fibreShift h z.val y.val) t
    (fibreConstant h z.val y.val) = _
  exact compensatedWave_fibre hF h z.val y.val t hh z.property y.property ht hchi

def fibreDeletionCount (h : F) (hh : Not (h=0))
    (D : Finset (shapeState h)) (z : regularState (F := F)) : Int :=
  Finset.univ.sum fun y : fibreAt z =>
    if Membership.mem D (deletionFibreShape h hh z y) then 1 else 0

def fibreDeletionPhase (h : F) (hh : Not (h=0))
    (D : Finset (shapeState h)) (z : regularState (F := F)) : Int :=
  -(Finset.univ.sum fun y : fibreAt z =>
    if Membership.mem D (deletionFibreShape h hh z y) then fibrePhase z.val y.val else 0)

theorem sum_fibreDeletionCount (h : F) (hh : Not (h=0))
    (D : Finset (shapeState h)) :
    (Finset.univ.sum fun z : regularState (F := F) => fibreDeletionCount h hh D z) =
      (D.card : Int) := by
  unfold fibreDeletionCount
  rw [sum_deletionFibre_transport h hh
    (fun p : shapeState h => if Membership.mem D p then 1 else 0)]
  simp

theorem sum_fibreAt_one (z : regularState (F := F)) :
    (Finset.univ.sum fun _ : fibreAt z => (1 : Int)) =
      (Fintype.card F : Int)-3 := by
  have hs := sum_fibreAt z (fun _ : Int => 1)
  have hz1 : Not ((1 : F)=z.val+1) := by
    intro hv
    apply z.property.1
    calc
      z.val = (z.val+1)-1 := by ring
      _ = 0 := by rw [<- hv]; ring
  change (Finset.univ.sum fun _ : fibreAt z => (1 : Int)) =
    (Finset.univ.sum fun y : F => admissibleWeight (1 : F) (z.val+1) y) at hs
  rw [hs,sum_admissibleWeight (1 : F) (z.val+1) one_ne_zero z.property.2 hz1]

theorem fibreDeletionCount_bounds (h : F) (hh : Not (h=0))
    (D : Finset (shapeState h)) (z : regularState (F := F)) :
    0 <= fibreDeletionCount h hh D z /\
      fibreDeletionCount h hh D z <= (Fintype.card F : Int)-3 := by
  constructor
  . apply Finset.sum_nonneg
    intro y _
    split_ifs <;> omega
  . calc
      _ <= Finset.univ.sum (fun _ : fibreAt z => (1 : Int)) := by
        apply Finset.sum_le_sum
        intro y _
        split_ifs <;> omega
      _ = _ := sum_fibreAt_one z

theorem fibreDeletionPhase_square_le (h : F) (hh : Not (h=0))
    (D : Finset (shapeState h)) (z : regularState (F := F)) :
    (fibreDeletionPhase h hh D z)^2 <= (fibreDeletionCount h hh D z)^2 := by
  have hp (y : fibreAt z) : (fibrePhase z.val y.val)^2=1 :=
    quadraticChar_sq_one
      (mul_ne_zero (mul_ne_zero y.property.1 y.property.2.1) y.property.2.2)
  have hlo : -(fibreDeletionCount h hh D z) <=
      Finset.univ.sum (fun y : fibreAt z =>
        if Membership.mem D (deletionFibreShape h hh z y)
          then fibrePhase z.val y.val else 0) := by
    unfold fibreDeletionCount
    rw [<- Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro y _
    split_ifs <;> nlinarith only [hp y]
  have hhi : (Finset.univ.sum fun y : fibreAt z =>
        if Membership.mem D (deletionFibreShape h hh z y)
          then fibrePhase z.val y.val else 0) <= fibreDeletionCount h hh D z := by
    apply Finset.sum_le_sum
    intro y _
    split_ifs <;> nlinarith only [hp y]
  unfold fibreDeletionPhase
  have hm := mul_nonneg (sub_nonneg.mpr hhi)
    (show 0 <= fibreDeletionCount h hh D z +
      (Finset.univ.sum fun y : fibreAt z =>
        if Membership.mem D (deletionFibreShape h hh z y)
          then fibrePhase z.val y.val else 0) from by linarith only [hlo])
  nlinarith only [hm]


theorem sum_trace_fibreDeletionPhase (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (D : Finset (shapeState h)) :
    (Finset.univ.sum fun z : regularState (F := F) =>
      splitCubicPointTrace z.val (z.val+1)*fibreDeletionPhase h hh D z) =
      -(D.sum fun p : shapeState h => compensatedWave h p.val.1 t p.val.2) := by
  have hrow (z : regularState (F := F)) :
      splitCubicPointTrace z.val (z.val+1)*fibreDeletionPhase h hh D z =
      -(Finset.univ.sum fun y : fibreAt z =>
        if Membership.mem D (deletionFibreShape h hh z y)
          then fibrePhase z.val y.val*splitCubicPointTrace z.val (z.val+1) else 0) := by
    unfold fibreDeletionPhase
    rw [mul_neg,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> ring
  calc
    _ = Finset.univ.sum (fun z : regularState (F := F) =>
        -(Finset.univ.sum fun y : fibreAt z =>
          if Membership.mem D (deletionFibreShape h hh z y)
            then fibrePhase z.val y.val*splitCubicPointTrace z.val (z.val+1) else 0)) := by
      apply Finset.sum_congr rfl
      intro z _
      exact hrow z
    _ = -(Finset.univ.sum fun z : regularState (F := F) =>
        Finset.univ.sum fun y : fibreAt z =>
          if Membership.mem D (deletionFibreShape h hh z y)
            then fibrePhase z.val y.val*splitCubicPointTrace z.val (z.val+1) else 0) := by
      rw [Finset.sum_neg_distrib]
    _ = -(Finset.univ.sum fun z : regularState (F := F) =>
        Finset.univ.sum fun y : fibreAt z =>
          if Membership.mem D (deletionFibreShape h hh z y)
            then compensatedWave h (deletionFibreShape h hh z y).val.1 t
              (deletionFibreShape h hh z y).val.2 else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro y _
      by_cases hd : Membership.mem D (deletionFibreShape h hh z y)
      . simp only [if_pos hd]
        exact (deletionFibreShape_wave hF h t hh ht hchi z y).symm
      . simp only [if_neg hd]
    _ = _ := by
      rw [sum_deletionFibre_transport h hh
        (fun p : shapeState h =>
          if Membership.mem D p then compensatedWave h p.val.1 t p.val.2 else 0)]
      simp

theorem signed_deletion_packet_identity (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (D : Finset (shapeState h))
    (hcenter : ((Finset.univ : Finset (shapeState h)) \ D).sum
      (fun p => compensatedWave h p.val.1 t p.val.2) = 0) :
    (Finset.univ.sum fun z : regularState (F := F) =>
      (fibreDeletionPhase h hh D z)^2) =
      ((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1) +
        (Finset.univ.sum fun z : regularState (F := F) =>
          (fibreDeletionPhase h hh D z-splitCubicPointTrace z.val (z.val+1))^2) := by
  have hsplit := Finset.sum_sdiff
    (f := fun p : shapeState h => compensatedWave h p.val.1 t p.val.2)
    (Finset.subset_univ D)
  rw [hcenter,full_shape_first_moment hF h t hh ht hchi] at hsplit
  have hd : (D.sum fun p : shapeState h => compensatedWave h p.val.1 t p.val.2) =
      -((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1) := by
    linarith only [hsplit]
  have hpair := sum_trace_fibreDeletionPhase hF h t hh ht hchi D
  rw [hd] at hpair
  have hsq := sum_regular_trace_square (F := F) hF
  have he (z : regularState (F := F)) :
      (fibreDeletionPhase h hh D z-splitCubicPointTrace z.val (z.val+1))^2 =
      (fibreDeletionPhase h hh D z)^2 -
        2*(splitCubicPointTrace z.val (z.val+1)*fibreDeletionPhase h hh D z) +
          (splitCubicPointTrace z.val (z.val+1))^2 := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,<- Finset.mul_sum]
  linarith only [hpair,hsq]

theorem deletion_count_square_constraints (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (D : Finset (shapeState h))
    (hcenter : ((Finset.univ : Finset (shapeState h)) \ D).sum
      (fun p => compensatedWave h p.val.1 t p.val.2) = 0) :
    ((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1) <= (D.card : Int)^2 /\
      4*((Fintype.card F : Int)-3) <=
        ((D.card : Int)-((Fintype.card F : Int)-3))^2 := by
  have hp := signed_deletion_packet_identity hF h t hh ht hchi D hcenter
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
  have hlow : ((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1) <=
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

theorem uniform_deletion_sqrt_bound (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F)
    (D : Finset (shapeState h))
    (hcenter : ((Finset.univ : Finset (shapeState h)) \ D).sum
      (fun p => compensatedWave h p.val.1 t p.val.2) = 0) :
    ((Fintype.card F : Real)-3)+2*Real.sqrt ((Fintype.card F : Real)-3) <=
      (D.card : Real) := by
  have hi := deletion_count_square_constraints hF h t hh ht hchi D hcenter
  have hsCast : ((Fintype.card F : Real)-3)*((Fintype.card F : Real)+1) <=
      (D.card : Real)^2 := by exact_mod_cast hi.1
  have htCast : 4*((Fintype.card F : Real)-3) <=
      ((D.card : Real)-((Fintype.card F : Real)-3))^2 := by exact_mod_cast hi.2
  let a : Real := (Fintype.card F : Real)-3
  let m : Real := D.card
  change a+2*Real.sqrt a <= m
  have hqr : (5 : Real) < Fintype.card F := by exact_mod_cast hq
  have ha : 0 < a := by dsimp only [a]; linarith only [hqr]
  have hm : 0 <= m := by dsimp only [m]; positivity
  have hs : a*(a+4) <= m^2 := by
    dsimp only [a,m]
    nlinarith only [hsCast]
  have ht : 4*a <= (m-a)^2 := htCast
  have hma : 0 <= m-a := by
    by_contra hn
    have hfactor := mul_nonneg (show 0 <= a-m from by linarith only [hn])
      (add_nonneg ha.le hm)
    nlinarith only [hfactor,hs,ha]
  have hroot := Real.sqrt_nonneg a
  have hsqrt := Real.sq_sqrt ha.le
  have hrootpos : 0 < Real.sqrt a := by nlinarith only [hroot,hsqrt,ha]
  by_contra hn
  have hlt : m-a < 2*Real.sqrt a := by linarith only [hn]
  have hfactor := mul_pos (sub_pos.mpr hlt)
    (show 0 < 2*Real.sqrt a+(m-a) from by linarith only [hrootpos,hma])
  nlinarith only [hfactor,ht,hsqrt]

end FiniteField.QuadraticTripleTwist
