/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticTripleDeletionHeight
/-!
# Integer stability certificates for quadratic-triple deletions

The deletion-height slack splits exactly into a capped-count slack,
four times the number of mixed-sign deleted pairs in each rational fibre,
and the squared actual retained character sums. All three terms are
nonnegative integers. The certificate bounds the number of unbalanced
fibres, forces one deleted sign per fibre below four slack units, and
shows that zero slack forces the full retained fluctuation sum to vanish.
These statements concern finite-field parameter subsets only.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticTripleTwist
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]


def deletionSlack (h t : F) (D : Finset (shapeState h)) : Int :=
  ((D.card : Int)-((Fintype.card F : Int)-3))^2 -
    4*((Fintype.card F : Int)-3)-2*retainedWave h t D

def deletionCapSlack (h : F) (hh : Not (h=0)) (D : Finset (shapeState h)) : Int :=
  ((Fintype.card F : Int)-3)^2 +
    ((D.card : Int)-((Fintype.card F : Int)-3))^2 -
      (Finset.univ.sum fun z : regularState (F := F) => (fibreDeletionCount h hh D z)^2)

def positiveFibreDeletionCount (h : F) (hh : Not (h=0))
    (D : Finset (shapeState h)) (z : regularState (F := F)) : Int :=
  Finset.univ.sum fun y : fibreAt z =>
    if Membership.mem D (deletionFibreShape h hh z y)
      then if fibrePhase z.val y.val=1 then 1 else 0 else 0

def negativeFibreDeletionCount (h : F) (hh : Not (h=0))
    (D : Finset (shapeState h)) (z : regularState (F := F)) : Int :=
  Finset.univ.sum fun y : fibreAt z =>
    if Membership.mem D (deletionFibreShape h hh z y)
      then if fibrePhase z.val y.val = -1 then 1 else 0 else 0

def retainedFibrePhase (h : F) (hh : Not (h=0))
    (D : Finset (shapeState h)) (z : regularState (F := F)) : Int :=
  Finset.univ.sum fun y : fibreAt z =>
    if Membership.mem D (deletionFibreShape h hh z y) then 0 else fibrePhase z.val y.val

theorem fibrePhase_sign (z : regularState (F := F)) (y : fibreAt z) :
    fibrePhase z.val y.val=1 \/ fibrePhase z.val y.val = -1 := by
  have hs : (fibrePhase z.val y.val)^2=1 :=
    quadraticChar_sq_one
      (mul_ne_zero (mul_ne_zero y.property.1 y.property.2.1) y.property.2.2)
  have hp : (fibrePhase z.val y.val-1)*(fibrePhase z.val y.val+1)=0 := by
    nlinarith only [hs]
  rcases mul_eq_zero.mp hp with hp | hp
  . left
    linarith only [hp]
  . right
    linarith only [hp]

theorem fibreDeletion_sign_counts (h : F) (hh : Not (h=0))
    (D : Finset (shapeState h)) (z : regularState (F := F)) :
    fibreDeletionCount h hh D z =
      positiveFibreDeletionCount h hh D z+negativeFibreDeletionCount h hh D z /\
    fibreDeletionPhase h hh D z =
      negativeFibreDeletionCount h hh D z-positiveFibreDeletionCount h hh D z := by
  constructor
  . unfold fibreDeletionCount positiveFibreDeletionCount negativeFibreDeletionCount
    rw [<- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    rcases fibrePhase_sign z y with hp | hp
    . by_cases hd : Membership.mem D (deletionFibreShape h hh z y)
      <;> simp [hp,hd]
    . by_cases hd : Membership.mem D (deletionFibreShape h hh z y)
      <;> simp [hp,hd]
  . unfold fibreDeletionPhase positiveFibreDeletionCount negativeFibreDeletionCount
    rw [<- Finset.sum_sub_distrib,<- Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro y _
    rcases fibrePhase_sign z y with hp | hp
    . by_cases hd : Membership.mem D (deletionFibreShape h hh z y)
      <;> simp [hp,hd]
    . by_cases hd : Membership.mem D (deletionFibreShape h hh z y)
      <;> simp [hp,hd]

theorem fibreDeletion_sign_nonneg (h : F) (hh : Not (h=0))
    (D : Finset (shapeState h)) (z : regularState (F := F)) :
    0 <= positiveFibreDeletionCount h hh D z /\
      0 <= negativeFibreDeletionCount h hh D z := by
  constructor
  . apply Finset.sum_nonneg
    intro y _
    split_ifs <;> omega
  . apply Finset.sum_nonneg
    intro y _
    split_ifs <;> omega

theorem fibreDeletion_mixed_pair_identity (h : F) (hh : Not (h=0))
    (D : Finset (shapeState h)) (z : regularState (F := F)) :
    (fibreDeletionCount h hh D z)^2 =
      (fibreDeletionPhase h hh D z)^2 +
        4*(positiveFibreDeletionCount h hh D z*negativeFibreDeletionCount h hh D z) := by
  have hc := fibreDeletion_sign_counts h hh D z
  rw [hc.1,hc.2]
  ring

theorem sum_fibrePhaseAt (hF : Not (ringChar F = 2))
    (z : regularState (F := F)) :
    (Finset.univ.sum fun y : fibreAt z => fibrePhase z.val y.val) =
      -splitCubicPointTrace z.val (z.val+1) := by
  have hs := Finset.sum_subtype (F := (inferInstance : Fintype (fibreAt z)))
    (p := fun y : F => admissible (1 : F) (z.val+1) y)
    (Finset.univ.filter (fun y : F => admissible (1 : F) (z.val+1) y))
    (fun y => by simp) (fun y : F => fibrePhase z.val y)
  calc
    _ = (Finset.univ.filter (fun y : F => admissible (1 : F) (z.val+1) y)).sum
        (fun y : F => fibrePhase z.val y) := hs.symm
    _ = Finset.univ.sum (fun y : F => fibrePhase z.val y) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : admissible (1 : F) (z.val+1) y
      . simp only [if_pos hy]
      . simp only [if_neg hy,fibrePhase_zero z.val y hy]
    _ = _ := sum_fibrePhase hF z.val

theorem retainedFibrePhase_eq (hF : Not (ringChar F = 2))
    (h : F) (hh : Not (h=0)) (D : Finset (shapeState h))
    (z : regularState (F := F)) :
    retainedFibrePhase h hh D z =
      fibreDeletionPhase h hh D z-splitCubicPointTrace z.val (z.val+1) := by
  unfold retainedFibrePhase
  calc
    _ = Finset.univ.sum (fun y : fibreAt z =>
        fibrePhase z.val y.val -
          (if Membership.mem D (deletionFibreShape h hh z y)
            then fibrePhase z.val y.val else 0)) := by
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> ring
    _ = _ := by
      rw [Finset.sum_sub_distrib,sum_fibrePhaseAt hF z]
      unfold fibreDeletionPhase
      ring

theorem deletionCapSlack_nonneg (h : F) (hh : Not (h=0))
    (D : Finset (shapeState h)) : 0 <= deletionCapSlack h hh D := by
  have hc0 (z : regularState (F := F))
      (_ : Membership.mem (Finset.univ : Finset (regularState (F := F))) z) :
      0 <= fibreDeletionCount h hh D z := (fibreDeletionCount_bounds h hh D z).1
  have hca (z : regularState (F := F))
      (_ : Membership.mem (Finset.univ : Finset (regularState (F := F))) z) :
      fibreDeletionCount h hh D z <= (Fintype.card F : Int)-3 :=
    (fibreDeletionCount_bounds h hh D z).2
  have hp := capped_count_squares Finset.univ (fibreDeletionCount h hh D)
    ((Fintype.card F : Int)-3) hc0 hca
  rw [sum_fibreDeletionCount h hh D] at hp
  unfold deletionCapSlack
  linarith only [hp]

theorem signed_deletion_slack_certificate (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (D : Finset (shapeState h)) :
    deletionSlack h t D = deletionCapSlack h hh D +
      4*(Finset.univ.sum fun z : regularState (F := F) =>
        positiveFibreDeletionCount h hh D z*negativeFibreDeletionCount h hh D z) +
      (Finset.univ.sum fun z : regularState (F := F) => (retainedFibrePhase h hh D z)^2) := by
  have hp := full_signed_deletion_identity hF h t hh ht hchi D
  have hs : (Finset.univ.sum fun z : regularState (F := F) =>
      (fibreDeletionCount h hh D z)^2) =
      (Finset.univ.sum fun z : regularState (F := F) =>
        (fibreDeletionPhase h hh D z)^2) +
      4*(Finset.univ.sum fun z : regularState (F := F) =>
        positiveFibreDeletionCount h hh D z*negativeFibreDeletionCount h hh D z) := by
    calc
      _ = Finset.univ.sum (fun z : regularState (F := F) =>
          (fibreDeletionPhase h hh D z)^2 +
            4*(positiveFibreDeletionCount h hh D z*negativeFibreDeletionCount h hh D z)) := by
        apply Finset.sum_congr rfl
        intro z _
        exact fibreDeletion_mixed_pair_identity h hh D z
      _ = _ := by rw [Finset.sum_add_distrib,<- Finset.mul_sum]
  have he : (Finset.univ.sum fun z : regularState (F := F) =>
      (retainedFibrePhase h hh D z)^2) =
      (Finset.univ.sum fun z : regularState (F := F) =>
        (fibreDeletionPhase h hh D z-splitCubicPointTrace z.val (z.val+1))^2) := by
    apply Finset.sum_congr rfl
    intro z _
    rw [retainedFibrePhase_eq hF h hh D z]
  unfold deletionSlack deletionCapSlack
  nlinarith only [hp,hs,he]


theorem mixedDeletionPairs_nonneg (h : F) (hh : Not (h=0))
    (D : Finset (shapeState h)) :
    0 <= (Finset.univ.sum fun z : regularState (F := F) =>
      positiveFibreDeletionCount h hh D z*negativeFibreDeletionCount h hh D z) := by
  apply Finset.sum_nonneg
  intro z _
  have hp := fibreDeletion_sign_nonneg h hh D z
  exact mul_nonneg hp.1 hp.2

theorem deletion_slack_budgets (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (D : Finset (shapeState h)) :
    0 <= deletionSlack h t D /\
      deletionCapSlack h hh D <= deletionSlack h t D /\
      4*(Finset.univ.sum fun z : regularState (F := F) =>
        positiveFibreDeletionCount h hh D z*negativeFibreDeletionCount h hh D z) <=
          deletionSlack h t D /\
      (Finset.univ.sum fun z : regularState (F := F) =>
        (retainedFibrePhase h hh D z)^2) <= deletionSlack h t D := by
  have hid := signed_deletion_slack_certificate hF h t hh ht hchi D
  have hc := deletionCapSlack_nonneg h hh D
  have hm := mixedDeletionPairs_nonneg h hh D
  have hr : 0 <= (Finset.univ.sum fun z : regularState (F := F) =>
      (retainedFibrePhase h hh D z)^2) :=
    Finset.sum_nonneg (fun z _ => sq_nonneg _)
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  all_goals linarith only [hid,hc,hm,hr]

def unbalancedFibreSet (h : F) (hh : Not (h=0)) (D : Finset (shapeState h)) :
    Finset (regularState (F := F)) :=
  Finset.univ.filter (fun z => Not (retainedFibrePhase h hh D z=0))

theorem unbalanced_fibre_count_bound (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (D : Finset (shapeState h)) :
    ((unbalancedFibreSet h hh D).card : Int) <= deletionSlack h t D := by
  have hc : ((unbalancedFibreSet h hh D).card : Int) =
      (Finset.univ.sum fun z : regularState (F := F) =>
        if Not (retainedFibrePhase h hh D z=0) then (1 : Int) else 0) := by
    rw [<- Finset.sum_filter]
    simp [unbalancedFibreSet]
  have hp : ((unbalancedFibreSet h hh D).card : Int) <=
      (Finset.univ.sum fun z : regularState (F := F) =>
        (retainedFibrePhase h hh D z)^2) := by
    rw [hc]
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : retainedFibrePhase h hh D z=0
    . simp [hz]
    . have hs : (1 : Int) <= (retainedFibrePhase h hh D z)^2 := by
        by_cases hpos : 0 <= retainedFibrePhase h hh D z
        . have hge : 1 <= retainedFibrePhase h hh D z := by omega
          nlinarith only [hge,sq_nonneg (retainedFibrePhase h hh D z-1)]
        . have hle : retainedFibrePhase h hh D z <= -1 := by omega
          nlinarith only [hle,sq_nonneg (retainedFibrePhase h hh D z+1)]
      simpa only [if_pos hz] using hs
  exact le_trans hp (deletion_slack_budgets hF h t hh ht hchi D).2.2.2

theorem small_slack_phase_purity (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (D : Finset (shapeState h))
    (hB : deletionSlack h t D < 4) :
    forall z : regularState (F := F),
      positiveFibreDeletionCount h hh D z=0 \/ negativeFibreDeletionCount h hh D z=0 := by
  have hb := (deletion_slack_budgets hF h t hh ht hchi D).2.2.1
  have hm := mixedDeletionPairs_nonneg h hh D
  have hz : (Finset.univ.sum fun z : regularState (F := F) =>
      positiveFibreDeletionCount h hh D z*negativeFibreDeletionCount h hh D z) = 0 := by
    omega
  intro z
  have hp := Finset.single_le_sum
    (fun s (_ : Membership.mem (Finset.univ : Finset (regularState (F := F))) s) =>
      mul_nonneg (fibreDeletion_sign_nonneg h hh D s).1
        (fibreDeletion_sign_nonneg h hh D s).2) (Finset.mem_univ z)
  rw [hz] at hp
  have he : positiveFibreDeletionCount h hh D z*negativeFibreDeletionCount h hh D z=0 :=
    le_antisymm hp (mul_nonneg (fibreDeletion_sign_nonneg h hh D z).1
      (fibreDeletion_sign_nonneg h hh D z).2)
  exact mul_eq_zero.mp he

theorem zero_slack_fibre_balance (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (D : Finset (shapeState h))
    (hB : deletionSlack h t D=0) :
    forall z : regularState (F := F), retainedFibrePhase h hh D z=0 := by
  have hb := (deletion_slack_budgets hF h t hh ht hchi D).2.2.2
  rw [hB] at hb
  have hs : (Finset.univ.sum fun z : regularState (F := F) =>
      (retainedFibrePhase h hh D z)^2) = 0 :=
    le_antisymm hb (Finset.sum_nonneg (fun z _ => sq_nonneg _))
  intro z
  have hp := Finset.single_le_sum
    (fun s (_ : Membership.mem (Finset.univ : Finset (regularState (F := F))) s) =>
      sq_nonneg (retainedFibrePhase h hh D s)) (Finset.mem_univ z)
  rw [hs] at hp
  exact sq_eq_zero_iff.mp (le_antisymm hp (sq_nonneg _))

theorem deletion_zero_slack_iff (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (D : Finset (shapeState h)) :
    deletionSlack h t D=0 <->
      deletionCapSlack h hh D=0 /\
      (Finset.univ.sum fun z : regularState (F := F) =>
        positiveFibreDeletionCount h hh D z*negativeFibreDeletionCount h hh D z)=0 /\
      forall z : regularState (F := F), retainedFibrePhase h hh D z=0 := by
  constructor
  . intro hB
    have hb := deletion_slack_budgets hF h t hh ht hchi D
    have hc := deletionCapSlack_nonneg h hh D
    have hm := mixedDeletionPairs_nonneg h hh D
    have he := zero_slack_fibre_balance hF h t hh ht hchi D hB
    refine And.intro ?_ (And.intro ?_ he)
    . linarith only [hB,hb.2.1,hc]
    . omega
  . intro hc
    have hi := signed_deletion_slack_certificate hF h t hh ht hchi D
    have he : (Finset.univ.sum fun z : regularState (F := F) =>
        (retainedFibrePhase h hh D z)^2)=0 := by
      simp_rw [hc.2.2]
      simp
    rw [hc.1,hc.2.1,he] at hi
    linarith only [hi]

theorem zero_slack_retainedWave (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (D : Finset (shapeState h))
    (hB : deletionSlack h t D=0) : retainedWave h t D=0 := by
  have he := zero_slack_fibre_balance hF h t hh ht hchi D hB
  have hd (z : regularState (F := F)) :
      fibreDeletionPhase h hh D z=splitCubicPointTrace z.val (z.val+1) := by
    have hz := he z
    rw [retainedFibrePhase_eq hF h hh D z] at hz
    linarith only [hz]
  have hp := full_signed_deletion_identity hF h t hh ht hchi D
  have henergy : (Finset.univ.sum fun z : regularState (F := F) =>
      (fibreDeletionPhase h hh D z)^2) =
      ((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1) := by
    simp_rw [hd]
    exact sum_regular_trace_square hF
  have hres : (Finset.univ.sum fun z : regularState (F := F) =>
      (fibreDeletionPhase h hh D z-splitCubicPointTrace z.val (z.val+1))^2)=0 := by
    simp_rw [hd]
    simp
  rw [henergy,hres] at hp
  linarith only [hp]

theorem positive_retained_slack_ge_one (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (D : Finset (shapeState h))
    (hR : 0 < retainedWave h t D) : 1 <= deletionSlack h t D := by
  have hb := (deletion_slack_budgets hF h t hh ht hchi D).1
  have hne : Not (deletionSlack h t D=0) := by
    intro hz
    have hr := zero_slack_retainedWave hF h t hh ht hchi D hz
    omega
  omega

end FiniteField.QuadraticTripleTwist
