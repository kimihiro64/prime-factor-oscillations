/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticTripleFluctuation
/-!
# Canonical companion symmetry for quadratic triples

The affine weight q-3+Delta is twice an actual opposite-character companion
count. It symmetrizes the full compensated triple fluctuation law. The
normalization, affine uniqueness and exceptional small fields are developed
without a Hasse bound or an integer-prime transfer claim.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticTripleTwist
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem sum_regular_one :
    (Finset.univ.sum fun _ : regularState (F := F) => (1 : Int)) =
      (Fintype.card F : Int)-2 := by
  have hp (z : F) :
      (if regular z then (1 : Int) else 0) +
      (if z=0 then 1 else 0) + (if z = -1 then 1 else 0) = 1 := by
    by_cases hz : z=0
    . subst z
      simp [regular]
    . by_cases hm : z = -1
      . subst z
        simp [regular]
      . have hz1 : Not (z+1=0) := by
          intro he
          apply hm
          calc
            z = (z+1)-1 := by ring
            _ = -1 := by rw [he]; ring
        simp [regular,hz,hm,hz1]
  have hs := Finset.sum_subtype
    (F := (inferInstance : Fintype (regularState (F := F))))
    (p := fun z : F => regular z)
    (Finset.univ.filter (fun z : F => regular z))
    (fun z => by simp) (fun _ : F => (1 : Int))
  have hsum : (Finset.univ.sum fun z : F =>
      (if regular z then (1 : Int) else 0) +
      (if z=0 then 1 else 0) + (if z = -1 then 1 else 0)) =
      (Fintype.card F : Int) := by
    simp_rw [hp]
    simp
  simp only [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hsum
  rw [<- hs,Finset.sum_filter]
  linarith only [hsum]

theorem full_shape_mass (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h=0)) (ht : Not (t=0)) (hchi : quadraticChar F t = -1) :
    (Finset.univ.sum fun _ : shapeState h => (1 : Int)) =
      ((Fintype.card F : Int)-2)*((Fintype.card F : Int)-3) := by
  have hf := full_shape_fluctuation hF h t hh ht hchi (fun _ : Int => 1)
  have hs : (Finset.univ.sum fun z : regularState (F := F) =>
      ((Fintype.card F : Int)-3-splitCubicPointTrace z.val (z.val+1))*1 +
      ((Fintype.card F : Int)-3+splitCubicPointTrace z.val (z.val+1))*1) =
      (2*((Fintype.card F : Int)-3))*((Fintype.card F : Int)-2) := by
    calc
      _ = Finset.univ.sum (fun _ : regularState (F := F) =>
          (2*((Fintype.card F : Int)-3))*1) := by
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by rw [<- Finset.mul_sum,sum_regular_one]
  nlinarith only [hf,hs]

def symmetryWeight (h t : F) (p : shapeState h) : Int :=
  (Fintype.card F : Int)-3+compensatedWave h p.val.1 t p.val.2

def symmetryNormalizer (F : Type*) [Fintype F] : Int :=
  ((Fintype.card F : Int)-3)*((Fintype.card F : Int)-1)*
    ((Fintype.card F : Int)-5)

theorem sum_symmetryWeight (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h=0)) (ht : Not (t=0)) (hchi : quadraticChar F t = -1) :
    (Finset.univ.sum fun p : shapeState h => symmetryWeight h t p) =
      symmetryNormalizer F := by
  unfold symmetryWeight symmetryNormalizer
  rw [Finset.sum_add_distrib]
  have hc := full_shape_mass hF h t hh ht hchi
  have hm := full_shape_first_moment hF h t hh ht hchi
  have hs : (Finset.univ.sum fun _ : shapeState h =>
      (Fintype.card F : Int)-3) =
      ((Fintype.card F : Int)-3)*
      (((Fintype.card F : Int)-2)*((Fintype.card F : Int)-3)) := by
    calc
      _ = Finset.univ.sum (fun _ : shapeState h =>
          ((Fintype.card F : Int)-3)*1) := by simp only [mul_one]
      _ = _ := by rw [<- Finset.mul_sum,hc]
  rw [hs,hm]
  ring

theorem full_shape_weighted_reflection (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h=0)) (ht : Not (t=0)) (hchi : quadraticChar F t = -1)
    (f : Int -> Int) :
    (Finset.univ.sum fun p : shapeState h =>
      symmetryWeight h t p * f (compensatedWave h p.val.1 t p.val.2)) =
    (Finset.univ.sum fun p : shapeState h =>
      symmetryWeight h t p * f (-compensatedWave h p.val.1 t p.val.2)) := by
  have hf := full_shape_fluctuation hF h t hh ht hchi
    (fun v : Int => ((Fintype.card F : Int)-3+v)*f v)
  have hg := full_shape_fluctuation hF h t hh ht hchi
    (fun v : Int => ((Fintype.card F : Int)-3+v)*f (-v))
  have he : (Finset.univ.sum fun z : regularState (F := F) =>
      ((Fintype.card F : Int)-3-splitCubicPointTrace z.val (z.val+1)) *
        (((Fintype.card F : Int)-3+splitCubicPointTrace z.val (z.val+1)) *
          f (splitCubicPointTrace z.val (z.val+1))) +
      ((Fintype.card F : Int)-3+splitCubicPointTrace z.val (z.val+1)) *
        (((Fintype.card F : Int)-3+(-splitCubicPointTrace z.val (z.val+1))) *
          f (-splitCubicPointTrace z.val (z.val+1)))) =
    (Finset.univ.sum fun z : regularState (F := F) =>
      ((Fintype.card F : Int)-3-splitCubicPointTrace z.val (z.val+1)) *
        (((Fintype.card F : Int)-3+splitCubicPointTrace z.val (z.val+1)) *
          f (-splitCubicPointTrace z.val (z.val+1))) +
      ((Fintype.card F : Int)-3+splitCubicPointTrace z.val (z.val+1)) *
        (((Fintype.card F : Int)-3+(-splitCubicPointTrace z.val (z.val+1))) *
          f (-(-splitCubicPointTrace z.val (z.val+1))))) := by
    apply Finset.sum_congr rfl
    intro z _
    simp only [neg_neg]
    ring
  change 2*(Finset.univ.sum fun p : shapeState h =>
    symmetryWeight h t p*f (compensatedWave h p.val.1 t p.val.2)) = _ at hf
  change 2*(Finset.univ.sum fun p : shapeState h =>
    symmetryWeight h t p*f (-compensatedWave h p.val.1 t p.val.2)) = _ at hg
  linarith only [hf,hg,he]


def oppositeCompanionCount (z e : F) : Int :=
  Finset.univ.sum fun y : F =>
    if IsSquare (e*(y*(y+1)*(y+(z+1)))) then 0 else 1

theorem twice_oppositeCompanion_indicator (z e y : F) (he : Not (e=0)) :
    2*(if IsSquare (e*(y*(y+1)*(y+(z+1)))) then (0 : Int) else 1) =
      admissibleWeight (1 : F) (z+1) y -
        quadraticChar F e * fibrePhase z y := by
  rw [twice_nonsquare_indicator]
  by_cases hy : admissible (1 : F) (z+1) y
  . have hv : Not (e*(y*(y+1)*(y+(z+1)))=0) :=
      mul_ne_zero he (mul_ne_zero (mul_ne_zero hy.1 hy.2.1) hy.2.2)
    simp [hv,admissibleWeight,hy,fibrePhase,map_mul]
  . have hv : y*(y+1)*(y+(z+1))=0 := by
      by_cases hy0 : y=0
      . simp [hy0]
      . by_cases hy1 : y+1=0
        . simp [hy1]
        . by_cases hyz : y+(z+1)=0
          . simp [hyz]
          . exact False.elim (hy (And.intro hy0 (And.intro hy1 hyz)))
    simp [hv,admissibleWeight,hy,fibrePhase]

theorem twice_oppositeCompanionCount (hF : Not (ringChar F = 2))
    (z e : F) (hz : regular z) (he : Not (e=0)) :
    2*oppositeCompanionCount z e =
      (Fintype.card F : Int)-3+
        quadraticChar F e*splitCubicPointTrace z (z+1) := by
  have hz1 : Not ((1 : F)=z+1) := by
    intro hv
    apply hz.1
    calc
      z = (z+1)-1 := by ring
      _ = 0 := by rw [<- hv]; ring
  unfold oppositeCompanionCount
  rw [Finset.mul_sum]
  calc
    _ = Finset.univ.sum (fun y : F =>
        admissibleWeight (1 : F) (z+1) y -
          quadraticChar F e*fibrePhase z y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact twice_oppositeCompanion_indicator z e y he
    _ = _ := by
      rw [Finset.sum_sub_distrib,<- Finset.mul_sum,
        sum_admissibleWeight (1 : F) (z+1) one_ne_zero hz.2 hz1,
        sum_fibrePhase hF z]
      ring

theorem oppositeCompanionCount_nonneg (z e : F) :
    0 <= oppositeCompanionCount z e := by
  apply Finset.sum_nonneg
  intro y _
  split_ifs <;> omega

theorem symmetryWeight_eq_twice_companion (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (p : shapeState h) :
    symmetryWeight h t p =
      2*oppositeCompanionCount (shapeParameter h p.val.1 p.val.2)
        ((p.val.1-h)*p.val.2) := by
  have hz := (shapeParameter_admissible_iff h p.val.1 hh
    p.property.1 p.property.2.1 p.val.2).mp p.property.2.2
  have he : Not ((p.val.1-h)*p.val.2=0) :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm p.property.2.1)) p.property.2.2.1
  have hd := compensatedWave_eq_trace hF h p.val.1 t p.val.2 hh
    p.property.1 p.property.2.1 ht hchi p.property.2.2
  rw [shapeParameter_trace hF h p.val.1 p.val.2
    p.property.2.1 p.property.2.2.1] at hd
  unfold symmetryWeight
  rw [hd]
  exact (twice_oppositeCompanionCount hF _ _ hz.1 he).symm

theorem symmetryWeight_nonneg (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (p : shapeState h) :
    0 <= symmetryWeight h t p := by
  rw [symmetryWeight_eq_twice_companion hF h t hh ht hchi p]
  exact mul_nonneg (by omega) (oppositeCompanionCount_nonneg _ _)

theorem full_shape_weighted_odd_moment_zero (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (m : Nat) :
    (Finset.univ.sum fun p : shapeState h =>
      symmetryWeight h t p*(compensatedWave h p.val.1 t p.val.2)^(2*m+1)) = 0 := by
  have hi := full_shape_weighted_reflection hF h t hh ht hchi
    (fun v : Int => v^(2*m+1))
  simp_rw [neg_odd_power,mul_neg,Finset.sum_neg_distrib] at hi
  omega

omit [Field F] [DecidableEq F] in
theorem symmetryNormalizer_pos (hq : 5 < Fintype.card F) :
    0 < symmetryNormalizer F := by
  have hi : (5 : Int) < Fintype.card F := by exact_mod_cast hq
  unfold symmetryNormalizer
  exact mul_pos (mul_pos (by omega) (by omega)) (by omega)

def symmetryMass (h t : F) (p : shapeState h) : Real :=
  (symmetryWeight h t p : Real)/(symmetryNormalizer F : Real)

theorem symmetryMass_nonneg (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F)
    (p : shapeState h) : 0 <= symmetryMass h t p := by
  apply div_nonneg
  . exact_mod_cast symmetryWeight_nonneg hF h t hh ht hchi p
  . exact_mod_cast (symmetryNormalizer_pos (F := F) hq).le

theorem sum_symmetryMass (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F) :
    (Finset.univ.sum fun p : shapeState h => symmetryMass h t p) = 1 := by
  have hi := sum_symmetryWeight hF h t hh ht hchi
  have hr : (Finset.univ.sum fun p : shapeState h =>
      (symmetryWeight h t p : Real)) = (symmetryNormalizer F : Real) := by
    exact_mod_cast hi
  have hn : Not ((symmetryNormalizer F : Real)=0) := by
    have hp : (0 : Real) < symmetryNormalizer F := by
      exact_mod_cast symmetryNormalizer_pos (F := F) hq
    exact ne_of_gt hp
  unfold symmetryMass
  rw [<- Finset.sum_div,hr,div_self hn]

theorem symmetryMass_reflected_test (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (f : Int -> Int) :
    (Finset.univ.sum fun p : shapeState h =>
      symmetryMass h t p*(f (compensatedWave h p.val.1 t p.val.2) : Real)) =
    (Finset.univ.sum fun p : shapeState h =>
      symmetryMass h t p*(f (-compensatedWave h p.val.1 t p.val.2) : Real)) := by
  have hi := full_shape_weighted_reflection hF h t hh ht hchi f
  have hr : (Finset.univ.sum fun p : shapeState h =>
      (symmetryWeight h t p : Real)*(f (compensatedWave h p.val.1 t p.val.2) : Real)) =
    (Finset.univ.sum fun p : shapeState h =>
      (symmetryWeight h t p : Real)*(f (-compensatedWave h p.val.1 t p.val.2) : Real)) := by
    exact_mod_cast hi
  unfold symmetryMass
  simp_rw [div_mul_eq_mul_div]
  rw [<- Finset.sum_div,<- Finset.sum_div,hr]

theorem symmetryMass_first_moment_zero (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) :
    (Finset.univ.sum fun p : shapeState h =>
      symmetryMass h t p*(compensatedWave h p.val.1 t p.val.2 : Real)) = 0 := by
  have hi := full_shape_weighted_odd_moment_zero hF h t hh ht hchi 0
  have hr : (Finset.univ.sum fun p : shapeState h =>
      (symmetryWeight h t p : Real)*(compensatedWave h p.val.1 t p.val.2 : Real)) = 0 := by
    simpa using (congrArg (fun v : Int => (v : Real)) hi)
  unfold symmetryMass
  simp_rw [div_mul_eq_mul_div]
  rw [<- Finset.sum_div,hr,zero_div]

theorem sum_affine_shape_mass (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (A B : Real) :
    (Finset.univ.sum fun p : shapeState h =>
      A+B*(compensatedWave h p.val.1 t p.val.2 : Real)) =
    A*((Fintype.card F : Real)-2)*((Fintype.card F : Real)-3) -
      B*((Fintype.card F : Real)-3)*((Fintype.card F : Real)+1) := by
  have hc : (Finset.univ.sum fun _ : shapeState h => (1 : Real)) =
      ((Fintype.card F : Real)-2)*((Fintype.card F : Real)-3) := by
    exact_mod_cast full_shape_mass hF h t hh ht hchi
  have hm : (Finset.univ.sum fun p : shapeState h =>
      (compensatedWave h p.val.1 t p.val.2 : Real)) =
      -((Fintype.card F : Real)-3)*((Fintype.card F : Real)+1) := by
    exact_mod_cast full_shape_first_moment hF h t hh ht hchi
  calc
    _ = A*(Finset.univ.sum fun _ : shapeState h => (1 : Real)) +
        B*(Finset.univ.sum fun p : shapeState h =>
          (compensatedWave h p.val.1 t p.val.2 : Real)) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_one]
    _ = _ := by rw [hc,hm]; ring

theorem sum_affine_shape_first_moment (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (A B : Real) :
    (Finset.univ.sum fun p : shapeState h =>
      (A+B*(compensatedWave h p.val.1 t p.val.2 : Real))*
        (compensatedWave h p.val.1 t p.val.2 : Real)) =
    -A*((Fintype.card F : Real)-3)*((Fintype.card F : Real)+1) +
      B*((Fintype.card F : Real)-3)^2*((Fintype.card F : Real)+1) := by
  have hm : (Finset.univ.sum fun p : shapeState h =>
      (compensatedWave h p.val.1 t p.val.2 : Real)) =
      -((Fintype.card F : Real)-3)*((Fintype.card F : Real)+1) := by
    exact_mod_cast full_shape_first_moment hF h t hh ht hchi
  have hs : (Finset.univ.sum fun p : shapeState h =>
      (compensatedWave h p.val.1 t p.val.2 : Real)^2) =
      ((Fintype.card F : Real)-3)^2*((Fintype.card F : Real)+1) := by
    exact_mod_cast full_shape_second_moment hF h t hh ht hchi
  calc
    _ = Finset.univ.sum (fun p : shapeState h =>
        A*(compensatedWave h p.val.1 t p.val.2 : Real) +
          B*(compensatedWave h p.val.1 t p.val.2 : Real)^2) := by
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib,<- Finset.mul_sum,<- Finset.mul_sum,hm,hs]
      ring

theorem affine_centered_mass_unique (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F)
    (A B : Real)
    (hnorm : (Finset.univ.sum fun p : shapeState h =>
      A+B*(compensatedWave h p.val.1 t p.val.2 : Real)) = 1)
    (hmean : (Finset.univ.sum fun p : shapeState h =>
      (A+B*(compensatedWave h p.val.1 t p.val.2 : Real))*
        (compensatedWave h p.val.1 t p.val.2 : Real)) = 0) :
    A = ((Fintype.card F : Real)-3)/(symmetryNormalizer F : Real) /\
      B = 1/(symmetryNormalizer F : Real) := by
  rw [sum_affine_shape_mass hF h t hh ht hchi A B] at hnorm
  rw [sum_affine_shape_first_moment hF h t hh ht hchi A B] at hmean
  have hqr : (5 : Real) < Fintype.card F := by exact_mod_cast hq
  have hc : Not ((((Fintype.card F : Real)-3)*((Fintype.card F : Real)+1))=0) :=
    mul_ne_zero (ne_of_gt (by linarith only [hqr]))
      (ne_of_gt (by linarith only [hqr]))
  have he : (((Fintype.card F : Real)-3)*((Fintype.card F : Real)+1)) *
      (A-((Fintype.card F : Real)-3)*B) = 0 := by
    calc
      _ = -(-A*((Fintype.card F : Real)-3)*((Fintype.card F : Real)+1) +
          B*((Fintype.card F : Real)-3)^2*((Fintype.card F : Real)+1)) := by ring
      _ = 0 := by rw [hmean]; ring
  have hA : A = ((Fintype.card F : Real)-3)*B :=
    sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hc)
  have hz : (symmetryNormalizer F : Real) =
      ((Fintype.card F : Real)-3)*((Fintype.card F : Real)-1)*
        ((Fintype.card F : Real)-5) := by simp [symmetryNormalizer]
  have hn : Not ((symmetryNormalizer F : Real)=0) := by
    have hp : (0 : Real) < symmetryNormalizer F := by
      exact_mod_cast symmetryNormalizer_pos (F := F) hq
    exact ne_of_gt hp
  have hB : B = 1/(symmetryNormalizer F : Real) := by
    apply (eq_div_iff hn).mpr
    calc
      _ = (((Fintype.card F : Real)-3)*B)*
          ((Fintype.card F : Real)-2)*((Fintype.card F : Real)-3) -
          B*((Fintype.card F : Real)-3)*((Fintype.card F : Real)+1) := by
        rw [hz]
        ring
      _ = 1 := by rw [<- hA]; exact hnorm
  exact And.intro (by rw [hA,hB]; ring) hB

theorem no_affine_centered_mass_small (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1)
    (hq : Fintype.card F = 3 \/ Fintype.card F = 5) (A B : Real)
    (hnorm : (Finset.univ.sum fun p : shapeState h =>
      A+B*(compensatedWave h p.val.1 t p.val.2 : Real)) = 1)
    (hmean : (Finset.univ.sum fun p : shapeState h =>
      (A+B*(compensatedWave h p.val.1 t p.val.2 : Real))*
        (compensatedWave h p.val.1 t p.val.2 : Real)) = 0) : False := by
  rw [sum_affine_shape_mass hF h t hh ht hchi A B] at hnorm
  rw [sum_affine_shape_first_moment hF h t hh ht hchi A B] at hmean
  rcases hq with hq | hq
  . norm_num [hq] at hnorm
  . norm_num [hq] at hnorm hmean
    linarith only [hnorm,hmean]

theorem wave_card_five (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : Fintype.card F = 5)
    (p : shapeState h) : compensatedWave h p.val.1 t p.val.2 = -2 := by
  have hp := symmetryWeight_nonneg hF h t hh ht hchi p
  have hle : symmetryWeight h t p <=
      Finset.univ.sum (fun s : shapeState h => symmetryWeight h t s) :=
    Finset.single_le_sum
      (fun s _ => symmetryWeight_nonneg hF h t hh ht hchi s) (Finset.mem_univ p)
  rw [sum_symmetryWeight hF h t hh ht hchi] at hle
  norm_num [symmetryNormalizer,hq] at hle
  unfold symmetryWeight at hp hle
  norm_num [hq] at hp hle
  omega


theorem symmetryMass_reflected_bin (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (r : Int) :
    (Finset.univ.sum fun p : shapeState h =>
      if compensatedWave h p.val.1 t p.val.2 = r then symmetryMass h t p else 0) =
    (Finset.univ.sum fun p : shapeState h =>
      if compensatedWave h p.val.1 t p.val.2 = -r then symmetryMass h t p else 0) := by
  have hi := symmetryMass_reflected_test hF h t hh ht hchi
    (fun v : Int => if v=r then 1 else 0)
  simpa only [apply_ite,Int.cast_one,Int.cast_zero,mul_ite,mul_one,mul_zero,
    neg_eq_iff_eq_neg] using hi

theorem affine_centered_mass_eq_symmetryMass (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : 5 < Fintype.card F)
    (A B : Real)
    (hnorm : (Finset.univ.sum fun p : shapeState h =>
      A+B*(compensatedWave h p.val.1 t p.val.2 : Real)) = 1)
    (hmean : (Finset.univ.sum fun p : shapeState h =>
      (A+B*(compensatedWave h p.val.1 t p.val.2 : Real))*
        (compensatedWave h p.val.1 t p.val.2 : Real)) = 0)
    (p : shapeState h) :
    A+B*(compensatedWave h p.val.1 t p.val.2 : Real) = symmetryMass h t p := by
  have hc := affine_centered_mass_unique hF h t hh ht hchi hq A B hnorm hmean
  rw [hc.1,hc.2]
  simp only [symmetryMass,symmetryWeight,Int.cast_add,Int.cast_sub,
    Int.cast_natCast,Int.cast_ofNat]
  ring

theorem shapeState_card_three (hF : Not (ringChar F = 2))
    (h t : F) (hh : Not (h=0)) (ht : Not (t=0))
    (hchi : quadraticChar F t = -1) (hq : Fintype.card F = 3) :
    Fintype.card (shapeState h) = 0 := by
  have hi := full_shape_mass hF h t hh ht hchi
  norm_num [hq] at hi
  exact_mod_cast hi

end FiniteField.QuadraticTripleTwist
