/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldCharacterProjection

/-!
# The optimal character-only probability law

The exact minimizer retains both forbidden rows and has a one-character
correction on admissible rows. It is a nonnegative mean-one density.
Every statistic formed from the two character signs has exactly the same
expectation under this law and the original raw law. Their unavoidable
mean-square difference is nevertheless of reciprocal-cardinality size.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldOptimalCharacterLaw
attribute [local instance] Classical.propDecidable
open _root_.FiniteField _root_.FiniteField.QuadraticPairEuler
open FiniteFieldCharacterProjection FiniteFieldRawHellinger
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem raw_optimal_sign_statistics (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) (g : Int -> Int -> Real) :
    (Finset.univ.sum fun c : F =>
      rawDensity h c*g ((quadraticChar F) c) ((quadraticChar F) (c+h)))=
    (Finset.univ.sum fun c : F =>
      optimalDensity h c*g ((quadraticChar F) c) ((quadraticChar F) (c+h))) := by
  have hz := masked_trace_table_sum hF hm h hh g
  calc
    _ = Finset.univ.sum (fun c : F =>
      optimalDensity h c*g ((quadraticChar F) c) ((quadraticChar F) (c+h))-
        (1/((Fintype.card F : Real)-3))*
          ((maskedTrace h c : Real)*g ((quadraticChar F) c) ((quadraticChar F) (c+h)))) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [raw_density_decomposition hF hm h hh hq c]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib,<- Finset.mul_sum,hz,mul_zero,sub_zero]

theorem sum_optimal_density (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) :
    Finset.univ.sum (optimalDensity h)=(Fintype.card F : Real) := by
  have hs := raw_optimal_sign_statistics hF hm h hh hq (fun _ _ => (1 : Real))
  simp only [mul_one] at hs
  rw [sum_raw_density hF h hh hq] at hs
  exact hs.symm

theorem optimal_density_good_bounds (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) (c : F)
    (hc : Not (c=0)) (hch : Not (c+h=0)) :
    1<=optimalDensity h c /\ optimalDensity h c<=2 := by
  let q : Real := Fintype.card F
  have hq' : 16<=q := hq
  have hd : 0<q-3 := by linarith only [hq']
  have hx : Not ((quadraticChar F) c=0) := by
    intro hz
    have hs := quadraticChar_sq_one hc
    rw [hz] at hs
    norm_num at hs
  have hy : Not ((quadraticChar F) (c+h)=0) := by
    intro hz
    have hs := quadraticChar_sq_one hch
    rw [hz] at hs
    norm_num at hs
  have hb (z : F) (hz : Not (z=0)) :
      -1<=((quadraticChar F) z : Real) /\ ((quadraticChar F) z : Real)<=1 := by
    rcases quadraticChar_real_signs z hz with hs | hs <;> rw [hs] <;>
      constructor <;> norm_num
  have hX := hb c hc
  have hY := hb (c+h) hch
  let B : Real := q-1-
    (1+((quadraticChar F) h : Real))*((quadraticChar F) c : Real)-
    (1-((quadraticChar F) h : Real))*((quadraticChar F) (c+h) : Real)
  have hB : q-3<=B /\ B<=q+1 := by
    dsimp only [B]
    rcases quadraticChar_real_signs h hh with hp | hn
    . rw [hp]
      constructor <;> nlinarith only [hX.1,hX.2]
    . rw [hn]
      constructor <;> nlinarith only [hY.1,hY.2]
  have he : optimalDensity h c=B/(q-3) := by
    simp only [optimalDensity,optimalTable,ite_eq_right hx,ite_eq_right hy,B,q]
  rw [he]
  constructor
  . have ht := div_le_div_of_nonneg_right hB.1 hd.le
    simpa only [div_self (ne_of_gt hd)] using ht
  . calc
      _ <= (2*(q-3))/(q-3) :=
        div_le_div_of_nonneg_right (by linarith only [hB.2,hq']) hd.le
      _ = 2 := by field_simp [ne_of_gt hd]

theorem optimal_density_bounds (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) (c : F) :
    0<=optimalDensity h c /\ optimalDensity h c<=2 := by
  by_cases hc : c=0
  . subst c
    have hz : optimalDensity h 0=0 := by simp [optimalDensity,optimalTable]
    rw [hz]
    norm_num
  . by_cases hch : c+h=0
    . have hz : optimalDensity h c=0 := by
        simp [optimalDensity,optimalTable,hch]
      rw [hz]
      norm_num
    . have hb := optimal_density_good_bounds h hh hq c hc hch
      exact And.intro (le_trans (by norm_num) hb.1) hb.2

theorem optimal_density_square_shift (h c : F)
    (hc : Not (c=0)) (hch : Not (c+h=0)) (he : (quadraticChar F) h=1) :
    optimalDensity h c=((Fintype.card F : Real)-1-2*((quadraticChar F) c : Real))/
      ((Fintype.card F : Real)-3) := by
  have hx : Not ((quadraticChar F) c=0) := by
    intro hz
    have hs := quadraticChar_sq_one hc
    rw [hz] at hs
    norm_num at hs
  have hy : Not ((quadraticChar F) (c+h)=0) := by
    intro hz
    have hs := quadraticChar_sq_one hch
    rw [hz] at hs
    norm_num at hs
  simp only [optimalDensity,optimalTable,ite_eq_right hx,ite_eq_right hy,he,Int.cast_one]
  ring

theorem optimal_density_nonsquare_shift (h c : F)
    (hc : Not (c=0)) (hch : Not (c+h=0)) (he : (quadraticChar F) h=-1) :
    optimalDensity h c=((Fintype.card F : Real)-1-2*((quadraticChar F) (c+h) : Real))/
      ((Fintype.card F : Real)-3) := by
  have hx : Not ((quadraticChar F) c=0) := by
    intro hz
    have hs := quadraticChar_sq_one hc
    rw [hz] at hs
    norm_num at hs
  have hy : Not ((quadraticChar F) (c+h)=0) := by
    intro hz
    have hs := quadraticChar_sq_one hch
    rw [hz] at hs
    norm_num at hs
  simp only [optimalDensity,optimalTable,ite_eq_right hx,ite_eq_right hy,he,
    Int.cast_neg,Int.cast_one]
  ring

theorem character_only_error_reciprocal (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) (g : Int -> Int -> Real) :
    1/(Fintype.card F : Real)<=
      FiniteFieldPairAffinity.squareDistance (Fintype.card F : Real)
        (rawDensity h) (fun c => g ((quadraticChar F) c) ((quadraticChar F) (c+h))) := by
  let q : Real := Fintype.card F
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have hd : 0<q-3 := by dsimp only [q]; linarith only [hq]
  have he : (q+1)/(q*(q-3))-1/q=4/(q*(q-3)) := by
    field_simp [ne_of_gt hq0,ne_of_gt hd]
    <;> ring
  have hn : 0<=4/(q*(q-3)) := div_nonneg (by norm_num) (mul_pos hq0 hd).le
  have hb : 1/q<=(q+1)/(q*(q-3)) := by linarith only [he,hn]
  exact hb.trans (character_only_error_lower hF hm h hh hq g)


theorem character_only_affinity_upper (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) (g : Int -> Int -> Real)
    (hg0 : forall c : F, 0<=g ((quadraticChar F) c) ((quadraticChar F) (c+h)))
    (hg2 : forall c : F, g ((quadraticChar F) c) ((quadraticChar F) (c+h))<=2)
    (hgm : (Finset.univ.sum fun c : F =>
      g ((quadraticChar F) c) ((quadraticChar F) (c+h)))=(Fintype.card F : Real)) :
    FiniteFieldPairAffinity.affinity (Fintype.card F : Real)
      (rawDensity h) (fun c => g ((quadraticChar F) c) ((quadraticChar F) (c+h))) <=
        1-1/(32*(Fintype.card F : Real)) := by
  let q : Real := Fintype.card F
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have he := FiniteFieldPairAffinity.square_distance_le_affinity_defect q 8
    (rawDensity h) (fun c => g ((quadraticChar F) c) ((quadraticChar F) (c+h)))
    (fun c => (raw_density_bounds hF h hh hq c).1) hg0 hq0
    (sum_raw_density hF h hh hq) hgm
    (fun c => by
      have hu := (raw_density_bounds hF h hh hq c).2
      have hg := hg2 c
      linarith only [hu,hg])
  have hl := character_only_error_reciprocal hF hm h hh hq g
  norm_num only [show (4 : Real)*8=32 from by norm_num] at he
  have hid : 1/(32*q)=(1/q)/32 := by
    field_simp [ne_of_gt hq0]
    <;> ring
  change 1/q<=FiniteFieldPairAffinity.squareDistance q (rawDensity h)
    (fun c => g ((quadraticChar F) c) ((quadraticChar F) (c+h))) at hl
  change FiniteFieldPairAffinity.affinity q (rawDensity h)
    (fun c => g ((quadraticChar F) c) ((quadraticChar F) (c+h)))<=1-1/(32*q)
  linarith only [he,hl,hid]

theorem raw_optimal_affinity_upper (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) :
    FiniteFieldPairAffinity.affinity (Fintype.card F : Real)
      (rawDensity h) (optimalDensity h)<=1-1/(32*(Fintype.card F : Real)) := by
  exact character_only_affinity_upper hF hm h hh hq (optimalTable h)
    (fun c => (optimal_density_bounds h hh hq c).1)
    (fun c => (optimal_density_bounds h hh hq c).2)
    (sum_optimal_density hF hm h hh hq)


end PrimeFactorOscillations.FiniteFieldOptimalCharacterLaw
