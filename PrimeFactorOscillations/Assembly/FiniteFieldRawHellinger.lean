/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldPairAffinity
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairMoments
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistLikelihood

/-!
# The original pair law has a nonsummable affinity defect

The actual irreducible-quadratic count is normalized by its full mean.
Its exact second moment differs from flat admissibility at order 1/q.
The elementary count bound gives a uniform density cap, hence an affinity
defect at least 1/(64*q). All singular rows are retained. No Hasse estimate
or integer prime-pair hypothesis is used.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace PrimeFactorOscillations.FiniteFieldRawHellinger
attribute [local instance] Classical.propDecidable
open _root_.FiniteField _root_.FiniteField.QuadraticPairEuler
open _root_.FiniteField.QuadraticPairTwistLikelihood
open FiniteFieldPairAffinity
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev rawDensity (h c : F) : Real := normalizedPairCount c h
abbrev flatDensity (h c : F) : Real := flatPairWeight c h

theorem pair_count_bounds (c h : F) :
    0<=(monicQuadraticPairCount c h : Real) /\
      (monicQuadraticPairCount c h : Real)<=(Fintype.card F : Real) := by
  have hn : (0 : Int)<=monicQuadraticPairCount c h := by
    unfold monicQuadraticPairCount
    apply Finset.sum_nonneg
    intro b _
    split_ifs <;> norm_num
  have hc : monicQuadraticPairCount c h<=(Fintype.card F : Int) := by
    calc
      _ <= Finset.univ.sum (fun _ : F => (1 : Int)) := by
        unfold monicQuadraticPairCount
        apply Finset.sum_le_sum
        intro b _
        split_ifs <;> norm_num
      _ = _ := by simp
  exact And.intro (by exact_mod_cast hn) (by exact_mod_cast hc)

theorem normalization_total (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) :
    4*(Finset.univ.sum fun c : F => (monicQuadraticPairCount c h : Real)) =
      (Fintype.card F : Real)*
        ((Fintype.card F : Real)-(quadraticPairOffset h : Real)) := by
  have hi :
      4*(Finset.univ.sum fun c : F => monicQuadraticPairCount c h) =
        (Fintype.card F : Int)*((Fintype.card F : Int)-quadraticPairOffset h) := by
    rw [sum_monicQuadraticPairCount_eq hF h hh]
    unfold quadraticPairOffset
    ring
  exact_mod_cast hi

theorem denominator_pos (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) :
    0<(Fintype.card F : Real)-(quadraticPairOffset h : Real) := by
  have hb := quadraticPairOffset_real_bounds h hh
  linarith only [hq,hb.2]

theorem raw_density_quotient (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 16<=(Fintype.card F : Real)) (c : F) :
    rawDensity h c=4*(monicQuadraticPairCount c h : Real)/
      ((Fintype.card F : Real)-(quadraticPairOffset h : Real)) := by
  let q : Real := Fintype.card F
  let d : Real := quadraticPairOffset h
  let S : Real := Finset.univ.sum fun t : F => (monicQuadraticPairCount t h : Real)
  have ht := normalization_total hF h hh
  change 4*S=q*(q-d) at ht
  have hS : S=q*(q-d)/4 := by linarith only [ht]
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have hd : 0<q-d := denominator_pos h hh hq
  change q*(monicQuadraticPairCount c h : Real)/S=
    4*(monicQuadraticPairCount c h : Real)/(q-d)
  rw [hS]
  field_simp [ne_of_gt hq0,ne_of_gt hd]
  <;> ring

theorem raw_density_bounds (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 16<=(Fintype.card F : Real)) (c : F) :
    0<=rawDensity h c /\ rawDensity h c<=6 := by
  let q : Real := Fintype.card F
  let d : Real := quadraticPairOffset h
  have hw := pair_count_bounds c h
  have hb := quadraticPairOffset_real_bounds h hh
  have hd : 0<q-d := denominator_pos h hh hq
  rw [raw_density_quotient hF h hh hq]
  change 0<=4*(monicQuadraticPairCount c h : Real)/(q-d) /\
    4*(monicQuadraticPairCount c h : Real)/(q-d)<=6
  constructor
  . exact div_nonneg (mul_nonneg (by norm_num) hw.1) hd.le
  . have ht : 4*(monicQuadraticPairCount c h : Real)<=6*(q-d) := by
      dsimp only [q,d]
      linarith only [hw.2,hq,hb.2]
    calc
      _ <= (6*(q-d))/(q-d) := div_le_div_of_nonneg_right ht hd.le
      _ = _ := by field_simp [ne_of_gt hd]

theorem sum_raw_density (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 16<=(Fintype.card F : Real)) :
    Finset.univ.sum (rawDensity h)=(Fintype.card F : Real) := by
  have hm := normalizedPairCount_mean_one hF h hh (ne_of_gt (denominator_pos h hh hq))
  have hq0 : 0<(Fintype.card F : Real) := by linarith only [hq]
  change (1/(Fintype.card F : Real))*(Finset.univ.sum (rawDensity h))=1 at hm
  field_simp [ne_of_gt hq0] at hm
  exact hm

theorem raw_mul_mask (hF : Not (ringChar F=2)) (h c : F) :
    rawDensity h c*admissibilityMask c h=rawDensity h c := by
  by_cases hc : c=0
  . simp [hc,rawDensity,normalizedPairCount,monicQuadraticPairCount_zero hF]
  . by_cases hn : c=-h
    . simp [hn,rawDensity,normalizedPairCount,monicQuadraticPairCount_neg_shift hF]
    . simp [admissibilityMask,hc,hn]

theorem flat_density_bounds (h : F) (hq : 16<=(Fintype.card F : Real)) (c : F) :
    0<=flatDensity h c /\ flatDensity h c<=2 := by
  let q : Real := Fintype.card F
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have hd : 0<q-2 := by dsimp only [q]; linarith only [hq]
  have hm : 0<=admissibilityMask c h /\ admissibilityMask c h<=1 := by
    unfold admissibilityMask
    split_ifs <;> constructor <;> norm_num
  have hs : 0<=q/(q-2) := div_nonneg hq0.le hd.le
  have hcap : q/(q-2)<=2 := by
    calc
      _ <= (2*(q-2))/(q-2) := div_le_div_of_nonneg_right
        (by dsimp only [q]; linarith only [hq]) hd.le
      _ = _ := by field_simp [ne_of_gt hd]
  change 0<=(q/(q-2))*admissibilityMask c h /\
    (q/(q-2))*admissibilityMask c h<=2
  exact And.intro (mul_nonneg hs hm.1)
    (le_trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hm.2 hs) hcap)

theorem sum_flat_density (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) :
    Finset.univ.sum (flatDensity h)=(Fintype.card F : Real) := by
  have hd : 0<(Fintype.card F : Real)-2 := by linarith only [hq]
  unfold flatDensity flatPairWeight
  rw [<- Finset.mul_sum,sum_mask h hh]
  field_simp [ne_of_gt hd]

theorem raw_flat_cross_moment (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 16<=(Fintype.card F : Real)) :
    (1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => rawDensity h c*flatDensity h c) =
        (Fintype.card F : Real)/((Fintype.card F : Real)-2) := by
  let q : Real := Fintype.card F
  have hp (c : F) : rawDensity h c*flatDensity h c=(q/(q-2))*rawDensity h c := by
    change rawDensity h c*((q/(q-2))*admissibilityMask c h)=_
    calc
      _ = (q/(q-2))*(rawDensity h c*admissibilityMask c h) := by ring
      _ = _ := by rw [raw_mul_mask hF]
  simp_rw [hp]
  rw [<- Finset.mul_sum,sum_raw_density hF h hh hq]
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  change (1/q)*((q/(q-2))*q)=q/(q-2)
  field_simp [ne_of_gt hq0]
  <;> ring

theorem flat_second_moment (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) :
    (1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => (flatDensity h c)^2) =
        (Fintype.card F : Real)/((Fintype.card F : Real)-2) := by
  let q : Real := Fintype.card F
  have hp (c : F) : (flatDensity h c)^2=(q/(q-2))*flatDensity h c := by
    unfold flatDensity flatPairWeight
    rw [mul_pow,mask_square]
    dsimp only [q]
    ring
  simp_rw [hp]
  rw [<- Finset.mul_sum,sum_flat_density h hh hq]
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  change (1/q)*((q/(q-2))*q)=q/(q-2)
  field_simp [ne_of_gt hq0]
  <;> ring

theorem raw_flat_square_distance_eq (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 16<=(Fintype.card F : Real)) :
    squareDistance (Fintype.card F : Real) (rawDensity h) (flatDensity h) =
      (1/(Fintype.card F : Real))*
        (Finset.univ.sum fun c : F => (rawDensity h c)^2)-
          (Fintype.card F : Real)/((Fintype.card F : Real)-2) := by
  have hp (c : F) : (rawDensity h c-flatDensity h c)^2=
      (rawDensity h c)^2-2*(rawDensity h c*flatDensity h c)+(flatDensity h c)^2 := by ring
  unfold squareDistance
  simp_rw [hp]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,<- Finset.mul_sum]
  have hc := raw_flat_cross_moment hF h hh hq
  have hf := flat_second_moment h hh hq
  nlinarith only [hc,hf]

theorem raw_second_moment_lower (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 16<=(Fintype.card F : Real)) :
    1+3/(Fintype.card F : Real) <=
      (1/(Fintype.card F : Real))*
        (Finset.univ.sum fun c : F => (rawDensity h c)^2) := by
  let q : Real := Fintype.card F
  let d : Real := quadraticPairOffset h
  have hm := normalizedPairCount_second_moment_large hF h hh hq
  change (1/q)*(Finset.univ.sum fun c : F => (rawDensity h c)^2)=
    1+(3*q+d)/(q*(q-d)) at hm
  rw [hm]
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have hd : 0<q-d := denominator_pos h hh hq
  have hb := quadraticPairOffset_real_bounds h hh
  have hd0 : 0<=d := by dsimp only [d]; linarith only [hb.1]
  have he : (3*q+d)/(q*(q-d))-3/q=4*d/(q*(q-d)) := by
    field_simp [ne_of_gt hq0,ne_of_gt hd]
    <;> ring
  have hn : 0<=4*d/(q*(q-d)) :=
    div_nonneg (mul_nonneg (by norm_num) hd0) (mul_pos hq0 hd).le
  change 1+3/q<=1+(3*q+d)/(q*(q-d))
  linarith only [he,hn]

theorem raw_flat_square_distance_lower (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 16<=(Fintype.card F : Real)) :
    1/(2*(Fintype.card F : Real)) <=
      squareDistance (Fintype.card F : Real) (rawDensity h) (flatDensity h) := by
  let q : Real := Fintype.card F
  have hm := raw_second_moment_lower hF h hh hq
  have heq := raw_flat_square_distance_eq hF h hh hq
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have hq2 : 0<q-2 := by dsimp only [q]; linarith only [hq]
  have he : 1+3/q-q/(q-2)-1/(2*q)=(q-10)/(2*q*(q-2)) := by
    field_simp [ne_of_gt hq0,ne_of_gt hq2]
    <;> ring
  have hn : 0<=(q-10)/(2*q*(q-2)) := by
    apply div_nonneg
    . dsimp only [q]
      linarith only [hq]
    . exact (mul_pos (mul_pos (by norm_num) hq0) hq2).le
  change 1/(2*q)<=squareDistance q (rawDensity h) (flatDensity h)
  change 1+3/q<=(1/q)*(Finset.univ.sum fun c : F => (rawDensity h c)^2) at hm
  change squareDistance q (rawDensity h) (flatDensity h)=
    (1/q)*(Finset.univ.sum fun c : F => (rawDensity h c)^2)-q/(q-2) at heq
  linarith only [hm,heq,he,hn]

theorem raw_flat_affinity_upper (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 16<=(Fintype.card F : Real)) :
    affinity (Fintype.card F : Real) (rawDensity h) (flatDensity h) <=
      1-1/(64*(Fintype.card F : Real)) := by
  let q : Real := Fintype.card F
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have he := square_distance_le_affinity_defect q 8 (rawDensity h) (flatDensity h)
    (fun c => (raw_density_bounds hF h hh hq c).1)
    (fun c => (flat_density_bounds h hq c).1) hq0
    (sum_raw_density hF h hh hq) (sum_flat_density h hh hq)
    (fun c => by
      have hu := (raw_density_bounds hF h hh hq c).2
      have hv := (flat_density_bounds h hq c).2
      linarith only [hu,hv])
  have hg := raw_flat_square_distance_lower hF h hh hq
  have hid : 1/(64*q)=(1/(2*q))/32 := by
    field_simp [ne_of_gt hq0]
    <;> norm_num
  norm_num only [show (4 : Real)*8=32 from by norm_num] at he
  change 1/(2*q)<=squareDistance q (rawDensity h) (flatDensity h) at hg
  change affinity q (rawDensity h) (flatDensity h)<=1-1/(64*q)
  linarith only [he,hg,hid]

end PrimeFactorOscillations.FiniteFieldRawHellinger
