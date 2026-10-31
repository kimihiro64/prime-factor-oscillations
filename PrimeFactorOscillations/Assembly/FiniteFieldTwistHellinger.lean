/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldRawHellinger

/-!
# The raw and averaged quadratic-pair laws separate

The trace-free correction has summable squared size. Its affinity defect
from flat admissibility is at most 5/q^2. The original count instead has
a defect of order 1/q. Keeping their common flat reference and the cross
term gives a quantitative raw-versus-averaged separation.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldTwistHellinger
attribute [local instance] Classical.propDecidable
open _root_.FiniteField _root_.FiniteField.QuadraticPairTwistLikelihood
open FiniteFieldPairAffinity FiniteFieldRawHellinger
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev twistDensity (h c : F) : Real := traceFreePairWeight c h

theorem scalar_sqrt_defect_le_square (a : Real) (ha : 0<=a) :
    (Real.sqrt a-1)^2<=(a-1)^2 := by
  have hs := Real.sq_sqrt ha
  have hn := Real.sqrt_nonneg a
  have he : (Real.sqrt a-1)*(Real.sqrt a+1)=a-1 := by nlinarith only [hs]
  have hp : 0<=(Real.sqrt a+1)^2-1 := by nlinarith only [hn,sq_nonneg (Real.sqrt a)]
  have hm := mul_nonneg (sq_nonneg (Real.sqrt a-1)) hp
  calc
    _ <= (Real.sqrt a-1)^2*(Real.sqrt a+1)^2 := by nlinarith only [hm]
    _ = _ := by rw [<- mul_pow,he]

theorem twist_density_nonneg (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) (c : F) : 0<=twistDensity h c := by
  have h7 : 7<=(Fintype.card F : Real) := by linarith only [hq]
  have hf := (flat_density_bounds h hq c).1
  have hd := (likelihood_factor_bounds c h hh h7).1
  change 0<=traceFreePairWeight c h
  rw [local_factorization c h h7]
  exact mul_nonneg hf (by linarith only [hd])

theorem sum_twist_density (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 16<=(Fintype.card F : Real)) :
    Finset.univ.sum (twistDensity h)=(Fintype.card F : Real) := by
  have hm := traceFreePairWeight_mean_one hF h hh (by linarith only [hq])
  have hq0 : 0<(Fintype.card F : Real) := by linarith only [hq]
  change (1/(Fintype.card F : Real))*(Finset.univ.sum (twistDensity h))=1 at hm
  field_simp [ne_of_gt hq0] at hm
  exact hm

theorem twist_flat_sqrt_gap_le (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) (c : F) :
    (Real.sqrt (twistDensity h c)-Real.sqrt (flatDensity h c))^2 <=
      2*(localCorrection c h)^2 := by
  let f := flatDensity h c
  let a := 1+localCorrection c h
  have h7 : 7<=(Fintype.card F : Real) := by linarith only [hq]
  have hf := flat_density_bounds h hq c
  have ha : 0<=a := by
    have hh0 := (likelihood_factor_bounds c h hh h7).1
    dsimp only [a]
    linarith only [hh0]
  have hs := scalar_sqrt_defect_le_square a ha
  have he : twistDensity h c=f*a := local_factorization c h h7
  rw [he,Real.sqrt_mul hf.1]
  have hfe : (Real.sqrt f*Real.sqrt a-Real.sqrt f)^2=
      f*(Real.sqrt a-1)^2 := by
    calc
      _ = (Real.sqrt f)^2*(Real.sqrt a-1)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hf.1]
  rw [hfe]
  calc
    _ <= f*(a-1)^2 := mul_le_mul_of_nonneg_left hs hf.1
    _ <= 2*(a-1)^2 := mul_le_mul_of_nonneg_right hf.2 (sq_nonneg _)
    _ = _ := by dsimp only [a]; ring

theorem twist_flat_affinity_defect_upper (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 16<=(Fintype.card F : Real)) :
    1-affinity (Fintype.card F : Real) (twistDensity h) (flatDensity h) <=
      5/(Fintype.card F : Real)^2 := by
  let q : Real := Fintype.card F
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have hsum := Finset.sum_le_sum (fun c (_ : Membership.mem (Finset.univ : Finset F) c) =>
    twist_flat_sqrt_gap_le h hh hq c)
  rw [<- Finset.mul_sum] at hsum
  have hs := sqrt_energy_identity q (twistDensity h) (flatDensity h)
    (twist_density_nonneg h hh hq) (fun c => (flat_density_bounds h hq c).1)
    hq0 (sum_twist_density hF h hh hq) (sum_flat_density h hh hq)
  rw [hs] at hsum
  have hv := local_correction_variance_le hF h hh (by linarith only [hq])
  have hm := mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hq0.le)
  have hid : (1/q)*(2*q*(1-affinity q (twistDensity h) (flatDensity h)))=
      2*(1-affinity q (twistDensity h) (flatDensity h)) := by
    field_simp [ne_of_gt hq0]
  rw [hid] at hm
  change (1/q)*(Finset.univ.sum fun c : F => (localCorrection c h)^2)<=5/q^2 at hv
  change 1-affinity q (twistDensity h) (flatDensity h)<=5/q^2
  nlinarith only [hm,hv]

theorem raw_twist_affinity_upper (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 2048<=(Fintype.card F : Real)) :
    affinity (Fintype.card F : Real) (rawDensity h) (twistDensity h) <=
      1-1/(256*(Fintype.card F : Real)) := by
  let q : Real := Fintype.card F
  have h16 : 16<=(Fintype.card F : Real) := by linarith only [hq]
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have hr := raw_flat_affinity_upper hF h hh h16
  have ht := twist_flat_affinity_defect_upper hF h hh h16
  have hj := affinity_defect_triangle q (rawDensity h) (twistDensity h) (flatDensity h)
    (fun c => (raw_density_bounds hF h hh h16 c).1)
    (twist_density_nonneg h hh h16) (fun c => (flat_density_bounds h h16 c).1)
    hq0 (sum_raw_density hF h hh h16) (sum_twist_density hF h hh h16)
    (sum_flat_density h hh h16)
  have he : 1/(128*q)-5/q^2-1/(256*q)=(q-1280)/(256*q^2) := by
    field_simp [ne_of_gt hq0]
    <;> ring
  have hn : 0<=(q-1280)/(256*q^2) := by
    apply div_nonneg
    . dsimp only [q]
      linarith only [hq]
    . positivity
  have hhalf : (1/(64*q))/2=1/(128*q) := by
    field_simp [ne_of_gt hq0]
    <;> norm_num
  change affinity q (rawDensity h) (flatDensity h)<=1-1/(64*q) at hr
  change 1-affinity q (twistDensity h) (flatDensity h)<=5/q^2 at ht
  change affinity q (rawDensity h) (twistDensity h)<=1-1/(256*q)
  linarith only [hr,ht,hj,he,hn,hhalf]

end PrimeFactorOscillations.FiniteFieldTwistHellinger
