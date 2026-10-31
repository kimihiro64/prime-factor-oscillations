/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Proof.PrimeClassDeletion.RepairHellinger

/-!
# Finite affinity bounds for normalized field-pair densities

Densities of total mass q are compared by normalized affinity and overlap.
A bounded pointwise sum converts a squared-density gap into an affinity
defect. The three-density estimate retains the full square-root cross term.
These lemmas concern finite probability laws, not integer pair supply.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace PrimeFactorOscillations.FiniteFieldPairAffinity
variable {I : Type*} [Fintype I]

def affinity (q : Real) (u v : I -> Real) : Real :=
  (1/q)*(Finset.univ.sum fun i => Real.sqrt (u i*v i))

def overlap (q : Real) (u v : I -> Real) : Real :=
  (1/q)*(Finset.univ.sum fun i => min (u i) (v i))

def squareDistance (q : Real) (u v : I -> Real) : Real :=
  (1/q)*(Finset.univ.sum fun i => (u i-v i)^2)

theorem affinity_nonneg (q : Real) (hq : 0<q) (u v : I -> Real) :
    0<=affinity q u v := by
  exact mul_nonneg (one_div_nonneg.mpr hq.le)
    (Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _))

theorem affinity_symm (q : Real) (u v : I -> Real) :
    affinity q u v=affinity q v u := by
  unfold affinity
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

theorem sqrt_energy_identity (q : Real) (u v : I -> Real)
    (hu : forall i, 0<=u i) (hv : forall i, 0<=v i) (hq : 0<q)
    (hsu : Finset.univ.sum u=q) (hsv : Finset.univ.sum v=q) :
    (Finset.univ.sum fun i => (Real.sqrt (u i)-Real.sqrt (v i))^2) =
      2*q*(1-affinity q u v) := by
  have hp (i : I) :
      (Real.sqrt (u i)-Real.sqrt (v i))^2 =
        u i+v i-2*Real.sqrt (u i*v i) := by
    rw [Real.sqrt_mul (hu i)]
    nlinarith only [Real.sq_sqrt (hu i),Real.sq_sqrt (hv i)]
  simp_rw [hp]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,<- Finset.mul_sum,hsu,hsv]
  unfold affinity
  field_simp [ne_of_gt hq]
  <;> ring

theorem affinity_le_one (q : Real) (u v : I -> Real)
    (hu : forall i, 0<=u i) (hv : forall i, 0<=v i) (hq : 0<q)
    (hsu : Finset.univ.sum u=q) (hsv : Finset.univ.sum v=q) :
    affinity q u v<=1 := by
  have he := sqrt_energy_identity q u v hu hv hq hsu hsv
  have hn : 0<=Finset.univ.sum (fun i => (Real.sqrt (u i)-Real.sqrt (v i))^2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hp : 0<2*q := by linarith only [hq]
  have hd : 0<=1-affinity q u v :=
    nonneg_of_mul_nonneg_left (by rw [mul_comm,<- he]; exact hn) hp
  linarith only [hd]

theorem scalar_square_gap_le (u v B : Real) (hu : 0<=u) (hv : 0<=v)
    (hB : u+v<=B) :
    (u-v)^2<=2*B*(Real.sqrt u-Real.sqrt v)^2 := by
  have hsu := Real.sq_sqrt hu
  have hsv := Real.sq_sqrt hv
  have hs : (Real.sqrt u+Real.sqrt v)^2<=2*B := by
    nlinarith only [hsu,hsv,sq_nonneg (Real.sqrt u-Real.sqrt v),hB]
  calc
    _ = ((Real.sqrt u)^2-(Real.sqrt v)^2)^2 := by rw [hsu,hsv]
    _ = (Real.sqrt u-Real.sqrt v)^2*(Real.sqrt u+Real.sqrt v)^2 := by ring
    _ <= (Real.sqrt u-Real.sqrt v)^2*(2*B) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by ring

theorem square_distance_le_affinity_defect (q B : Real) (u v : I -> Real)
    (hu : forall i, 0<=u i) (hv : forall i, 0<=v i) (hq : 0<q)
    (hsu : Finset.univ.sum u=q) (hsv : Finset.univ.sum v=q)
    (hB : forall i, u i+v i<=B) :
    squareDistance q u v<=4*B*(1-affinity q u v) := by
  have hs := Finset.sum_le_sum (fun i (_ : Membership.mem (Finset.univ : Finset I) i) =>
    scalar_square_gap_le (u i) (v i) B (hu i) (hv i) (hB i))
  rw [<- Finset.mul_sum,sqrt_energy_identity q u v hu hv hq hsu hsv] at hs
  unfold squareDistance
  calc
    _ <= (1/q)*(2*B*(2*q*(1-affinity q u v))) :=
      mul_le_mul_of_nonneg_left hs (one_div_nonneg.mpr hq.le)
    _ = _ := by field_simp [ne_of_gt hq] <;> ring

theorem affinity_defect_triangle (q : Real) (u v w : I -> Real)
    (hu : forall i, 0<=u i) (hv : forall i, 0<=v i) (hw : forall i, 0<=w i)
    (hq : 0<q) (hsu : Finset.univ.sum u=q)
    (hsv : Finset.univ.sum v=q) (hsw : Finset.univ.sum w=q) :
    (1-affinity q u w)/2-(1-affinity q v w)<=1-affinity q u v := by
  have hp (i : I) :
      (Real.sqrt (u i)-Real.sqrt (w i))^2 <=
        2*(Real.sqrt (u i)-Real.sqrt (v i))^2+
          2*(Real.sqrt (v i)-Real.sqrt (w i))^2 := by
    nlinarith only [sq_nonneg (Real.sqrt (u i)-2*Real.sqrt (v i)+Real.sqrt (w i))]
  have hs := Finset.sum_le_sum (fun i (_ : Membership.mem (Finset.univ : Finset I) i) =>
    hp i)
  rw [Finset.sum_add_distrib,<- Finset.mul_sum,<- Finset.mul_sum,
    sqrt_energy_identity q u w hu hw hq hsu hsw,
    sqrt_energy_identity q u v hu hv hq hsu hsv,
    sqrt_energy_identity q v w hv hw hq hsv hsw] at hs
  have he : 1-affinity q u w <=
      2*(1-affinity q u v)+2*(1-affinity q v w) := by
    by_contra hf
    have ht : 2*(1-affinity q u v)+2*(1-affinity q v w)<1-affinity q u w :=
      lt_of_not_ge hf
    have hpq : 0<2*q := by linarith only [hq]
    have hp : 0<(2*q)*((1-affinity q u w)-
        (2*(1-affinity q u v)+2*(1-affinity q v w))) :=
      mul_pos hpq (sub_pos.mpr ht)
    nlinarith only [hs,hp]
  linarith only [he]

theorem overlap_le_affinity (q : Real) (u v : I -> Real)
    (hu : forall i, 0<=u i) (hv : forall i, 0<=v i) (hq : 0<q) :
    overlap q u v<=affinity q u v := by
  have hp (i : I) : min (u i) (v i)<=Real.sqrt (u i*v i) := by
    have hr := Real.sqrt_nonneg (u i*v i)
    have hs := Real.sq_sqrt (mul_nonneg (hu i) (hv i))
    by_cases h : u i<=v i
    . rw [min_eq_left h]
      have ht := mul_le_mul_of_nonneg_left h (hu i)
      nlinarith only [ht,hr,hs,hu i]
    . have h' : v i<=u i := (lt_of_not_ge h).le
      rw [min_eq_right h']
      have ht := mul_le_mul_of_nonneg_right h' (hv i)
      nlinarith only [ht,hr,hs,hv i]
  unfold overlap affinity
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hp i))
    (one_div_nonneg.mpr hq.le)

end PrimeFactorOscillations.FiniteFieldPairAffinity
