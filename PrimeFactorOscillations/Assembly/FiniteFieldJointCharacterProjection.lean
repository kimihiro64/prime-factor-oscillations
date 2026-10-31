/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldOptimalCharacterLaw
import PrimeFactorOscillations.Mathlib.Algebra.BigOperators.WeightedFiberProduct
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistJoint

/-!
# Exact optimal joint character approximation of the raw pair law

Every coupled statistic of the two quadratic signs in every field has the
same weighted mean under the raw law and its explicit product projection.
The exact Pythagorean identity and retained-energy Euler factor quantify
what arbitrary cross-field character couplings cannot reconstruct. The
measure is the complete finite product, not an incomplete integer window.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldJointCharacterProjection
attribute [local instance] Classical.propDecidable
open _root_.FiniteField _root_.FiniteField.QuadraticPairEuler
open _root_.FiniteField.QuadraticPairTwistJoint
open FiniteFieldCharacterProjection FiniteFieldOptimalCharacterLaw FiniteFieldRawHellinger
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def characterLabels (h : F) : Finset (Prod Int Int) :=
  Finset.univ.image (fun c : F =>
    Prod.mk ((quadraticChar F) c) ((quadraticChar F) (c+h)))

abbrev CharacterLabel (h : F) :=
  {s : Prod Int Int // Membership.mem (characterLabels h) s}

def characterLabel (h c : F) : CharacterLabel h :=
  Subtype.mk (Prod.mk ((quadraticChar F) c) ((quadraticChar F) (c+h)))
    (Finset.mem_image.mpr (Exists.intro c (And.intro (Finset.mem_univ c) rfl)))

theorem character_label_eq (h c : F) (l : CharacterLabel h) :
    characterLabel h c=l <->
      Prod.mk ((quadraticChar F) c) ((quadraticChar F) (c+h))=l.val := by
  exact Subtype.ext_iff

theorem raw_optimal_label_mass (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) (l : CharacterLabel h) :
    ((Finset.univ.filter fun c : F => characterLabel h c=l).sum (rawDensity h))=
      ((Finset.univ.filter fun c : F => characterLabel h c=l).sum (optimalDensity h)) := by
  have hs := raw_optimal_sign_statistics hF hm h hh hq
    (fun a b => if Prod.mk a b=l.val then (1 : Real) else 0)
  simpa only [Finset.sum_filter,character_label_eq,mul_ite,mul_one,mul_zero] using hs

def rawMoment (q : Real) : Real := (q^2+3)/(q*(q-3))
def visibleMoment (q : Real) : Real := (q^2-q+2)/(q*(q-3))
def retainedFraction (q : Real) : Real := (q^2-q+2)/(q^2+3)

theorem raw_second_moment_exact (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) :
    (1/(Fintype.card F : Real))*(Finset.univ.sum fun c : F => (rawDensity h c)^2)=
      rawMoment (Fintype.card F : Real) := by
  let q : Real := Fintype.card F
  have hneg : (quadraticChar F) (-h)=-(quadraticChar F) h := by
    have he : -h=(-1 : F)*h := by ring
    rw [he,map_mul,hm,neg_one_mul]
  have hoff : quadraticPairOffset h=3 := by
    unfold quadraticPairOffset
    rw [hneg]
    ring
  have ht := normalizedPairCount_second_moment_large hF h hh hq
  change (1/q)*(Finset.univ.sum fun c : F => (rawDensity h c)^2)=
    1+(3*q+(quadraticPairOffset h : Real))/(q*(q-(quadraticPairOffset h : Real))) at ht
  rw [hoff] at ht
  norm_num only [Int.cast_ofNat] at ht
  rw [ht]
  have hq0 : Not (q=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  have hd : Not (q-3=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  unfold rawMoment
  change 1+(3*q+3)/(q*(q-3))=(q^2+3)/(q*(q-3))
  field_simp [hq0,hd]
  ring

theorem optimal_second_moment_exact (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) :
    (1/(Fintype.card F : Real))*(Finset.univ.sum fun c : F => (optimalDensity h c)^2)=
      visibleMoment (Fintype.card F : Real) := by
  let q : Real := Fintype.card F
  have hp := raw_projection_pythagoras hF hm h hh hq (fun _ _ => (0 : Real))
  simp only [FiniteFieldPairAffinity.squareDistance,sub_zero] at hp
  rw [raw_second_moment_exact hF hm h hh hq] at hp
  have hq0 : Not (q=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  have hd : Not (q-3=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  have he : rawMoment q-(q+1)/(q*(q-3))=visibleMoment q := by
    unfold rawMoment visibleMoment
    field_simp [hq0,hd]
    ring
  change rawMoment q=(q+1)/(q*(q-3))+
    (1/q)*(Finset.univ.sum fun c : F => (optimalDensity h c)^2) at hp
  change (1/q)*(Finset.univ.sum fun c : F => (optimalDensity h c)^2)=visibleMoment q
  linarith only [hp,he]

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (K : I -> Type*) [forall i, Field (K i)] [forall i, Fintype (K i)]
variable [forall i, DecidableEq (K i)]

def jointTable (h : (i : I) -> K i) (g : ((i : I) -> CharacterLabel (h i)) -> Real)
    (x : (i : I) -> K i) : Real :=
  g (fun i => characterLabel (h i) (x i))

theorem raw_joint_character_statistics (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hm : forall i, (quadraticChar (K i)) (-1)=-1)
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real))
    (g : ((i : I) -> CharacterLabel (h i)) -> Real) :
    packetMean K (fun x => purePacket K (fun i => rawDensity (h i)) x*jointTable K h g x)=
      packetMean K (fun x => purePacket K (fun i => optimalDensity (h i)) x*jointTable K h g x) := by
  have hs := Fintype.sum_prod_mul_comp_eq_of_fiber_sums
    (fun i => characterLabel (h i))
    (fun i => rawDensity (h i)) (fun i => optimalDensity (h i))
    (fun i l => raw_optimal_label_mass (hodd i) (hm i) (h i) (hh i) (hq i) l) g
  unfold packetMean purePacket jointTable
  exact congrArg (fun z : Real =>
    (Finset.univ.prod fun i : I => 1/(Fintype.card (K i) : Real))*z) hs

theorem raw_joint_second_moment (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hm : forall i, (quadraticChar (K i)) (-1)=-1)
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real)) :
    packetMean K (fun x => (purePacket K (fun i => rawDensity (h i)) x)^2)=
      Finset.univ.prod (fun i => rawMoment (Fintype.card (K i) : Real)) := by
  calc
    _ = Finset.univ.prod (fun i =>
        (1/(Fintype.card (K i) : Real))*
          (Finset.univ.sum fun c : K i => (rawDensity (h i) c)^2)) := by
      simpa only [pow_two] using
        packetMean_pure_pairing K (fun i => rawDensity (h i)) (fun i => rawDensity (h i))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact raw_second_moment_exact (hodd i) (hm i) (h i) (hh i) (hq i)

theorem optimal_joint_second_moment (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hm : forall i, (quadraticChar (K i)) (-1)=-1)
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real)) :
    packetMean K (fun x => (purePacket K (fun i => optimalDensity (h i)) x)^2)=
      Finset.univ.prod (fun i => visibleMoment (Fintype.card (K i) : Real)) := by
  calc
    _ = Finset.univ.prod (fun i =>
        (1/(Fintype.card (K i) : Real))*
          (Finset.univ.sum fun c : K i => (optimalDensity (h i) c)^2)) := by
      simpa only [pow_two] using
        packetMean_pure_pairing K (fun i => optimalDensity (h i)) (fun i => optimalDensity (h i))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact optimal_second_moment_exact (hodd i) (hm i) (h i) (hh i) (hq i)

theorem joint_projection_pythagoras (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hm : forall i, (quadraticChar (K i)) (-1)=-1)
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real))
    (g : ((i : I) -> CharacterLabel (h i)) -> Real) :
    packetMean K (fun x =>
      (purePacket K (fun i => rawDensity (h i)) x-jointTable K h g x)^2)=
      (Finset.univ.prod fun i => rawMoment (Fintype.card (K i) : Real))-
        (Finset.univ.prod fun i => visibleMoment (Fintype.card (K i) : Real))+
      packetMean K (fun x =>
        (purePacket K (fun i => optimalDensity (h i)) x-jointTable K h g x)^2) := by
  have hs := raw_joint_character_statistics K h hodd hm hh hq g
  have hr := raw_joint_second_moment K h hodd hm hh hq
  have hv := optimal_joint_second_moment K h hodd hm hh hq
  have he (x : (i : I) -> K i) :
      (purePacket K (fun i => rawDensity (h i)) x-jointTable K h g x)^2=
      (purePacket K (fun i => rawDensity (h i)) x)^2-
        (purePacket K (fun i => optimalDensity (h i)) x)^2+
      (purePacket K (fun i => optimalDensity (h i)) x-jointTable K h g x)^2-
      2*(purePacket K (fun i => rawDensity (h i)) x*jointTable K h g x-
        purePacket K (fun i => optimalDensity (h i)) x*jointTable K h g x) := by ring
  simp_rw [he]
  unfold packetMean at *
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,<- Finset.mul_sum]
  nlinarith only [hs,hr,hv]

theorem joint_character_error_lower (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hm : forall i, (quadraticChar (K i)) (-1)=-1)
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real))
    (g : ((i : I) -> CharacterLabel (h i)) -> Real) :
    (Finset.univ.prod fun i => rawMoment (Fintype.card (K i) : Real))-
      (Finset.univ.prod fun i => visibleMoment (Fintype.card (K i) : Real)) <=
      packetMean K (fun x =>
        (purePacket K (fun i => rawDensity (h i)) x-jointTable K h g x)^2) := by
  rw [joint_projection_pythagoras K h hodd hm hh hq g]
  exact le_add_of_nonneg_right (packetMean_square_nonneg K _)


theorem raw_moment_pos (q : Real) (hq : 16<=q) : 0<rawMoment q := by
  unfold rawMoment
  exact div_pos (by nlinarith only [sq_nonneg q])
    (mul_pos (by linarith only [hq]) (by linarith only [hq]))

theorem moment_fraction_identity (q : Real) (hq : 16<=q) :
    visibleMoment q=retainedFraction q*rawMoment q := by
  have h0 : Not (q=0) := ne_of_gt (by linarith only [hq])
  have h3 : Not (q-3=0) := ne_of_gt (by linarith only [hq])
  have hs : Not (q^2+3=0) := ne_of_gt (by nlinarith only [sq_nonneg q])
  unfold visibleMoment retainedFraction rawMoment
  field_simp [h0,h3,hs]

theorem retained_fraction_bounds (q : Real) (hq : 16<=q) :
    0<retainedFraction q /\ retainedFraction q<=1-1/q := by
  have hq0 : 0<q := by linarith only [hq]
  have hs : 0<q^2+3 := by nlinarith only [sq_nonneg q]
  have hn : 0<q^2-q+2 := by nlinarith only [sq_nonneg (q-1)]
  have he : (1-1/q)-retainedFraction q=(q-3)/(q*(q^2+3)) := by
    unfold retainedFraction
    field_simp [ne_of_gt hq0,ne_of_gt hs]
    ring
  have hp : 0<=(q-3)/(q*(q^2+3)) :=
    div_nonneg (by linarith only [hq]) (mul_pos hq0 hs).le
  exact And.intro (div_pos hn hs) (by linarith only [he,hp])

theorem joint_relative_error_identity (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hm : forall i, (quadraticChar (K i)) (-1)=-1)
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real))
    (g : ((i : I) -> CharacterLabel (h i)) -> Real) :
    packetMean K (fun x =>
      (purePacket K (fun i => rawDensity (h i)) x-jointTable K h g x)^2)=
      (1-(Finset.univ.prod fun i => retainedFraction (Fintype.card (K i) : Real)))*
        (Finset.univ.prod fun i => rawMoment (Fintype.card (K i) : Real))+
      packetMean K (fun x =>
        (purePacket K (fun i => optimalDensity (h i)) x-jointTable K h g x)^2) := by
  have hv :
      (Finset.univ.prod fun i => visibleMoment (Fintype.card (K i) : Real))=
      (Finset.univ.prod fun i => retainedFraction (Fintype.card (K i) : Real))*
        (Finset.univ.prod fun i => rawMoment (Fintype.card (K i) : Real)) := by
    calc
      _ = Finset.univ.prod (fun i =>
          retainedFraction (Fintype.card (K i) : Real)*
            rawMoment (Fintype.card (K i) : Real)) := by
        apply Finset.prod_congr rfl
        intro i _
        exact moment_fraction_identity _ (hq i)
      _ = _ := Finset.prod_mul_distrib
  rw [joint_projection_pythagoras K h hodd hm hh hq g,hv]
  ring

theorem joint_relative_error_lower (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hm : forall i, (quadraticChar (K i)) (-1)=-1)
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real))
    (g : ((i : I) -> CharacterLabel (h i)) -> Real) :
    (1-(Finset.univ.prod fun i => retainedFraction (Fintype.card (K i) : Real)))*
      (Finset.univ.prod fun i => rawMoment (Fintype.card (K i) : Real)) <=
      packetMean K (fun x =>
        (purePacket K (fun i => rawDensity (h i)) x-jointTable K h g x)^2) := by
  rw [joint_relative_error_identity K h hodd hm hh hq g]
  exact le_add_of_nonneg_right (packetMean_square_nonneg K _)

def optimalJointTable (h : (i : I) -> K i) (l : (i : I) -> CharacterLabel (h i)) : Real :=
  Finset.univ.prod fun i => optimalTable (h i) (l i).val.1 (l i).val.2

omit [DecidableEq I] in
theorem optimal_joint_table_comp (h : (i : I) -> K i) (x : (i : I) -> K i) :
    jointTable K h (optimalJointTable K h) x=
      purePacket K (fun i => optimalDensity (h i)) x := by
  rfl

theorem joint_projection_error_exact (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hm : forall i, (quadraticChar (K i)) (-1)=-1)
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real)) :
    packetMean K (fun x =>
      (purePacket K (fun i => rawDensity (h i)) x-
        purePacket K (fun i => optimalDensity (h i)) x)^2)=
      (1-(Finset.univ.prod fun i => retainedFraction (Fintype.card (K i) : Real)))*
        (Finset.univ.prod fun i => rawMoment (Fintype.card (K i) : Real)) := by
  have he := joint_relative_error_identity K h hodd hm hh hq (optimalJointTable K h)
  simp_rw [optimal_joint_table_comp] at he
  have hz : packetMean K (fun x =>
      (purePacket K (fun i => optimalDensity (h i)) x-
        purePacket K (fun i => optimalDensity (h i)) x)^2)=0 := by
    simp [packetMean]
  rw [hz,add_zero] at he
  exact he

theorem raw_joint_energy_pos (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hm : forall i, (quadraticChar (K i)) (-1)=-1)
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real)) :
    0<packetMean K (fun x => (purePacket K (fun i => rawDensity (h i)) x)^2) := by
  rw [raw_joint_second_moment K h hodd hm hh hq]
  exact Finset.prod_pos (fun i _ => raw_moment_pos _ (hq i))

end PrimeFactorOscillations.FiniteFieldJointCharacterProjection
