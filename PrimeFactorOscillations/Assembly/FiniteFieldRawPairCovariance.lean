/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldJointCharacterProjection
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairCovariance

/-!
# Full raw pair cross moments and signed window kernels

The covariance function is the uncentered cross moment of the original
normalized count law. Its shared-endpoint value follows from the full
integer covariance identity. Arbitrary signed windows retain every mixed
term over complete products; no incomplete integer mass bound is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldRawPairCovariance
attribute [local instance] Classical.propDecidable
open _root_.FiniteField _root_.FiniteField.QuadraticPairTwistJoint
open FiniteFieldRawHellinger FiniteFieldJointCharacterProjection
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def covariance (h k : F) : Real :=
  (1/(Fintype.card F : Real))*(Finset.univ.sum fun c : F =>
    rawDensity h c*rawDensity h (c+k))

theorem covariance_count (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h k : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) :
    covariance h k=
      (16*(Finset.univ.sum fun c : F =>
        (monicQuadraticPairCount c h : Real)*(monicQuadraticPairCount (c+k) h : Real)))/
      ((Fintype.card F : Real)*((Fintype.card F : Real)-3)^2) := by
  let q : Real := Fintype.card F
  have hq0 : Not (q=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  have hd : Not (q-3=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  have hn : (quadraticChar F) (-h)=-(quadraticChar F) h := by
    rw [show -h=(-1 : F)*h from by ring,map_mul,hm,neg_one_mul]
  have hoff : quadraticPairOffset h=3 := by
    unfold quadraticPairOffset
    rw [hn]
    ring
  have hp (c : F) :
      rawDensity h c*rawDensity h (c+k)=
        (16/(q-3)^2)*
          ((monicQuadraticPairCount c h : Real)*(monicQuadraticPairCount (c+k) h : Real)) := by
    rw [raw_density_quotient hF h hh hq c,raw_density_quotient hF h hh hq (c+k),hoff]
    norm_num only [Int.cast_ofNat]
    change (4*(monicQuadraticPairCount c h : Real)/(q-3))*
      (4*(monicQuadraticPairCount (c+k) h : Real)/(q-3))=_
    field_simp [hd]
    ring
  unfold covariance
  simp_rw [hp]
  rw [<- Finset.mul_sum]
  change (1/q)*((16/(q-3)^2)*
    (Finset.univ.sum fun c : F =>
      (monicQuadraticPairCount c h : Real)*(monicQuadraticPairCount (c+k) h : Real)))=
    (16*(Finset.univ.sum fun c : F =>
      (monicQuadraticPairCount c h : Real)*(monicQuadraticPairCount (c+k) h : Real)))/
      (q*(q-3)^2)
  field_simp [hq0,hd]

theorem covariance_adjacent (hF : Not (ringChar F=2))
    (hm : (quadraticChar F) (-1)=-1) (h : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) :
    covariance h h=
      ((Fintype.card F : Real)^3-5*(Fintype.card F : Real)^2+
        (5-4*((quadraticChar F) (2 : F) : Real))*(Fintype.card F : Real)-9)/
      ((Fintype.card F : Real)*((Fintype.card F : Real)-3)^2) := by
  have hi :
      16*(Finset.univ.sum fun c : F =>
        (monicQuadraticPairCount c h : Real)*(monicQuadraticPairCount (c+h) h : Real))=
      (Fintype.card F : Real)^3-5*(Fintype.card F : Real)^2+
        (5-4*((quadraticChar F) (2 : F) : Real))*(Fintype.card F : Real)-9 := by
    exact_mod_cast monicQuadraticPairCount_adjacent_correlation hF hm h hh
  rw [covariance_count hF hm h h hh hq,hi]

omit [DecidableEq F] in
theorem covariance_shifted (h a b : F) :
    (1/(Fintype.card F : Real))*(Finset.univ.sum fun c : F =>
      rawDensity h (c+a)*rawDensity h (c+b))=covariance h (b-a) := by
  let e : Equiv F F :=
    { toFun := fun c => c+a
      invFun := fun c => c-a
      left_inv := by intro c; ring
      right_inv := by intro c; ring }
  have he := Equiv.sum_comp e (fun c : F =>
    rawDensity h c*rawDensity h (c+(b-a)))
  have hp (c : F) : e c+(b-a)=c+b := by change c+a+(b-a)=c+b; ring
  simp_rw [hp] at he
  exact congrArg (fun x : Real => (1/(Fintype.card F : Real))*x) he

section Products
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (K : I -> Type*) [forall i, Field (K i)] [forall i, Fintype (K i)]
  [forall i, DecidableEq (K i)]

def shiftedPacket (h s x : (i : I) -> K i) : Real :=
  purePacket K (fun i c => rawDensity (h i) (c+s i)) x

theorem packet_cross_moment (h a b : (i : I) -> K i) :
    packetMean K (fun x => shiftedPacket K h a x*shiftedPacket K h b x)=
      Finset.univ.prod (fun i => covariance (h i) (b i-a i)) := by
  unfold shiftedPacket
  rw [packetMean_pure_pairing]
  apply Finset.prod_congr rfl
  intro i _
  exact covariance_shifted (h i) (a i) (b i)

theorem signed_window_second_moment {J : Type*} [Fintype J]
    (h : (i : I) -> K i) (a : J -> Real) (s : J -> (i : I) -> K i) :
    packetMean K (fun x => (Finset.univ.sum fun j : J => a j*shiftedPacket K h (s j) x)^2)=
      Finset.univ.sum (fun j : J => Finset.univ.sum fun l : J =>
        (a j*a l)*(Finset.univ.prod fun i => covariance (h i) (s l i-s j i))) := by
  have hsum (f : J -> ((i : I) -> K i) -> Real) :
      packetMean K (fun x => Finset.univ.sum fun j : J => f j x)=
        Finset.univ.sum (fun j : J => packetMean K (f j)) := by
    unfold packetMean
    rw [Finset.sum_comm,Finset.mul_sum]
  have hmul (d : Real) (f : ((i : I) -> K i) -> Real) :
      packetMean K (fun x => d*f x)=d*packetMean K f := by
    unfold packetMean
    rw [<- Finset.mul_sum]
    ring
  have hp (x : (i : I) -> K i) :
      (Finset.univ.sum fun j : J => a j*shiftedPacket K h (s j) x)^2=
        Finset.univ.sum (fun j : J => Finset.univ.sum fun l : J =>
          (a j*a l)*(shiftedPacket K h (s j) x*shiftedPacket K h (s l) x)) := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [hp,hsum,hmul,packet_cross_moment]

end Products
end PrimeFactorOscillations.FiniteFieldRawPairCovariance
