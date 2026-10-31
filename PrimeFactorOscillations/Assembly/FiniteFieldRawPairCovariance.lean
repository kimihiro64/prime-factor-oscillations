/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldJointCharacterProjection
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairGeneralCovariance

/-!
# Full raw pair cross moments and signed window kernels

The covariance function is the uncentered cross moment of the original
normalized count law. Its shared-endpoint value follows from the full
integer covariance identity. Nonsquare-gap compensation has an exact
all-character normalized model, positive correlation and uniform 12/q^2
error for q>=16. Signed windows retain every mixed term over complete
products; no incomplete integer mass bound is assumed.
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
theorem covariance_count_general (hF : Not (ringChar F=2))
    (h k : F) (hh : Not (h=0)) (hq : 16<=(Fintype.card F : Real)) :
    covariance h k=
      (16*(Finset.univ.sum fun c : F =>
        (monicQuadraticPairCount c h : Real)*(monicQuadraticPairCount (c+k) h : Real)))/
      ((Fintype.card F : Real)*
        ((Fintype.card F : Real)-(quadraticPairOffset h : Real))^2) := by
  let q : Real := Fintype.card F
  let d : Real := quadraticPairOffset h
  have hq0 : Not (q=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  have hd : Not (q-d=0) := ne_of_gt (denominator_pos h hh hq)
  have hp (c : F) :
      rawDensity h c*rawDensity h (c+k)=
        (16/(q-d)^2)*
          ((monicQuadraticPairCount c h : Real)*(monicQuadraticPairCount (c+k) h : Real)) := by
    rw [raw_density_quotient hF h hh hq c,raw_density_quotient hF h hh hq (c+k)]
    change (4*(monicQuadraticPairCount c h : Real)/(q-d))*
      (4*(monicQuadraticPairCount (c+k) h : Real)/(q-d))=_
    field_simp [hd]
    ring
  unfold covariance
  simp_rw [hp]
  rw [<- Finset.mul_sum]
  change (1/q)*((16/(q-d)^2)*
    (Finset.univ.sum fun c : F =>
      (monicQuadraticPairCount c h : Real)*(monicQuadraticPairCount (c+k) h : Real)))=
    (16*(Finset.univ.sum fun c : F =>
      (monicQuadraticPairCount c h : Real)*(monicQuadraticPairCount (c+k) h : Real)))/
      (q*(q-d)^2)
  field_simp [hq0,hd]

def twistCompensatedCovariance (h a : F) : Real :=
  let q : Real := Fintype.card F
  let D : F -> Real := fun b => q-(quadraticPairOffset b : Real)
  ((D h)^2*covariance h h+(D (a*h))^2*covariance (a*h) (a*h))/
    ((D h)^2+(D (a*h))^2)

theorem twistCompensatedCovariance_eq_model
    (hF : Not (ringChar F=2)) (h a : F) (hh : Not (h=0))
    (ha : (quadraticChar F) a=-1) (hq : 16<=(Fintype.card F : Real)) :
    twistCompensatedCovariance h a=
      compensatedQuadraticPairCrossMoment (Fintype.card F : Real)
        ((quadraticChar F) (-1) : Real) ((quadraticChar F) (2 : F) : Real) := by
  let q : Real := Fintype.card F
  let D : Real := (q-3)^2+2*(1+((quadraticChar F) (-1) : Real))
  have hq0 : Not (q=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  have ha0 : Not (a=0) := by
    intro hz
    subst a
    norm_num at ha
  have hah : Not (a*h=0) := mul_ne_zero ha0 hh
  have he : (quadraticChar F) (a*h)=-(quadraticChar F) h := by
    rw [map_mul,ha,neg_one_mul]
  have hf : (quadraticChar F) (-(a*h))=-(quadraticChar F) (-h) := by
    rw [show -(a*h)=a*(-h) from by ring,map_mul,ha,neg_one_mul]
  have he2 : ((quadraticChar F) h : Real)^2=1 := by
    exact_mod_cast quadraticChar_sq_one hh
  have hf2 : ((quadraticChar F) (-h) : Real)^2=1 := by
    exact_mod_cast quadraticChar_sq_one (neg_ne_zero.mpr hh)
  have hep : (quadraticChar F) h*(quadraticChar F) (-h)=(quadraticChar F) (-1) := by
    rw [<- map_mul,show h*(-h)=(-1 : F)*h^2 from by ring,map_mul,map_pow,
      quadraticChar_sq_one hh,mul_one]
  have hepR :
      ((quadraticChar F) h : Real)*((quadraticChar F) (-h) : Real)=
        ((quadraticChar F) (-1) : Real) := by exact_mod_cast hep
  have hsq :
      (((quadraticChar F) h : Real)+((quadraticChar F) (-h) : Real))^2=
        2*(1+((quadraticChar F) (-1) : Real)) := by
    nlinarith only [he2,hf2,hepR]
  have hnorm :
      (q-(quadraticPairOffset h : Real))^2+
        (q-(quadraticPairOffset (a*h) : Real))^2=2*D := by
    unfold quadraticPairOffset
    rw [he,hf]
    norm_num only [Int.cast_sub,Int.cast_neg,Int.cast_ofNat]
    dsimp only [D]
    nlinarith only [hsq]
  have hd : 0<D := by
    have hl : 0<(q-(quadraticPairOffset h : Real))^2 :=
      sq_pos_of_pos (denominator_pos h hh hq)
    have hr : 0<=(q-(quadraticPairOffset (a*h) : Real))^2 := sq_nonneg _
    nlinarith only [hnorm,hl,hr]
  have hw (b : F) (hb : Not (b=0)) :
      (q-(quadraticPairOffset b : Real))^2*covariance b b=
        (16/q)*(Finset.univ.sum fun c : F =>
          (monicQuadraticPairCount c b : Real)*(monicQuadraticPairCount (c+b) b : Real)) := by
    have hd0 : Not (q-(quadraticPairOffset b : Real)=0) :=
      ne_of_gt (denominator_pos b hb hq)
    rw [covariance_count_general hF b b hb hq]
    change (q-(quadraticPairOffset b : Real))^2*
      ((16*(Finset.univ.sum fun c : F =>
        (monicQuadraticPairCount c b : Real)*(monicQuadraticPairCount (c+b) b : Real)))/
          (q*(q-(quadraticPairOffset b : Real))^2))=_
    field_simp [hq0,hd0]
  have hi :
      8*(Finset.univ.sum fun c : F =>
        (monicQuadraticPairCount c h : Real)*(monicQuadraticPairCount (c+h) h : Real)+
        (monicQuadraticPairCount c (a*h) : Real)*
          (monicQuadraticPairCount (c+a*h) (a*h) : Real))=
      q^3-5*q^2+(5-4*((quadraticChar F) (2 : F) : Real))*q-11-
        2*((quadraticChar F) (-1) : Real) := by
    have hint := monicQuadraticPairCount_twist_compensated_adjacent hF h a hh ha
    dsimp only at hint
    have hcast := congrArg (fun z : Int => (z : Real)) hint
    push_cast at hcast
    exact hcast
  rw [Finset.sum_add_distrib] at hi
  unfold twistCompensatedCovariance
  dsimp only
  change
    ((q-(quadraticPairOffset h : Real))^2*covariance h h+
      (q-(quadraticPairOffset (a*h) : Real))^2*covariance (a*h) (a*h))/
    ((q-(quadraticPairOffset h : Real))^2+
      (q-(quadraticPairOffset (a*h) : Real))^2)=_
  rw [hw h hh,hw (a*h) hah,hnorm]
  unfold compensatedQuadraticPairCrossMoment
  change
    ((16/q)*(Finset.univ.sum fun c : F =>
      (monicQuadraticPairCount c h : Real)*(monicQuadraticPairCount (c+h) h : Real))+
    (16/q)*(Finset.univ.sum fun c : F =>
      (monicQuadraticPairCount c (a*h) : Real)*
        (monicQuadraticPairCount (c+a*h) (a*h) : Real)))/(2*D)=
    (q^3-5*q^2+(5-4*((quadraticChar F) (2 : F) : Real))*q-11-
      2*((quadraticChar F) (-1) : Real))/(q*D)
  simp_rw [mul_comm a h] at hi
  simp_rw [mul_comm a h]
  field_simp [hq0,ne_of_gt hd]
  nlinarith only [hi]

theorem twistCompensatedCovariance_gt_one
    (hF : Not (ringChar F=2)) (h a : F) (hh : Not (h=0))
    (ha : (quadraticChar F) a=-1) (hq : 16<=(Fintype.card F : Real)) :
    1<twistCompensatedCovariance h a := by
  rw [twistCompensatedCovariance_eq_model hF h a hh ha hq]
  have ht : ((quadraticChar F) (-1) : Real)^2=1 := by
    exact_mod_cast quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero : Not ((-1 : F)=0))
  have hu : ((quadraticChar F) (2 : F) : Real)^2=1 := by
    exact_mod_cast quadraticChar_sq_one (two_ne_zero_of_odd hF)
  have hb (v : Real) (hv : v^2=1) : And (-1<=v) (v<=1) := by
    constructor <;> nlinarith only [hv,sq_nonneg (v-1),sq_nonneg (v+1)]
  exact compensatedQuadraticPairCrossMoment_gt_one _ _ _ hq (hb _ ht) (hb _ hu)

theorem twistCompensatedCovariance_error
    (hF : Not (ringChar F=2)) (h a : F) (hh : Not (h=0))
    (ha : (quadraticChar F) a=-1) (hq : 16<=(Fintype.card F : Real)) :
    abs (twistCompensatedCovariance h a-(1+1/(Fintype.card F : Real)))<=
      12/(Fintype.card F : Real)^2 := by
  rw [twistCompensatedCovariance_eq_model hF h a hh ha hq]
  have ht : ((quadraticChar F) (-1) : Real)^2=1 := by
    exact_mod_cast quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero : Not ((-1 : F)=0))
  have hu : ((quadraticChar F) (2 : F) : Real)^2=1 := by
    exact_mod_cast quadraticChar_sq_one (two_ne_zero_of_odd hF)
  have hb (v : Real) (hv : v^2=1) : And (-1<=v) (v<=1) := by
    constructor <;> nlinarith only [hv,sq_nonneg (v-1),sq_nonneg (v+1)]
  exact compensatedQuadraticPairCrossMoment_error _ _ _ hq (hb _ ht) (hb _ hu)

omit [DecidableEq F] in
theorem covariance_dilation_pullback (h k a : F) (ha : Not (a=0)) :
    (1/(Fintype.card F : Real))*(Finset.univ.sum fun c : F =>
      rawDensity (a*h) (a*c)*rawDensity (a*h) (a*(c+k)))=
      covariance (a*h) (a*k) := by
  let e : Equiv F F :=
    { toFun := fun c => a*c
      invFun := fun c => c/a
      left_inv := by intro c; field_simp [ha]
      right_inv := by intro c; field_simp [ha] }
  unfold covariance
  congr 1
  simp_rw [mul_add]
  exact Equiv.sum_comp e (fun c : F =>
    rawDensity (a*h) c*rawDensity (a*h) (c+a*k))

theorem twistCompensatedCovariance_same_gap (h a : F) (ha : Not (a=0)) :
    let q : Real := Fintype.card F
    let D : F -> Real := fun b => q-(quadraticPairOffset b : Real)
    (1/q)*(Finset.univ.sum fun c : F =>
      (D h)^2*(rawDensity h c*rawDensity h (c+h))+
      (D (a*h))^2*(rawDensity (a*h) (a*c)*rawDensity (a*h) (a*(c+h))))/
      ((D h)^2+(D (a*h))^2)=twistCompensatedCovariance h a := by
  let q : Real := Fintype.card F
  let D : F -> Real := fun b => q-(quadraticPairOffset b : Real)
  change (1/q)*(Finset.univ.sum fun c : F =>
      (D h)^2*(rawDensity h c*rawDensity h (c+h))+
      (D (a*h))^2*(rawDensity (a*h) (a*c)*rawDensity (a*h) (a*(c+h))))/
      ((D h)^2+(D (a*h))^2)=twistCompensatedCovariance h a
  rw [Finset.sum_add_distrib,<- Finset.mul_sum,<- Finset.mul_sum]
  unfold twistCompensatedCovariance
  change (1/q)*((D h)^2*(Finset.univ.sum fun c : F =>
        rawDensity h c*rawDensity h (c+h))+
      (D (a*h))^2*(Finset.univ.sum fun c : F =>
        rawDensity (a*h) (a*c)*rawDensity (a*h) (a*(c+h))))/
      ((D h)^2+(D (a*h))^2)=
    ((D h)^2*covariance h h+(D (a*h))^2*covariance (a*h) (a*h))/
      ((D h)^2+(D (a*h))^2)
  congr 1
  calc
    _=(D h)^2*((1/q)*(Finset.univ.sum fun c : F =>
        rawDensity h c*rawDensity h (c+h)))+
      (D (a*h))^2*((1/q)*(Finset.univ.sum fun c : F =>
        rawDensity (a*h) (a*c)*rawDensity (a*h) (a*(c+h)))) := by ring
    _=_ := by
      rw [covariance_dilation_pullback h h a ha]
      rfl

omit [Fintype F] [DecidableEq F] in
theorem dilation_pair_avoidance_iff (h a c : F) (ha : Not (a=0)) :
    And (Not (a*c=0)) (Not (a*(c+h)=0)) <->
      And (Not (c=0)) (Not (c+h=0)) := by
  constructor
  . intro hp
    constructor
    . intro hz
      apply hp.1
      rw [hz,mul_zero]
    . intro hz
      apply hp.2
      rw [hz,mul_zero]
  . intro hp
    exact And.intro (mul_ne_zero ha hp.1) (mul_ne_zero ha hp.2)

end PrimeFactorOscillations.FiniteFieldRawPairCovariance
