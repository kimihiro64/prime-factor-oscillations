/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldRawPairCovariance
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairCompensatedKernel

/-!
# The fixed-gap compensated kernel and its centered persistence law

Both classes retain their original raw count densities and their distinct
normalizers. Unit pullback aligns their physical shifts. The universal
all-lag count kernel yields an exact shared-endpoint correlation coefficient
tending to one third, without Hasse or an integer short-window estimate.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldCompensatedKernel
attribute [local instance] Classical.propDecidable
open _root_.FiniteField FiniteFieldRawHellinger FiniteFieldRawPairCovariance
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def moment (h a : F) (f g : F -> Real) : Real :=
  let q : Real := Fintype.card F
  let D : F -> Real := fun b => q-(quadraticPairOffset b : Real)
  (1/q)*(Finset.univ.sum fun c : F => (D h)^2*f c+(D (a*h))^2*g c)/
    ((D h)^2+(D (a*h))^2)

def kernel (h a k : F) : Real :=
  moment h a (fun c => rawDensity h c*rawDensity h (c+k))
    (fun c => rawDensity (a*h) (a*c)*rawDensity (a*h) (a*(c+k)))

theorem kernel_eq_covariances (h k a : F) (ha : Not (a=0)) :
    let q : Real := Fintype.card F
    let D : F -> Real := fun b => q-(quadraticPairOffset b : Real)
    kernel h a k=((D h)^2*covariance h k+
      (D (a*h))^2*covariance (a*h) (a*k))/((D h)^2+(D (a*h))^2) := by
  let q : Real := Fintype.card F
  let D : F -> Real := fun b => q-(quadraticPairOffset b : Real)
  unfold kernel moment
  dsimp only
  change (1/q)*(Finset.univ.sum fun c : F =>
      (D h)^2*(rawDensity h c*rawDensity h (c+k))+
      (D (a*h))^2*(rawDensity (a*h) (a*c)*rawDensity (a*h) (a*(c+k))))/
      ((D h)^2+(D (a*h))^2)=_
  rw [Finset.sum_add_distrib,<- Finset.mul_sum,<- Finset.mul_sum]
  congr 1
  calc
    _=(D h)^2*((1/q)*(Finset.univ.sum fun c : F =>
        rawDensity h c*rawDensity h (c+k)))+
      (D (a*h))^2*((1/q)*(Finset.univ.sum fun c : F =>
        rawDensity (a*h) (a*c)*rawDensity (a*h) (a*(c+k)))) := by ring
    _=_ := by rw [covariance_dilation_pullback h k a ha]; rfl

theorem normalization_pair (h a : F) (hh : Not (h=0))
    (hchi : (quadraticChar F) a=-1) :
    let q : Real := Fintype.card F
    (q-(quadraticPairOffset h : Real))^2+
      (q-(quadraticPairOffset (a*h) : Real))^2=
      2*((q-3)^2+2*(1+((quadraticChar F) (-1) : Real))) := by
  dsimp only
  have he : (quadraticChar F) (a*h)=-(quadraticChar F) h := by
    rw [map_mul,hchi,neg_one_mul]
  have hf : (quadraticChar F) (-(a*h))=-(quadraticChar F) (-h) := by
    rw [show -(a*h)=a*(-h) from by ring,map_mul,hchi,neg_one_mul]
  have he2 : ((quadraticChar F) h : Real)^2=1 := by
    exact_mod_cast quadraticChar_sq_one hh
  have hf2 : ((quadraticChar F) (-h) : Real)^2=1 := by
    exact_mod_cast quadraticChar_sq_one (neg_ne_zero.mpr hh)
  have hep : (quadraticChar F) h*(quadraticChar F) (-h)=(quadraticChar F) (-1) := by
    rw [<- map_mul,show h*(-h)=(-1 : F)*h^2 from by ring,map_mul,map_pow,
      quadraticChar_sq_one hh,mul_one]
  have hepR : ((quadraticChar F) h : Real)*((quadraticChar F) (-h) : Real)=
      ((quadraticChar F) (-1) : Real) := by exact_mod_cast hep
  unfold quadraticPairOffset
  rw [he,hf]
  norm_num only [Int.cast_sub,Int.cast_neg,Int.cast_ofNat]
  nlinarith only [he2,hf2,hepR]

theorem kernel_eq_model (hF : Not (ringChar F=2)) (h k a : F)
    (hh : Not (h=0)) (hchi : (quadraticChar F) a=-1)
    (hq : 16<=(Fintype.card F : Real)) :
    kernel h a k=(twistCompensatedPairKernel h k : Real)/
      ((Fintype.card F : Real)*
        (((Fintype.card F : Real)-3)^2+2*(1+((quadraticChar F) (-1) : Real)))) := by
  let q : Real := Fintype.card F
  let R : Real := (q-3)^2+2*(1+((quadraticChar F) (-1) : Real))
  have hq0 : Not (q=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  have ha : Not (a=0) := by intro hz; subst a; norm_num at hchi
  have hah : Not (a*h=0) := mul_ne_zero ha hh
  have hn := normalization_pair h a hh hchi
  change (q-(quadraticPairOffset h : Real))^2+
      (q-(quadraticPairOffset (a*h) : Real))^2=2*R at hn
  have hR : 0<R := by
    have hp : 0<(q-(quadraticPairOffset h : Real))^2 :=
      sq_pos_of_pos (denominator_pos h hh hq)
    have hs := sq_nonneg (q-(quadraticPairOffset (a*h) : Real))
    nlinarith only [hn,hp,hs]
  have hw (b l : F) (hb : Not (b=0)) :
      (q-(quadraticPairOffset b : Real))^2*covariance b l=
      (16/q)*(Finset.univ.sum fun c : F =>
        (monicQuadraticPairCount c b : Real)*(monicQuadraticPairCount (c+l) b : Real)) := by
    have hd : Not (q-(quadraticPairOffset b : Real)=0) := ne_of_gt (denominator_pos b hb hq)
    rw [covariance_count_general hF b l hb hq]
    change (q-(quadraticPairOffset b : Real))^2*
      ((16*(Finset.univ.sum fun c : F =>
        (monicQuadraticPairCount c b : Real)*(monicQuadraticPairCount (c+l) b : Real)))/
        (q*(q-(quadraticPairOffset b : Real))^2))=_
    field_simp [hq0,hd]
  have hi :
      8*(Finset.univ.sum fun c : F =>
        (monicQuadraticPairCount c h : Real)*(monicQuadraticPairCount (c+k) h : Real)+
        (monicQuadraticPairCount c (a*h) : Real)*
          (monicQuadraticPairCount (c+a*k) (a*h) : Real))=
      (twistCompensatedPairKernel h k : Real) := by
    have hi := monicQuadraticPairCount_twist_compensated_correlation hF h k a hh hchi
    have hc := congrArg (fun z : Int => (z : Real)) hi
    push_cast at hc
    exact hc
  rw [Finset.sum_add_distrib] at hi
  rw [kernel_eq_covariances h k a ha]
  dsimp only
  change
    ((q-(quadraticPairOffset h : Real))^2*covariance h k+
      (q-(quadraticPairOffset (a*h) : Real))^2*covariance (a*h) (a*k))/
      ((q-(quadraticPairOffset h : Real))^2+
        (q-(quadraticPairOffset (a*h) : Real))^2)=_
  rw [hw h k hh,hw (a*h) (a*k) hah,hn]
  change _=(twistCompensatedPairKernel h k : Real)/(q*R)
  simp_rw [mul_comm a h,mul_comm a k] at hi
  simp_rw [mul_comm a h,mul_comm a k]
  field_simp [hq0,ne_of_gt hR]
  nlinarith only [hi]

theorem kernel_zero_eq_model (hF : Not (ringChar F=2)) (h a : F)
    (hh : Not (h=0)) (hchi : (quadraticChar F) a=-1)
    (hq : 16<=(Fintype.card F : Real)) :
    let q : Real := Fintype.card F
    let t : Real := (quadraticChar F) (-1)
    kernel h a 0=(q^3-3*q^2+(5+2*t)*q-11-2*t)/
      (q*((q-3)^2+2*(1+t))) := by
  dsimp only
  have hz := twistCompensatedPairKernel_zero h hh
  dsimp only at hz
  have hc := congrArg (fun z : Int => (z : Real)) hz
  push_cast at hc
  rw [kernel_eq_model hF h 0 a hh hchi hq,hc]

theorem kernel_adjacent (h a : F) (ha : Not (a=0)) :
    kernel h a h=twistCompensatedCovariance h a := by
  rw [kernel_eq_covariances h h a ha]
  rfl

def centeredPersistence (h a : F) : Real :=
  (kernel h a h-1)/(kernel h a 0-1)

theorem centeredPersistence_eq_model (hF : Not (ringChar F=2)) (h a : F)
    (hh : Not (h=0)) (hchi : (quadraticChar F) a=-1)
    (hq : 16<=(Fintype.card F : Real)) :
    centeredPersistence h a=compensatedQuadraticPairPersistence (Fintype.card F : Real)
      ((quadraticChar F) (-1) : Real) ((quadraticChar F) (2 : F) : Real) := by
  let q : Real := Fintype.card F
  let t : Real := (quadraticChar F) (-1)
  let u : Real := (quadraticChar F) (2 : F)
  let R : Real := (q-3)^2+2*(1+t)
  have ha : Not (a=0) := by intro hz; subst a; norm_num at hchi
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have ht2 : t^2=1 := by
    dsimp only [t]
    exact_mod_cast quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero : Not ((-1 : F)=0))
  have htlow : -1<=t := by nlinarith only [ht2,sq_nonneg (t-1)]
  have hR : 0<R := by
    have hl : (q-3)^2<=R := by dsimp only [R]; linarith only [htlow]
    exact lt_of_lt_of_le (sq_pos_of_pos (by dsimp only [q]; linarith only [hq])) hl
  have hB : 0<3*q^2-6*q-11-2*t :=
    compensatedQuadraticPairPersistence_denominator_pos q t hq
      (by nlinarith only [ht2,sq_nonneg (t+1)])
  unfold centeredPersistence
  rw [kernel_zero_eq_model hF h a hh hchi hq,kernel_adjacent h a ha,
    twistCompensatedCovariance_eq_model hF h a hh hchi hq]
  unfold compensatedQuadraticPairCrossMoment compensatedQuadraticPairPersistence
  change
    ((q^3-5*q^2+(5-4*u)*q-11-2*t)/(q*R)-1)/
      ((q^3-3*q^2+(5+2*t)*q-11-2*t)/(q*R)-1)=
      (q^2-(6+4*u+2*t)*q-11-2*t)/(3*q^2-6*q-11-2*t)
  have hd : Not ((q^3-3*q^2+(5+2*t)*q-11-2*t)/(q*R)-1=0) := by
    have he : (q^3-3*q^2+(5+2*t)*q-11-2*t)/(q*R)-1=
        (3*q^2-6*q-11-2*t)/(q*R) := by
      field_simp [ne_of_gt hq0,ne_of_gt hR]
      dsimp only [R]
      ring
    rw [he]
    exact ne_of_gt (div_pos hB (mul_pos hq0 hR))
  field_simp [ne_of_gt hq0,ne_of_gt hR,ne_of_gt hB,hd]
  dsimp only [R]
  ring

theorem centeredPersistence_law (hF : Not (ringChar F=2)) (h a : F)
    (hh : Not (h=0)) (hchi : (quadraticChar F) a=-1)
    (hq : 16<=(Fintype.card F : Real)) :
    And (And (0<centeredPersistence h a) (centeredPersistence h a<1/2))
      (abs (centeredPersistence h a-1/3)<=5/(Fintype.card F : Real)) := by
  rw [centeredPersistence_eq_model hF h a hh hchi hq]
  have hb (x : F) (hx : Not (x=0)) :
      And (-1<=((quadraticChar F) x : Real)) (((quadraticChar F) x : Real)<=1) := by
    have hs : ((quadraticChar F) x : Real)^2=1 := by
      exact_mod_cast quadraticChar_sq_one hx
    constructor <;> nlinarith only [hs,sq_nonneg (((quadraticChar F) x : Real)-1),
      sq_nonneg (((quadraticChar F) x : Real)+1)]
  have ht := hb (-1) (neg_ne_zero.mpr one_ne_zero)
  have hu := hb (2 : F) (two_ne_zero_of_odd hF)
  exact And.intro
    (compensatedQuadraticPairPersistence_bounds _ _ _ hq ht hu)
    (compensatedQuadraticPairPersistence_error _ _ _ hq ht hu)

theorem kernel_shifted (h a x y : F) :
    moment h a (fun c => rawDensity h (c+x)*rawDensity h (c+y))
      (fun c => rawDensity (a*h) (a*(c+x))*rawDensity (a*h) (a*(c+y)))=
      kernel h a (y-x) := by
  let q : Real := Fintype.card F
  let D : F -> Real := fun b => q-(quadraticPairOffset b : Real)
  let e : Equiv F F :=
    { toFun := fun c => c+x
      invFun := fun c => c-x
      left_inv := by intro c; ring
      right_inv := by intro c; ring }
  have he := Equiv.sum_comp e (fun c : F =>
    (D h)^2*(rawDensity h c*rawDensity h (c+(y-x)))+
    (D (a*h))^2*(rawDensity (a*h) (a*c)*rawDensity (a*h) (a*(c+(y-x)))))
  change (Finset.univ.sum fun c : F =>
    (D h)^2*(rawDensity h (c+x)*rawDensity h (c+x+(y-x)))+
    (D (a*h))^2*(rawDensity (a*h) (a*(c+x))*
      rawDensity (a*h) (a*(c+x+(y-x)))))=_ at he
  have hi (c : F) : c+x+(y-x)=c+y := by ring
  simp_rw [hi] at he
  exact congrArg (fun z : Real =>
    (1/q)*z/((D h)^2+(D (a*h))^2)) he

theorem signed_window_kernel {J : Type*} [Fintype J]
    (h a : F) (b : J -> Real) (s : J -> F) :
    moment h a
      (fun c => (Finset.univ.sum fun j : J => b j*rawDensity h (c+s j))^2)
      (fun c => (Finset.univ.sum fun j : J =>
        b j*rawDensity (a*h) (a*(c+s j)))^2)=
      Finset.univ.sum (fun j : J => Finset.univ.sum fun l : J =>
        (b j*b l)*kernel h a (s l-s j)) := by
  let q : Real := Fintype.card F
  let D : F -> Real := fun v => q-(quadraticPairOffset v : Real)
  have hsum (f g : J -> F -> Real) :
      moment h a (fun c => Finset.univ.sum fun j : J => f j c)
        (fun c => Finset.univ.sum fun j : J => g j c)=
      Finset.univ.sum (fun j : J => moment h a (f j) (g j)) := by
    have hf : (Finset.univ.sum fun c : F => Finset.univ.sum fun j : J => f j c)=
        Finset.univ.sum (fun j : J => Finset.univ.sum fun c : F => f j c) :=
      Finset.sum_comm
    have hg : (Finset.univ.sum fun c : F => Finset.univ.sum fun j : J => g j c)=
        Finset.univ.sum (fun j : J => Finset.univ.sum fun c : F => g j c) :=
      Finset.sum_comm
    unfold moment
    dsimp only
    simp_rw [Finset.sum_add_distrib,<- Finset.mul_sum]
    rw [hf,hg]
    simp only [Finset.mul_sum,Finset.sum_div,mul_add,add_div,Finset.sum_add_distrib]
  have hmul (d : Real) (f g : F -> Real) :
      moment h a (fun c => d*f c) (fun c => d*g c)=d*moment h a f g := by
    have hp (c : F) :
        (D h)^2*(d*f c)+(D (a*h))^2*(d*g c)=
        d*((D h)^2*f c+(D (a*h))^2*g c) := by ring
    unfold moment
    change (1/q)*(Finset.univ.sum fun c : F =>
      (D h)^2*(d*f c)+(D (a*h))^2*(d*g c))/((D h)^2+(D (a*h))^2)=_
    simp_rw [hp]
    rw [<- Finset.mul_sum]
    change (1/q)*(d*(Finset.univ.sum fun c : F =>
      (D h)^2*f c+(D (a*h))^2*g c))/((D h)^2+(D (a*h))^2)=
      d*((1/q)*(Finset.univ.sum fun c : F =>
        (D h)^2*f c+(D (a*h))^2*g c)/((D h)^2+(D (a*h))^2))
    ring
  have hp (v : F -> Real) (c : F) :
      (Finset.univ.sum fun j : J => b j*v (c+s j))^2=
      Finset.univ.sum (fun j : J => Finset.univ.sum fun l : J =>
        (b j*b l)*(v (c+s j)*v (c+s l))) := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [hp (rawDensity h),hp (fun x : F => rawDensity (a*h) (a*x)),
    hsum,hmul,kernel_shifted]

end PrimeFactorOscillations.FiniteFieldCompensatedKernel
