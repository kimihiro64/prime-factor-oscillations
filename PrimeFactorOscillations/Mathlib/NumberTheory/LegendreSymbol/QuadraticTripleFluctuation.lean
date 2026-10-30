/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticTripleWave
/-!
# Signed fluctuation laws for common-scale quadratic triples

A rational parameterization retains every admissible shape pair and its
quadratic-character phase. Exact fibre counts keep both signs and all three
excluded roots. The full actual-count distribution consumer is developed here;
no new integer-prime or RH estimate is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticTripleTwist
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def fibrePhase (z y : F) : Int :=
  (quadraticChar F) (y*(y+1)*(y+(z+1)))

def fibreValue (z : F) (f : Int -> Int) (y : F) : Int :=
  if admissible (1 : F) (z+1) y
    then f (fibrePhase z y * splitCubicPointTrace z (z+1)) else 0

theorem sum_fibrePhase (hF : Not (ringChar F = 2)) (z : F) :
    (Finset.univ.sum fun y : F => fibrePhase z y) =
      -splitCubicPointTrace z (z+1) := by
  let e : Equiv F F :=
    { toFun := fun y => y+(z+1)
      invFun := fun x => x-(z+1)
      left_inv := by intro y; ring
      right_inv := by intro y; ring }
  let g : F -> Int := fun x =>
    (quadraticChar F) (x*(x-z)*(x-(z+1)))
  calc
    _ = Finset.univ.sum (fun y : F => g (e y)) := by
      apply Finset.sum_congr rfl
      intro y _
      unfold fibrePhase g
      congr 1
      change y*(y+1)*(y+(z+1)) =
        (y+(z+1))*((y+(z+1))-z)*((y+(z+1))-(z+1))
      ring
    _ = Finset.univ.sum g := Equiv.sum_comp e g
    _ = _ := by
      rw [splitCubicPointTrace_eq hF]
      simp only [g,neg_neg]

theorem fibrePhase_zero (z y : F) (hy : Not (admissible (1 : F) (z+1) y)) :
    fibrePhase z y = 0 := by
  by_cases hy0 : y=0
  . simp [fibrePhase,hy0]
  . by_cases hy1 : y+1=0
    . simp [fibrePhase,hy1]
    . by_cases hyz : y+(z+1)=0
      . simp [fibrePhase,hyz]
      . exact False.elim (hy (And.intro hy0 (And.intro hy1 hyz)))

theorem twice_fibreValue (z : F) (f : Int -> Int) (y : F) :
    2*fibreValue z f y =
      (admissibleWeight (1 : F) (z+1) y+fibrePhase z y) *
        f (splitCubicPointTrace z (z+1)) +
      (admissibleWeight (1 : F) (z+1) y-fibrePhase z y) *
        f (-splitCubicPointTrace z (z+1)) := by
  by_cases hy : admissible (1 : F) (z+1) y
  . have hq : (fibrePhase z y)^2=1 :=
      quadraticChar_sq_one
        (mul_ne_zero (mul_ne_zero hy.1 hy.2.1) hy.2.2)
    have hp : (fibrePhase z y-1)*(fibrePhase z y+1)=0 := by nlinarith only [hq]
    rcases mul_eq_zero.mp hp with hp | hm
    . have he : fibrePhase z y=1 := by linarith only [hp]
      simp [fibreValue,admissibleWeight,hy,he]
    . have he : fibrePhase z y = -1 := by linarith only [hm]
      simp [fibreValue,admissibleWeight,hy,he]
  . simp [fibreValue,admissibleWeight,hy,fibrePhase_zero z y hy]

theorem fibre_fluctuation (hF : Not (ringChar F = 2)) (z : F)
    (hz : regular z) (f : Int -> Int) :
    2*(Finset.univ.sum fun y : F => fibreValue z f y) =
      ((Fintype.card F : Int)-3-splitCubicPointTrace z (z+1)) *
        f (splitCubicPointTrace z (z+1)) +
      ((Fintype.card F : Int)-3+splitCubicPointTrace z (z+1)) *
        f (-splitCubicPointTrace z (z+1)) := by
  have hz1 : Not ((1 : F)=z+1) := by
    intro he
    apply hz.1
    calc
      z = (z+1)-1 := by ring
      _ = 0 := by rw [<- he]; ring
  calc
    _ = Finset.univ.sum (fun y : F =>
        (admissibleWeight (1 : F) (z+1) y+fibrePhase z y) *
          f (splitCubicPointTrace z (z+1)) +
        (admissibleWeight (1 : F) (z+1) y-fibrePhase z y) *
          f (-splitCubicPointTrace z (z+1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      exact twice_fibreValue z f y
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,<- Finset.sum_mul]
      rw [sum_admissibleWeight (1 : F) (z+1) one_ne_zero hz.2 hz1,
        sum_fibrePhase hF z]
      ring

def fibreConstant (h z y : F) : F := h*(y+1)/z
def fibreShift (h z y : F) : F := h*(y+1)*(z+1)/(z*y)
def inverseFibrePoint (h k x : F) : F := shapeParameter h k x*x/h-1

theorem fibreShift_sub (h z y : F) (hz : Not (z=0)) (hy : Not (y=0)) :
    fibreShift h z y-h = h*(y+(z+1))/(z*y) := by
  unfold fibreShift
  field_simp [hz,hy]
  <;> ring

theorem fibreConstant_add (h z y : F) (hz : Not (z=0)) :
    fibreConstant h z y+h = h*(y+(z+1))/z := by
  unfold fibreConstant
  field_simp [hz]
  <;> ring

theorem fibreConstant_add_shift (h z y : F)
    (hz : Not (z=0)) (hy : Not (y=0)) :
    fibreConstant h z y+fibreShift h z y =
      h*(y+1)*(y+(z+1))/(z*y) := by
  unfold fibreConstant fibreShift
  field_simp [hz,hy]
  <;> ring

theorem fibre_image_valid (h z y : F) (hh : Not (h=0))
    (hz : regular z) (hy : admissible (1 : F) (z+1) y) :
    Not (fibreShift h z y=0) /\ Not (h=fibreShift h z y) /\
      admissible h (fibreShift h z y) (fibreConstant h z y) := by
  have hk0 : Not (fibreShift h z y=0) := by
    unfold fibreShift
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hh hy.2.1) hz.2)
      (mul_ne_zero hz.1 hy.1)
  have hdiff : Not (fibreShift h z y-h=0) := by
    rw [fibreShift_sub h z y hz.1 hy.1]
    exact div_ne_zero (mul_ne_zero hh hy.2.2) (mul_ne_zero hz.1 hy.1)
  have hx0 : Not (fibreConstant h z y=0) := by
    unfold fibreConstant
    exact div_ne_zero (mul_ne_zero hh hy.2.1) hz.1
  have hxh : Not (fibreConstant h z y+h=0) := by
    rw [fibreConstant_add h z y hz.1]
    exact div_ne_zero (mul_ne_zero hh hy.2.2) hz.1
  have hxk : Not (fibreConstant h z y+fibreShift h z y=0) := by
    rw [fibreConstant_add_shift h z y hz.1 hy.1]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hh hy.2.1) hy.2.2)
      (mul_ne_zero hz.1 hy.1)
  exact And.intro hk0 (And.intro (Ne.symm (sub_ne_zero.mp hdiff))
    (And.intro hx0 (And.intro hxh hxk)))

theorem inverseFibrePoint_eq (h k x : F) (hh : Not (h=0))
    (hhk : Not (h=k)) (hx : Not (x=0)) :
    inverseFibrePoint h k x = (x+h)/(k-h) := by
  have hd : Not (k-h=0) := sub_ne_zero.mpr (Ne.symm hhk)
  unfold inverseFibrePoint shapeParameter
  field_simp [hh,hd,hx]
  <;> ring

theorem inverseFibrePoint_add_one (h k x : F) (hh : Not (h=0))
    (hhk : Not (h=k)) (hx : Not (x=0)) :
    inverseFibrePoint h k x+1 = (x+k)/(k-h) := by
  rw [inverseFibrePoint_eq h k x hh hhk hx]
  have hd : Not (k-h=0) := sub_ne_zero.mpr (Ne.symm hhk)
  field_simp [hd]
  <;> ring

theorem inverseFibrePoint_add_parameter (h k x : F) (hh : Not (h=0))
    (hhk : Not (h=k)) (hx : Not (x=0)) :
    inverseFibrePoint h k x+(shapeParameter h k x+1) =
      ((x+h)*(x+k))/((k-h)*x) := by
  have hd : Not (k-h=0) := sub_ne_zero.mpr (Ne.symm hhk)
  unfold inverseFibrePoint shapeParameter
  field_simp [hh,hd,hx]
  <;> ring

theorem inverse_fibre_valid (h k x : F)
    (hh : Not (h=0)) (hk : Not (k=0)) (hhk : Not (h=k))
    (hx : admissible h k x) :
    regular (shapeParameter h k x) /\
      admissible (1 : F) (shapeParameter h k x+1) (inverseFibrePoint h k x) := by
  have hz := (shapeParameter_admissible_iff h k hh hk hhk x).mp hx
  have hd : Not (k-h=0) := sub_ne_zero.mpr (Ne.symm hhk)
  have h0 : Not (inverseFibrePoint h k x=0) := by
    rw [inverseFibrePoint_eq h k x hh hhk hx.1]
    exact div_ne_zero hx.2.1 hd
  have h1 : Not (inverseFibrePoint h k x+1=0) := by
    rw [inverseFibrePoint_add_one h k x hh hhk hx.1]
    exact div_ne_zero hx.2.2 hd
  have h2 : Not (inverseFibrePoint h k x+(shapeParameter h k x+1)=0) := by
    rw [inverseFibrePoint_add_parameter h k x hh hhk hx.1]
    exact div_ne_zero (mul_ne_zero hx.2.1 hx.2.2) (mul_ne_zero hd hx.1)
  exact And.intro hz.1 (And.intro h0 (And.intro h1 h2))

theorem shapeParameter_fraction (h k x : F)
    (hhk : Not (h=k)) (hx : Not (x=0)) :
    shapeParameter h k x = h*(x+k)/((k-h)*x) := by
  have hd : Not (k-h=0) := sub_ne_zero.mpr (Ne.symm hhk)
  unfold shapeParameter
  field_simp [hd,hx]
  <;> ring

theorem shapeParameter_fibre (h z y : F) (hh : Not (h=0))
    (hz : regular z) (hy : admissible (1 : F) (z+1) y) :
    shapeParameter h (fibreShift h z y) (fibreConstant h z y)=z := by
  simp only [shapeParameter,fibreShift_sub h z y hz.1 hy.1]
  unfold fibreShift fibreConstant
  field_simp [hh,hz.1,hy.1,hy.2.1,hy.2.2]
  <;> ring

theorem inverseFibrePoint_fibre (h z y : F) (hh : Not (h=0))
    (hz : regular z) (hy : admissible (1 : F) (z+1) y) :
    inverseFibrePoint h (fibreShift h z y) (fibreConstant h z y)=y := by
  unfold inverseFibrePoint
  rw [shapeParameter_fibre h z y hh hz hy]
  unfold fibreConstant
  field_simp [hh,hz.1]
  <;> ring

theorem fibreConstant_inverse (h k x : F)
    (hh : Not (h=0)) (hk : Not (k=0)) (hhk : Not (h=k))
    (hx : admissible h k x) :
    fibreConstant h (shapeParameter h k x) (inverseFibrePoint h k x)=x := by
  have hz := (inverse_fibre_valid h k x hh hk hhk hx).1
  unfold fibreConstant inverseFibrePoint
  field_simp [hh,hz.1]
  <;> ring

theorem fibreShift_inverse (h k x : F)
    (hh : Not (h=0)) (hk : Not (k=0)) (hhk : Not (h=k))
    (hx : admissible h k x) :
    fibreShift h (shapeParameter h k x) (inverseFibrePoint h k x)=k := by
  have hd : Not (k-h=0) := sub_ne_zero.mpr (Ne.symm hhk)
  unfold fibreShift
  simp only [inverseFibrePoint_eq h k x hh hhk hx.1,
    shapeParameter_fraction h k x hhk hx.1]
  field_simp [hh,hd,hx.1,hx.2.1,hx.2.2]
  <;> ring

theorem fibre_phase (h z y : F) (hh : Not (h=0))
    (hz : regular z) (hy : admissible (1 : F) (z+1) y) :
    (quadraticChar F) ((fibreShift h z y-h)*fibreConstant h z y)=
      fibrePhase z y := by
  have he : (fibreShift h z y-h)*fibreConstant h z y =
      (y*(y+1)*(y+(z+1)))*(h/(z*y))^2 := by
    rw [fibreShift_sub h z y hz.1 hy.1]
    unfold fibreConstant
    field_simp [hz.1,hy.1]
    <;> ring
  have hn : Not (h/(z*y)=0) := div_ne_zero hh (mul_ne_zero hz.1 hy.1)
  unfold fibrePhase
  rw [he,map_mul,map_pow,quadraticChar_sq_one hn,mul_one]

theorem compensatedWave_fibre (hF : Not (ringChar F = 2)) (h z y t : F)
    (hh : Not (h=0)) (hz : regular z)
    (hy : admissible (1 : F) (z+1) y)
    (ht : Not (t=0)) (hchi : (quadraticChar F) t = -1) :
    compensatedWave h (fibreShift h z y) t (fibreConstant h z y)=
      fibrePhase z y*splitCubicPointTrace z (z+1) := by
  have hv := fibre_image_valid h z y hh hz hy
  rw [compensatedWave_eq_trace hF h (fibreShift h z y) t (fibreConstant h z y)
      hh hv.1 hv.2.1 ht hchi hv.2.2,
    shapeParameter_trace hF h (fibreShift h z y) (fibreConstant h z y)
      hv.2.1 hv.2.2.1,
    shapeParameter_fibre h z y hh hz hy,
    fibre_phase h z y hh hz hy]

abbrev shapeState (h : F) :=
  Subtype (fun p : Prod F F => Not (p.1=0) /\ Not (h=p.1) /\ admissible h p.1 p.2)

abbrev fibreState :=
  Subtype (fun p : Prod F F => regular p.1 /\ admissible (1 : F) (p.1+1) p.2)

abbrev regularState := Subtype (fun z : F => regular z)

abbrev fibreAt (z : regularState (F := F)) :=
  Subtype (fun y : F => admissible (1 : F) (z.val+1) y)

def fullShapeEquiv (h : F) (hh : Not (h=0)) :
    Equiv (shapeState h) (fibreState (F := F)) :=
  { toFun := fun p => Subtype.mk
      (Prod.mk (shapeParameter h p.val.1 p.val.2) (inverseFibrePoint h p.val.1 p.val.2))
      (inverse_fibre_valid h p.val.1 p.val.2 hh p.property.1 p.property.2.1 p.property.2.2)
    invFun := fun p => Subtype.mk
      (Prod.mk (fibreShift h p.val.1 p.val.2) (fibreConstant h p.val.1 p.val.2))
      (fibre_image_valid h p.val.1 p.val.2 hh p.property.1 p.property.2)
    left_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext
      . exact fibreShift_inverse h p.val.1 p.val.2 hh
          p.property.1 p.property.2.1 p.property.2.2
      . exact fibreConstant_inverse h p.val.1 p.val.2 hh
          p.property.1 p.property.2.1 p.property.2.2
    right_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext
      . exact shapeParameter_fibre h p.val.1 p.val.2 hh p.property.1 p.property.2
      . exact inverseFibrePoint_fibre h p.val.1 p.val.2 hh p.property.1 p.property.2 }

def fibreSigmaEquiv :
    Equiv (fibreState (F := F)) (Sigma (fun z : regularState (F := F) => fibreAt z)) :=
  { toFun := fun p => Sigma.mk
      (Subtype.mk p.val.1 p.property.1) (Subtype.mk p.val.2 p.property.2)
    invFun := fun p => Subtype.mk (Prod.mk p.fst.val p.snd.val)
      (And.intro p.fst.property p.snd.property)
    left_inv := by intro p; apply Subtype.ext; rfl
    right_inv := by intro p; cases p; rfl }

theorem sum_fibreAt (z : regularState (F := F)) (f : Int -> Int) :
    (Finset.univ.sum fun y : fibreAt z =>
      f (fibrePhase z.val y.val*splitCubicPointTrace z.val (z.val+1))) =
        Finset.univ.sum (fun y : F => fibreValue z.val f y) := by
  have hs := Finset.sum_subtype (F := (inferInstance : Fintype (fibreAt z)))
    (p := fun y : F => admissible (1 : F) (z.val+1) y)
    (Finset.univ.filter (fun y : F => admissible (1 : F) (z.val+1) y))
    (fun y => by simp)
    (fun y : F => f (fibrePhase z.val y*splitCubicPointTrace z.val (z.val+1)))
  calc
    _ = (Finset.univ.filter (fun y : F => admissible (1 : F) (z.val+1) y)).sum
        (fun y : F => f (fibrePhase z.val y*splitCubicPointTrace z.val (z.val+1))) := hs.symm
    _ = _ := by
      rw [Finset.sum_filter]
      rfl

theorem sum_shape_transport (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h=0)) (ht : Not (t=0)) (hchi : (quadraticChar F) t = -1)
    (f : Int -> Int) :
    (Finset.univ.sum fun p : shapeState h => f (compensatedWave h p.val.1 t p.val.2)) =
      Finset.univ.sum (fun z : regularState (F := F) =>
        Finset.univ.sum fun y : F => fibreValue z.val f y) := by
  let g : fibreState (F := F) -> Int := fun p =>
    f (fibrePhase p.val.1 p.val.2*splitCubicPointTrace p.val.1 (p.val.1+1))
  calc
    _ = Finset.univ.sum (fun p : fibreState (F := F) =>
        f (compensatedWave h (fibreShift h p.val.1 p.val.2) t
          (fibreConstant h p.val.1 p.val.2))) :=
      (Equiv.sum_comp (fullShapeEquiv h hh).symm
        (fun p : shapeState h => f (compensatedWave h p.val.1 t p.val.2))).symm
    _ = Finset.univ.sum g := by
      apply Finset.sum_congr rfl
      intro p _
      rw [compensatedWave_fibre hF h p.val.1 p.val.2 t hh p.property.1 p.property.2 ht hchi]
    _ = Finset.univ.sum (fun p : Sigma (fun z : regularState (F := F) => fibreAt z) =>
        f (fibrePhase p.fst.val p.snd.val *
          splitCubicPointTrace p.fst.val (p.fst.val+1))) :=
      (Equiv.sum_comp (fibreSigmaEquiv (F := F)).symm g).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro z _
      exact sum_fibreAt z f

theorem full_shape_fluctuation (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h=0)) (ht : Not (t=0)) (hchi : (quadraticChar F) t = -1)
    (f : Int -> Int) :
    2*(Finset.univ.sum fun p : shapeState h => f (compensatedWave h p.val.1 t p.val.2)) =
      Finset.univ.sum (fun z : regularState (F := F) =>
        ((Fintype.card F : Int)-3-splitCubicPointTrace z.val (z.val+1)) *
          f (splitCubicPointTrace z.val (z.val+1)) +
        ((Fintype.card F : Int)-3+splitCubicPointTrace z.val (z.val+1)) *
          f (-splitCubicPointTrace z.val (z.val+1))) := by
  rw [sum_shape_transport hF h t hh ht hchi f,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact fibre_fluctuation hF z.val z.property f

theorem sum_regular_trace_square (hF : Not (ringChar F = 2)) :
    (Finset.univ.sum fun z : regularState (F := F) =>
      (splitCubicPointTrace z.val (z.val+1))^2) =
        ((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1) := by
  have hs := Finset.sum_subtype (F := (inferInstance : Fintype (regularState (F := F))))
    (p := fun z : F => regular z) (Finset.univ.filter (fun z : F => regular z))
    (fun z => by simp) (fun z : F => traceSquare z)
  change (Finset.univ.sum fun z : regularState (F := F) => traceSquare z.val) = _
  rw [<- hs,Finset.sum_filter]
  simp_rw [<- regularTraceSquare_eq_ite]
  exact sum_regularTraceSquare hF

theorem full_shape_first_moment (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h=0)) (ht : Not (t=0)) (hchi : (quadraticChar F) t = -1) :
    (Finset.univ.sum fun p : shapeState h => compensatedWave h p.val.1 t p.val.2) =
      -((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1) := by
  have hf := full_shape_fluctuation hF h t hh ht hchi (fun w : Int => w)
  have hs : (Finset.univ.sum fun z : regularState (F := F) =>
        ((Fintype.card F : Int)-3-splitCubicPointTrace z.val (z.val+1)) *
          splitCubicPointTrace z.val (z.val+1) +
        ((Fintype.card F : Int)-3+splitCubicPointTrace z.val (z.val+1)) *
          (-splitCubicPointTrace z.val (z.val+1))) =
      -2*(((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1)) := by
    calc
      _ = Finset.univ.sum (fun z : regularState (F := F) =>
          -2*(splitCubicPointTrace z.val (z.val+1))^2) := by
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by rw [<- Finset.mul_sum,sum_regular_trace_square hF]
  nlinarith only [hf,hs]

theorem full_shape_second_moment (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h=0)) (ht : Not (t=0)) (hchi : (quadraticChar F) t = -1) :
    (Finset.univ.sum fun p : shapeState h => (compensatedWave h p.val.1 t p.val.2)^2) =
      ((Fintype.card F : Int)-3)^2*((Fintype.card F : Int)+1) := by
  have hf := full_shape_fluctuation hF h t hh ht hchi (fun w : Int => w^2)
  have hs : (Finset.univ.sum fun z : regularState (F := F) =>
        ((Fintype.card F : Int)-3-splitCubicPointTrace z.val (z.val+1)) *
          (splitCubicPointTrace z.val (z.val+1))^2 +
        ((Fintype.card F : Int)-3+splitCubicPointTrace z.val (z.val+1)) *
          (-splitCubicPointTrace z.val (z.val+1))^2) =
      (2*((Fintype.card F : Int)-3)) *
        (((Fintype.card F : Int)-3)*((Fintype.card F : Int)+1)) := by
    calc
      _ = Finset.univ.sum (fun z : regularState (F := F) =>
          (2*((Fintype.card F : Int)-3))*(splitCubicPointTrace z.val (z.val+1))^2) := by
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by rw [<- Finset.mul_sum,sum_regular_trace_square hF]
  nlinarith only [hf,hs]

theorem neg_odd_power (v : Int) (m : Nat) :
    (-v)^(2*m+1) = -(v^(2*m+1)) := by
  simp only [pow_add,pow_mul,pow_one]
  rw [show (-v)^2=v^2 by ring]
  ring

theorem full_shape_odd_moment (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h=0)) (ht : Not (t=0)) (hchi : (quadraticChar F) t = -1)
    (m : Nat) :
    (Finset.univ.sum fun p : shapeState h =>
      (compensatedWave h p.val.1 t p.val.2)^(2*m+1)) =
      -(Finset.univ.sum fun z : regularState (F := F) =>
        (splitCubicPointTrace z.val (z.val+1))^(2*m+2)) := by
  have hf := full_shape_fluctuation hF h t hh ht hchi (fun w : Int => w^(2*m+1))
  have hp (v : Int) :
      ((Fintype.card F : Int)-3-v)*v^(2*m+1) +
        ((Fintype.card F : Int)-3+v)*(-v)^(2*m+1) = -2*v^(2*m+2) := by
    have he : v^(2*m+2)=v^(2*m+1)*v := by
      rw [show 2*m+2=(2*m+1)+1 from rfl,pow_succ]
    rw [neg_odd_power,he]
    ring
  simp_rw [hp] at hf
  rw [<- Finset.mul_sum] at hf
  linarith only [hf]

theorem full_shape_odd_moment_nonpos (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h=0)) (ht : Not (t=0)) (hchi : (quadraticChar F) t = -1)
    (m : Nat) :
    (Finset.univ.sum fun p : shapeState h =>
      (compensatedWave h p.val.1 t p.val.2)^(2*m+1)) <= 0 := by
  rw [full_shape_odd_moment hF h t hh ht hchi m]
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro z _
  rw [show 2*m+2=(m+1)*2 by ring,pow_mul]
  exact sq_nonneg _

end FiniteField.QuadraticTripleTwist
