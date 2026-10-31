/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairCompensatedKernel

/-!
# Euler-factor bounds for compensated pair-law products

The shared-endpoint to diagonal moment ratio lies between two shifted
Euler squares. The diagonal moment lies between two inverse Euler cubes.
Every bound is uniform on q>=16 and both character parameters in [-1,1].
The positive shared-endpoint supply is retained before tensorization.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField

def compensatedQuadraticPairDiagonalMoment (q t : Real) : Real :=
  (q^3-3*q^2+(5+2*t)*q-11-2*t)/(q*((q-3)^2+2*(1+t)))

def compensatedQuadraticPairMomentRatio (q t u : Real) : Real :=
  (q^3-5*q^2+(5-4*u)*q-11-2*t)/(q^3-3*q^2+(5+2*t)*q-11-2*t)

theorem compensatedQuadraticPairBase_pos (q t : Real) (hq : 16<=q) (ht : -1<=t) :
    0<(q-3)^2+2*(1+t) := by
  have hs : 0<(q-3)^2 := sq_pos_of_pos (by linarith only [hq])
  linarith only [hs,ht]

theorem compensatedQuadraticPairDiagonalNumerator_pos
    (q t : Real) (hq : 16<=q) (ht : -1<=t) :
    0<q^3-3*q^2+(5+2*t)*q-11-2*t := by
  have hm : 0<(q-3)*(q^2+3) := mul_pos
    (by linarith only [hq]) (by nlinarith only [sq_nonneg q])
  have hs : 0<=(1+t)*(q-1) := mul_nonneg
    (by linarith only [ht]) (by linarith only [hq])
  nlinarith only [hm,hs]

theorem compensatedQuadraticPairMomentRatio_eq
    (q t u : Real) (hq : 16<=q) (ht : -1<=t) :
    compensatedQuadraticPairCrossMoment q t u/compensatedQuadraticPairDiagonalMoment q t=
      compensatedQuadraticPairMomentRatio q t u := by
  have hq0 : Not (q=0) := ne_of_gt (by linarith only [hq])
  have hR := ne_of_gt (compensatedQuadraticPairBase_pos q t hq ht)
  have hD := ne_of_gt (compensatedQuadraticPairDiagonalNumerator_pos q t hq ht)
  unfold compensatedQuadraticPairCrossMoment compensatedQuadraticPairDiagonalMoment
    compensatedQuadraticPairMomentRatio
  field_simp [hq0,hR,hD]

theorem compensatedQuadraticPairCrossMoment_lower
    (q t u : Real) (hq : 16<=q)
    (ht : And (-1<=t) (t<=1)) (hu : And (-1<=u) (u<=1)) :
    1+1/(4*q)<=compensatedQuadraticPairCrossMoment q t u := by
  let R : Real := (q-3)^2+2*(1+t)
  let H : Real := 3*q^2-(18+16*u+8*t)*q-55-10*t
  have hq0 : 0<q := by linarith only [hq]
  have hR : 0<R := compensatedQuadraticPairBase_pos q t hq ht.1
  have hs : 0<=(q-16)*q := mul_nonneg
    (by linarith only [hq]) hq0.le
  have h1 : 0<=(1-u)*q := mul_nonneg
    (by linarith only [hu.2]) hq0.le
  have h2 : 0<=(1-t)*(8*q+10) := mul_nonneg
    (by linarith only [ht.2]) (by linarith only [hq])
  have hH : 0<=H := by dsimp only [H]; nlinarith only [hq,hs,h1,h2]
  have hp : 0<=H/(4*q*R) := div_nonneg hH (by positivity)
  have he : compensatedQuadraticPairCrossMoment q t u-(1+1/(4*q))=H/(4*q*R) := by
    unfold compensatedQuadraticPairCrossMoment
    change (q^3-5*q^2+(5-4*u)*q-11-2*t)/(q*R)-(1+1/(4*q))=_
    field_simp [ne_of_gt hq0,ne_of_gt hR]
    dsimp only [R,H]
    ring
  rw [<- he] at hp
  linarith only [hp]

theorem compensatedQuadraticPairMomentRatio_bounds
    (q t u : Real) (hq : 16<=q)
    (ht : And (-1<=t) (t<=1)) (hu : And (-1<=u) (u<=1)) :
    And (((q-8)/(q-7))^2<=compensatedQuadraticPairMomentRatio q t u)
      (compensatedQuadraticPairMomentRatio q t u<=((q-1)/q)^2) := by
  let D : Real := q^3-3*q^2+(5+2*t)*q-11-2*t
  let P : Real := (7-2*t-4*u)*q^3+(-43+32*t+56*u)*q^2+
    (-97-132*t-196*u)*q+165+30*t
  let Q : Real := (7+2*t+4*u)*q^3-(13+4*t)*q^2+(27+6*t)*q-11-2*t
  have hq0 : 0<q := by linarith only [hq]
  have hD : 0<D := compensatedQuadraticPairDiagonalNumerator_pos q t hq ht.1
  have h7 : 0<q-7 := by linarith only [hq]
  have hq3 : 0<=q^3 := pow_nonneg hq0.le 3
  have hs : 0<=(q-16)*q^2 := mul_nonneg
    (by linarith only [hq]) (sq_nonneg q)
  have hco : 0<=2*q^3-32*q^2+132*q-30 := by nlinarith only [hs,hq]
  have hp1 := mul_nonneg (sub_nonneg.mpr ht.2) hco
  have hp2 := mul_nonneg (sub_nonneg.mpr hu.2)
    (mul_nonneg (by linarith only [hq] : 0<=4*q) (sq_nonneg (q-7)))
  have hp0 : 0<q*(q^2+45*q-425) := mul_pos hq0
    (by nlinarith only [hq,sq_nonneg (q-16)])
  have hP : 0<=P := by dsimp only [P]; nlinarith only [hp0,hp1,hp2]
  have hco2 : 0<=2*q^3-4*q^2+6*q-2 := by
    have hp := mul_nonneg (sq_nonneg q)
      (by linarith only [hq] : 0<=q-2)
    nlinarith only [hp,hq]
  have hq1 := mul_nonneg (by linarith only [ht.1] : 0<=1+t) hco2
  have hq2 := mul_nonneg (by linarith only [hu.1] : 0<=1+u) hq3
  have hqmain := mul_nonneg (sq_nonneg q)
    (by linarith only [hq] : 0<=q-9)
  have hQ : 0<=Q := by dsimp only [Q]; nlinarith only [hq,hqmain,hq1,hq2]
  constructor
  . have hp : 0<=P/((q-7)^2*D) := div_nonneg hP (by positivity)
    have he : compensatedQuadraticPairMomentRatio q t u-((q-8)/(q-7))^2=
        P/((q-7)^2*D) := by
      unfold compensatedQuadraticPairMomentRatio
      change (q^3-5*q^2+(5-4*u)*q-11-2*t)/D-((q-8)/(q-7))^2=_
      field_simp [ne_of_gt hD,ne_of_gt h7]
      dsimp only [P,D]
      ring
    rw [<- he] at hp
    linarith only [hp]
  . have hp : 0<=Q/(q^2*D) := div_nonneg hQ (by positivity)
    have he : ((q-1)/q)^2-compensatedQuadraticPairMomentRatio q t u=Q/(q^2*D) := by
      unfold compensatedQuadraticPairMomentRatio
      change ((q-1)/q)^2-(q^3-5*q^2+(5-4*u)*q-11-2*t)/D=_
      field_simp [ne_of_gt hq0,ne_of_gt hD]
      dsimp only [Q,D]
      ring
    rw [<- he] at hp
    linarith only [hp]

theorem compensatedQuadraticPairDiagonalMoment_bounds
    (q t : Real) (hq : 16<=q) (ht : And (-1<=t) (t<=1)) :
    And ((q/(q-1))^3<=compensatedQuadraticPairDiagonalMoment q t)
      (compensatedQuadraticPairDiagonalMoment q t<=((q-2)/(q-3))^3) := by
  let R : Real := (q-3)^2+2*(1+t)
  let P : Real := 6*q^4-(36+8*t)*q^3+(51+12*t)*q^2-(38+8*t)*q+11+2*t
  let Q : Real := (18+8*t)*(q-3)^3+(27+24*t)*(q-3)^2+
    20*(1+t)*(q-3)+6*(1+t)
  have hq0 : 0<q := by linarith only [hq]
  have h1 : 0<q-1 := by linarith only [hq]
  have h3 : 0<q-3 := by linarith only [hq]
  have hR : 0<R := compensatedQuadraticPairBase_pos q t hq ht.1
  have hc : 0<=8*q^3-12*q^2+8*q-2 := by
    have hp := mul_nonneg (sq_nonneg q)
      (by linarith only [hq] : 0<=2*q-3)
    nlinarith only [hp,hq]
  have hp0 := mul_nonneg (sub_nonneg.mpr ht.2) hc
  have hp1 := mul_nonneg (pow_nonneg hq0.le 3)
    (by linarith only [hq] : 0<=6*q-44)
  have hp2 := mul_nonneg hq0.le
    (by linarith only [hq] : 0<=63*q-46)
  have hP : 0<=P := by dsimp only [P]; nlinarith only [hp0,hp1,hp2]
  have hQ : 0<=Q := by
    have ht1 : 0<=1+t := by linarith only [ht.1]
    have ht2 : 0<=18+8*t := by linarith only [ht.1]
    have ht3 : 0<=27+24*t := by linarith only [ht.1]
    dsimp only [Q]
    positivity
  constructor
  . have hp : 0<=P/(q*R*(q-1)^3) := div_nonneg hP (by positivity)
    have he : compensatedQuadraticPairDiagonalMoment q t-(q/(q-1))^3=
        P/(q*R*(q-1)^3) := by
      unfold compensatedQuadraticPairDiagonalMoment
      change (q^3-3*q^2+(5+2*t)*q-11-2*t)/(q*R)-(q/(q-1))^3=_
      field_simp [ne_of_gt hq0,ne_of_gt hR,ne_of_gt h1]
      dsimp only [R,P]
      ring
    rw [<- he] at hp
    linarith only [hp]
  . have hp : 0<=Q/(q*R*(q-3)^3) := div_nonneg hQ (by positivity)
    have he : ((q-2)/(q-3))^3-compensatedQuadraticPairDiagonalMoment q t=
        Q/(q*R*(q-3)^3) := by
      unfold compensatedQuadraticPairDiagonalMoment
      change ((q-2)/(q-3))^3-(q^3-3*q^2+(5+2*t)*q-11-2*t)/(q*R)=_
      field_simp [ne_of_gt hq0,ne_of_gt hR,ne_of_gt h3]
      dsimp only [R,Q]
      ring
    rw [<- he] at hp
    linarith only [hp]

end FiniteField
