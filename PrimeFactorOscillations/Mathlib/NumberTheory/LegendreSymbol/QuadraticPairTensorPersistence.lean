/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.EulerProduct.ShiftedBounds
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairMaskOverlap
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairProductFactors

/-!
# Uniform tensorized compensated-pair persistence

Finite products retain their full diagonal and shared-endpoint moments.
The local comparisons give Euler-square relative overlap and Euler-cube
inverse diagonal bounds, uniformly over every finite set of distinct sizes.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField

private theorem real_prod_mono {I : Type*} (s : Finset I) (f g : I -> Real)
    (h0 : forall i, Membership.mem s i -> 0<=f i)
    (hfg : forall i, Membership.mem s i -> f i<=g i) : s.prod f<=s.prod g := by
  classical
  revert h0 hfg
  induction s using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert i s hi ih =>
    intro h0 hfg
    have hp : 0<=s.prod f := Finset.prod_nonneg
      (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
    have ht := ih (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi,Finset.prod_insert hi]
    exact mul_le_mul (hfg i (Finset.mem_insert_self i s)) ht hp
      ((h0 i (Finset.mem_insert_self i s)).trans (hfg i (Finset.mem_insert_self i s)))

private theorem euler_factor_pos (n : Nat) (c : Real) (hn : c+1<(n : Real)) :
    0<Finset.shiftedEulerFactor c n := by
  have hd : 0<(n : Real)-c := by linarith only [hn]
  have hi : 1/((n : Real)-c)<1 := (div_lt_one hd).mpr (by linarith only [hn])
  unfold Finset.shiftedEulerFactor
  linarith only [hi]

private theorem euler_factor_eq (n : Nat) (c : Real)
    (hn : Not ((n : Real)-c=0)) :
    Finset.shiftedEulerFactor c n=((n : Real)-c-1)/((n : Real)-c) := by
  unfold Finset.shiftedEulerFactor
  field_simp [hn]

def compensatedQuadraticPairDiagonalProduct (s : Finset Nat) (t : Nat -> Real) : Real :=
  s.prod (fun n => compensatedQuadraticPairDiagonalMoment (n : Real) (t n))

def compensatedQuadraticPairCrossProduct (s : Finset Nat) (t u : Nat -> Real) : Real :=
  s.prod (fun n => compensatedQuadraticPairCrossMoment (n : Real) (t n) (u n))

def compensatedQuadraticPairTensorPersistence
    (s : Finset Nat) (t u : Nat -> Real) (a b : Real) : Real :=
  (b*compensatedQuadraticPairCrossProduct s t u-1)/
    (a*compensatedQuadraticPairDiagonalProduct s t-1)

theorem compensatedQuadraticPairDiagonalProduct_pos
    (s : Finset Nat) (t : Nat -> Real)
    (hs : forall n, Membership.mem s n -> 17<=n)
    (ht : forall n, Membership.mem s n -> -1<=t n) :
    0<compensatedQuadraticPairDiagonalProduct s t := by
  apply Finset.prod_pos
  intro n hn
  have hq : 16<=(n : Real) := by have h:=hs n hn; norm_cast; omega
  exact div_pos
    (compensatedQuadraticPairDiagonalNumerator_pos (n : Real) (t n) hq (ht n hn))
    (mul_pos (by linarith only [hq])
      (compensatedQuadraticPairBase_pos (n : Real) (t n) hq (ht n hn)))

theorem compensatedQuadraticPairCrossProduct_lower
    (s : Finset Nat) (t u : Nat -> Real)
    (hs : forall n, Membership.mem s n -> 17<=n)
    (ht : forall n, Membership.mem s n -> And (-1<=t n) (t n<=1))
    (hu : forall n, Membership.mem s n -> And (-1<=u n) (u n<=1)) :
    1+(s.sum (fun n => 1/(n : Real)))/4<=
      compensatedQuadraticPairCrossProduct s t u := by
  classical
  revert hs ht hu
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp [compensatedQuadraticPairCrossProduct]
  | @insert n s hn ih =>
    intro hs ht hu
    have hs' := fun j hj => hs j (Finset.mem_insert_of_mem hj)
    have ht' := fun j hj => ht j (Finset.mem_insert_of_mem hj)
    have hu' := fun j hj => hu j (Finset.mem_insert_of_mem hj)
    have hq : 16<=(n : Real) := by
      have h:=hs n (Finset.mem_insert_self n s); norm_cast; omega
    have hb := compensatedQuadraticPairCrossMoment_lower (n : Real) (t n) (u n) hq
      (ht n (Finset.mem_insert_self n s)) (hu n (Finset.mem_insert_self n s))
    have hscale : 1/(4*(n : Real))=(1/(n : Real))/4 := by ring
    rw [hscale] at hb
    have hp := ih hs' ht' hu'
    have hL : 0<=s.sum (fun j => 1/(j : Real)) :=
      Finset.sum_nonneg (fun j _ => by positivity)
    have hi : 0<=1/(n : Real) := by positivity
    have hm := mul_le_mul hb hp (by linarith only [hL])
      (by linarith only [hb,hi])
    unfold compensatedQuadraticPairCrossProduct at *
    rw [Finset.prod_insert hn,Finset.sum_insert hn]
    nlinarith only [hm,mul_nonneg hi hL]

theorem compensatedQuadraticPairRatioProduct_bounds
    (s : Finset Nat) (t u : Nat -> Real)
    (hs : forall n, Membership.mem s n -> 17<=n)
    (ht : forall n, Membership.mem s n -> And (-1<=t n) (t n<=1))
    (hu : forall n, Membership.mem s n -> And (-1<=u n) (u n<=1)) :
    And
      ((81/256 : Real)*(s.prod (Finset.shiftedEulerFactor 0))^2<=
        compensatedQuadraticPairCrossProduct s t u/compensatedQuadraticPairDiagonalProduct s t)
      (compensatedQuadraticPairCrossProduct s t u/compensatedQuadraticPairDiagonalProduct s t<=
        (s.prod (Finset.shiftedEulerFactor 0))^2) := by
  have hq (n : Nat) (hn : Membership.mem s n) : 16<=(n : Real) := by
    have h:=hs n hn; norm_cast; omega
  have hb (n : Nat) (hn : Membership.mem s n) :
      And ((Finset.shiftedEulerFactor 7 n)^2<=
        compensatedQuadraticPairMomentRatio (n : Real) (t n) (u n))
      (compensatedQuadraticPairMomentRatio (n : Real) (t n) (u n)<=
        (Finset.shiftedEulerFactor 0 n)^2) := by
    have he7 := euler_factor_eq n 7 (by have h:=hq n hn; linarith only [h])
    have he0 := euler_factor_eq n 0 (by have h:=hq n hn; linarith only [h])
    rw [he7,he0]
    have hn7 : (n : Real)-7-1=(n : Real)-8 := by ring
    rw [hn7]
    simpa only [sub_zero] using
      compensatedQuadraticPairMomentRatio_bounds (n : Real) (t n) (u n)
        (hq n hn) (ht n hn) (hu n hn)
  have hlo := real_prod_mono s
    (fun n => (Finset.shiftedEulerFactor 7 n)^2)
    (fun n => compensatedQuadraticPairMomentRatio (n : Real) (t n) (u n))
    (fun n _ => sq_nonneg _) (fun n hn => (hb n hn).1)
  have hhi := real_prod_mono s
    (fun n => compensatedQuadraticPairMomentRatio (n : Real) (t n) (u n))
    (fun n => (Finset.shiftedEulerFactor 0 n)^2)
    (fun n hn => (sq_nonneg _).trans (hb n hn).1) (fun n hn => (hb n hn).2)
  have he : s.prod (fun n => compensatedQuadraticPairMomentRatio (n : Real) (t n) (u n))=
      compensatedQuadraticPairCrossProduct s t u/compensatedQuadraticPairDiagonalProduct s t := by
    unfold compensatedQuadraticPairCrossProduct compensatedQuadraticPairDiagonalProduct
    rw [<- Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro n hn
    exact (compensatedQuadraticPairMomentRatio_eq (n : Real) (t n) (u n)
      (hq n hn) (ht n hn).1).symm
  rw [Finset.prod_pow,he] at hlo hhi
  have hshift := (Finset.shiftedEulerProduct_bounds s 7 17 (by norm_num)
    (by norm_num) hs).1
  have hE : 0<s.prod (Finset.shiftedEulerFactor 0) := Finset.prod_pos
    (fun n hn => euler_factor_pos n 0 (by have h:=hq n hn; linarith only [h]))
  have hF : 0<s.prod (Finset.shiftedEulerFactor 7) := Finset.prod_pos
    (fun n hn => euler_factor_pos n 7 (by have h:=hq n hn; linarith only [h]))
  norm_num only [Nat.cast_ofNat] at hshift
  have hmul := mul_le_mul hshift hshift
    (mul_nonneg (by norm_num : (0 : Real)<=9/16) hE.le) hF.le
  exact And.intro (by nlinarith only [hmul,hlo]) hhi

theorem compensatedQuadraticPairInverseDiagonalProduct_bounds
    (s : Finset Nat) (t : Nat -> Real)
    (hs : forall n, Membership.mem s n -> 17<=n)
    (ht : forall n, Membership.mem s n -> And (-1<=t n) (t n<=1)) :
    And
      ((343/512 : Real)*(s.prod (Finset.shiftedEulerFactor 0))^3<=
        1/compensatedQuadraticPairDiagonalProduct s t)
      (1/compensatedQuadraticPairDiagonalProduct s t<=
        (s.prod (Finset.shiftedEulerFactor 0))^3) := by
  have hq (n : Nat) (hn : Membership.mem s n) : 16<=(n : Real) := by
    have h:=hs n hn; norm_cast; omega
  have hb (n : Nat) (hn : Membership.mem s n) :
      And ((Finset.shiftedEulerFactor 2 n)^3<=
        1/compensatedQuadraticPairDiagonalMoment (n : Real) (t n))
      (1/compensatedQuadraticPairDiagonalMoment (n : Real) (t n)<=
        (Finset.shiftedEulerFactor 0 n)^3) := by
    have hN : 0<(n : Real) := by have h:=hq n hn; linarith only [h]
    have h1 : 0<(n : Real)-1 := by have h:=hq n hn; linarith only [h]
    have h2 : 0<(n : Real)-2 := by have h:=hq n hn; linarith only [h]
    have h3 : 0<(n : Real)-3 := by have h:=hq n hn; linarith only [h]
    have hD : 0<compensatedQuadraticPairDiagonalMoment (n : Real) (t n) := div_pos
      (compensatedQuadraticPairDiagonalNumerator_pos (n : Real) (t n) (hq n hn) (ht n hn).1)
      (mul_pos hN (compensatedQuadraticPairBase_pos (n : Real) (t n) (hq n hn) (ht n hn).1))
    have hd := compensatedQuadraticPairDiagonalMoment_bounds (n : Real) (t n) (hq n hn) (ht n hn)
    have hlow := one_div_le_one_div_of_le hD hd.2
    have hupp := one_div_le_one_div_of_le (by positivity : 0<((n : Real)/((n : Real)-1))^3) hd.1
    have e2 : 1/(((n : Real)-2)/((n : Real)-3))^3=
        (Finset.shiftedEulerFactor 2 n)^3 := by
      unfold Finset.shiftedEulerFactor
      field_simp [ne_of_gt h2,ne_of_gt h3]
      ring
    have e0 : 1/((n : Real)/((n : Real)-1))^3=
        (Finset.shiftedEulerFactor 0 n)^3 := by
      unfold Finset.shiftedEulerFactor
      field_simp [ne_of_gt hN,ne_of_gt h1]
      ring
    rw [e2] at hlow
    rw [e0] at hupp
    exact And.intro hlow hupp
  have hlo := real_prod_mono s
    (fun n => (Finset.shiftedEulerFactor 2 n)^3)
    (fun n => 1/compensatedQuadraticPairDiagonalMoment (n : Real) (t n))
    (fun n hn => pow_nonneg (euler_factor_pos n 2
      (by have h:=hq n hn; linarith only [h])).le 3)
    (fun n hn => (hb n hn).1)
  have hhi := real_prod_mono s
    (fun n => 1/compensatedQuadraticPairDiagonalMoment (n : Real) (t n))
    (fun n => (Finset.shiftedEulerFactor 0 n)^3)
    (fun n hn => (pow_nonneg (euler_factor_pos n 2
      (by have h:=hq n hn; linarith only [h])).le 3).trans (hb n hn).1)
    (fun n hn => (hb n hn).2)
  have he : s.prod (fun n => 1/compensatedQuadraticPairDiagonalMoment (n : Real) (t n))=
      1/compensatedQuadraticPairDiagonalProduct s t := by
    unfold compensatedQuadraticPairDiagonalProduct
    simp only [one_div,Finset.prod_inv_distrib]
  rw [Finset.prod_pow,he] at hlo hhi
  have hshift := (Finset.shiftedEulerProduct_bounds s 2 17 (by norm_num)
    (by norm_num) hs).1
  norm_num only [Nat.cast_ofNat] at hshift
  have hE : 0<s.prod (Finset.shiftedEulerFactor 0) := Finset.prod_pos
    (fun n hn => euler_factor_pos n 0 (by have h:=hq n hn; linarith only [h]))
  have hF : 0<s.prod (Finset.shiftedEulerFactor 2) := Finset.prod_pos
    (fun n hn => euler_factor_pos n 2 (by have h:=hq n hn; linarith only [h]))
  have h0 : 0<=(7/8 : Real)*s.prod (Finset.shiftedEulerFactor 0) := by positivity
  have hm2 := mul_le_mul hshift hshift h0 hF.le
  have hm3 := mul_le_mul hm2 hshift h0 (mul_nonneg hF.le hF.le)
  exact And.intro (by nlinarith only [hm3,hlo]) hhi


private theorem ordinary_euler_bounds (s : Finset Nat)
    (hs : forall n, Membership.mem s n -> 17<=n) :
    And (0<s.prod (Finset.shiftedEulerFactor 0))
      (s.prod (Finset.shiftedEulerFactor 0)<=1) := by
  have hp (n : Nat) (hn : Membership.mem s n) : 0<Finset.shiftedEulerFactor 0 n := by
    apply euler_factor_pos
    have h:=hs n hn
    norm_cast
    omega
  have hm := real_prod_mono s (Finset.shiftedEulerFactor 0) (fun _ => 1)
    (fun n hn => (hp n hn).le) (fun n _ => by
      unfold Finset.shiftedEulerFactor
      have h0 : 0<=1/(n : Real) := by positivity
      simpa only [sub_zero] using sub_le_self (1 : Real) h0)
  exact And.intro (Finset.prod_pos hp) (by simpa using hm)

private theorem centered_fraction_upper (d n : Real) (hd : 1<d) (hn : n<=d) :
    (n-1)/(d-1)<=n/d := by
  have hd0 : 0<d := by linarith only [hd]
  have hd1 : 0<d-1 := by linarith only [hd]
  have hp : 0<=(d-n)/(d*(d-1)) := div_nonneg
    (by linarith only [hn]) (mul_pos hd0 hd1).le
  have he : n/d-(n-1)/(d-1)=(d-n)/(d*(d-1)) := by
    field_simp [ne_of_gt hd0,ne_of_gt hd1] ; ring
  rw [<- he] at hp
  linarith only [hp]

private theorem centered_fraction_lower (d n b : Real)
    (hd : 1<d) (hb : 1<=b) (hn : b<=n) :
    (n-b)/d<=(n-1)/(d-1) := by
  have hd0 : 0<d := by linarith only [hd]
  have hd1 : 0<d-1 := by linarith only [hd]
  have hp : 0<=((b-1)*d+(n-b))/(d*(d-1)) := div_nonneg
    (add_nonneg (mul_nonneg (by linarith only [hb]) hd0.le)
      (by linarith only [hn])) (mul_pos hd0 hd1).le
  have he : (n-1)/(d-1)-(n-b)/d=((b-1)*d+(n-b))/(d*(d-1)) := by
    field_simp [ne_of_gt hd0,ne_of_gt hd1] ; ring
  rw [<- he] at hp
  linarith only [hp]

private theorem centered_compatible_bounds (A B a b L : Real)
    (hA : 0<A) (hB : 1+L/4<=B) (hL : 0<=L)
    (ha : 2<=a) (hb : 1<=b) (hba : b<=a) (hBA : B<=A) :
    And ((b/a)*(B/A)*(L/(L+4))<=(b*B-1)/(a*A-1))
      ((b*B-1)/(a*A-1)<=(b/a)*(B/A)) := by
  have hB1 : 1<=B := by linarith only [hB,hL]
  have hB0 : 0<B := by linarith only [hB1]
  have ha0 : 0<a := by linarith only [ha]
  have hb0 : 0<=b := by linarith only [hb]
  have hA1 : 1<=A := hB1.trans hBA
  have hd : 1<a*A := by
    have hp := mul_le_mul_of_nonneg_left hA1 ha0.le
    nlinarith only [hp,ha]
  have hnb : b<=b*B := by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hB1 hb0
  have hnd : b*B<=a*A := mul_le_mul hba hBA hB0.le ha0.le
  have hlow := centered_fraction_lower (a*A) (b*B) b hd hb hnb
  have hupp := centered_fraction_upper (a*A) (b*B) hd hnd
  have he : (b*B-b)/(a*A)=(b/a)*(B/A)*(1-1/B) := by
    field_simp [ne_of_gt hA,ne_of_gt hB0,ne_of_gt ha0]
  have hf : L/(L+4)<=1-1/B := by
    have hL4 : 0<L+4 := by linarith only [hL]
    have hp : 0<=(4*B-L-4)/(B*(L+4)) :=
      div_nonneg (by linarith only [hB]) (mul_pos hB0 hL4).le
    have hi : 1-1/B-L/(L+4)=(4*B-L-4)/(B*(L+4)) := by
      field_simp [ne_of_gt hB0,ne_of_gt hL4] ; ring
    rw [<- hi] at hp
    linarith only [hp]
  have hm := mul_le_mul_of_nonneg_left hf
    (mul_nonneg (div_nonneg hb0 ha0.le) (div_nonneg hB0.le hA.le))
  rw [he] at hlow
  have heu : (b*B)/(a*A)=(b/a)*(B/A) := by
    field_simp [ne_of_gt hA,ne_of_gt ha0]
  rw [heu] at hupp
  exact And.intro (hm.trans hlow) hupp

private theorem tail_fraction_mono (a x y : Real) (ha : 0<=a)
    (hxy : x<=y) (hy : y<a) : x/(a-x)<=y/(a-y) := by
  have hax : 0<a-x := by linarith only [hxy,hy]
  have hay : 0<a-y := by linarith only [hy]
  have hp : 0<=a*(y-x)/((a-y)*(a-x)) := div_nonneg
    (mul_nonneg ha (by linarith only [hxy])) (mul_pos hay hax).le
  have he : y/(a-y)-x/(a-x)=a*(y-x)/((a-y)*(a-x)) := by
    field_simp [ne_of_gt hax,ne_of_gt hay] ; ring
  rw [<- he] at hp
  linarith only [hp]

theorem compensatedQuadraticPairTensorPersistence_compatible
    (s : Finset Nat) (t u : Nat -> Real) (a b : Real)
    (hs : forall n, Membership.mem s n -> 17<=n)
    (ht : forall n, Membership.mem s n -> And (-1<=t n) (t n<=1))
    (hu : forall n, Membership.mem s n -> And (-1<=u n) (u n<=1))
    (ha : 2<=a) (hb : 1<=b) (hba : b<=a) :
    let E := s.prod (Finset.shiftedEulerFactor 0)
    let L := s.sum (fun n => 1/(n : Real))
    And ((81/256 : Real)*(b/a)*(L/(L+4))*E^2<=
      compensatedQuadraticPairTensorPersistence s t u a b)
      (compensatedQuadraticPairTensorPersistence s t u a b<=(b/a)*E^2) := by
  let A := compensatedQuadraticPairDiagonalProduct s t
  let B := compensatedQuadraticPairCrossProduct s t u
  let E := s.prod (Finset.shiftedEulerFactor 0)
  let L := s.sum (fun n => 1/(n : Real))
  have hA : 0<A := compensatedQuadraticPairDiagonalProduct_pos s t hs (fun n hn => (ht n hn).1)
  have hB : 1+L/4<=B := compensatedQuadraticPairCrossProduct_lower s t u hs ht hu
  have hratio := compensatedQuadraticPairRatioProduct_bounds s t u hs ht hu
  change And ((81/256 : Real)*E^2<=B/A) (B/A<=E^2) at hratio
  have hE : And (0<E) (E<=1) := ordinary_euler_bounds s hs
  have hL : 0<=L := Finset.sum_nonneg (fun n _ => by positivity)
  have hBA : B<=A := (div_le_one hA).mp
    (hratio.2.trans (by nlinarith only [hE.1,hE.2]))
  have hmain := centered_compatible_bounds A B a b L hA hB hL ha hb hba hBA
  have hcoef : 0<=b/a := div_nonneg (by linarith only [hb]) (by linarith only [ha])
  have hfrac : 0<=L/(L+4) := div_nonneg hL (by linarith only [hL])
  change And ((81/256 : Real)*(b/a)*(L/(L+4))*E^2<=(b*B-1)/(a*A-1))
    ((b*B-1)/(a*A-1)<=(b/a)*E^2)
  constructor
  . calc
      _=(b/a)*(((81/256 : Real)*E^2)*(L/(L+4))) := by ring
      _<=(b/a)*((B/A)*(L/(L+4))) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hratio.1 hfrac) hcoef
      _=(b/a)*(B/A)*(L/(L+4)) := by ring
      _<=_ := hmain.1
  . exact hmain.2.trans (mul_le_mul_of_nonneg_left hratio.2 hcoef)

theorem compensatedQuadraticPairTensorPersistence_obstructed
    (s : Finset Nat) (t u : Nat -> Real) (a : Real)
    (hs : forall n, Membership.mem s n -> 17<=n)
    (ht : forall n, Membership.mem s n -> And (-1<=t n) (t n<=1))
    (ha : 2<=a) :
    let E := s.prod (Finset.shiftedEulerFactor 0)
    let z := (343/512 : Real)*E^3
    And (z/(a-z)<= -compensatedQuadraticPairTensorPersistence s t u a 0)
      (-compensatedQuadraticPairTensorPersistence s t u a 0<=E^3/(a-E^3)) := by
  let A := compensatedQuadraticPairDiagonalProduct s t
  let E := s.prod (Finset.shiftedEulerFactor 0)
  let z := (343/512 : Real)*E^3
  have hA : 0<A := compensatedQuadraticPairDiagonalProduct_pos s t hs (fun n hn => (ht n hn).1)
  have hinv := compensatedQuadraticPairInverseDiagonalProduct_bounds s t hs ht
  change And (z<=1/A) (1/A<=E^3) at hinv
  have hE : And (0<E) (E<=1) := ordinary_euler_bounds s hs
  have hm2 := mul_le_mul hE.2 hE.2 hE.1.le (by norm_num : (0 : Real)<=1)
  have hm3 := mul_le_mul hm2 hE.2 hE.1.le (by norm_num : (0 : Real)<=1*1)
  have hE3 : E^3<=1 := by nlinarith only [hm3]
  have hD : 1/A<=1 := hinv.2.trans hE3
  have hA1 : 1<=A := by
    have hp := mul_le_mul_of_nonneg_right hD hA.le
    have hc : (1/A)*A=1 := by field_simp [ne_of_gt hA]
    simpa only [hc,one_mul] using hp
  have hden : 0<a*A-1 := by
    have hp := mul_le_mul_of_nonneg_left hA1 (by linarith only [ha] : 0<=a)
    nlinarith only [hp,ha]
  have had : 0<a-1/A := by linarith only [ha,hD]
  have he : -compensatedQuadraticPairTensorPersistence s t u a 0=(1/A)/(a-1/A) := by
    unfold compensatedQuadraticPairTensorPersistence
    change -((0*compensatedQuadraticPairCrossProduct s t u-1)/(a*A-1))=(1/A)/(a-1/A)
    field_simp [ne_of_gt hA,ne_of_gt hden,ne_of_gt had] ; ring
  change And (z/(a-z)<= -compensatedQuadraticPairTensorPersistence s t u a 0)
    (-compensatedQuadraticPairTensorPersistence s t u a 0<=E^3/(a-E^3))
  rw [he]
  exact And.intro
    (tail_fraction_mono a z (1/A) (by linarith only [ha]) hinv.1 (by linarith only [ha,hD]))
    (tail_fraction_mono a (1/A) (E^3) (by linarith only [ha]) hinv.2
      (by linarith only [ha,hE3]))

end FiniteField
