/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldCompensatedKernel
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTensorPersistence

/-!
# Tensor persistence of the actual shared-label compensated law

A coordinate consists of a class label and one field element. Both
observations use that same label. Its mass retains the distinct squared
normalizers, and unit pullback aligns the physical shifts. Exact finite
tensorization identifies the full centered correlation with the proved
Euler-square or obstructed Euler-cube comparison. No short integer-window
positivity estimate is assumed or asserted.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldTensorPersistence
attribute [local instance] Classical.propDecidable
open _root_.FiniteField FiniteFieldRawHellinger FiniteFieldRawPairCovariance
open FiniteFieldCompensatedKernel
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def atomWeight (h a : F) (x : Sum F F) : Real :=
  let q : Real := Fintype.card F
  let D : F -> Real := fun b => q-(quadraticPairOffset b : Real)
  Sum.elim (fun _ => (1/q)*(D h)^2/((D h)^2+(D (a*h))^2))
    (fun _ => (1/q)*(D (a*h))^2/((D h)^2+(D (a*h))^2)) x

def atomValue (h a k : F) (x : Sum F F) : Real :=
  Sum.elim (fun c => rawDensity h (c+k))
    (fun c => rawDensity (a*h) (a*(c+k))) x

theorem atomic_sum (h a : F) (f g : F -> Real) :
    (Finset.univ.sum fun x : Sum F F => atomWeight h a x*Sum.elim f g x)=
      moment h a f g := by
  rw [Fintype.sum_sum_type]
  unfold atomWeight moment
  dsimp only [Sum.elim_inl,Sum.elim_inr]
  rw [<- Finset.mul_sum,<- Finset.mul_sum,Finset.sum_add_distrib,
    <- Finset.mul_sum,<- Finset.mul_sum]
  ring

theorem atom_weight_nonneg (h a : F) (x : Sum F F) : 0<=atomWeight h a x := by
  have hq : 0<=(Fintype.card F : Real) := by positivity
  cases x <;> unfold atomWeight <;> dsimp only [Sum.elim_inl,Sum.elim_inr] <;> positivity

theorem atom_weight_one (h a : F) (hh : Not (h=0))
    (hq : 16<=(Fintype.card F : Real)) :
    (Finset.univ.sum fun x : Sum F F => atomWeight h a x)=1 := by
  let q : Real := Fintype.card F
  let D : F -> Real := fun b => q-(quadraticPairOffset b : Real)
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have hd : 0<(D h)^2+(D (a*h))^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_pos (denominator_pos h hh hq)) (sq_nonneg _)
  have he := atomic_sum h a (fun _ => 1) (fun _ => 1)
  have hv (x : Sum F F) : Sum.elim (fun _ : F => (1 : Real)) (fun _ : F => 1) x=1 := by
    cases x <;> rfl
  simp_rw [hv,mul_one] at he
  rw [he]
  unfold moment
  dsimp only
  simp only [mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change (1/q)*(q*((D h)^2+(D (a*h))^2))/((D h)^2+(D (a*h))^2)=1
  field_simp [ne_of_gt hq0,ne_of_gt hd]

theorem atom_value_mean (hF : Not (ringChar F=2)) (h a k : F)
    (hh : Not (h=0)) (ha : Not (a=0))
    (hq : 16<=(Fintype.card F : Real)) :
    (Finset.univ.sum fun x : Sum F F => atomWeight h a x*atomValue h a k x)=1 := by
  let q : Real := Fintype.card F
  let D : F -> Real := fun b => q-(quadraticPairOffset b : Real)
  let e : Equiv F F :=
    { toFun := fun c => c+k
      invFun := fun c => c-k
      left_inv := by intro c; ring
      right_inv := by intro c; ring }
  let f : Equiv F F :=
    { toFun := fun c => a*(c+k)
      invFun := fun c => c/a-k
      left_inv := by intro c; field_simp [ha]; ring
      right_inv := by intro c; field_simp [ha]; ring }
  have he := Equiv.sum_comp e (rawDensity h)
  have hf := Equiv.sum_comp f (rawDensity (a*h))
  rw [sum_raw_density hF h hh hq] at he
  rw [sum_raw_density hF (a*h) (mul_ne_zero ha hh) hq] at hf
  change (Finset.univ.sum fun c : F => rawDensity h (c+k))=q at he
  change (Finset.univ.sum fun c : F => rawDensity (a*h) (a*(c+k)))=q at hf
  have hq0 : 0<q := by dsimp only [q]; linarith only [hq]
  have hd : 0<(D h)^2+(D (a*h))^2 := add_pos_of_pos_of_nonneg
    (sq_pos_of_pos (denominator_pos h hh hq)) (sq_nonneg _)
  change (Finset.univ.sum fun x : Sum F F => atomWeight h a x*
    Sum.elim (fun c => rawDensity h (c+k)) (fun c => rawDensity (a*h) (a*(c+k))) x)=1
  rw [atomic_sum]
  unfold moment
  dsimp only
  rw [Finset.sum_add_distrib,<- Finset.mul_sum,<- Finset.mul_sum,he,hf]
  change (1/q)*((D h)^2*q+(D (a*h))^2*q)/((D h)^2+(D (a*h))^2)=1
  field_simp [ne_of_gt hq0,ne_of_gt hd]

theorem atomic_kernel (h a k : F) :
    (Finset.univ.sum fun x : Sum F F =>
      atomWeight h a x*atomValue h a 0 x*atomValue h a k x)=kernel h a k := by
  have he (x : Sum F F) :
      atomWeight h a x*atomValue h a 0 x*atomValue h a k x=
      atomWeight h a x*Sum.elim
        (fun c => rawDensity h c*rawDensity h (c+k))
        (fun c => rawDensity (a*h) (a*c)*rawDensity (a*h) (a*(c+k))) x := by
    cases x <;> simp only [atomValue,Sum.elim_inl,Sum.elim_inr,add_zero] <;> ring
  simp_rw [he]
  exact atomic_sum h a _ _

section Packet
variable (s : Finset Nat) (K : Nat -> Type*)
  [forall n, Field (K n)] [forall n, Fintype (K n)] [forall n, DecidableEq (K n)]
  (h r : (n : Nat) -> K n)

def packetKernel (k : (n : Nat) -> K n) : Real :=
  Finset.univ.sum fun x : (n : s) -> Sum (K n) (K n) =>
    Finset.univ.prod fun n : s =>
      atomWeight (h n) (r n) (x n)*atomValue (h n) (r n) 0 (x n)*
        atomValue (h n) (r n) (k n) (x n)

theorem packet_kernel (k : (n : Nat) -> K n) :
    packetKernel s K h r k=s.prod (fun n => kernel (h n) (r n) (k n)) := by
  unfold packetKernel
  rw [<- Fintype.prod_sum (fun (n : s) (x : Sum (K n) (K n)) =>
    atomWeight (h n) (r n) x*atomValue (h n) (r n) 0 x*
      atomValue (h n) (r n) (k n) x)]
  simp_rw [atomic_kernel]
  exact Finset.prod_coe_sort s (fun n => kernel (h n) (r n) (k n))

theorem packet_shifted_kernel (x y : (n : Nat) -> K n) :
    (Finset.univ.sum fun z : (n : s) -> Sum (K n) (K n) =>
      Finset.univ.prod fun n : s =>
        atomWeight (h n) (r n) (z n)*atomValue (h n) (r n) (x n) (z n)*
          atomValue (h n) (r n) (y n) (z n))=
      s.prod (fun n => kernel (h n) (r n) (y n-x n)) := by
  rw [<- Fintype.prod_sum (fun (n : s) (z : Sum (K n) (K n)) =>
    atomWeight (h n) (r n) z*atomValue (h n) (r n) (x n) z*
      atomValue (h n) (r n) (y n) z)]
  have he (n : s) :
      (Finset.univ.sum fun z : Sum (K n) (K n) =>
        atomWeight (h n) (r n) z*atomValue (h n) (r n) (x n) z*
          atomValue (h n) (r n) (y n) z)=kernel (h n) (r n) (y n-x n) := by
    have hi (z : Sum (K n) (K n)) :
        atomWeight (h n) (r n) z*atomValue (h n) (r n) (x n) z*
          atomValue (h n) (r n) (y n) z=
        atomWeight (h n) (r n) z*Sum.elim
          (fun c => rawDensity (h n) (c+x n)*rawDensity (h n) (c+y n))
          (fun c => rawDensity (r n*h n) (r n*(c+x n))*
            rawDensity (r n*h n) (r n*(c+y n))) z := by
      cases z <;> simp only [atomValue,Sum.elim_inl,Sum.elim_inr] <;> ring
    simp_rw [hi]
    rw [atomic_sum]
    exact kernel_shifted (h n) (r n) (x n) (y n)
  simp_rw [he]
  exact Finset.prod_coe_sort s (fun n => kernel (h n) (r n) (y n-x n))

theorem packet_shifted_diagonal (x : (n : Nat) -> K n) :
    (Finset.univ.sum fun z : (n : s) -> Sum (K n) (K n) =>
      Finset.univ.prod fun n : s =>
        atomWeight (h n) (r n) (z n)*atomValue (h n) (r n) (x n) (z n)*
          atomValue (h n) (r n) (x n) (z n))=
      packetKernel s K h r (fun n => (0 : K n)) := by
  rw [packet_shifted_kernel,packet_kernel]
  simp only [sub_self]

theorem packet_weight_one
    (hh : forall n, Membership.mem s n -> Not (h n=0))
    (hq : forall n, Membership.mem s n -> 16<=(Fintype.card (K n) : Real)) :
    (Finset.univ.sum fun x : (n : s) -> Sum (K n) (K n) =>
      Finset.univ.prod fun n : s => atomWeight (h n) (r n) (x n))=1 := by
  rw [<- Fintype.prod_sum]
  have he (n : s) : (Finset.univ.sum fun x : Sum (K n) (K n) =>
      atomWeight (h n) (r n) x)=1 := atom_weight_one (h n) (r n)
        (hh n n.property) (hq n n.property)
  simp_rw [he]
  simp

theorem packet_value_mean (k : (n : Nat) -> K n)
    (hF : forall n, Membership.mem s n -> Not (ringChar (K n)=2))
    (hh : forall n, Membership.mem s n -> Not (h n=0))
    (hr : forall n, Membership.mem s n -> Not (r n=0))
    (hq : forall n, Membership.mem s n -> 16<=(Fintype.card (K n) : Real)) :
    (Finset.univ.sum fun x : (n : s) -> Sum (K n) (K n) =>
      Finset.univ.prod fun n : s =>
        atomWeight (h n) (r n) (x n)*atomValue (h n) (r n) (k n) (x n))=1 := by
  rw [<- Fintype.prod_sum (fun (n : s) (x : Sum (K n) (K n)) =>
    atomWeight (h n) (r n) x*atomValue (h n) (r n) (k n) x)]
  have he (n : s) : (Finset.univ.sum fun x : Sum (K n) (K n) =>
      atomWeight (h n) (r n) x*atomValue (h n) (r n) (k n) x)=1 :=
    atom_value_mean (hF n n.property) (h n) (r n) (k n)
      (hh n n.property) (hr n n.property) (hq n n.property)
  simp_rw [he]
  simp

def centeredPacketPersistence (a b : Real) : Real :=
  (b*packetKernel s K h r h-1)/(a*packetKernel s K h r (fun n => (0 : K n))-1)

variable
  (hs : forall n, Membership.mem s n -> 17<=n)
  (hcard : forall n, Membership.mem s n -> Fintype.card (K n)=n)
  (hF : forall n, Membership.mem s n -> Not (ringChar (K n)=2))
  (hh : forall n, Membership.mem s n -> Not (h n=0))
  (hr : forall n, Membership.mem s n -> (quadraticChar (K n)) (r n)=-1)

omit [forall n, Field (K n)] [forall n, DecidableEq (K n)] in
include hs hcard in
private theorem field_size (n : Nat) (hn : Membership.mem s n) :
    16<=(Fintype.card (K n) : Real) := by
  rw [hcard n hn]
  have h:=hs n hn
  norm_cast
  omega

include hs hcard hF hh hr in
theorem packet_diagonal_model :
    packetKernel s K h r (fun n => (0 : K n))=
      compensatedQuadraticPairDiagonalProduct s
        (fun n => ((quadraticChar (K n)) (-1) : Real)) := by
  rw [packet_kernel]
  apply Finset.prod_congr rfl
  intro n hn
  simpa only [compensatedQuadraticPairDiagonalMoment,hcard n hn] using
    kernel_zero_eq_model (hF n hn) (h n) (r n) (hh n hn) (hr n hn)
      (field_size s K hs hcard n hn)

include hs hcard hF hh hr in
theorem packet_adjacent_model :
    packetKernel s K h r h=compensatedQuadraticPairCrossProduct s
      (fun n => ((quadraticChar (K n)) (-1) : Real))
      (fun n => ((quadraticChar (K n)) (2 : K n) : Real)) := by
  rw [packet_kernel]
  apply Finset.prod_congr rfl
  intro n hn
  have ha : Not (r n=0) := by
    intro hz
    have hc := hr n hn
    rw [hz] at hc
    norm_num at hc
  rw [kernel_adjacent (h n) (r n) ha]
  simpa only [hcard n hn] using
    twistCompensatedCovariance_eq_model (hF n hn) (h n) (r n) (hh n hn) (hr n hn)
      (field_size s K hs hcard n hn)

private theorem character_bounds (n : Nat) (x : K n) (hx : Not (x=0)) :
    And (-1<=((quadraticChar (K n)) x : Real)) (((quadraticChar (K n)) x : Real)<=1) := by
  have he : ((quadraticChar (K n)) x : Real)^2=1 := by
    exact_mod_cast quadraticChar_sq_one hx
  constructor <;> nlinarith only [he,
    sq_nonneg (((quadraticChar (K n)) x : Real)-1),
    sq_nonneg (((quadraticChar (K n)) x : Real)+1)]

include hs hcard hF hh hr in
theorem centered_packet_compatible (a b : Real) (ha : 2<=a) (hb : 1<=b) (hba : b<=a) :
    let E := s.prod (Finset.shiftedEulerFactor 0)
    let L := s.sum (fun n => 1/(n : Real))
    And ((81/256 : Real)*(b/a)*(L/(L+4))*E^2<=centeredPacketPersistence s K h r a b)
      (centeredPacketPersistence s K h r a b<=(b/a)*E^2) := by
  unfold centeredPacketPersistence
  rw [packet_diagonal_model s K h r hs hcard hF hh hr,
    packet_adjacent_model s K h r hs hcard hF hh hr]
  exact compensatedQuadraticPairTensorPersistence_compatible s _ _ a b hs
    (fun n _ => character_bounds K n (-1) (neg_ne_zero.mpr one_ne_zero))
    (fun n hn => character_bounds K n (2 : K n) (two_ne_zero_of_odd (hF n hn))) ha hb hba

include hs hcard hF hh hr in
theorem centered_packet_obstructed (a : Real) (ha : 2<=a) :
    let E := s.prod (Finset.shiftedEulerFactor 0)
    let z := (343/512 : Real)*E^3
    And (z/(a-z)<= -centeredPacketPersistence s K h r a 0)
      (-centeredPacketPersistence s K h r a 0<=E^3/(a-E^3)) := by
  unfold centeredPacketPersistence
  rw [packet_diagonal_model s K h r hs hcard hF hh hr,
    packet_adjacent_model s K h r hs hcard hF hh hr]
  exact compensatedQuadraticPairTensorPersistence_obstructed s _ _ a hs
    (fun n _ => character_bounds K n (-1) (neg_ne_zero.mpr one_ne_zero)) ha

end Packet
end PrimeFactorOscillations.FiniteFieldTensorPersistence
