/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.GCongr
import PrimeFactorOscillations.Proof.DetectorPackets.RamanujanIncidenceGram

/-!
# RamanujanIncidenceEstimate

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

set_option maxHeartbeats 1800000

noncomputable section
namespace OAI.SevenEighths.RamanujanIncidenceGram
open scoped Classical BigOperators
open IdealMobiusDivisorSum CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def sharedMass (A Q : Id) : Real :=
  (idealDivisors Q).sum fun D=>if Dvd.dvd D A then (D.absNorm:Real) else 0

theorem sharedMass_nonneg (A Q : Id) : 0<=sharedMass A Q := by
  unfold sharedMass
  exact Finset.sum_nonneg fun D hD=>by split_ifs <;> positivity

theorem sharedMass_symm (A Q : Id) (hA : Not (A=0)) (hQ : Not (Q=0)) :
    sharedMass A Q=sharedMass Q A := by
  unfold sharedMass
  rw [<-Finset.sum_filter,<-Finset.sum_filter]
  congr 1
  ext D
  simp only [Finset.mem_filter,mem_idealDivisors hA,mem_idealDivisors hQ]
  exact and_comm

theorem multiples_harmonic (C : Finset Id) (Q : Real)
    (hC0 : forall I, Membership.mem C I -> Not (I=0))
    (hC : forall I, Membership.mem C I -> (I.absNorm:Real)<=Q)
    (D : Id) (hD : Not (D=0)) :
    (C.sum fun I=>if Dvd.dvd D I then (D.absNorm:Real)/(I.absNorm:Real) else 0)<=
      256*(columnDyadicLength Q+1:Real) := by
  let T := C.filter fun I=>Dvd.dvd D I
  let q (I : T) : Id := Classical.choose (Finset.mem_filter.mp I.property).2
  have hq (I : T) : I.val=D*q I := Classical.choose_spec (Finset.mem_filter.mp I.property).2
  have hq0 (I : T) : Not (q I=0) := by
    intro he
    exact hC0 I.val (Finset.mem_filter.mp I.property).1
      (by rw [hq I,he,mul_zero])
  have hDn : (1:Real)<=(D.absNorm:Real) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hqN (I : T) : ((q I).absNorm:Real)<=Q := by
    have hh := hC I.val (Finset.mem_filter.mp I.property).1
    rw [hq I,map_mul,Nat.cast_mul] at hh
    have hn : (0:Real)<=((q I).absNorm:Real) := Nat.cast_nonneg _
    nlinarith
  let F := Finset.univ.image q
  have hi : Function.Injective q := by
    intro I J he
    apply Subtype.ext
    exact (hq I).trans ((congrArg (fun x:Id=>D*x) he).trans (hq J).symm)
  have hf0 (J : Id) (hJ : Membership.mem F J) : Not (J=0) := by
    choose I hI he using Finset.mem_image.mp hJ
    simpa only [<-he] using hq0 I
  have hfN (J : Id) (hJ : Membership.mem F J) : (J.absNorm:Real)<=Q := by
    choose I hI he using Finset.mem_image.mp hJ
    simpa only [<-he] using hqN I
  have he :
      (C.sum fun I=>if Dvd.dvd D I then (D.absNorm:Real)/(I.absNorm:Real) else 0)=
        F.sum (fun J=>1/(J.absNorm:Real)) := by
    rw [<-Finset.sum_filter]
    change T.sum (fun I=>(D.absNorm:Real)/(I.absNorm:Real))=_
    rw [<-Finset.sum_coe_sort T (fun I=>(D.absNorm:Real)/(I.absNorm:Real))]
    change _=(Finset.univ.image q).sum (fun J=>1/(J.absNorm:Real))
    rw [Finset.sum_image (fun I _ J _ he=>hi he)]
    apply Finset.sum_congr rfl
    intro I hI
    rw [hq I,map_mul,Nat.cast_mul]
    have hD0 : Not ((D.absNorm:Real)=0) := ne_of_gt (lt_of_lt_of_le zero_lt_one hDn)
    have hq0N : Not (((q I).absNorm:Real)=0) := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (hq0 I)
    field_simp
  rw [he]
  exact finite_inverse_norm_sum F Q hf0 hfN

theorem sharedMass_column (R : Finset Id) (M : Real) (hM : 1<=M)
    (hR0 : forall A, Membership.mem R A -> Not (A=0))
    (hR : forall A, Membership.mem R A -> (A.absNorm:Real)<=M)
    (Q : Id) (hQ : Not (Q=0)) :
    (R.sum fun A=>sharedMass A Q)<=128*M*((idealDivisors Q).card:Real) := by
  unfold sharedMass
  rw [Finset.sum_comm]
  calc
    _ <= (idealDivisors Q).sum (fun _=>128*M) := by
      apply Finset.sum_le_sum
      intro D hD
      have hD0 := IdealDivisorBound.divisor_ne_zero hQ hD
      have hh := multiples_weighted_count R M hM hR0 hR D hD0
      have he : (R.sum fun A=>if Dvd.dvd D A then (D.absNorm:Real) else 0)=
          ((R.filter fun A=>Dvd.dvd D A).card:Real)*(D.absNorm:Real) := by
        rw [<-Finset.sum_filter]
        simp
      rwa [he]
    _ = _ := by simp;ring

theorem sharedMass_row (C : Finset Id) (Q : Real)
    (hC0 : forall I, Membership.mem C I -> Not (I=0))
    (hC : forall I, Membership.mem C I -> (I.absNorm:Real)<=Q)
    (A : Id) (hA : Not (A=0)) :
    (C.sum fun I=>sharedMass A I/(I.absNorm:Real))<=
      ((idealDivisors A).card:Real)*(256*(columnDyadicLength Q+1:Real)) := by
  calc
    _ = C.sum (fun I=>(idealDivisors A).sum fun D=>
        if Dvd.dvd D I then (D.absNorm:Real)/(I.absNorm:Real) else 0) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [sharedMass_symm A I hA (hC0 I hI),sharedMass,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro D hD
      split_ifs <;> simp
    _ = (idealDivisors A).sum (fun D=>C.sum fun I=>
        if Dvd.dvd D I then (D.absNorm:Real)/(I.absNorm:Real) else 0) := Finset.sum_comm
    _ <= (idealDivisors A).sum (fun _=>256*(columnDyadicLength Q+1:Real)) := by
      apply Finset.sum_le_sum
      intro D hD
      exact multiples_harmonic C Q hC0 hC D (IdealDivisorBound.divisor_ne_zero hA hD)
    _ = _ := by simp

end OAI.SevenEighths.RamanujanIncidenceGram
