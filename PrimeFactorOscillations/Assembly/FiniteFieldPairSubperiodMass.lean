/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldPairProductSeparation

/-!
# Positive pair mass on a strict subset of a CRT period

The full mean and the exact joint second moment bound the mass lost
outside any selected finite subset. No row or overlap is removed from
the product energy. The criterion allows an integer sample shorter
than its CRT period, once its image is identified with a subset.
The critical square-height coverage estimate is not asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldPairSubperiodMass
attribute [local instance] Classical.propDecidable

section FiniteMass
variable {J : Type*} [Fintype J] [DecidableEq J]

def missingCount (A : Finset J) : Nat := (Finset.univ \ A).card

theorem mass_deficit_square_bound (A : Finset J) (u : J -> Real) (M : Real)
    (hmean : Finset.univ.sum u=M) :
    (M-A.sum u)^2 <= (missingCount A : Real)*
      (Finset.univ.sum fun j => (u j)^2) := by
  let C := Finset.univ \ A
  have hc := Finset.sum_mul_sq_le_sq_mul_sq C (fun _ => (1 : Real)) u
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
  have htail : (C.sum fun j => (u j)^2) <=
      (Finset.univ.sum fun j => (u j)^2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
    intro j _ _
    exact sq_nonneg _
  have ht := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg C.card)
  have hp : C.sum u+A.sum u=M := by
    rw [<- hmean]
    exact Finset.sum_sdiff (Finset.subset_univ A)
  have he : M-A.sum u=C.sum u := by linarith only [hp]
  rw [he]
  change (C.sum u)^2 <= (C.card : Real)*
    (Finset.univ.sum fun j => (u j)^2)
  exact hc.trans ht

theorem subset_mass_lower (A : Finset J) (u : J -> Real) (M : Real)
    (hmean : Finset.univ.sum u=M) :
    M-Real.sqrt ((missingCount A : Real)*
      (Finset.univ.sum fun j => (u j)^2)) <= A.sum u := by
  have hb := mass_deficit_square_bound A u M hmean
  have hn : 0 <= (missingCount A : Real)*
      (Finset.univ.sum fun j => (u j)^2) := by positivity
  have hs := Real.sq_sqrt hn
  have hr := Real.sqrt_nonneg ((missingCount A : Real)*
      (Finset.univ.sum fun j => (u j)^2))
  nlinarith only [hb,hs,hr]

theorem subset_mass_positive (A : Finset J) (u : J -> Real) (M : Real)
    (hM : 0 < M) (hmean : Finset.univ.sum u=M)
    (hroom : (missingCount A : Real)*
      (Finset.univ.sum fun j => (u j)^2)<M^2) :
    0 < A.sum u := by
  have hb := mass_deficit_square_bound A u M hmean
  by_contra hbad
  have hA : A.sum u<=0 := le_of_not_gt hbad
  have hp := mul_nonneg hM.le (neg_nonneg.mpr hA)
  nlinarith only [hb,hroom,hp,sq_nonneg (A.sum u)]

end FiniteMass

open _root_.FiniteField _root_.FiniteField.QuadraticPairTwistJoint
open FiniteFieldRawHellinger
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (K : I -> Type*) [forall i, Field (K i)] [forall i, Fintype (K i)]
  [forall i, DecidableEq (K i)]

def rawPacket (h : (i : I) -> K i) (x : (i : I) -> K i) : Real :=
  purePacket K (fun i => rawDensity (h i)) x

def rawEnergy (h : (i : I) -> K i) : Real :=
  Finset.univ.prod fun i => QuadraticPairEnergy.moment
    (Fintype.card (K i) : Real) (quadraticPairOffset (h i) : Real)

theorem raw_packet_mean (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real)) :
    Finset.univ.sum (rawPacket K h)=(Fintype.card ((i : I) -> K i) : Real) := by
  calc
    _ = Finset.univ.prod (fun i => Finset.univ.sum (rawDensity (h i))) := by
      unfold rawPacket purePacket
      exact (Fintype.prod_sum (fun i c => rawDensity (h i) c)).symm
    _ = Finset.univ.prod (fun i => (Fintype.card (K i) : Real)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact sum_raw_density (hodd i) (h i) (hh i) (hq i)
    _ = _ := by simp only [Fintype.card_pi,Nat.cast_prod]

theorem raw_packet_square_sum (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real)) :
    (Finset.univ.sum fun x => (rawPacket K h x)^2)=
      (Fintype.card ((i : I) -> K i) : Real)*rawEnergy K h := by
  let M : Real := Fintype.card ((i : I) -> K i)
  have hM : 0 < M := by
    dsimp only [M]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ((i : I) -> K i))
  have hc : M=Finset.univ.prod (fun i => (Fintype.card (K i) : Real)) := by
    simp only [M,Fintype.card_pi,Nat.cast_prod]
  have hn : (Finset.univ.prod fun i => 1/(Fintype.card (K i) : Real))=1/M := by
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const_one]
    rw [hc]
  have he := QuadraticPairEnergy.normalized_packet_energy K h hodd hh hq
  change (Finset.univ.prod fun i => 1/(Fintype.card (K i) : Real))*
    (Finset.univ.sum fun x => (rawPacket K h x)^2)=rawEnergy K h at he
  rw [hn] at he
  field_simp [ne_of_gt hM] at he
  change (Finset.univ.sum fun x => (rawPacket K h x)^2)=M*rawEnergy K h
  nlinarith only [he]

theorem raw_subset_mass_lower (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real))
    (A : Finset ((i : I) -> K i)) :
    (Fintype.card ((i : I) -> K i) : Real)-
      Real.sqrt ((missingCount A : Real)*
        ((Fintype.card ((i : I) -> K i) : Real)*rawEnergy K h)) <=
          A.sum (rawPacket K h) := by
  have he := subset_mass_lower A (rawPacket K h)
    (Fintype.card ((i : I) -> K i) : Real) (raw_packet_mean K h hodd hh hq)
  rw [raw_packet_square_sum K h hodd hh hq] at he
  exact he

theorem raw_subset_mass_positive (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real))
    (A : Finset ((i : I) -> K i))
    (hroom : (missingCount A : Real)*rawEnergy K h<
      (Fintype.card ((i : I) -> K i) : Real)) :
    0 < A.sum (rawPacket K h) := by
  let M : Real := Fintype.card ((i : I) -> K i)
  have hM : 0 < M := by
    dsimp only [M]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ((i : I) -> K i))
  apply subset_mass_positive A (rawPacket K h) M hM (raw_packet_mean K h hodd hh hq)
  rw [raw_packet_square_sum K h hodd hh hq]
  have ht := mul_lt_mul_of_pos_left hroom hM
  change M*((missingCount A : Real)*rawEnergy K h)<M*M at ht
  change (missingCount A : Real)*(M*rawEnergy K h)<M^2
  nlinarith only [ht]

end PrimeFactorOscillations.FiniteFieldPairSubperiodMass
