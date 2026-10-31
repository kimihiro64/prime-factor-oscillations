/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldTwistHellinger
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistJoint

/-!
# Finite products retain the raw pair-law separation

Affinity tensorizes on the complete finite product space. The original
quadratic-pair law loses affinity at the reciprocal-cardinality rate,
whereas the trace-free law differs from flat admissibility by at most
the sum of the inverse-square errors. This is a complete-product theorem;
it asserts no positivity for an incomplete integer interval.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldPairProductSeparation
attribute [local instance] Classical.propDecidable
open _root_.FiniteField.QuadraticPairTwistJoint
open FiniteFieldPairAffinity FiniteFieldRawHellinger FiniteFieldTwistHellinger
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (K : I -> Type*) [forall i, Fintype (K i)] [forall i, DecidableEq (K i)]

def packetAffinity (u v : (i : I) -> K i -> Real) : Real :=
  packetMean K (fun x => Real.sqrt (purePacket K u x*purePacket K v x))

theorem sqrt_product (s : Finset I) (f : I -> Real)
    (hf : forall i, Membership.mem s i -> 0<=f i) :
    Real.sqrt (s.prod f)=s.prod (fun i => Real.sqrt (f i)) := by
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert i s hi ih =>
    intro hf
    rw [Finset.prod_insert hi,Real.sqrt_mul (hf i (Finset.mem_insert_self i s)),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)),Finset.prod_insert hi]

theorem packet_affinity_factorization (u v : (i : I) -> K i -> Real)
    (hu : forall i c, 0<=u i c) (hv : forall i c, 0<=v i c) :
    packetAffinity K u v =
      Finset.univ.prod (fun i => affinity (Fintype.card (K i) : Real) (u i) (v i)) := by
  have he (x : (i : I) -> K i) :
      Real.sqrt (purePacket K u x*purePacket K v x)=
        purePacket K (fun i c => Real.sqrt (u i c*v i c)) x := by
    unfold purePacket
    rw [<- Finset.prod_mul_distrib]
    exact sqrt_product Finset.univ _ (fun i _ => mul_nonneg (hu i (x i)) (hv i (x i)))
  unfold packetAffinity
  simp_rw [he]
  exact packetMean_pure K _

theorem affinity_product_exp_bound (a b : I -> Real)
    (ha : forall i, 0<=a i) (hb : forall i, a i<=1-b i) :
    Finset.univ.prod a<=Real.exp (-(Finset.univ.sum b)) := by
  have hc (s : Finset I) : s.prod a<=s.prod (fun i => Real.exp (-b i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi,Finset.prod_insert hi]
      have hei := Real.add_one_le_exp (-b i)
      have hai : a i<=Real.exp (-b i) := by linarith only [hb i,hei]
      have hp : 0<=s.prod a := Finset.prod_nonneg (fun j _ => ha j)
      calc
        _ <= Real.exp (-b i)*s.prod a := mul_le_mul_of_nonneg_right hai hp
        _ <= _ := mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
  calc
    _ <= Finset.univ.prod (fun i => Real.exp (-b i)) := hc Finset.univ
    _ = _ := by rw [<- Real.exp_sum,Finset.sum_neg_distrib]

theorem product_defect_bound (s : Finset I) (a e : I -> Real)
    (ha0 : forall i, Membership.mem s i -> 0<=a i)
    (ha1 : forall i, Membership.mem s i -> a i<=1)
    (he : forall i, Membership.mem s i -> 1-a i<=e i) :
    And (0<=s.prod a) (And (s.prod a<=1) (1-s.prod a<=s.sum e)) := by
  revert ha0 ha1 he
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert i s hi ih =>
    intro ha0 ha1 he
    have h0 := ha0 i (Finset.mem_insert_self i s)
    have h1 := ha1 i (Finset.mem_insert_self i s)
    have hei := he i (Finset.mem_insert_self i s)
    have ht := ih
      (fun j hj => ha0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
      (fun j hj => he j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    refine And.intro (mul_nonneg h0 ht.1) (And.intro ?_ ?_)
    . nlinarith only [h1,ht.2.1,mul_nonneg h0 (sub_nonneg.mpr ht.2.1)]
    . have hp := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr ht.2.1)
      nlinarith only [ht.2.2,hei,hp]

variable [forall i, Field (K i)]

theorem raw_flat_packet_upper (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real)) :
    packetAffinity K (fun i => rawDensity (h i)) (fun i => flatDensity (h i)) <=
      Real.exp (-(Finset.univ.sum fun i => 1/(64*(Fintype.card (K i) : Real)))) := by
  rw [packet_affinity_factorization K _ _
    (fun i c => (raw_density_bounds (hodd i) (h i) (hh i) (hq i) c).1)
    (fun i c => (flat_density_bounds (h i) (hq i) c).1)]
  apply affinity_product_exp_bound
  . intro i
    exact affinity_nonneg _ (by have hi := hq i; linarith only [hi]) _ _
  . intro i
    exact raw_flat_affinity_upper (hodd i) (h i) (hh i) (hq i)

theorem raw_twist_packet_upper (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hh : forall i, Not (h i=0)) (hq : forall i, 2048<=(Fintype.card (K i) : Real)) :
    packetAffinity K (fun i => rawDensity (h i)) (fun i => twistDensity (h i)) <=
      Real.exp (-(Finset.univ.sum fun i => 1/(256*(Fintype.card (K i) : Real)))) := by
  have h16 (i : I) : 16<=(Fintype.card (K i) : Real) := by
    have hi := hq i
    linarith only [hi]
  rw [packet_affinity_factorization K _ _
    (fun i c => (raw_density_bounds (hodd i) (h i) (hh i) (h16 i) c).1)
    (fun i c => twist_density_nonneg (h i) (hh i) (h16 i) c)]
  apply affinity_product_exp_bound
  . intro i
    exact affinity_nonneg _ (by have hi := hq i; linarith only [hi]) _ _
  . intro i
    exact raw_twist_affinity_upper (hodd i) (h i) (hh i) (hq i)

theorem twist_flat_packet_lower (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i)=2))
    (hh : forall i, Not (h i=0)) (hq : forall i, 16<=(Fintype.card (K i) : Real)) :
    1-(Finset.univ.sum fun i => 5/(Fintype.card (K i) : Real)^2) <=
      packetAffinity K (fun i => twistDensity (h i)) (fun i => flatDensity (h i)) := by
  rw [packet_affinity_factorization K _ _
    (fun i c => twist_density_nonneg (h i) (hh i) (hq i) c)
    (fun i c => (flat_density_bounds (h i) (hq i) c).1)]
  have hb := product_defect_bound Finset.univ
    (fun i => affinity (Fintype.card (K i) : Real) (twistDensity (h i)) (flatDensity (h i)))
    (fun i => 5/(Fintype.card (K i) : Real)^2)
    (fun i _ => affinity_nonneg _ (by have hi := hq i; linarith only [hi]) _ _)
    (fun i _ => affinity_le_one _ _ _
      (twist_density_nonneg (h i) (hh i) (hq i))
      (fun c => (flat_density_bounds (h i) (hq i) c).1)
      (by have hi := hq i; linarith only [hi])
      (sum_twist_density (hodd i) (h i) (hh i) (hq i))
      (sum_flat_density (h i) (hh i) (hq i)))
    (fun i _ => twist_flat_affinity_defect_upper (hodd i) (h i) (hh i) (hq i))
  linarith only [hb.2.2]

end PrimeFactorOscillations.FiniteFieldPairProductSeparation
