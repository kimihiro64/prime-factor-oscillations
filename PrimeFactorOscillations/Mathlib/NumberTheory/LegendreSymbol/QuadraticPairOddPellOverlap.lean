/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellMean

/-!
# Exact common odd-Pell endpoint sectors

Common endpoint collapse is the meet of the two odd degrees under gcd.
The trace criterion descends through the algebraic closure over every field
with 2 nonzero. Native split and nonsplit intersection sizes retain both
erased endpoints. These are geometric inputs to the signed defect law.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

def oddPellGcdIndex (k l : Nat) : Nat :=
  ((2*k+1).gcd (2*l+1)-1)/2

theorem oddPell_gcdIndex_degree (k l : Nat) :
    2*oddPellGcdIndex k l+1=(2*k+1).gcd (2*l+1) := by
  have ho : Odd ((2*k+1).gcd (2*l+1)) :=
    Odd.of_dvd_nat (Exists.intro k rfl) (Nat.gcd_dvd_left _ _)
  let a : Nat := Classical.choose ho
  have ha : (2*k+1).gcd (2*l+1)=2*a+1 := Classical.choose_spec ho
  unfold oddPellGcdIndex
  rw [ha]
  omega

theorem oddPell_trace_common_endpoints {K : Type*} [Field K]
    (z : K) (hz : Not (z=0)) (htwo : Not ((2 : K)=0))
    (k l r : Nat) (hg : (2*k+1).gcd (2*l+1)=2*r+1) :
    ((oddPellMap (oddTraceInput z) k=0 \/ oddPellMap (oddTraceInput z) k=-2) /\
      (oddPellMap (oddTraceInput z) l=0 \/ oddPellMap (oddTraceInput z) l=-2)) <->
        (oddPellMap (oddTraceInput z) r=0 \/ oddPellMap (oddTraceInput z) r=-2) := by
  rw [oddPell_map_endpoint_union_iff z hz htwo k,
    oddPell_map_endpoint_union_iff z hz htwo l,
    oddPell_map_endpoint_union_iff z hz htwo r]
  have hg2 : (2*(2*k+1)).gcd (2*(2*l+1))=2*(2*r+1) := by
    rw [Nat.gcd_mul_left,hg]
  constructor
  . intro hp
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hp.1)
      (orderOf_dvd_of_pow_eq_one hp.2)
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [<- hg2]
    exact hd
  . intro hp
    have hd : Dvd.dvd (orderOf z) ((2*(2*k+1)).gcd (2*(2*l+1))) := by
      rw [hg2]
      exact orderOf_dvd_of_pow_eq_one hp
    apply And.intro
    . apply orderOf_dvd_iff_pow_eq_one.mp
      exact Nat.dvd_trans hd (Nat.gcd_dvd_left _ _)
    . apply orderOf_dvd_iff_pow_eq_one.mp
      exact Nat.dvd_trans hd (Nat.gcd_dvd_right _ _)

variable {F : Type*} [Field F]

theorem oddPell_common_endpoints (c : F) (k l r : Nat)
    (hg : (2*k+1).gcd (2*l+1)=2*r+1) (htwo : Not ((2 : F)=0)) :
    ((oddPellMap c k=0 \/ oddPellMap c k=-2) /\
      (oddPellMap c l=0 \/ oddPellMap c l=-2)) <->
        (oddPellMap c r=0 \/ oddPellMap c r=-2) := by
  let K := AlgebraicClosure F
  let f : RingHom F K := algebraMap F K
  have hf2 : f (2 : F)=(2 : K) := by
    rw [show (2 : F)=1+1 by ring]
    simp only [map_add,map_one]
    ring
  have hfn : f (-2 : F)=(-2 : K) := by rw [map_neg,hf2]
  have htwoK : Not ((2 : K)=0) := by
    intro he
    apply htwo
    apply f.injective
    rw [hf2,map_zero]
    exact he
  have hend (j : Nat) :
      (oddPellMap c j=0 \/ oddPellMap c j=-2) <->
        (oddPellMap (f c) j=0 \/ oddPellMap (f c) j=-2) := by
    constructor
    . intro he
      apply Or.elim he
      . intro h0
        apply Or.inl
        simpa only [oddPell_map_map,map_zero] using congrArg f h0
      . intro hn
        apply Or.inr
        simpa only [oddPell_map_map,hfn] using congrArg f hn
    . intro he
      apply Or.elim he
      . intro h0
        apply Or.inl
        apply f.injective
        simpa only [oddPell_map_map,map_zero] using h0
      . intro hn
        apply Or.inr
        apply f.injective
        simpa only [oddPell_map_map,hfn] using hn
  have hex := exists_oddTraceInput (K:=K) htwoK (f c)
  let z : K := Classical.choose hex
  have hz : Not (z=0) /\ oddTraceInput z=f c := Classical.choose_spec hex
  have htrace := oddPell_trace_common_endpoints z hz.1 htwoK k l r hg
  rw [hz.2] at htrace
  rw [hend k,hend l,hend r]
  exact htrace

variable [Fintype F] [DecidableEq F]

theorem oddPell_endpoint_sector_inter (P : F -> Prop) (k l r : Nat)
    (hg : (2*k+1).gcd (2*l+1)=2*r+1) (htwo : Not ((2 : F)=0)) :
    Inter.inter (oddPellEndpointSector P k) (oddPellEndpointSector P l)=
      oddPellEndpointSector P r := by
  classical
  apply Finset.ext
  intro c
  simp only [Finset.mem_inter,oddPellEndpointSector,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  . intro he
    have hc := (oddPell_common_endpoints c k l r hg htwo).mp
      (And.intro he.1.2.2.2 he.2.2.2.2)
    exact And.intro he.1.1
      (And.intro he.1.2.1 (And.intro he.1.2.2.1 hc))
  . intro he
    have hc := (oddPell_common_endpoints c k l r hg htwo).mpr he.2.2.2
    apply And.intro
    . exact And.intro he.1 (And.intro he.2.1 (And.intro he.2.2.1 hc.1))
    . exact And.intro he.1 (And.intro he.2.1 (And.intro he.2.2.1 hc.2))

theorem oddPell_common_sector_counts (k l : Nat) (htwo : Not ((2 : F)=0)) :
    (2*(Inter.inter (oddPellEndpointSector (fun c : F => IsSquare (c*(c+2))) k)
          (oddPellEndpointSector (fun c : F => IsSquare (c*(c+2))) l)).card+2=
      (Fintype.card F-1).gcd (2*((2*k+1).gcd (2*l+1)))) /\
    (2*(Inter.inter (oddPellEndpointSector (fun c : F => Not (IsSquare (c*(c+2)))) k)
          (oddPellEndpointSector (fun c : F => Not (IsSquare (c*(c+2)))) l)).card+2=
      (Fintype.card F+1).gcd (2*((2*k+1).gcd (2*l+1)))) := by
  let r := oddPellGcdIndex k l
  have hg : (2*k+1).gcd (2*l+1)=2*r+1 := (oddPell_gcdIndex_degree k l).symm
  have hc := oddPell_endpoint_split_nonsplit_counts (F:=F) r htwo
  apply And.intro
  . rw [oddPell_endpoint_sector_inter _ k l r hg htwo]
    simpa only [hg] using hc.1
  . rw [oddPell_endpoint_sector_inter _ k l r hg htwo]
    simpa only [hg] using hc.2


private theorem oddPell_half_kernel_card (n A r : Nat)
    (h : 2*A+2=n.gcd (2*(2*r+1))) :
    A+1=n.gcd (2*r+1) := by
  have hd : Dvd.dvd 2 n := by
    apply Nat.dvd_trans ?_ (Nat.gcd_dvd_left n (2*(2*r+1)))
    exact Exists.intro (A+1) (by omega)
  let a : Nat := Classical.choose hd
  have ha : n=2*a := Classical.choose_spec hd
  have he : n.gcd (2*(2*r+1))=2*(n.gcd (2*r+1)) := by
    rw [ha]
    exact oddPell_gcd_twice_index a r
  omega

theorem oddPell_common_sector_sizes (k l : Nat) (htwo : Not ((2 : F)=0)) :
    ((Inter.inter (oddPellEndpointSector (fun c : F => IsSquare (c*(c+2))) k)
        (oddPellEndpointSector (fun c : F => IsSquare (c*(c+2))) l)).card+1=
      (Fintype.card F-1).gcd ((2*k+1).gcd (2*l+1))) /\
    ((Inter.inter (oddPellEndpointSector (fun c : F => Not (IsSquare (c*(c+2)))) k)
        (oddPellEndpointSector (fun c : F => Not (IsSquare (c*(c+2)))) l)).card+1=
      (Fintype.card F+1).gcd ((2*k+1).gcd (2*l+1))) := by
  let r := oddPellGcdIndex k l
  have hg : 2*r+1=(2*k+1).gcd (2*l+1) := oddPell_gcdIndex_degree k l
  have hc := oddPell_common_sector_counts (F:=F) k l htwo
  apply And.intro
  . have hp := oddPell_half_kernel_card (Fintype.card F-1)
      (Inter.inter (oddPellEndpointSector (fun c : F => IsSquare (c*(c+2))) k)
        (oddPellEndpointSector (fun c : F => IsSquare (c*(c+2))) l)).card r
      (by simpa only [hg] using hc.1)
    simpa only [hg] using hp
  . have hp := oddPell_half_kernel_card (Fintype.card F+1)
      (Inter.inter (oddPellEndpointSector (fun c : F => Not (IsSquare (c*(c+2)))) k)
        (oddPellEndpointSector (fun c : F => Not (IsSquare (c*(c+2)))) l)).card r
      (by simpa only [hg] using hc.2)
    simpa only [hg] using hp

end FiniteField
