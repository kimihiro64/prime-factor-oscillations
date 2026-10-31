/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Totient
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellOverlap

/-!
# Exact signed odd-Pell defect energy

The actual probability loss obeys a pointwise gcd meet law. Its bilinear
moments retain both native endpoint sectors and the complete all-shift
normalization. A classical totient decomposition supplies the primitive
divisor coordinates used by the finite signed energy law.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

def oddPellPrimitiveDivisors (N : Nat) : Finset Nat :=
  N.divisors.filter (fun d => 1<d /\ Odd d)

theorem oddPell_totient_gcd_kernel (N k l : Nat) (hN : 0<N) :
    (oddPellPrimitiveDivisors N).sum
      (fun d => if Dvd.dvd d (2*k+1) /\ Dvd.dvd d (2*l+1)
        then (d.totient : Real) else 0)=
      ((N.gcd ((2*k+1).gcd (2*l+1)) : Nat) : Real)-1 := by
  classical
  let g := N.gcd ((2*k+1).gcd (2*l+1))
  have hgN : Dvd.dvd g N := Nat.gcd_dvd_left _ _
  have hgm : Dvd.dvd g (2*k+1) :=
    Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  have hgn : Dvd.dvd g (2*l+1) :=
    Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
  have hg0 : Not (g=0) := by
    intro he
    rw [he] at hgN
    have hzero : N=0 := by simpa using hgN
    omega
  have hset :
      (oddPellPrimitiveDivisors N).filter
        (fun d => Dvd.dvd d (2*k+1) /\ Dvd.dvd d (2*l+1))=
          g.divisors.erase 1 := by
    apply Finset.ext
    intro d
    simp only [oddPellPrimitiveDivisors,Finset.mem_filter,Nat.mem_divisors,Finset.mem_erase]
    constructor
    . intro hd
      apply And.intro (by omega)
      apply And.intro
      . exact Nat.dvd_gcd hd.1.1.1 (Nat.dvd_gcd hd.2.1 hd.2.2)
      . exact hg0
    . intro hd
      have hdN : Dvd.dvd d N := Nat.dvd_trans hd.2.1 hgN
      have hdm : Dvd.dvd d (2*k+1) := Nat.dvd_trans hd.2.1 hgm
      have hdn : Dvd.dvd d (2*l+1) := Nat.dvd_trans hd.2.1 hgn
      have hd0 : Not (d=0) := by
        intro he
        rw [he] at hdN
        have hz : N=0 := by simpa using hdN
        omega
      have hd1 : 1<d := by omega
      have hodd : Odd d := Odd.of_dvd_nat (Exists.intro k rfl) hdm
      exact And.intro
        (And.intro (And.intro hdN (by omega)) (And.intro hd1 hodd))
        (And.intro hdm hdn)
  have hmem : Membership.mem g.divisors 1 :=
    Nat.mem_divisors.mpr (And.intro (one_dvd g) hg0)
  have hsum :
      (g.divisors.erase 1).sum (fun d => (d.totient : Real))=
        (g : Real)-1 := by
    have hs := Finset.sum_erase_add g.divisors (fun d => (d.totient : Real)) hmem
    have ht : g.divisors.sum (fun d => (d.totient : Real))=(g : Real) := by
      exact_mod_cast Nat.sum_totient g
    rw [ht,Nat.totient_one,Nat.cast_one] at hs
    linarith only [hs]
  calc
    _ = ((oddPellPrimitiveDivisors N).filter
        (fun d => Dvd.dvd d (2*k+1) /\ Dvd.dvd d (2*l+1))).sum
          (fun d => (d.totient : Real)) := by rw [Finset.sum_filter]
    _ = (g.divisors.erase 1).sum (fun d => (d.totient : Real)) := by rw [hset]
    _ = _ := hsum



theorem oddPell_gcd_energy_diagonal (N : Nat) (hN : 0<N)
    (S : Finset Nat) (a : Nat -> Real) :
    S.sum (fun k => S.sum (fun l => a k*a l*
      ((((N.gcd ((2*k+1).gcd (2*l+1))) : Real)-1))))=
      (oddPellPrimitiveDivisors N).sum (fun d => (d.totient : Real)*
        ((S.filter (fun k => Dvd.dvd d (2*k+1))).sum a)^2) := by
  classical
  let b : Nat -> Nat -> Real := fun d k => if Dvd.dvd d (2*k+1) then a k else 0
  have hpair (k l : Nat) :
      a k*a l*((((N.gcd ((2*k+1).gcd (2*l+1))) : Real)-1))=
        (oddPellPrimitiveDivisors N).sum
          (fun d => (d.totient : Real)*b d k*b d l) := by
    rw [<- oddPell_totient_gcd_kernel N k l hN,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hk : Dvd.dvd d (2*k+1)
    <;> by_cases hl : Dvd.dvd d (2*l+1)
    <;> simp [b,hk,hl]
    ring
  calc
    _ = S.sum (fun k => S.sum (fun l => (oddPellPrimitiveDivisors N).sum
        (fun d => (d.totient : Real)*b d k*b d l))) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      exact hpair k l
    _ = S.sum (fun k => (oddPellPrimitiveDivisors N).sum
        (fun d => S.sum (fun l => (d.totient : Real)*b d k*b d l))) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = (oddPellPrimitiveDivisors N).sum
        (fun d => S.sum (fun k => S.sum (fun l => (d.totient : Real)*b d k*b d l))) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hs : S.sum (fun k => S.sum (fun l => (d.totient : Real)*b d k*b d l))=
          (d.totient : Real)*(S.sum (fun k => b d k))^2 := by
        calc
          _ = (S.sum (fun k => (d.totient : Real)*b d k))*
              (S.sum (fun l => b d l)) := by
            simp only [Finset.sum_mul,Finset.mul_sum]
            rw [Finset.sum_comm]
          _ = _ := by rw [<- Finset.mul_sum]; ring
      rw [hs]
      have hb : (S.sum (fun k => b d k))=
          (S.filter (fun k => Dvd.dvd d (2*k+1))).sum a := by
        dsimp only [b]
        rw [Finset.sum_filter]
      rw [hb]


variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def oddPellDefect (h c : F) (k : Nat) : Real :=
  traceFreePairWeight c h-traceFreePairWeight (oddPellShiftMap h c k) h

noncomputable def oddPellSplitWeight : Real :=
  ((Fintype.card F : Real)+((quadraticChar F) (-1) : Real))/
    ((Fintype.card F : Real)-3)

noncomputable def oddPellNonsplitWeight : Real :=
  ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))/
    ((Fintype.card F : Real)-3)

theorem oddPell_defect_two_mask (c : F) (k : Nat) (htwo : Not ((2 : F)=0)) :
    oddPellDefect 2 c k=
      if oddPellMap c k=0 \/ oddPellMap c k=-2 then traceFreePairWeight c 2 else 0 := by
  simp only [oddPellDefect,oddPellShiftMap,div_self htwo,one_mul]
  rw [oddPell_weight_loss_pointwise c k]
  split_ifs <;> ring

theorem oddPell_defect_meet_two (c : F) (k l r : Nat)
    (hg : (2*k+1).gcd (2*l+1)=2*r+1) (htwo : Not ((2 : F)=0)) :
    oddPellDefect 2 c k*oddPellDefect 2 c l=(oddPellDefect 2 c r)^2 := by
  rw [oddPell_defect_two_mask c k htwo,oddPell_defect_two_mask c l htwo,
    oddPell_defect_two_mask c r htwo]
  have he := oddPell_common_endpoints c k l r hg htwo
  by_cases hk : oddPellMap c k=0 \/ oddPellMap c k=-2
  . by_cases hl : oddPellMap c l=0 \/ oddPellMap c l=-2
    . have hr := he.mp (And.intro hk hl)
      rw [ite_eq_left hk,ite_eq_left hl,ite_eq_left hr]
      ring
    . have hr : Not (oddPellMap c r=0 \/ oddPellMap c r=-2) := by
        intro hp
        exact hl (he.mpr hp).2
      rw [ite_eq_left hk,ite_eq_right hl,ite_eq_right hr]
      ring
  . have hr : Not (oddPellMap c r=0 \/ oddPellMap c r=-2) := by
      intro hp
      exact hk (he.mpr hp).1
    rw [ite_eq_right hk,ite_eq_right hr]
    ring

theorem oddPell_defect_normalize (h c : F) (k : Nat)
    (hh : Not (h=0)) (htwo : Not ((2 : F)=0)) :
    oddPellDefect h c k=oddPellDefect 2 ((2/h)*c) k := by
  have hs : Not (h/2=0) := div_ne_zero hh htwo
  have hc : (h/2)*((2/h)*c)=c := by field_simp [hh,htwo]
  have h2 : (h/2)*(2 : F)=h := by field_simp [htwo]
  have hw : traceFreePairWeight c h=traceFreePairWeight ((2/h)*c) 2 := by
    simpa only [hc,h2] using
      (traceFreePairWeight_common_scale (h/2) ((2/h)*c) 2 hs)
  have hp : traceFreePairWeight (oddPellShiftMap h c k) h=
      traceFreePairWeight (oddPellMap ((2/h)*c) k) 2 := by
    unfold oddPellShiftMap
    simpa only [h2] using
      (traceFreePairWeight_common_scale (h/2) (oddPellMap ((2/h)*c) k) 2 hs)
  unfold oddPellDefect
  rw [hw,hp]
  simp only [oddPellShiftMap,div_self htwo,one_mul]

theorem oddPell_defect_meet (h c : F) (k l r : Nat)
    (hg : (2*k+1).gcd (2*l+1)=2*r+1)
    (hh : Not (h=0)) (htwo : Not ((2 : F)=0)) :
    oddPellDefect h c k*oddPellDefect h c l=(oddPellDefect h c r)^2 := by
  rw [oddPell_defect_normalize h c k hh htwo,
    oddPell_defect_normalize h c l hh htwo,
    oddPell_defect_normalize h c r hh htwo]
  exact oddPell_defect_meet_two ((2/h)*c) k l r hg htwo

theorem oddPell_defect_square_sectors (c : F) (k : Nat) (htwo : Not ((2 : F)=0)) :
    (oddPellDefect 2 c k)^2=
      (if Membership.mem (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k) c
        then (oddPellSplitWeight (F:=F))^2 else 0)+
      (if Membership.mem (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k) c
        then (oddPellNonsplitWeight (F:=F))^2 else 0) := by
  classical
  have hd : oddPellDefect 2 c k=
      (if Membership.mem (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k) c
        then oddPellSplitWeight (F:=F) else 0)+
      (if Membership.mem (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k) c
        then oddPellNonsplitWeight (F:=F) else 0) := by
    simp only [oddPellDefect,oddPellShiftMap,div_self htwo,one_mul]
    rw [oddPell_weight_loss_sectors c k htwo]
    unfold oddPellSplitWeight oddPellNonsplitWeight
    ring
  rw [hd]
  by_cases hs : IsSquare (c*(c+2))
  . have hm : Not (Membership.mem
        (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k) c) := by
      intro he
      simp only [oddPellEndpointSector,Finset.mem_filter,Finset.mem_univ,true_and] at he
      exact he.2.2.1 hs
    by_cases hp : Membership.mem
        (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k) c
    <;> simp only [hp,hm,ite_true,ite_false] <;> ring
  . have hp : Not (Membership.mem
        (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k) c) := by
      intro he
      simp only [oddPellEndpointSector,Finset.mem_filter,Finset.mem_univ,true_and] at he
      exact hs he.2.2.1
    by_cases hm : Membership.mem
        (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k) c
    <;> simp only [hp,hm,ite_true,ite_false] <;> ring

theorem oddPell_defect_square_sum (k : Nat) (htwo : Not ((2 : F)=0)) :
    (Finset.univ.sum fun c : F => (oddPellDefect 2 c k)^2)=
      (oddPellSplitWeight (F:=F))^2*
        ((((Fintype.card F-1).gcd (2*k+1)) : Real)-1)+
      (oddPellNonsplitWeight (F:=F))^2*
        ((((Fintype.card F+1).gcd (2*k+1)) : Real)-1) := by
  classical
  have hc := oddPell_common_sector_sizes (F:=F) k k htwo
  have hA :
      (oddPellEndpointSector (fun c : F => IsSquare (c*(c+2))) k).card+1=
        (Fintype.card F-1).gcd (2*k+1) := by simpa using hc.1
  have hB :
      (oddPellEndpointSector (fun c : F => Not (IsSquare (c*(c+2)))) k).card+1=
        (Fintype.card F+1).gcd (2*k+1) := by simpa using hc.2
  have hAr :
      ((oddPellEndpointSector (fun c : F => IsSquare (c*(c+2))) k).card : Real)=
        ((((Fintype.card F-1).gcd (2*k+1)) : Real)-1) := by
    have he :
        ((oddPellEndpointSector (fun c : F => IsSquare (c*(c+2))) k).card : Real)+1=
          (((Fintype.card F-1).gcd (2*k+1)) : Real) := by exact_mod_cast hA
    linarith only [he]
  have hBr :
      ((oddPellEndpointSector (fun c : F => Not (IsSquare (c*(c+2)))) k).card : Real)=
        ((((Fintype.card F+1).gcd (2*k+1)) : Real)-1) := by
    have he :
        ((oddPellEndpointSector (fun c : F => Not (IsSquare (c*(c+2)))) k).card : Real)+1=
          (((Fintype.card F+1).gcd (2*k+1)) : Real) := by exact_mod_cast hB
    linarith only [he]
  calc
    _ = Finset.univ.sum (fun c : F =>
        (if Membership.mem (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k) c
          then (oddPellSplitWeight (F:=F))^2 else 0)+
        (if Membership.mem (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k) c
          then (oddPellNonsplitWeight (F:=F))^2 else 0)) :=
      Finset.sum_congr rfl (fun c _ => oddPell_defect_square_sectors c k htwo)
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_ite_mem,Finset.sum_ite_mem]
      simp only [Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,hAr,hBr]
      ring


theorem oddPell_defect_inner_two (k l : Nat) (htwo : Not ((2 : F)=0)) :
    (1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => oddPellDefect 2 c k*oddPellDefect 2 c l)=
      (1/(Fintype.card F : Real))*(
        (oddPellSplitWeight (F:=F))^2*
          ((((Fintype.card F-1).gcd ((2*k+1).gcd (2*l+1))) : Real)-1)+
        (oddPellNonsplitWeight (F:=F))^2*
          ((((Fintype.card F+1).gcd ((2*k+1).gcd (2*l+1))) : Real)-1)) := by
  let r := oddPellGcdIndex k l
  have hg : 2*r+1=(2*k+1).gcd (2*l+1) := oddPell_gcdIndex_degree k l
  have hs :
      (Finset.univ.sum fun c : F => oddPellDefect 2 c k*oddPellDefect 2 c l)=
        (Finset.univ.sum fun c : F => (oddPellDefect 2 c r)^2) :=
    Finset.sum_congr rfl (fun c _ => oddPell_defect_meet_two c k l r hg.symm htwo)
  rw [hs,oddPell_defect_square_sum r htwo,hg]

theorem oddPell_defect_inner (h : F) (hh : Not (h=0)) (k l : Nat)
    (htwo : Not ((2 : F)=0)) :
    (1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => oddPellDefect h c k*oddPellDefect h c l)=
      (1/(Fintype.card F : Real))*(
        (oddPellSplitWeight (F:=F))^2*
          ((((Fintype.card F-1).gcd ((2*k+1).gcd (2*l+1))) : Real)-1)+
        (oddPellNonsplitWeight (F:=F))^2*
          ((((Fintype.card F+1).gcd ((2*k+1).gcd (2*l+1))) : Real)-1)) := by
  let e : Equiv F F :=
    { toFun := fun c => (2/h)*c
      invFun := fun c => (h/2)*c
      left_inv := by intro c; field_simp [hh,htwo]
      right_inv := by intro c; field_simp [hh,htwo] }
  have hs :
      (Finset.univ.sum fun c : F => oddPellDefect h c k*oddPellDefect h c l)=
        (Finset.univ.sum fun c : F => oddPellDefect 2 c k*oddPellDefect 2 c l) := by
    calc
      _ = Finset.univ.sum (fun c : F => oddPellDefect 2 (e c) k*oddPellDefect 2 (e c) l) :=
        Finset.sum_congr rfl (fun c _ => by
          change oddPellDefect h c k*oddPellDefect h c l=
            oddPellDefect 2 ((2/h)*c) k*oddPellDefect 2 ((2/h)*c) l
          rw [oddPell_defect_normalize h c k hh htwo,
            oddPell_defect_normalize h c l hh htwo])
      _ = _ := Equiv.sum_comp e (fun c : F => oddPellDefect 2 c k*oddPellDefect 2 c l)
  rw [hs]
  exact oddPell_defect_inner_two k l htwo

theorem oddPell_defect_energy (h : F) (hh : Not (h=0))
    (S : Finset Nat) (a : Nat -> Real) (hq : 5<=Fintype.card F)
    (htwo : Not ((2 : F)=0)) :
    (1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => (S.sum (fun k => a k*oddPellDefect h c k))^2)=
      (1/(Fintype.card F : Real))*(
        (oddPellSplitWeight (F:=F))^2*
          (oddPellPrimitiveDivisors (Fintype.card F-1)).sum
            (fun d => (d.totient : Real)*
              ((S.filter (fun k => Dvd.dvd d (2*k+1))).sum a)^2)+
        (oddPellNonsplitWeight (F:=F))^2*
          (oddPellPrimitiveDivisors (Fintype.card F+1)).sum
            (fun d => (d.totient : Real)*
              ((S.filter (fun k => Dvd.dvd d (2*k+1))).sum a)^2)) := by
  classical
  have hpoint (c : F) :
      (S.sum (fun k => a k*oddPellDefect h c k))^2=
        S.sum (fun k => S.sum (fun l =>
          a k*a l*(oddPellDefect h c k*oddPellDefect h c l))) := by
    rw [pow_two,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hcomm :
      (Finset.univ.sum fun c : F => S.sum (fun k => S.sum (fun l =>
        a k*a l*(oddPellDefect h c k*oddPellDefect h c l))))=
      S.sum (fun k => S.sum (fun l => Finset.univ.sum (fun c : F =>
        a k*a l*(oddPellDefect h c k*oddPellDefect h c l)))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_comm]
  have hgram :
      (1/(Fintype.card F : Real))*
        (Finset.univ.sum fun c : F => (S.sum (fun k => a k*oddPellDefect h c k))^2)=
        S.sum (fun k => S.sum (fun l => a k*a l*
          ((1/(Fintype.card F : Real))*
            (Finset.univ.sum fun c : F => oddPellDefect h c k*oddPellDefect h c l)))) := by
    simp_rw [hpoint]
    rw [hcomm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro c hc
    ring
  have hi (k l : Nat) := oddPell_defect_inner h hh k l htwo
  have hnminus : 0<Fintype.card F-1 := by omega
  have hnplus : 0<Fintype.card F+1 := by omega
  rw [hgram]
  simp_rw [hi]
  rw [<- oddPell_gcd_energy_diagonal (Fintype.card F-1) hnminus S a,
    <- oddPell_gcd_energy_diagonal (Fintype.card F+1) hnplus S a]
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
  congr 1
  all_goals
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring

theorem oddPell_defect_zero (h c : F) (hh : Not (h=0))
    (htwo : Not ((2 : F)=0)) : oddPellDefect h c 0=0 := by
  rw [oddPell_defect_normalize h c 0 hh htwo]
  simp [oddPellDefect,oddPellShiftMap,oddPellMap,oddPellPair,htwo]

theorem oddPell_defect_coprime (h c : F) (k l : Nat)
    (hg : (2*k+1).gcd (2*l+1)=1)
    (hh : Not (h=0)) (htwo : Not ((2 : F)=0)) :
    oddPellDefect h c k*oddPellDefect h c l=0 := by
  have he := oddPell_defect_meet h c k l 0 (by simpa using hg) hh htwo
  rw [oddPell_defect_zero h c hh htwo] at he
  simpa using he

end FiniteField
