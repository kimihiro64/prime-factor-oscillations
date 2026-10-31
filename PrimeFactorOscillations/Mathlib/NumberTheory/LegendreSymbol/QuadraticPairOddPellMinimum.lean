/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellArithmetic
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellMean

/-!
# Exact odd-Pell semigroup minimum

The actual trace-free mean is minimized simultaneously in its split and
nonsplit gcd terms. Its exact two-primary excess above the mandatory
core mass vanishes precisely at field orders congruent to 3 or 5 modulo 8.
All nonzero shifts and all odd indices are retained; q is at least 5.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def oddPellExpectedWeight (h : F) (k : Nat) : Real :=
  (1/(Fintype.card F : Real))*
    (Finset.univ.sum fun c : F => traceFreePairWeight (oddPellShiftMap h c k) h)

noncomputable def oddPellGcdMass (u v : Nat) : Real :=
  1-(
    ((Fintype.card F : Real)+((quadraticChar F) (-1) : Real))*((u : Real)-1)+
    ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))*((v : Real)-1))/
      ((Fintype.card F : Real)*((Fintype.card F : Real)-3))

theorem oddPell_minimum_odd_parts
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real))
    (a b u v : Nat) (hu : Odd u) (hv : Odd v)
    (ha : Fintype.card F-1=2^a*u) (hb : Fintype.card F+1=2^b*v) :
    (forall k : Nat, oddPellGcdMass (F:=F) u v<=oddPellExpectedWeight h k) /\
      exists k : Nat, oddPellExpectedWeight h k=oddPellGcdMass (F:=F) u v := by
  have ht : -1<=((quadraticChar F) (-1) : Real) /\
      ((quadraticChar F) (-1) : Real)<=1 := by
    apply Or.elim (oddPell_character_mod_four (F:=F) hF)
    . intro hp
      rw [hp.1]
      norm_num
    . intro hn
      rw [hn.1]
      norm_num
  have hp : 0<=(Fintype.card F : Real)+((quadraticChar F) (-1) : Real) := by
    linarith only [hq,ht.1]
  have hn : 0<=(Fintype.card F : Real)-((quadraticChar F) (-1) : Real) := by
    linarith only [hq,ht.2]
  have hden : 0<=(Fintype.card F : Real)*((Fintype.card F : Real)-3) := by
    apply mul_nonneg <;> linarith only [hq]
  apply And.intro
  . intro k
    have hm : Odd (2*k+1) := Exists.intro k rfl
    have hgu : (Fintype.card F-1).gcd (2*k+1)<=u :=
      oddPell_gcd_odd_bound _ a u _ ha hu hm
    have hgv : (Fintype.card F+1).gcd (2*k+1)<=v :=
      oddPell_gcd_odd_bound _ b v _ hb hv hm
    have hgur : (((Fintype.card F-1).gcd (2*k+1) : Nat) : Real)<=u := by
      exact_mod_cast hgu
    have hgvr : (((Fintype.card F+1).gcd (2*k+1) : Nat) : Real)<=v := by
      exact_mod_cast hgv
    have huineq := mul_le_mul_of_nonneg_left (sub_le_sub_right hgur 1) hp
    have hvineq := mul_le_mul_of_nonneg_left (sub_le_sub_right hgvr 1) hn
    unfold oddPellExpectedWeight
    rw [oddPell_shift_mean hF h hh k hq]
    unfold oddPellGcdMass
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_right (add_le_add huineq hvineq) hden
  . let k : Nat := Classical.choose (hu.mul hv)
    have hm : u*v=2*k+1 := Classical.choose_spec (hu.mul hv)
    have hgu := oddPell_gcd_odd_product_left _ a u v ha hu hv
    have hgv := oddPell_gcd_odd_product_right _ b u v hb hu hv
    apply Exists.intro k
    unfold oddPellExpectedWeight oddPellGcdMass
    rw [oddPell_shift_mean hF h hh k hq]
    rw [hm] at hgu hgv
    rw [hgu,hgv]


noncomputable def oddPellCoreCard : Nat := by
  classical
  exact (Finset.univ.filter fun c : F => squarePairCore c 2).card

theorem oddPell_core_count (hF : Not (ringChar F=2)) :
    4*(oddPellCoreCard (F:=F) : Int)=
      (Fintype.card F : Int)-(quadraticChar F) (-1) := by
  classical
  have htwo : Not ((2 : F)=0) := _root_.FiniteField.two_ne_zero_of_odd hF
  have hi := sum_squarePairCore_indicator hF (2 : F) htwo
  have hs :
      (Finset.univ.sum fun c : F => if squarePairCore c 2 then (1 : Int) else 0)=
        (oddPellCoreCard (F:=F) : Int) := by
    change _ = ((Finset.univ.filter fun c : F => squarePairCore c 2).card : Int)
    rw [<- Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [hs] at hi
  exact hi

theorem oddPell_core_pos (hF : Not (ringChar F=2))
    (hq : 5<=(Fintype.card F : Real)) :
    0<oddPellCoreCard (F:=F) := by
  have hi := oddPell_core_count (F:=F) hF
  have hqn : 5<=Fintype.card F := by exact_mod_cast hq
  apply Or.elim (oddPell_character_mod_four (F:=F) hF)
  . intro hp
    rw [hp.1] at hi
    omega
  . intro hn
    rw [hn.1] at hi
    omega

theorem oddPell_core_odd_iff (hF : Not (ringChar F=2)) :
    Odd (oddPellCoreCard (F:=F)) <->
      Fintype.card F%8=3 \/ Fintype.card F%8=5 := by
  have hi := oddPell_core_count (F:=F) hF
  apply Iff.intro
  . intro ho
    let a : Nat := Classical.choose ho
    have ha : oddPellCoreCard (F:=F)=2*a+1 := Classical.choose_spec ho
    apply Or.elim (oddPell_character_mod_four (F:=F) hF)
    . intro hp
      rw [hp.1] at hi
      apply Or.inr
      omega
    . intro hn
      rw [hn.1] at hi
      apply Or.inl
      omega
  . intro hm
    apply Or.elim (Nat.even_or_odd (oddPellCoreCard (F:=F)))
    . intro he
      let a : Nat := Classical.choose he
      have ha : oddPellCoreCard (F:=F)=a+a := Classical.choose_spec he
      apply False.elim
      rcases oddPell_character_mod_four (F:=F) hF with hp | hn
      . rw [hp.1] at hi
        rcases hm with h3 | h5 <;> omega
      . rw [hn.1] at hi
        rcases hm with h3 | h5 <;> omega
    . intro ho
      exact ho


noncomputable def oddPellCoreMass (u : Nat) : Real :=
  (oddPellCoreCard (F:=F) : Real)/(Fintype.card F : Real)+
    ((Fintype.card F : Real)+1)*((oddPellCoreCard (F:=F) : Real)-(u : Real))/
      ((Fintype.card F : Real)*((Fintype.card F : Real)-3))

theorem oddPell_minimum_core_parts
    (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real))
    (s u : Nat) (hu : Odd u) (hC : oddPellCoreCard (F:=F)=2^s*u) :
    (forall k : Nat, oddPellCoreMass (F:=F) u<=oddPellExpectedWeight h k) /\
      exists k : Nat, oddPellExpectedWeight h k=oddPellCoreMass (F:=F) u := by
  let C : Nat := oddPellCoreCard (F:=F)
  let q : Nat := Fintype.card F
  have hi := oddPell_core_count (F:=F) hF
  have hCp : 0<C := oddPell_core_pos hF hq
  have hfour : 4*C=2^(s+2)*u := by
    change 4*oddPellCoreCard (F:=F)=2^(s+2)*u
    rw [hC,pow_add]
    ring
  have hq0 : Not ((q : Real)=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  have hq3 : Not ((q : Real)-3=0) := ne_of_gt (by dsimp only [q]; linarith only [hq])
  apply Or.elim (oddPell_character_mod_four (F:=F) hF)
  . intro hp
    rw [hp.1] at hi
    have hqi : (q : Int)=4*(C : Int)+1 := by
      change (Fintype.card F : Int)=4*(oddPellCoreCard (F:=F) : Int)+1
      linarith only [hi]
    have hqn : q=4*C+1 := by exact_mod_cast hqi
    have hqr : (q : Real)=4*(C : Real)+1 := by exact_mod_cast hqn
    have ha : Fintype.card F-1=2^(s+2)*u := by change q-1=_; omega
    have hb : Fintype.card F+1=2^1*(2*C+1) := by
      change q+1=_
      norm_num only [pow_one]
      omega
    have hv : Odd (2*C+1) := Exists.intro C rfl
    have hm := oddPell_minimum_odd_parts hF h hh hq (s+2) 1 u (2*C+1) hu hv ha hb
    have hmass : oddPellGcdMass (F:=F) u (2*C+1)=oddPellCoreMass (F:=F) u := by
      unfold oddPellGcdMass oddPellCoreMass
      dsimp only [C,q]
      dsimp only [C,q] at hqr
      dsimp only [q] at hq0 hq3
      rw [hp.1]
      norm_num only [Int.cast_one,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      field_simp [hq0,hq3]
      rw [hqr]
      ring
    rw [hmass] at hm
    exact hm
  . intro hn
    rw [hn.1] at hi
    have hqi : (q : Int)+1=4*(C : Int) := by
      change (Fintype.card F : Int)+1=4*(oddPellCoreCard (F:=F) : Int)
      linarith only [hi]
    have hqn : q+1=4*C := by exact_mod_cast hqi
    have hqr : (q : Real)+1=4*(C : Real) := by exact_mod_cast hqn
    have hqr' : (q : Real)=4*(C : Real)-1 := by linarith only [hqr]
    have ha : Fintype.card F-1=2^1*(2*C-1) := by
      change q-1=_
      norm_num only [pow_one]
      omega
    have hb : Fintype.card F+1=2^(s+2)*u := by change q+1=_; omega
    have hv : Odd (2*C-1) := Exists.intro (C-1) (by omega)
    have hm := oddPell_minimum_odd_parts hF h hh hq 1 (s+2) (2*C-1) u hv hu ha hb
    have hsub : 1<=2*C := by omega
    have hmass : oddPellGcdMass (F:=F) (2*C-1) u=oddPellCoreMass (F:=F) u := by
      unfold oddPellGcdMass oddPellCoreMass
      dsimp only [C,q]
      dsimp only [C,q] at hqr'
      dsimp only [q] at hq0 hq3
      rw [hn.1,Nat.cast_sub hsub]
      norm_num only [Int.cast_neg,Int.cast_one,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      field_simp [hq0,hq3]
      rw [hqr']
      ring
    rw [hmass] at hm
    exact hm

theorem oddPell_minimum (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 5<=(Fintype.card F : Real)) :
    exists s u : Nat, Odd u /\ oddPellCoreCard (F:=F)=2^s*u /\
      (forall k : Nat, oddPellCoreMass (F:=F) u<=oddPellExpectedWeight h k) /\
        exists k : Nat, oddPellExpectedWeight h k=oddPellCoreMass (F:=F) u := by
  have hex := oddPell_exists_two_part (oddPellCoreCard (F:=F)) (oddPell_core_pos hF hq)
  let s : Nat := Classical.choose hex
  have hexu : exists u : Nat, Odd u /\ oddPellCoreCard (F:=F)=2^s*u :=
    Classical.choose_spec hex
  let u : Nat := Classical.choose hexu
  have hu : Odd u /\ oddPellCoreCard (F:=F)=2^s*u := Classical.choose_spec hexu
  exact Exists.intro s (Exists.intro u
    (And.intro hu.1 (And.intro hu.2 (oddPell_minimum_core_parts hF h hh hq s u hu.1 hu.2))))

theorem oddPell_attains_core_iff (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 5<=(Fintype.card F : Real)) :
    (exists k : Nat, oddPellExpectedWeight h k=
      (oddPellCoreCard (F:=F) : Real)/(Fintype.card F : Real)) <->
        Odd (oddPellCoreCard (F:=F)) := by
  apply Iff.intro
  . intro hexk
    let k : Nat := Classical.choose hexk
    have hk : oddPellExpectedWeight h k=
        (oddPellCoreCard (F:=F) : Real)/(Fintype.card F : Real) :=
      Classical.choose_spec hexk
    have hCp := oddPell_core_pos hF hq
    have hex := oddPell_exists_two_part (oddPellCoreCard (F:=F)) hCp
    let s : Nat := Classical.choose hex
    have hexu : exists u : Nat, Odd u /\ oddPellCoreCard (F:=F)=2^s*u :=
      Classical.choose_spec hex
    let u : Nat := Classical.choose hexu
    have hu : Odd u /\ oddPellCoreCard (F:=F)=2^s*u := Classical.choose_spec hexu
    have hmin := oddPell_minimum_core_parts hF h hh hq s u hu.1 hu.2
    have hb := hmin.1 k
    rw [hk] at hb
    unfold oddPellCoreMass at hb
    have hdiv : Dvd.dvd u (oddPellCoreCard (F:=F)) :=
      Exists.intro (2^s) (by rw [hu.2]; ring)
    have huC : u<=oddPellCoreCard (F:=F) := Nat.le_of_dvd hCp hdiv
    have huCr : (u : Real)<=(oddPellCoreCard (F:=F) : Real) := by exact_mod_cast huC
    have hden : 0<(Fintype.card F : Real)*((Fintype.card F : Real)-3) := by
      apply mul_pos <;> linarith only [hq]
    have hd :
        ((Fintype.card F : Real)+1)*((oddPellCoreCard (F:=F) : Real)-(u : Real))/
          ((Fintype.card F : Real)*((Fintype.card F : Real)-3))<=0 := by
      linarith only [hb]
    have hn : ((Fintype.card F : Real)+1)*
        ((oddPellCoreCard (F:=F) : Real)-(u : Real))<=0 := by
      have he := mul_le_mul_of_nonneg_right hd (le_of_lt hden)
      have hc :
          (((Fintype.card F : Real)+1)*
            ((oddPellCoreCard (F:=F) : Real)-(u : Real))/
              ((Fintype.card F : Real)*((Fintype.card F : Real)-3)))*
                ((Fintype.card F : Real)*((Fintype.card F : Real)-3))=
                  ((Fintype.card F : Real)+1)*
                    ((oddPellCoreCard (F:=F) : Real)-(u : Real)) := by
        have hq0 : Not ((Fintype.card F : Real)=0) :=
          ne_of_gt (by linarith only [hq])
        have hq3 : Not ((Fintype.card F : Real)-3=0) :=
          ne_of_gt (by linarith only [hq])
        field_simp [hq0,hq3]
      linarith only [he,hc]
    have hcle : (oddPellCoreCard (F:=F) : Real)<=(u : Real) := by
      by_contra hnot
      have hdiff : 0<(oddPellCoreCard (F:=F) : Real)-(u : Real) := by linarith only [hnot]
      have hqp : 0<(Fintype.card F : Real)+1 := by linarith only [hq]
      have hprod := mul_pos hqp hdiff
      linarith only [hprod,hn]
    have heq : oddPellCoreCard (F:=F)=u := by
      exact_mod_cast (le_antisymm hcle huCr)
    simpa only [heq] using hu.1
  . intro ho
    have hmin := oddPell_minimum_core_parts hF h hh hq 0
      (oddPellCoreCard (F:=F)) ho (by simp only [pow_zero,one_mul])
    let k : Nat := Classical.choose hmin.2
    have hk : oddPellExpectedWeight h k=
        oddPellCoreMass (F:=F) (oddPellCoreCard (F:=F)) :=
      Classical.choose_spec hmin.2
    apply Exists.intro k
    simpa only [oddPellCoreMass,sub_self,mul_zero,zero_div,add_zero] using hk

theorem oddPell_attains_minimum_iff (hF : Not (ringChar F=2))
    (h : F) (hh : Not (h=0)) (hq : 5<=(Fintype.card F : Real)) :
    (exists k : Nat, oddPellExpectedWeight h k=
      (oddPellCoreCard (F:=F) : Real)/(Fintype.card F : Real)) <->
        Fintype.card F%8=3 \/ Fintype.card F%8=5 := by
  exact (oddPell_attains_core_iff hF h hh hq).trans (oddPell_core_odd_iff hF)

end FiniteField
