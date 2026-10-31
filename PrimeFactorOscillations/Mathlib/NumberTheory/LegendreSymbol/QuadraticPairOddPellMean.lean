/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellSectors

/-!
# Exact all-index Pell means at every nonzero shift

The pointwise transport loss retains both collapsed endpoint sectors and
their character product. Native gcd counts give the exact normalized
mean for every odd index over every odd finite field of cardinal at
least five. Common scaling transfers the actual weight and recurrence
to every nonzero shift. No incomplete integer-window mass is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem oddPell_collapsed_numerator (c : F) (k : Nat)
    (htwo : Not ((2 : F)=0)) (hc0 : Not (c=0)) (hcn : Not (c=-2))
    (hcol : oddPellMap c k=0 \/ oddPellMap c k=-2) :
    traceFreePairNumerator c 2=(Fintype.card F : Int)+
      (quadraticChar F) (-1)*(quadraticChar F) (c*(c+2)) := by
  have hr := oddPell_map_reachable c k
  have hpos : (quadraticChar F) (2*(c+2))=1 \/
      (quadraticChar F) ((-2)*c)=1 := by
    apply Or.elim hcol
    . intro he
      left
      apply (squarePairReach_zero_iff c 2 htwo).mp
      rw [<- he]
      exact hr
    . intro he
      right
      apply (squarePairReach_neg_shift_iff c 2 htwo).mp
      rw [<- he]
      exact hr
  let a : Int := (quadraticChar F) (-2)*(quadraticChar F) c
  let b : Int := (quadraticChar F) 2*(quadraticChar F) (c+2)
  have hpos' : b=1 \/ a=1 := by simpa only [a,b,map_mul] using hpos
  have hsum : a+b=1+a*b := by
    apply Or.elim hpos'
    . intro he
      rw [he]
      ring
    . intro he
      rw [he]
      ring
  have hneg2 : (quadraticChar F) (-2)=
      (quadraticChar F) (-1)*(quadraticChar F) 2 := by
    rw [show (-2 : F)=(-1)*2 by ring,map_mul]
  have hab : a*b=(quadraticChar F) (-1)*(quadraticChar F) (c*(c+2)) := by
    calc
      a*b=(quadraticChar F) (-1)*((quadraticChar F) 2)^2*
          ((quadraticChar F) c*(quadraticChar F) (c+2)) := by
        change ((quadraticChar F) (-2)*(quadraticChar F) c)*
          ((quadraticChar F) 2*(quadraticChar F) (c+2))=_
        rw [hneg2]
        ring
      _ = _ := by rw [quadraticChar_sq_one htwo,mul_one,map_mul]
  simp only [traceFreePairNumerator,ite_eq_right hc0,ite_eq_right hcn,twistPairNumerator]
  change (Fintype.card F : Int)-1+a+b=_
  calc
    _ = (Fintype.card F : Int)-1+(a+b) := by ring
    _ = _ := by rw [hsum,hab]; ring

theorem oddPell_collapsed_weight (c : F) (k : Nat)
    (htwo : Not ((2 : F)=0)) (hc0 : Not (c=0)) (hcn : Not (c=-2))
    (hcol : oddPellMap c k=0 \/ oddPellMap c k=-2) :
    traceFreePairWeight c 2=
      ((Fintype.card F : Real)+((quadraticChar F) (-1) : Real)*
        ((quadraticChar F) (c*(c+2)) : Real))/((Fintype.card F : Real)-3) := by
  have hn := oddPell_collapsed_numerator c k htwo hc0 hcn hcol
  simpa only [traceFreePairWeight,Int.cast_add,Int.cast_natCast,Int.cast_mul] using
    (congrArg (fun r : Int => (r : Real)/((Fintype.card F : Real)-3)) hn)

theorem oddPell_weight_loss_pointwise (c : F) (k : Nat) :
    traceFreePairWeight (oddPellMap c k) 2=
      if oddPellMap c k=0 \/ oddPellMap c k=-2 then 0 else traceFreePairWeight c 2 := by
  by_cases hcol : oddPellMap c k=0 \/ oddPellMap c k=-2
  . rw [ite_eq_left hcol]
    apply Or.elim hcol
    . intro he
      rw [he]
      exact traceFreePairWeight_zero (2 : F)
    . intro he
      rw [he]
      exact traceFreePairWeight_neg_shift (2 : F)
  . rw [ite_eq_right hcol]
    have hPhi0 : Not (oddPellMap c k=0) := by intro he; exact hcol (Or.inl he)
    have hPhin : Not (oddPellMap c k=-2) := by intro he; exact hcol (Or.inr he)
    have hA : Not ((oddPellPair c k).1=0) := by
      intro he
      apply hPhi0
      simp only [oddPellMap,he,zero_pow (by decide : Not (2=0)),mul_zero]
    have hB : Not ((oddPellPair c k).2=0) := by
      intro he
      apply hPhin
      have hs := oddPell_shifted_square c k
      rw [he] at hs
      have hz : oddPellMap c k+2=0 := by
        simpa only [zero_pow (by decide : Not (2=0)),mul_zero] using hs
      exact eq_neg_of_add_eq_zero_left hz
    exact traceFreePairWeight_square_transport_gap c (oddPellMap c k) 2
      (oddPellPair c k).1 (oddPellPair c k).2 hA hB rfl (oddPell_shifted_square c k)


theorem oddPell_weight_loss_sectors (c : F) (k : Nat) (htwo : Not ((2 : F)=0)) :
    traceFreePairWeight (oddPellMap c k) 2=traceFreePairWeight c 2-
      (if Membership.mem (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k) c
        then ((Fintype.card F : Real)+((quadraticChar F) (-1) : Real))/
          ((Fintype.card F : Real)-3) else 0)-
      (if Membership.mem (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k) c
        then ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))/
          ((Fintype.card F : Real)-3) else 0) := by
  classical
  have hA : Membership.mem (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k) c <->
      Not (c=0) /\ Not (c=-2) /\ IsSquare (c*(c+2)) /\
        (oddPellMap c k=0 \/ oddPellMap c k=-2) := by
    simp only [oddPellEndpointSector,Finset.mem_filter,Finset.mem_univ,true_and]
  have hB : Membership.mem
      (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k) c <->
      Not (c=0) /\ Not (c=-2) /\ Not (IsSquare (c*(c+2))) /\
        (oddPellMap c k=0 \/ oddPellMap c k=-2) := by
    simp only [oddPellEndpointSector,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hgood : Not (c=0) /\ Not (c=-2)
  . by_cases hcol : oddPellMap c k=0 \/ oddPellMap c k=-2
    . have hcp : Not (c+2=0) := by
        intro he
        exact hgood.2 (eq_neg_of_add_eq_zero_left he)
      have hD : Not (c*(c+2)=0) := mul_ne_zero hgood.1 hcp
      by_cases hs : IsSquare (c*(c+2))
      . have ha := hA.mpr (And.intro hgood.1 (And.intro hgood.2 (And.intro hs hcol)))
        have hb : Not (Membership.mem
            (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k) c) := by
          intro he
          exact (hB.mp he).2.2.1 hs
        have hchi : (quadraticChar F) (c*(c+2))=1 :=
          (quadraticChar_one_iff_isSquare hD).mpr hs
        have hW : traceFreePairWeight c 2=
            ((Fintype.card F : Real)+((quadraticChar F) (-1) : Real))/
              ((Fintype.card F : Real)-3) := by
          simpa only [hchi,Int.cast_one,mul_one] using
            (oddPell_collapsed_weight c k htwo hgood.1 hgood.2 hcol)
        rw [oddPell_weight_loss_pointwise,ite_eq_left hcol,ite_eq_left ha,
          ite_eq_right hb,hW]
        ring
      . have ha : Not (Membership.mem
            (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k) c) := by
          intro he
          exact hs (hA.mp he).2.2.1
        have hb := hB.mpr (And.intro hgood.1 (And.intro hgood.2 (And.intro hs hcol)))
        have hchi : (quadraticChar F) (c*(c+2))=-1 := by
          have hsq := quadraticChar_sq_one hD
          have hp : ((quadraticChar F) (c*(c+2))-1)*
              ((quadraticChar F) (c*(c+2))+1)=0 := by nlinarith only [hsq]
          have hn : Not ((quadraticChar F) (c*(c+2))-1=0) := by
            intro he
            exact hs ((quadraticChar_one_iff_isSquare hD).mp (sub_eq_zero.mp he))
          exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hp).resolve_left hn)
        have hW : traceFreePairWeight c 2=
            ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))/
              ((Fintype.card F : Real)-3) := by
          simpa only [hchi,Int.cast_neg,Int.cast_one,mul_neg_one,sub_eq_add_neg] using
            (oddPell_collapsed_weight c k htwo hgood.1 hgood.2 hcol)
        rw [oddPell_weight_loss_pointwise,ite_eq_left hcol,ite_eq_right ha,
          ite_eq_left hb,hW]
        ring
    . have ha : Not (Membership.mem
          (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k) c) := by
        intro he
        exact hcol (hA.mp he).2.2.2
      have hb : Not (Membership.mem
          (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k) c) := by
        intro he
        exact hcol (hB.mp he).2.2.2
      rw [oddPell_weight_loss_pointwise,ite_eq_right hcol,ite_eq_right ha,ite_eq_right hb]
      ring
  . have ha : Not (Membership.mem
        (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k) c) := by
      intro he
      have hp := hA.mp he
      exact hgood (And.intro hp.1 hp.2.1)
    have hb : Not (Membership.mem
        (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k) c) := by
      intro he
      have hp := hB.mp he
      exact hgood (And.intro hp.1 hp.2.1)
    have hW : traceFreePairWeight c 2=0 := by
      by_cases hc0 : c=0
      . rw [hc0]
        exact traceFreePairWeight_zero (2 : F)
      . have hcn : c=-2 := by
          by_contra hn
          exact hgood (And.intro hc0 hn)
        rw [hcn]
        exact traceFreePairWeight_neg_shift (2 : F)
    rw [oddPell_weight_loss_pointwise,ite_eq_right ha,ite_eq_right hb,hW]
    split_ifs <;> ring


theorem oddPell_weight_sum (k : Nat) (htwo : Not ((2 : F)=0)) :
    (Finset.univ.sum fun c : F => traceFreePairWeight (oddPellMap c k) 2)=
      (Finset.univ.sum fun c : F => traceFreePairWeight c 2)-
        ((oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k).card : Real)*
          (((Fintype.card F : Real)+((quadraticChar F) (-1) : Real))/
            ((Fintype.card F : Real)-3))-
        ((oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k).card : Real)*
          (((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))/
            ((Fintype.card F : Real)-3)) := by
  classical
  have hA :
      (Finset.univ.sum fun c : F =>
        if Membership.mem (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k) c
          then ((Fintype.card F : Real)+((quadraticChar F) (-1) : Real))/
            ((Fintype.card F : Real)-3) else 0)=
        ((oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k).card : Real)*
          (((Fintype.card F : Real)+((quadraticChar F) (-1) : Real))/
            ((Fintype.card F : Real)-3)) := by
    rw [Finset.sum_ite_mem]
    simp only [Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
  have hB :
      (Finset.univ.sum fun c : F =>
        if Membership.mem (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k) c
          then ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))/
            ((Fintype.card F : Real)-3) else 0)=
        ((oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k).card : Real)*
          (((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))/
            ((Fintype.card F : Real)-3)) := by
    rw [Finset.sum_ite_mem]
    simp only [Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
  calc
    _ = Finset.univ.sum (fun c : F => traceFreePairWeight c 2-
        (if Membership.mem (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k) c
          then ((Fintype.card F : Real)+((quadraticChar F) (-1) : Real))/
            ((Fintype.card F : Real)-3) else 0)-
        (if Membership.mem (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k) c
          then ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))/
            ((Fintype.card F : Real)-3) else 0)) :=
      Finset.sum_congr rfl (fun c _ => oddPell_weight_loss_sectors c k htwo)
    _ = _ := by rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,hA,hB]

theorem oddPell_gcd_twice_index (a k : Nat) :
    (2*a).gcd (2*(2*k+1))=2*((2*a).gcd (2*k+1)) := by
  have hc : Nat.Coprime 2 (2*k+1) :=
    Nat.coprime_two_left.mpr (Exists.intro k (by omega))
  rw [Nat.gcd_mul_left,Nat.Coprime.gcd_mul_left_cancel a hc]

theorem oddPell_mean (hF : Not (ringChar F=2)) (k : Nat)
    (hq : 5<=(Fintype.card F : Real)) :
    (1/(Fintype.card F : Real))*
        (Finset.univ.sum fun c : F => traceFreePairWeight (oddPellMap c k) 2)=
      1-(
        ((Fintype.card F : Real)+((quadraticChar F) (-1) : Real))*
          ((((Fintype.card F-1).gcd (2*k+1)) : Real)-1)+
        ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))*
          ((((Fintype.card F+1).gcd (2*k+1)) : Real)-1))/
        ((Fintype.card F : Real)*((Fintype.card F : Real)-3)) := by
  classical
  let n : Nat := Fintype.card F
  let m : Nat := 2*k+1
  let q : Real := n
  let t : Real := (quadraticChar F) (-1)
  let A : Nat := (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) k).card
  let B : Nat := (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) k).card
  let u : Nat := (n-1).gcd m
  let v : Nat := (n+1).gcd m
  have htwo : Not ((2 : F)=0) := _root_.FiniteField.two_ne_zero_of_odd hF
  have hcounts := oddPell_endpoint_split_nonsplit_counts (F:=F) k htwo
  have hcA : 2*A+2=(n-1).gcd (2*m) := hcounts.1
  have hcB : 2*B+2=(n+1).gcd (2*m) := hcounts.2
  have hdivA : Dvd.dvd 2 (n-1) := by
    apply Nat.dvd_trans ?_ (Nat.gcd_dvd_left (n-1) (2*m))
    exact Exists.intro (A+1) (by omega)
  have hdivB : Dvd.dvd 2 (n+1) := by
    apply Nat.dvd_trans ?_ (Nat.gcd_dvd_left (n+1) (2*m))
    exact Exists.intro (B+1) (by omega)
  have hgA : (n-1).gcd (2*m)=2*u := by
    let a : Nat := Classical.choose hdivA
    have ha : n-1=2*a := Classical.choose_spec hdivA
    dsimp only [u]
    rw [ha]
    exact oddPell_gcd_twice_index a k
  have hgB : (n+1).gcd (2*m)=2*v := by
    let a : Nat := Classical.choose hdivB
    have ha : n+1=2*a := Classical.choose_spec hdivB
    dsimp only [v]
    rw [ha]
    exact oddPell_gcd_twice_index a k
  have hAu : A+1=u := by omega
  have hBv : B+1=v := by omega
  have hAr : (A : Real)=(u : Real)-1 := by
    have he : (A : Real)+1=(u : Real) := by exact_mod_cast hAu
    linarith only [he]
  have hBr : (B : Real)=(v : Real)-1 := by
    have he : (B : Real)+1=(v : Real) := by exact_mod_cast hBv
    linarith only [he]
  have hq0 : Not (q=0) := ne_of_gt (by dsimp only [q,n]; linarith only [hq])
  have hq3 : Not (q-3=0) := ne_of_gt (by dsimp only [q,n]; linarith only [hq])
  have hsum :
      (Finset.univ.sum fun c : F => traceFreePairWeight (oddPellMap c k) 2)=
        (Finset.univ.sum fun c : F => traceFreePairWeight c 2)-
          (A : Real)*((q+t)/(q-3))-(B : Real)*((q-t)/(q-3)) :=
    oddPell_weight_sum k htwo
  have hm : (1/q)*(Finset.univ.sum fun c : F => traceFreePairWeight c 2)=1 :=
    traceFreePairWeight_mean_one hF 2 htwo hq
  change (1/q)*(Finset.univ.sum fun c : F => traceFreePairWeight (oddPellMap c k) 2)=
    1-((q+t)*((u : Real)-1)+(q-t)*((v : Real)-1))/(q*(q-3))
  rw [hsum,hAr,hBr]
  calc
    _ = (1/q)*(Finset.univ.sum fun c : F => traceFreePairWeight c 2)-
        ((q+t)*((u : Real)-1)+(q-t)*((v : Real)-1))/(q*(q-3)) := by
      field_simp [hq0,hq3]; ring
    _ = _ := by rw [hm]


theorem traceFreePairNumerator_common_scale (s c h : F) (hs : Not (s=0)) :
    traceFreePairNumerator (s*c) (s*h)=traceFreePairNumerator c h := by
  have hz : (s*c=0) <-> c=0 := by simp [hs]
  have hn : (s*c=-(s*h)) <-> c=-h := by
    constructor
    . intro he
      have hp : s*(c+h)=0 := by rw [mul_add,he]; ring
      exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hp).resolve_left hs)
    . intro he
      rw [he]
      ring
  have ha :
      (quadraticChar F) (-(s*h))*(quadraticChar F) (s*c)=
        (quadraticChar F) (-h)*(quadraticChar F) c := by
    have he : -(s*h)=s*(-h) := by ring
    calc
      _ = ((quadraticChar F) s)^2*
          ((quadraticChar F) (-h)*(quadraticChar F) c) := by
        simp only [he,map_mul]
        ring
      _ = _ := by rw [quadraticChar_sq_one hs,one_mul]
  have hb :
      (quadraticChar F) (s*h)*(quadraticChar F) (s*c+s*h)=
        (quadraticChar F) h*(quadraticChar F) (c+h) := by
    have he : s*c+s*h=s*(c+h) := by ring
    calc
      _ = ((quadraticChar F) s)^2*
          ((quadraticChar F) h*(quadraticChar F) (c+h)) := by
        simp only [he,map_mul]
        ring
      _ = _ := by rw [quadraticChar_sq_one hs,one_mul]
  simp only [traceFreePairNumerator,hz,hn,twistPairNumerator,ha,hb]

theorem traceFreePairWeight_common_scale (s c h : F) (hs : Not (s=0)) :
    traceFreePairWeight (s*c) (s*h)=traceFreePairWeight c h := by
  unfold traceFreePairWeight
  rw [traceFreePairNumerator_common_scale s c h hs]

def oddPellShiftMap (h c : F) (k : Nat) : F :=
  (h/2)*oddPellMap ((2/h)*c) k

omit [Fintype F] [DecidableEq F] in
theorem oddPellShiftMap_reachable (h c : F) (k : Nat)
    (hh : Not (h=0)) (htwo : Not ((2 : F)=0)) :
    squarePairReach c (oddPellShiftMap h c k) h := by
  let x : F := (2/h)*c
  let A : F := (oddPellPair x k).1
  let B : F := (oddPellPair x k).2
  have hx : (h/2)*x=c := by
    dsimp only [x]
    field_simp [hh,htwo]
  have h2 : (h/2)*(2 : F)=h := by field_simp [htwo]
  apply Exists.intro A
  apply Exists.intro B
  constructor
  . change (h/2)*oddPellMap x k=c*A^2
    calc
      _ = (h/2)*(x*A^2) := rfl
      _ = ((h/2)*x)*A^2 := by ring
      _ = _ := by rw [hx]
  . change (h/2)*oddPellMap x k+h=(c+h)*B^2
    calc
      _ = (h/2)*(oddPellMap x k+2) := by rw [mul_add,h2]
      _ = (h/2)*((x+2)*B^2) := by rw [oddPell_shifted_square]
      _ = ((h/2)*x+(h/2)*2)*B^2 := by ring
      _ = _ := by rw [hx,h2]

omit [Fintype F] [DecidableEq F] in
theorem oddPellShiftMap_two (c : F) (k : Nat) (htwo : Not ((2 : F)=0)) :
    oddPellShiftMap 2 c k=oddPellMap c k := by
  simp only [oddPellShiftMap,div_self htwo,one_mul]

theorem oddPell_shift_mean (hF : Not (ringChar F=2)) (h : F) (hh : Not (h=0))
    (k : Nat) (hq : 5<=(Fintype.card F : Real)) :
    (1/(Fintype.card F : Real))*
        (Finset.univ.sum fun c : F => traceFreePairWeight (oddPellShiftMap h c k) h)=
      1-(
        ((Fintype.card F : Real)+((quadraticChar F) (-1) : Real))*
          ((((Fintype.card F-1).gcd (2*k+1)) : Real)-1)+
        ((Fintype.card F : Real)-((quadraticChar F) (-1) : Real))*
          ((((Fintype.card F+1).gcd (2*k+1)) : Real)-1))/
        ((Fintype.card F : Real)*((Fintype.card F : Real)-3)) := by
  classical
  have htwo : Not ((2 : F)=0) := _root_.FiniteField.two_ne_zero_of_odd hF
  have hs : Not (h/2=0) := div_ne_zero hh htwo
  have h2 : (h/2)*(2 : F)=h := by field_simp [htwo]
  have hpoint (c : F) :
      traceFreePairWeight (oddPellShiftMap h c k) h=
        traceFreePairWeight (oddPellMap ((2/h)*c) k) 2 := by
    unfold oddPellShiftMap
    simpa only [h2] using
      (traceFreePairWeight_common_scale (h/2) (oddPellMap ((2/h)*c) k) 2 hs)
  let e : Equiv F F :=
    { toFun := fun c => (2/h)*c
      invFun := fun c => (h/2)*c
      left_inv := by intro c; field_simp [hh,htwo]
      right_inv := by intro c; field_simp [hh,htwo] }
  have hsum :
      (Finset.univ.sum fun c : F => traceFreePairWeight (oddPellShiftMap h c k) h)=
        (Finset.univ.sum fun c : F => traceFreePairWeight (oddPellMap c k) 2) := by
    calc
      _ = Finset.univ.sum (fun c : F => traceFreePairWeight (oddPellMap (e c) k) 2) :=
        Finset.sum_congr rfl (fun c _ => hpoint c)
      _ = _ := Equiv.sum_comp e (fun c : F => traceFreePairWeight (oddPellMap c k) 2)
  rw [hsum]
  exact oddPell_mean hF k hq

end FiniteField
