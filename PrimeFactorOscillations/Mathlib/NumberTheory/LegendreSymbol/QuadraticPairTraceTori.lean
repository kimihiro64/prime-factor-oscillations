/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPell

/-!
# Trace fibers and finite torus power kernels

The normalized trace coordinate is defined on an arbitrary extension field.
Its fibers are inverse pairs, with singleton fibers exactly at the two
endpoints. The native Frobenius criterion identifies the split/nonsplit
torus cover of base-field inputs. Finite power-kernel counts retain both
endpoint corrections. These are inputs to the odd Pell mass calculation;
no incomplete integer-window mass assertion is made here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField
open _root_.Polynomial
variable {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]

theorem pow_card_eq_self_iff_mem_range (y : K) :
    y^Fintype.card F=y <-> exists x : F, algebraMap F K x=y := by
  classical
  constructor
  . intro hy
    let q : Nat := Fintype.card F
    have hq : 2<=q := Fintype.one_lt_card
    let P : Polynomial K := X^q-X
    have hP : Not (P=0) := by
      intro he
      have hc := congrArg (fun p : Polynomial K => p.coeff q) he
      have hq1 : Not (q=1) := by omega
      simp [P,Polynomial.coeff_X,Ne.symm hq1] at hc
    have hdegree : P.natDegree<=q := by
      calc
        _ <= max ((X^q : Polynomial K).natDegree) (X : Polynomial K).natDegree :=
          Polynomial.natDegree_sub_le _ _
        _ = q := by
          simp only [Polynomial.natDegree_X_pow,Polynomial.natDegree_X,
            max_eq_left (by omega : 1<=q)]
    let S : Finset K := Finset.univ.image (algebraMap F K)
    have hinj : Function.Injective (algebraMap F K) := (algebraMap F K).injective
    have hcard : S.card=q := by
      change (Finset.univ.image (algebraMap F K)).card=Fintype.card F
      rw [Finset.card_image_of_injective _ hinj,Finset.card_univ]
    have hroots (a : K) (ha : Membership.mem S a) :
        Membership.mem P.roots.toFinset a := by
      have hex := Finset.mem_image.mp ha
      let x : F := Classical.choose hex
      have hx := Classical.choose_spec hex
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hP).mpr
      change P.eval a=0
      rw [<- hx.2]
      simp only [P,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X]
      rw [<- map_pow]
      change algebraMap F K (x^Fintype.card F)-algebraMap F K x=0
      rw [FiniteField.pow_card,sub_self]
    have hyroot : Membership.mem P.roots.toFinset y := by
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hP).mpr
      change P.eval y=0
      simpa only [P,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X]
        using (sub_eq_zero.mpr hy)
    by_contra hnone
    have hyS : Not (Membership.mem S y) := by
      intro hm
      have hex := Finset.mem_image.mp hm
      exact hnone (Exists.intro (Classical.choose hex) (Classical.choose_spec hex).2)
    have hsubset : Insert.insert y S<=P.roots.toFinset := by
      intro a ha
      apply Or.elim (Finset.mem_insert.mp ha)
      . intro he
        rw [he]
        exact hyroot
      . exact hroots a
    have hbound : q+1<=q := calc
      q+1 = (Insert.insert y S).card := by rw [Finset.card_insert_of_notMem hyS,hcard]
      _ <= P.roots.toFinset.card := Finset.card_le_card hsubset
      _ <= P.roots.card := Multiset.toFinset_card_le P.roots
      _ <= P.natDegree := P.card_roots'
      _ <= q := hdegree
    omega
  . intro he
    let x : F := Classical.choose he
    have hx := Classical.choose_spec he
    rw [<- hx,<- map_pow,FiniteField.pow_card]

def oddTraceInput (z : K) : K := (z-1)^2/(2*z)

theorem oddTraceInput_map {L : Type*} [Field L] (f : RingHom K L) (z : K) :
    f (oddTraceInput z)=oddTraceInput (f z) := by
  have hf2 : f (2 : K)=2 := by
    rw [show (2 : K)=1+1 by ring]
    simp only [map_add,map_one]
    ring
  simp [oddTraceInput,hf2]

theorem oddTraceInput_sub_scaled (z w : K)
    (hz : Not (z=0)) (hw : Not (w=0)) (htwo : Not ((2 : K)=0)) :
    2*z*w*(oddTraceInput z-oddTraceInput w)=(z-w)*(z*w-1) := by
  unfold oddTraceInput
  field_simp [htwo,hz,hw]
  ring

theorem oddTraceInput_eq_iff (z w : K)
    (hz : Not (z=0)) (hw : Not (w=0)) (htwo : Not ((2 : K)=0)) :
    oddTraceInput z=oddTraceInput w <-> z=w \/ z*w=1 := by
  have hscale : Not (2*z*w=0) := mul_ne_zero (mul_ne_zero htwo hz) hw
  constructor
  . intro he
    have hp : (z-w)*(z*w-1)=0 := by
      rw [<- oddTraceInput_sub_scaled z w hz hw htwo,he,sub_self,mul_zero]
    apply Or.elim (mul_eq_zero.mp hp)
    . intro h
      exact Or.inl (sub_eq_zero.mp h)
    . intro h
      exact Or.inr (sub_eq_zero.mp h)
  . intro he
    apply Or.elim he
    . intro h
      rw [h]
    . intro h
      have hp : 2*z*w*(oddTraceInput z-oddTraceInput w)=0 := by
        rw [oddTraceInput_sub_scaled z w hz hw htwo,h,sub_self,mul_zero]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hscale)

theorem oddTraceInput_eq_zero_iff (z : K)
    (hz : Not (z=0)) (htwo : Not ((2 : K)=0)) :
    oddTraceInput z=0 <-> z=1 := by
  simpa [oddTraceInput,oddPellMap,oddPellPair] using
    (oddPell_map_eq_zero_iff z hz htwo 0)

theorem oddTraceInput_eq_neg_two_iff (z : K)
    (hz : Not (z=0)) (htwo : Not ((2 : K)=0)) :
    oddTraceInput z=-2 <-> z=-1 := by
  simpa [oddTraceInput,oddPellMap,oddPellPair] using
    (oddPell_map_eq_neg_two_iff z hz htwo 0)

theorem exists_oddTraceInput [IsAlgClosed K] (htwo : Not ((2 : K)=0)) (c : K) :
    exists z : K, Not (z=0) /\ oddTraceInput z=c := by
  have hex : exists u : K, u^2=c*(c+2) :=
    IsAlgClosed.exists_pow_nat_eq (c*(c+2)) (by decide : 0<2)
  let u : K := Classical.choose hex
  have hu : u^2=c*(c+2) := Classical.choose_spec hex
  let z : K := c+1+u
  have hprod : z*(c+1-u)=1 := by
    dsimp [z]
    calc
      _ = (c+1)^2-u^2 := by ring
      _ = 1 := by rw [hu]; ring
  have hz : Not (z=0) := by
    intro he
    have hp := hprod
    rw [he,zero_mul] at hp
    exact zero_ne_one hp
  have he : 2*z*c=(z-1)^2 := by
    dsimp [z]
    calc
      _ = (c+u)^2+(c*(c+2)-u^2) := by ring
      _ = (c+u)^2 := by rw [hu]; ring
      _ = _ := by ring
  apply Exists.intro z
  apply And.intro hz
  unfold oddTraceInput
  calc
    _ = (2*z*c)/(2*z) := by rw [he]
    _ = c := by field_simp [htwo,hz]

theorem oddTraceInput_mem_base_iff (z : K)
    (hz : Not (z=0)) (htwo : Not ((2 : K)=0)) :
    (exists c : F, algebraMap F K c=oddTraceInput z) <->
      z^(Fintype.card F-1)=1 \/ z^(Fintype.card F+1)=1 := by
  let q : Nat := Fintype.card F
  have hq : 2<=q := Fintype.one_lt_card
  have hmap : (oddTraceInput z)^q=oddTraceInput (z^q) := by
    have he := oddTraceInput_map (FiniteField.frobeniusAlgHom F K).toRingHom z
    change (FiniteField.frobeniusAlgHom F K) (oddTraceInput z)=
      oddTraceInput ((FiniteField.frobeniusAlgHom F K) z) at he
    simpa only [FiniteField.frobeniusAlgHom_apply] using he
  constructor
  . intro hb
    have hfix : (oddTraceInput z)^q=oddTraceInput z :=
      (pow_card_eq_self_iff_mem_range (F:=F) (oddTraceInput z)).mpr hb
    have heq : oddTraceInput (z^q)=oddTraceInput z := hmap.symm.trans hfix
    have hcases := (oddTraceInput_eq_iff (z^q) z (pow_ne_zero _ hz) hz htwo).mp heq
    apply Or.elim hcases
    . intro he
      left
      have hp : z^(q-1)*z=z := by
        calc
          _ = z^q := by rw [<- pow_succ,Nat.sub_add_cancel (by omega : 1<=q)]
          _ = z := he
      have hp0 : (z^(q-1)-1)*z=0 := by rw [sub_mul,one_mul,hp,sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hp0).resolve_right hz)
    . intro he
      right
      simpa only [pow_succ] using he
  . intro hb
    apply (pow_card_eq_self_iff_mem_range (F:=F) (oddTraceInput z)).mp
    change (oddTraceInput z)^q=oddTraceInput z
    rw [hmap]
    apply (oddTraceInput_eq_iff (z^q) z (pow_ne_zero _ hz) hz htwo).mpr
    apply Or.elim hb
    . intro he
      left
      calc
        z^q = z^(q-1)*z := by rw [<- pow_succ,Nat.sub_add_cancel (by omega : 1<=q)]
        _ = z := by rw [he,one_mul]
    . intro he
      right
      simpa only [pow_succ] using he


theorem card_oddTraceInput_image [DecidableEq K] (S : Finset K)
    (hzero : forall z : K, Membership.mem S z -> Not (z=0))
    (hinv : forall z : K, Membership.mem S z -> Membership.mem S ((Inv.inv z)))
    (hone : Membership.mem S (1 : K))
    (hnegone : Membership.mem S (-1 : K))
    (htwo : Not ((2 : K)=0)) :
    S.card+2=2*(S.image oddTraceInput).card := by
  classical
  let T : Finset K := S.image oddTraceInput
  have hneg : Not ((-2 : K)=0) := neg_ne_zero.mpr htwo
  have hT0 : Membership.mem T (0 : K) := by
    apply Finset.mem_image.mpr
    exact Exists.intro 1 (And.intro hone (by simp [oddTraceInput]))
  have hTneg : Membership.mem T (-2 : K) := by
    apply Finset.mem_image.mpr
    apply Exists.intro (-1)
    apply And.intro hnegone
    exact (oddTraceInput_eq_neg_two_iff (-1) (neg_ne_zero.mpr one_ne_zero) htwo).mpr rfl
  have hfiber (b : K) (hb : Membership.mem T b) :
      (S.filter (fun z => oddTraceInput z=b)).card+
        (if b=0 then 1 else 0)+(if b=-2 then 1 else 0)=2 := by
    have hex := Finset.mem_image.mp hb
    let z : K := Classical.choose hex
    have hz := Classical.choose_spec hex
    have hz0 : Not (z=0) := hzero z hz.1
    have hzi : Membership.mem S ((Inv.inv z)) := hinv z hz.1
    have hzi' : Membership.mem S ((Inv.inv z)) := hzi
    have hfilter :
        S.filter (fun w => oddTraceInput w=b)=Insert.insert z (Singleton.singleton (Inv.inv z)) := by
      apply Finset.ext
      intro w
      constructor
      . intro hw
        have hws := (Finset.mem_filter.mp hw).1
        have hwe := (Finset.mem_filter.mp hw).2
        have hcases := (oddTraceInput_eq_iff w z (hzero w hws) hz0 htwo).mp
          (hwe.trans hz.2.symm)
        apply Finset.mem_insert.mpr
        apply Or.elim hcases
        . exact Or.inl
        . intro he
          apply Or.inr
          apply Finset.mem_singleton.mpr
          simpa only [one_div] using (eq_div_iff hz0).mpr he
      . intro hw
        apply Or.elim (Finset.mem_insert.mp hw)
        . intro he
          rw [he]
          exact Finset.mem_filter.mpr hz
        . intro he
          have hwz : w=(Inv.inv z) := Finset.mem_singleton.mp he
          apply Finset.mem_filter.mpr
          apply And.intro (by simpa only [hwz] using hzi')
          calc
            oddTraceInput w = oddTraceInput z := by
              apply (oddTraceInput_eq_iff w z (by simpa only [hwz] using inv_ne_zero hz0)
                hz0 htwo).mpr
              right
              simp [hwz,hz0]
            _ = b := hz.2
    rw [hfilter]
    by_cases hb0 : b=0
    . have hz1 : z=1 := (oddTraceInput_eq_zero_iff z hz0 htwo).mp (hz.2.trans hb0)
      simp [hz1,hb0,Ne.symm hneg]
    . by_cases hbn : b=-2
      . have hzn : z=-1 :=
          (oddTraceInput_eq_neg_two_iff z hz0 htwo).mp (hz.2.trans hbn)
        simp [hzn,hbn,hneg]
      . have hne : Not (z=(Inv.inv z)) := by
          intro he
          have hzz : z*z=1 := by
            calc
              z*z = z*(Inv.inv z) := congrArg (fun w : K => z*w) he
              _ = 1 := by simpa only [div_eq_mul_inv] using (div_self hz0)
          have hp : (z-1)*(z+1)=0 := by
            calc
              _ = z*z-1 := by ring
              _ = 0 := by rw [hzz,sub_self]
          apply Or.elim (mul_eq_zero.mp hp)
          . intro he1
            have hz1 : z=1 := sub_eq_zero.mp he1
            apply hb0
            exact hz.2.symm.trans ((oddTraceInput_eq_zero_iff z hz0 htwo).mpr hz1)
          . intro he1
            have hzn : z=-1 := eq_neg_of_add_eq_zero_left he1
            apply hbn
            exact hz.2.symm.trans ((oddTraceInput_eq_neg_two_iff z hz0 htwo).mpr hzn)
        simp [hne,hb0,hbn]
  have hmaps : Set.MapsTo oddTraceInput (S : Set K) (T : Set K) := by
    intro z hz
    exact Finset.mem_image.mpr (Exists.intro z (And.intro hz rfl))
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hsum0 : T.sum (fun b => if b=0 then (1 : Nat) else 0)=1 := by simp [hT0]
  have hsumneg : T.sum (fun b => if b=-2 then (1 : Nat) else 0)=1 := by simp [hTneg]
  calc
    S.card+2 =
        T.sum (fun b => (S.filter (fun z => oddTraceInput z=b)).card)+
          T.sum (fun b => if b=0 then 1 else 0)+
            T.sum (fun b => if b=-2 then 1 else 0) := by rw [<- hcard,hsum0,hsumneg]
    _ = T.sum (fun b => (S.filter (fun z => oddTraceInput z=b)).card+
          (if b=0 then 1 else 0)+(if b=-2 then 1 else 0)) := by
        simp only [Finset.sum_add_distrib]
    _ = T.sum (fun _ => (2 : Nat)) := Finset.sum_congr rfl hfiber
    _ = 2*T.card := by simp [Nat.mul_comm]


theorem exists_torus_power_kernel (n d : Nat) [NeZero n]
    [HasEnoughRootsOfUnity K n] :
    exists S : Finset K,
      (forall z : K, Membership.mem S z <-> z^n=1 /\ z^d=1) /\
        S.card=n.gcd d := by
  classical
  let G := rootsOfUnity n K
  let H : Subgroup G := (powMonoidHom d).ker
  let _ : Fintype H := Fintype.ofFinite H
  let value : H -> K := fun z => ((z.1.1 : Units K) : K)
  have hinj : Function.Injective value := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact he
  let S : Finset K := Finset.univ.image value
  apply Exists.intro S
  constructor
  . intro z
    constructor
    . intro hz
      have hex := Finset.mem_image.mp hz
      let a : H := Classical.choose hex
      have ha : value a=z := (Classical.choose_spec hex).2
      have hn : (value a)^n=1 :=
        (mem_rootsOfUnity' n (a.1.1 : Units K)).mp a.1.2
      have hd : (a.1 : G)^d=1 := MonoidHom.mem_ker.mp a.2
      have hdval := congrArg (fun u : G => ((u.1 : Units K) : K)) hd
      have hd' : (value a)^d=1 := hdval
      exact And.intro (by rw [<- ha]; exact hn) (by rw [<- ha]; exact hd')
    . intro hz
      have hz0 : Not (z=0) := by
        intro he
        have hn := hz.1
        rw [he,zero_pow (NeZero.ne n)] at hn
        exact zero_ne_one hn
      let u : Units K := Units.mk0 z hz0
      let a : G := Subtype.mk u ((mem_rootsOfUnity' n u).mpr hz.1)
      have ha : a^d=1 := by
        apply Subtype.ext
        apply Units.ext
        exact hz.2
      let b : H := Subtype.mk a (MonoidHom.mem_ker.mpr ha)
      apply Finset.mem_image.mpr
      exact Exists.intro b (And.intro (Finset.mem_univ _) rfl)
  . change (Finset.univ.image value).card=n.gcd d
    rw [Finset.card_image_of_injective _ hinj,Finset.card_univ]
    rw [<- Nat.card_eq_fintype_card]
    have hk := IsCyclic.card_powMonoidHom_ker G d
    have hn : Nat.card G=n := HasEnoughRootsOfUnity.natCard_rootsOfUnity K n
    simpa only [hn] using hk

theorem exists_torus_trace_kernel_image [DecidableEq K] (n m : Nat) [NeZero n]
    [HasEnoughRootsOfUnity K n]
    (hneg : (-1 : K)^n=1) (htwo : Not ((2 : K)=0)) :
    exists S : Finset K,
      (forall z : K, Membership.mem S z <-> z^n=1 /\ z^(2*m)=1) /\
        S.card=n.gcd (2*m) /\
          2*(S.image oddTraceInput).card=n.gcd (2*m)+2 := by
  classical
  have hex := exists_torus_power_kernel (K:=K) n (2*m)
  let S : Finset K := Classical.choose hex
  have hS := Classical.choose_spec hex
  have hzero (z : K) (hz : Membership.mem S z) : Not (z=0) := by
    intro he
    have hn := ((hS.1 z).mp hz).1
    rw [he,zero_pow (NeZero.ne n)] at hn
    exact zero_ne_one hn
  have hinv (z : K) (hz : Membership.mem S z) : Membership.mem S (Inv.inv z) := by
    have hp := (hS.1 z).mp hz
    apply (hS.1 (Inv.inv z)).mpr
    constructor
    . rw [inv_pow,hp.1,inv_one]
    . rw [inv_pow,hp.2,inv_one]
  have hone : Membership.mem S (1 : K) := (hS.1 1).mpr (by simp)
  have hnegone : Membership.mem S (-1 : K) := by
    apply (hS.1 (-1)).mpr
    apply And.intro hneg
    rw [pow_mul]
    simp
  have hcard := card_oddTraceInput_image S hzero hinv hone hnegone htwo
  have hsize : S.card=n.gcd (2*m) := hS.2
  apply Exists.intro S
  exact And.intro hS.1 (And.intro hsize (by rw [<- hsize]; exact hcard.symm))

end FiniteField
