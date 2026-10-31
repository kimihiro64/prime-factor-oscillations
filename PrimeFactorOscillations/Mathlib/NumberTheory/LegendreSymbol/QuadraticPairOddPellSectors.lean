/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTraceTori

/-!
# Native split and nonsplit Pell endpoint counts

The square class of the trace discriminant identifies the two finite-field
tori. Exact trace-image cardinalities descend to the base field and retain
both endpoint corrections. The joint endpoint counts hold in every odd
finite field, including characteristic-divisible Pell indices and q = 3.
The normalized probability law still requires q >= 5; no incomplete
integer-window mass is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem oddTraceInput_discriminant_square (z : K)
    (hz : Not (z=0)) (htwo : Not ((2 : K)=0)) :
    (z-(oddTraceInput z+1))^2=oddTraceInput z*(oddTraceInput z+2) := by
  unfold oddTraceInput
  field_simp [htwo,hz]
  ring

theorem oddTraceInput_discriminant_isSquare_iff_mem_base (c : F) (z : K)
    (hz : Not (z=0)) (htwo : Not ((2 : K)=0))
    (hc : oddTraceInput z=algebraMap F K c) :
    IsSquare (c*(c+2)) <-> exists a : F, algebraMap F K a=z := by
  have hmap2 : algebraMap F K (2 : F)=(2 : K) := by
    rw [show (2 : F)=1+1 by ring]
    simp only [map_add,map_one]
    ring
  have hdisc : (z-(algebraMap F K c+1))^2=algebraMap F K (c*(c+2)) := by
    simpa only [hc,map_mul,map_add,hmap2] using
      (oddTraceInput_discriminant_square z hz htwo)
  constructor
  . intro hs
    let r : F := Classical.choose hs
    have hr : c*(c+2)=r*r := Classical.choose_spec hs
    have hrmap : algebraMap F K (c*(c+2))=(algebraMap F K r)^2 := by
      rw [hr,map_mul,pow_two]
    have hp :
        ((z-(algebraMap F K c+1))-algebraMap F K r)*
          ((z-(algebraMap F K c+1))+algebraMap F K r)=0 := by
      calc
        _ = (z-(algebraMap F K c+1))^2-(algebraMap F K r)^2 := by ring
        _ = 0 := by rw [hdisc,hrmap,sub_self]
    apply Or.elim (mul_eq_zero.mp hp)
    . intro he
      have hu : z-(algebraMap F K c+1)=algebraMap F K r := sub_eq_zero.mp he
      apply Exists.intro (c+1+r)
      calc
        algebraMap F K (c+1+r)=(algebraMap F K c+1)+algebraMap F K r := by
          rw [map_add,map_add,map_one]
        _ = (algebraMap F K c+1)+(z-(algebraMap F K c+1)) := by rw [hu]
        _ = z := by ring
    . intro he
      have hu : z-(algebraMap F K c+1)=-algebraMap F K r :=
        eq_neg_of_add_eq_zero_left he
      apply Exists.intro (c+1-r)
      calc
        algebraMap F K (c+1-r)=(algebraMap F K c+1)-algebraMap F K r := by
          rw [map_sub,map_add,map_one]
        _ = (algebraMap F K c+1)+(z-(algebraMap F K c+1)) := by rw [hu]; ring
        _ = z := by ring
  . intro he
    let a : F := Classical.choose he
    have ha : algebraMap F K a=z := Classical.choose_spec he
    apply Exists.intro (a-(c+1))
    apply (algebraMap F K).injective
    calc
      algebraMap F K (c*(c+2))=(z-(algebraMap F K c+1))^2 := hdisc.symm
      _ = algebraMap F K ((a-(c+1))*(a-(c+1))) := by
        simp only [map_mul,map_sub,map_add,map_one,ha,pow_two]


theorem pow_card_sub_one_eq_one_iff_mem_range [Fintype F] (z : K)
    (hz : Not (z=0)) :
    z^(Fintype.card F-1)=1 <-> exists a : F, algebraMap F K a=z := by
  rw [<- pow_card_eq_self_iff_mem_range]
  let q : Nat := Fintype.card F
  have hq : 2<=q := Fintype.one_lt_card
  have hp : z^(q-1)*z=z^q := by
    rw [<- pow_succ,Nat.sub_add_cancel (by omega : 1<=q)]
  constructor
  . intro he
    change z^q=z
    rw [<- hp,he,one_mul]
  . intro he
    change z^q=z at he
    have hzero : (z^(q-1)-1)*z=0 := by rw [sub_mul,one_mul,hp,he,sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hz)

theorem oddPell_map_endpoint_union_iff (z : K)
    (hz : Not (z=0)) (htwo : Not ((2 : K)=0)) (k : Nat) :
    (oddPellMap (oddTraceInput z) k=0 \/ oddPellMap (oddTraceInput z) k=-2) <->
      z^(2*(2*k+1))=1 := by
  unfold oddTraceInput
  rw [oddPell_map_eq_zero_iff z hz htwo k,oddPell_map_eq_neg_two_iff z hz htwo k]
  let m : Nat := 2*k+1
  change (z^m=1 \/ z^m=-1) <-> z^(2*m)=1
  have hpow : z^(2*m)=(z^m)^2 := by rw [Nat.mul_comm 2 m,pow_mul]
  constructor
  . intro he
    apply Or.elim he
    . intro h
      rw [hpow,h]
      simp
    . intro h
      rw [hpow,h]
      ring
  . intro he
    have hs : (z^m)^2=1 := by rw [<- hpow]; exact he
    have hp : (z^m-1)*(z^m+1)=0 := by
      calc
        _ = (z^m)^2-1 := by ring
        _ = 0 := by rw [hs,sub_self]
    apply Or.elim (mul_eq_zero.mp hp)
    . intro h
      exact Or.inl (sub_eq_zero.mp h)
    . intro h
      exact Or.inr (eq_neg_of_add_eq_zero_left h)


theorem oddPell_pair_map {R S : Type*} [CommRing R] [CommRing S]
    (f : RingHom R S) (x : R) (k : Nat) :
    f (oddPellPair x k).1=(oddPellPair (f x) k).1 /\
      f (oddPellPair x k).2=(oddPellPair (f x) k).2 := by
  have hf2 : f (2 : R)=(2 : S) := by
    rw [show (2 : R)=1+1 by ring]
    simp only [map_add,map_one]
    ring
  induction k with
  | zero =>
      constructor <;> simp only [oddPellPair,map_one]
  | succ k ih =>
      change f ((x+1)*(oddPellPair x k).1+(x+2)*(oddPellPair x k).2)=
          (f x+1)*(oddPellPair (f x) k).1+(f x+2)*(oddPellPair (f x) k).2 /\
        f (x*(oddPellPair x k).1+(x+1)*(oddPellPair x k).2)=
          f x*(oddPellPair (f x) k).1+(f x+1)*(oddPellPair (f x) k).2
      constructor <;> simp only [map_add,map_mul,map_one,hf2,ih.1,ih.2]

theorem oddPell_map_map {R S : Type*} [CommRing R] [CommRing S]
    (f : RingHom R S) (x : R) (k : Nat) :
    f (oddPellMap x k)=oddPellMap (f x) k := by
  unfold oddPellMap
  rw [map_mul,map_pow,(oddPell_pair_map f x k).1]


theorem exists_base_torus_trace_kernel [Fintype F] (n m : Nat) [NeZero n]
    [HasEnoughRootsOfUnity K n]
    (hneg : (-1 : K)^n=1) (htwo : Not ((2 : K)=0))
    (htrace : forall z : K, Not (z=0) -> z^n=1 ->
      exists c : F, algebraMap F K c=oddTraceInput z) :
    exists C : Finset F,
      (forall c : F, Membership.mem C c <->
        exists z : K, z^n=1 /\ z^(2*m)=1 /\ oddTraceInput z=algebraMap F K c) /\
      2*C.card=n.gcd (2*m)+2 := by
  classical
  have hex := exists_torus_trace_kernel_image (K:=K) n m hneg htwo
  let S : Finset K := Classical.choose hex
  have hS :
      (forall z : K, Membership.mem S z <-> z^n=1 /\ z^(2*m)=1) /\
        S.card=n.gcd (2*m) /\
          2*(S.image oddTraceInput).card=n.gcd (2*m)+2 :=
    Classical.choose_spec hex
  let C : Finset F := Finset.univ.filter (fun c =>
    exists z : K, Membership.mem S z /\ oddTraceInput z=algebraMap F K c)
  have hC (c : F) : Membership.mem C c <->
      exists z : K, z^n=1 /\ z^(2*m)=1 /\ oddTraceInput z=algebraMap F K c := by
    constructor
    . intro hc
      have hex' := (Finset.mem_filter.mp hc).2
      let z : K := Classical.choose hex'
      have hz : Membership.mem S z /\ oddTraceInput z=algebraMap F K c :=
        Classical.choose_spec hex'
      have hp := (hS.1 z).mp hz.1
      exact Exists.intro z (And.intro hp.1 (And.intro hp.2 hz.2))
    . intro hc
      let z : K := Classical.choose hc
      have hz : z^n=1 /\ z^(2*m)=1 /\ oddTraceInput z=algebraMap F K c :=
        Classical.choose_spec hc
      apply Finset.mem_filter.mpr
      exact And.intro (Finset.mem_univ _)
        (Exists.intro z (And.intro ((hS.1 z).mpr (And.intro hz.1 hz.2.1)) hz.2.2))
  have himage : C.image (algebraMap F K)=S.image oddTraceInput := by
    apply Finset.ext
    intro w
    constructor
    . intro hw
      have hex' := Finset.mem_image.mp hw
      let c : F := Classical.choose hex'
      have hc : Membership.mem C c /\ algebraMap F K c=w := Classical.choose_spec hex'
      have hez := (Finset.mem_filter.mp hc.1).2
      let z : K := Classical.choose hez
      have hz : Membership.mem S z /\ oddTraceInput z=algebraMap F K c :=
        Classical.choose_spec hez
      exact Finset.mem_image.mpr (Exists.intro z (And.intro hz.1 (hz.2.trans hc.2)))
    . intro hw
      have hex' := Finset.mem_image.mp hw
      let z : K := Classical.choose hex'
      have hz : Membership.mem S z /\ oddTraceInput z=w := Classical.choose_spec hex'
      have hp := (hS.1 z).mp hz.1
      have hz0 : Not (z=0) := by
        intro he
        have hn := hp.1
        rw [he,zero_pow (NeZero.ne n)] at hn
        exact zero_ne_one hn
      have hec := htrace z hz0 hp.1
      let c : F := Classical.choose hec
      have hc : algebraMap F K c=oddTraceInput z := Classical.choose_spec hec
      apply Finset.mem_image.mpr
      apply Exists.intro c
      apply And.intro
      . apply Finset.mem_filter.mpr
        exact And.intro (Finset.mem_univ _) (Exists.intro z (And.intro hz.1 hc.symm))
      . exact hc.trans hz.2
  have hcard : C.card=(S.image oddTraceInput).card := by
    calc
      C.card=(C.image (algebraMap F K)).card :=
        (Finset.card_image_of_injective C (algebraMap F K).injective).symm
      _ = (S.image oddTraceInput).card := congrArg Finset.card himage
  apply Exists.intro C
  apply And.intro hC
  rw [hcard]
  exact hS.2.2


noncomputable def oddPellEndpointSector [Fintype F] (P : F -> Prop) (k : Nat) : Finset F := by
  classical
  exact Finset.univ.filter (fun c : F =>
    Not (c=0) /\ Not (c=-2) /\ P c /\ (oddPellMap c k=0 \/ oddPellMap c k=-2))

theorem card_oddPell_endpoint_sector [Fintype F] [IsAlgClosed K]
    (n k : Nat) [NeZero n] [HasEnoughRootsOfUnity K n] (P : F -> Prop)
    (hneg : (-1 : K)^n=1) (htwo : Not ((2 : K)=0))
    (htrace : forall z : K, Not (z=0) -> z^n=1 ->
      exists c : F, algebraMap F K c=oddTraceInput z)
    (hsector : forall c : F, Not (c=0) -> Not (c=-2) ->
      forall z : K, Not (z=0) -> oddTraceInput z=algebraMap F K c ->
        (z^n=1 <-> P c)) :
    2*(oddPellEndpointSector P k).card+2=n.gcd (2*(2*k+1)) := by
  classical
  let m : Nat := 2*k+1
  have hmap2 : algebraMap F K (2 : F)=(2 : K) := by
    rw [show (2 : F)=1+1 by ring]
    simp only [map_add,map_one]
    ring
  have htwoF : Not ((2 : F)=0) := by
    intro he
    apply htwo
    calc
      (2 : K)=algebraMap F K (2 : F) := hmap2.symm
      _ = algebraMap F K 0 := congrArg (algebraMap F K) he
      _ = 0 := map_zero _
  have hPhi (c : F) :
      (oddPellMap (algebraMap F K c) k=0 \/ oddPellMap (algebraMap F K c) k=-2) <->
        (oddPellMap c k=0 \/ oddPellMap c k=-2) := by
    have hz : oddPellMap (algebraMap F K c) k=0 <-> oddPellMap c k=0 := by
      constructor
      . intro he
        apply (algebraMap F K).injective
        simpa only [oddPell_map_map,map_zero] using he
      . intro he
        rw [<- oddPell_map_map (algebraMap F K) c k,he,map_zero]
    have hn : oddPellMap (algebraMap F K c) k=-2 <-> oddPellMap c k=-2 := by
      constructor
      . intro he
        apply (algebraMap F K).injective
        simpa only [oddPell_map_map,map_neg,hmap2] using he
      . intro he
        rw [<- oddPell_map_map (algebraMap F K) c k,he,map_neg,hmap2]
    exact or_congr hz hn
  have hcollapse (c : F) (z : K) (hz : Not (z=0))
      (hc : oddTraceInput z=algebraMap F K c) :
      z^(2*m)=1 <-> (oddPellMap c k=0 \/ oddPellMap c k=-2) := by
    change z^(2*(2*k+1))=1 <-> _
    rw [<- oddPell_map_endpoint_union_iff z hz htwo k,hc]
    exact hPhi c
  have hex := exists_base_torus_trace_kernel (F:=F) (K:=K) n m hneg htwo htrace
  let C : Finset F := Classical.choose hex
  have hC :
      (forall c : F, Membership.mem C c <->
        exists z : K, z^n=1 /\ z^(2*m)=1 /\ oddTraceInput z=algebraMap F K c) /\
      2*C.card=n.gcd (2*m)+2 := Classical.choose_spec hex
  have hC0 : Membership.mem C (0 : F) := by
    apply (hC.1 0).mpr
    exact Exists.intro 1 (by simp [oddTraceInput])
  have hCn : Membership.mem C (-2 : F) := by
    apply (hC.1 (-2)).mpr
    apply Exists.intro (-1)
    apply And.intro hneg
    apply And.intro
    . rw [pow_mul]
      simp
    . rw [map_neg,hmap2]
      exact (oddTraceInput_eq_neg_two_iff (-1)
        (neg_ne_zero.mpr one_ne_zero) htwo).mpr rfl
  have hU (c : F) : Membership.mem (oddPellEndpointSector P k) c <->
      Not (c=0) /\ Not (c=-2) /\ P c /\ (oddPellMap c k=0 \/ oddPellMap c k=-2) := by
    simp only [oddPellEndpointSector,Finset.mem_filter,Finset.mem_univ,true_and]
  have hUeq : oddPellEndpointSector P k=(C.erase 0).erase (-2) := by
    apply Finset.ext
    intro c
    constructor
    . intro hu
      have hp := (hU c).mp hu
      have hez := exists_oddTraceInput (K:=K) htwo (algebraMap F K c)
      let z : K := Classical.choose hez
      have hz : Not (z=0) /\ oddTraceInput z=algebraMap F K c :=
        Classical.choose_spec hez
      have hn : z^n=1 := (hsector c hp.1 hp.2.1 z hz.1 hz.2).mpr hp.2.2.1
      have hm : z^(2*m)=1 := (hcollapse c z hz.1 hz.2).mpr hp.2.2.2
      have hcC : Membership.mem C c :=
        (hC.1 c).mpr (Exists.intro z (And.intro hn (And.intro hm hz.2)))
      exact Finset.mem_erase.mpr (And.intro hp.2.1
        (Finset.mem_erase.mpr (And.intro hp.1 hcC)))
    . intro hu
      have hpn := Finset.mem_erase.mp hu
      have hp0 := Finset.mem_erase.mp hpn.2
      have hez := (hC.1 c).mp hp0.2
      let z : K := Classical.choose hez
      have hz : z^n=1 /\ z^(2*m)=1 /\ oddTraceInput z=algebraMap F K c :=
        Classical.choose_spec hez
      have hz0 : Not (z=0) := by
        intro he
        have hn := hz.1
        rw [he,zero_pow (NeZero.ne n)] at hn
        exact zero_ne_one hn
      apply (hU c).mpr
      exact And.intro hp0.1 (And.intro hpn.1
        (And.intro ((hsector c hp0.1 hpn.1 z hz0 hz.2.2).mp hz.1)
          ((hcollapse c z hz0 hz.2.2).mp hz.2.1)))
  have hneg0 : Not ((-2 : F)=0) := neg_ne_zero.mpr htwoF
  have hCne : Membership.mem (C.erase 0) (-2 : F) :=
    Finset.mem_erase.mpr (And.intro hneg0 hCn)
  have hcard0 := Finset.card_erase_add_one hC0
  have hcardn := Finset.card_erase_add_one hCne
  have hUcard : (oddPellEndpointSector P k).card+2=C.card := by
    rw [hUeq]
    omega
  have htotal : 2*C.card=n.gcd (2*m)+2 := hC.2
  change 2*(oddPellEndpointSector P k).card+2=n.gcd (2*m)
  omega


theorem oddPell_endpoint_split_nonsplit_counts [Fintype F]
    (k : Nat) (htwoF : Not ((2 : F)=0)) :
    2*(oddPellEndpointSector (fun c : F => IsSquare (c*(c+2))) k).card+2=
        (Fintype.card F-1).gcd (2*(2*k+1)) /\
    2*(oddPellEndpointSector (fun c : F => Not (IsSquare (c*(c+2)))) k).card+2=
        (Fintype.card F+1).gcd (2*(2*k+1)) := by
  classical
  let L := AlgebraicClosure F
  let q : Nat := Fintype.card F
  have hq : 2<=q := Fintype.one_lt_card
  let _ : NeZero (q-1) := NeZero.mk (by omega)
  let _ : NeZero (q+1) := NeZero.mk (by omega)
  have hqF : (q : F)=0 := FiniteField.cast_card_eq_zero F
  have hminusF : Not (((q-1 : Nat) : F)=0) := by
    rw [Nat.cast_sub (by omega : 1<=q),Nat.cast_one,hqF,zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  have hplusF : Not (((q+1 : Nat) : F)=0) := by
    rw [Nat.cast_add,Nat.cast_one,hqF,zero_add]
    exact one_ne_zero
  let _ : NeZero ((q-1 : Nat) : F) := NeZero.mk hminusF
  let _ : NeZero ((q+1 : Nat) : F) := NeZero.mk hplusF
  let _ : HasEnoughRootsOfUnity L (q-1) := AlgebraicClosure.hasEnoughRootsOfUnity F (q-1)
  let _ : HasEnoughRootsOfUnity L (q+1) := AlgebraicClosure.hasEnoughRootsOfUnity F (q+1)
  have hmap2 : algebraMap F L (2 : F)=(2 : L) := by
    rw [show (2 : F)=1+1 by ring]
    simp only [map_add,map_one]
    ring
  have htwoL : Not ((2 : L)=0) := by
    intro he
    apply htwoF
    apply (algebraMap F L).injective
    calc
      algebraMap F L (2 : F)=(2 : L) := hmap2
      _ = 0 := he
      _ = algebraMap F L 0 := (map_zero _).symm
  have hneg0 : Not ((-1 : L)=0) := neg_ne_zero.mpr one_ne_zero
  have hnegminus : (-1 : L)^(q-1)=1 := by
    apply (pow_card_sub_one_eq_one_iff_mem_range (F:=F) (-1 : L) hneg0).mpr
    exact Exists.intro (-1 : F) (by rw [map_neg,map_one])
  have hnegplus : (-1 : L)^(q+1)=1 := by
    have he : q+1=q-1+2 := by omega
    rw [he,pow_add,hnegminus]
    ring
  have htraceMinus (z : L) (hz : Not (z=0)) (hn : z^(q-1)=1) :
      exists c : F, algebraMap F L c=oddTraceInput z :=
    (oddTraceInput_mem_base_iff (F:=F) z hz htwoL).mpr (Or.inl hn)
  have htracePlus (z : L) (hz : Not (z=0)) (hn : z^(q+1)=1) :
      exists c : F, algebraMap F L c=oddTraceInput z :=
    (oddTraceInput_mem_base_iff (F:=F) z hz htwoL).mpr (Or.inr hn)
  have hpos (c : F) (z : L) (hz : Not (z=0))
      (hc : oddTraceInput z=algebraMap F L c) :
      z^(q-1)=1 <-> IsSquare (c*(c+2)) :=
    (pow_card_sub_one_eq_one_iff_mem_range (F:=F) z hz).trans
      (oddTraceInput_discriminant_isSquare_iff_mem_base c z hz htwoL hc).symm
  have hminusSector (c : F) (_hc0 : Not (c=0)) (_hcn : Not (c=-2))
      (z : L) (hz : Not (z=0)) (hc : oddTraceInput z=algebraMap F L c) :
      z^(q-1)=1 <-> IsSquare (c*(c+2)) := hpos c z hz hc
  have hplusSector (c : F) (hc0 : Not (c=0)) (hcn : Not (c=-2))
      (z : L) (hz : Not (z=0)) (hc : oddTraceInput z=algebraMap F L c) :
      z^(q+1)=1 <-> Not (IsSquare (c*(c+2))) := by
    have hcover : z^(q-1)=1 \/ z^(q+1)=1 :=
      (oddTraceInput_mem_base_iff (F:=F) z hz htwoL).mp
        (Exists.intro c hc.symm)
    have hnotboth : Not (z^(q-1)=1 /\ z^(q+1)=1) := by
      intro hp
      have hs : z^2=1 := by
        have he : q+1=q-1+2 := by omega
        have hs' := hp.2
        rw [he,pow_add,hp.1,one_mul] at hs'
        exact hs'
      have hf : (z-1)*(z+1)=0 := by
        calc
          _ = z^2-1 := by ring
          _ = 0 := by rw [hs,sub_self]
      apply Or.elim (mul_eq_zero.mp hf)
      . intro he
        have hz1 : z=1 := sub_eq_zero.mp he
        apply hc0
        apply (algebraMap F L).injective
        calc
          algebraMap F L c=oddTraceInput z := hc.symm
          _ = 0 := (oddTraceInput_eq_zero_iff z hz htwoL).mpr hz1
          _ = algebraMap F L 0 := (map_zero _).symm
      . intro he
        have hzn : z=-1 := eq_neg_of_add_eq_zero_left he
        apply hcn
        apply (algebraMap F L).injective
        calc
          algebraMap F L c=oddTraceInput z := hc.symm
          _ = -2 := (oddTraceInput_eq_neg_two_iff z hz htwoL).mpr hzn
          _ = algebraMap F L (-2 : F) := by rw [map_neg,hmap2]
    constructor
    . intro hn hs
      exact hnotboth (And.intro ((hpos c z hz hc).mpr hs) hn)
    . intro hns
      exact hcover.resolve_left (by intro hn; exact hns ((hpos c z hz hc).mp hn))
  constructor
  . exact card_oddPell_endpoint_sector (F:=F) (K:=L) (q-1) k
      (fun c : F => IsSquare (c*(c+2))) hnegminus htwoL htraceMinus hminusSector
  . exact card_oddPell_endpoint_sector (F:=F) (K:=L) (q+1) k
      (fun c : F => Not (IsSquare (c*(c+2)))) hnegplus htwoL htracePlus hplusSector

end FiniteField
