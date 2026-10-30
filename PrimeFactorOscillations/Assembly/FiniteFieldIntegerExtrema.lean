/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerPrimes
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistExtrema
/-!
# Sharp fourth-power peaks of the full integer pair packet

For every fixed positive even shift and every Q >= 13, a compatible integer
residue below the full prime period generates a whole progression on which
the actual positive packet is at least an explicit constant times log(Q)^4.
The existing upper envelope has the same exponent. The proof retains all
small rows, primes dividing the shift, and the full integer height of the
CRT lift. It asserts no prime-pair recurrence at the square-root cutoff.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerExtrema
attribute [local instance] Classical.propDecidable

theorem finite_prime_crt {I : Type*} [DecidableEq I]
    (s : Finset I) (p r : I -> Nat)
    (hp : forall i, Membership.mem s i -> Nat.Prime (p i))
    (hi : Function.Injective p) :
    exists a : Nat, a<s.prod p /\
      forall i, Membership.mem s i -> (a : ZMod (p i))=(r i : ZMod (p i)) := by
  induction s using Finset.induction_on with
  | empty =>
    refine Exists.intro 0 (And.intro ?_ ?_)
    . simp
    . intro i hmem
      exact False.elim (Finset.notMem_empty i hmem)
  | @insert i s hnot ih =>
    have hps : forall j, Membership.mem s j -> Nat.Prime (p j) :=
      fun j hj => hp j (Finset.mem_insert_of_mem hj)
    have hex := ih hps
    let a : Nat := Classical.choose hex
    have ha := Classical.choose_spec hex
    change a<s.prod p /\
      (forall j, Membership.mem s j -> (a : ZMod (p j))=(r j : ZMod (p j))) at ha
    have hpi := hp i (Finset.mem_insert_self i s)
    have hcop : Nat.Coprime (p i) (s.prod p) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro j hj
      apply hpi.coprime_iff_not_dvd.mpr
      intro hd
      rcases (Nat.dvd_prime (hps j hj)).mp hd with he | he
      . exact hpi.ne_one he
      . have hij := hi he
        subst j
        exact hnot hj
    let c : Nat := (Nat.chineseRemainder hcop (r i) a).val
    have hc := (Nat.chineseRemainder hcop (r i) a).property
    change Nat.ModEq (p i) c (r i) /\ Nat.ModEq (s.prod p) c a at hc
    have hbound : c<(p i)*(s.prod p) :=
      Nat.chineseRemainder_lt_mul hcop (r i) a hpi.ne_zero (by omega)
    refine Exists.intro c (And.intro ?_ ?_)
    . rwa [Finset.prod_insert hnot]
    . intro j hj
      rcases Finset.mem_insert.mp hj with he | he
      . subst j
        exact (ZMod.natCast_eq_natCast_iff c (r i) (p i)).mpr hc.1
      . have hdiv : Dvd.dvd (p j) (s.prod p) := Finset.dvd_prod_of_mem p he
        have hca : Nat.ModEq (p j) c a := hc.2.of_dvd hdiv
        exact (ZMod.natCast_eq_natCast_iff c (r j) (p j)).mpr
          (hca.trans ((ZMod.natCast_eq_natCast_iff a (r j) (p j)).mp (ha.2 j he)))


open PrimeFactorOscillations.FiniteFieldIntegerTail
open PrimeFactorOscillations.FiniteFieldIntegerMass

def crestFactor (h p : Nat) : Real :=
  if Nat.Prime p /\ 13<=p /\ Not (Dvd.dvd p h) then
    ((p : Real)+1)/((p : Real)-3) else 1

def crestPrimeSet (h Q : Nat) : Finset Nat :=
  (Finset.Icc 1 Q).filter (fun p => Nat.Prime p /\ 13<=p /\ Not (Dvd.dvd p h))

def primePeriod (Q : Nat) : Nat :=
  ((Finset.Icc 1 Q).attach.filter (fun q => Nat.Prime q.val)).prod (fun q => q.val)

theorem actual_local_ge_one {Q : Nat} (h : Nat) (q : BoundedModulus Q)
    (hp : Nat.Prime q.val) (hsmall : q.val=2 -> ((h : Int) : ZMod q.val)=0)
    (c : ZMod q.val) (hc : Not (c=0)) (hch : Not (c+((h : Int) : ZMod q.val)=0)) :
    1<=actualLocal (h : Int) q c := by
  letI : Fact (Nat.Prime q.val) := Fact.mk hp
  have hn : Not (c=-((h : Int) : ZMod q.val)) := by
    intro he
    apply hch
    rw [he]
    ring
  by_cases hg : 5<=q.val /\ Not (((h : Int) : ZMod q.val)=0)
  . simp only [actualLocal,dif_pos hp,if_pos hg]
    exact (FiniteField.traceFreePairWeight_good_bounds c _ hc hch hg.2
      (by rw [ZMod.card]; exact_mod_cast hg.1)).1
  . simp only [actualLocal,dif_pos hp,if_neg hg,flatFallback,integerMask,
      if_neg hc,if_neg hn,mul_one]
    have hpR : (2 : Real)<=(q.val : Real) := by exact_mod_cast hp.two_le
    by_cases hh : ((h : Int) : ZMod q.val)=0
    . rw [if_pos hh]
      apply (one_le_div (by linarith only [hpR])).mpr
      linarith
    . rw [if_neg hh]
      have hp3 : 3<=q.val := by
        have hneq : Not (q.val=2) := fun he => hh (hsmall he)
        have h2 := hp.two_le
        omega
      have hp3R : (3 : Real)<=(q.val : Real) := by exact_mod_cast hp3
      apply (one_le_div (by linarith only [hp3R])).mpr
      linarith

theorem exists_actual_local_ge_one {Q : Nat} (h : Nat) (heven : Dvd.dvd 2 h)
    (q : BoundedModulus Q) (hp : Nat.Prime q.val) :
    exists c : ZMod q.val, 1<=actualLocal (h : Int) q c := by
  letI : Fact (Nat.Prime q.val) := Fact.mk hp
  have hsmall : q.val=2 -> ((h : Int) : ZMod q.val)=0 := by
    intro he
    have hd : Dvd.dvd q.val h := by rwa [he]
    simpa only [Int.cast_natCast] using
      (CharP.cast_eq_zero_iff (ZMod q.val) q.val h).mpr hd
  by_cases hh : ((h : Int) : ZMod q.val)=0
  . refine Exists.intro 1 (actual_local_ge_one h q hp hsmall 1 one_ne_zero ?_)
    have hhNat : (h : ZMod q.val)=0 := by simpa only [Int.cast_natCast] using hh
    simpa only [Int.cast_natCast,hhNat,add_zero] using
      (one_ne_zero : Not ((1 : ZMod q.val)=0))
  . have hp3 : 3<=q.val := by
      have hn : Not (q.val=2) := fun he => hh (hsmall he)
      have h2 := hp.two_le
      omega
    have htwo : Not (((2 : Nat) : ZMod q.val)=0) := by
      intro hz
      have hd := (CharP.cast_eq_zero_iff (ZMod q.val) q.val 2).mp hz
      exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hd
    refine Exists.intro ((h : Int) : ZMod q.val)
      (actual_local_ge_one h q hp hsmall _ hh ?_)
    have he : ((h : Int) : ZMod q.val)+((h : Int) : ZMod q.val)=
        (2 : ZMod q.val)*((h : Int) : ZMod q.val) := by ring
    rw [he]
    exact mul_ne_zero htwo hh

theorem exists_crest_residue {Q : Nat} (h : Nat) (heven : Dvd.dvd 2 h)
    (q : BoundedModulus Q) :
    exists c : ZMod q.val, crestFactor h q.val<=actualLocal (h : Int) q c := by
  by_cases hp : Nat.Prime q.val
  . letI : Fact (Nat.Prime q.val) := Fact.mk hp
    by_cases hg : Nat.Prime q.val /\ 13<=q.val /\ Not (Dvd.dvd q.val h)
    . have hh : Not (((h : Int) : ZMod q.val)=0) := by
        intro hz
        apply hg.2.2
        apply (CharP.cast_eq_zero_iff (ZMod q.val) q.val h).mp
        simpa only [Int.cast_natCast] using hz
      have hF : Not (ringChar (ZMod q.val)=2) := by
        rw [ringChar.eq (ZMod q.val) q.val]
        omega
      have hx := FiniteField.QuadraticPairTwistExtrema.exists_local_maximum hF
        (((h : Int) : ZMod q.val)) hh (by rw [ZMod.card]; exact_mod_cast hg.2.1)
      let c : ZMod q.val := Classical.choose hx
      have hc := Classical.choose_spec hx
      refine Exists.intro c ?_
      simp only [crestFactor,if_pos hg,actualLocal,dif_pos hp,
        if_pos (show 5<=q.val /\ Not (((h : Int) : ZMod q.val)=0) from
          And.intro (by omega) hh)]
      rw [hc.2.2,ZMod.card]
    . simp only [crestFactor,if_neg hg]
      exact exists_actual_local_ge_one h heven q hp
  . refine Exists.intro 0 ?_
    have hg : Not (Nat.Prime q.val /\ 13<=q.val /\ Not (Dvd.dvd q.val h)) :=
      fun he => hp he.1
    simp [crestFactor,actualLocal,hp,hg]

theorem crest_factor_ge_one (h p : Nat) : 1<=crestFactor h p := by
  unfold crestFactor
  split_ifs with hg
  . have hp : (13 : Real)<=(p : Real) := by exact_mod_cast hg.2.1
    apply (one_le_div (by linarith only [hp])).mpr
    linarith
  . exact le_refl _

theorem exists_integer_crest_rows (h Q : Nat) (heven : Dvd.dvd 2 h) :
    exists a : Nat, a<primePeriod Q /\
      forall t : Nat, forall q : BoundedModulus Q, crestFactor h q.val<=
        actualLocal (h : Int) q ((a+primePeriod Q*t : Nat) : ZMod q.val) := by
  have hex : forall q : BoundedModulus Q,
      exists c : ZMod q.val, crestFactor h q.val<=actualLocal (h : Int) q c :=
    exists_crest_residue h heven
  choose c hc using hex
  let S : Finset (BoundedModulus Q) :=
    (Finset.Icc 1 Q).attach.filter (fun q => Nat.Prime q.val)
  have hp : forall q, Membership.mem S q -> Nat.Prime q.val :=
    fun q hq => (Finset.mem_filter.mp hq).2
  have hcrt := finite_prime_crt S (fun q => q.val) (fun q => (c q).val) hp
    (fun _ _ he => Subtype.ext he)
  let a : Nat := Classical.choose hcrt
  have ha := Classical.choose_spec hcrt
  refine Exists.intro a (And.intro ha.1 ?_)
  intro t
  intro q
  by_cases hqprime : Nat.Prime q.val
  . have hmem : Membership.mem S q :=
      Finset.mem_filter.mpr (And.intro (Finset.mem_attach _ q) hqprime)
    have hdiv : Dvd.dvd q.val (primePeriod Q) :=
      Finset.dvd_prod_of_mem (fun q : BoundedModulus Q => q.val) hmem
    have hz : ((primePeriod Q) : ZMod q.val)=0 :=
      (CharP.cast_eq_zero_iff (ZMod q.val) q.val (primePeriod Q)).mpr hdiv
    have har : (a : ZMod q.val)=c q := by
      rw [ha.2 q hmem,ZMod.natCast_zmod_val]
    simpa only [Nat.cast_add,Nat.cast_mul,hz,zero_mul,add_zero,har] using hc q
  . have hg : Not (Nat.Prime q.val /\ 13<=q.val /\ Not (Dvd.dvd q.val h)) :=
      fun he => hqprime he.1
    simp [crestFactor,actualLocal,hqprime,hg]

theorem exists_integer_crest_product (h Q : Nat) (heven : Dvd.dvd 2 h) :
    exists a : Nat, a<primePeriod Q /\
      forall t : Nat, (Finset.Icc 1 Q).prod (crestFactor h)<=
        actualPacket (h : Int) Q (a+primePeriod Q*t) := by
  have hex := exists_integer_crest_rows h Q heven
  let a : Nat := Classical.choose hex
  have ha := Classical.choose_spec hex
  refine Exists.intro a (And.intro ha.1 ?_)
  intro t
  unfold actualPacket
  calc
    _ = (Finset.Icc 1 Q).attach.prod (fun q => crestFactor h q.val) :=
      (Finset.prod_attach (Finset.Icc 1 Q) (crestFactor h)).symm
    _ <= _ := by
      apply real_product_le_of_nonneg
      . intro q _
        exact le_trans (by norm_num) (crest_factor_ge_one h q.val)
      . intro q _
        exact ha.2 t q

theorem reciprocal_prime_lower (Q : Nat) (hQ : 2<=Q) :
    Real.log (Real.log (Q : Real))-mertensBudget<=
      PrimeFactorUnimodality.reciprocalPrimeSumBelow (Q+1) := by
  have hlower := PrimeFactorUnimodality.reciprocalPrimeSumBelow_lower_of_estimate
    PrimeFactorUnimodality.hasMertensReciprocalPrimeEstimate hQ
  have hl2 : (0 : Real)<Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2<=Real.log (Q : Real) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hQ)
  have he := div_le_div_of_nonneg_left
    PrimeFactorUnimodality.mertensErrorConstant_nonneg hl2 hl
  have hm := (abs_le.mp (le_refl (abs Mertens.M))).1
  unfold mertensBudget
  linarith only [hlower,he,hm]

theorem retained_reciprocal_mass (h Q : Nat) (hh : 0<h) :
    PrimeFactorUnimodality.reciprocalPrimeSumBelow (Q+1)<=
      (crestPrimeSet h Q).sum (fun p => (1 : Real)/(p : Real))+(12+h : Nat) := by
  let A := crestPrimeSet h Q
  let T := Finset.Icc 1 (12+h)
  have hsub : Nat.primesBelow (Q+1)<=Union.union A T := by
    intro p hp
    have hd := Nat.mem_primesBelow.mp hp
    have h2 := hd.2.two_le
    by_cases hlo : p<=12+h
    . exact Finset.mem_union_right A (Finset.mem_Icc.mpr (And.intro (by omega) hlo))
    . apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine And.intro (Finset.mem_Icc.mpr (And.intro (by omega) (by omega))) ?_
      refine And.intro hd.2 (And.intro (by omega) ?_)
      intro hdiv
      have hi := Nat.le_of_dvd hh hdiv
      omega
  have hfirst := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => (show (0 : Real)<=1/(p : Real) from by positivity))
  have hsum : (Union.union A T).sum (fun p => (1 : Real)/(p : Real))+
      (Inter.inter A T).sum (fun p => (1 : Real)/(p : Real))=
      A.sum (fun p => (1 : Real)/(p : Real))+T.sum (fun p => (1 : Real)/(p : Real)) :=
    Finset.sum_union_inter
  have hnonneg : 0<=(Inter.inter A T).sum (fun p => (1 : Real)/(p : Real)) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hT : T.sum (fun p => (1 : Real)/(p : Real))<=(12+h : Nat) := by
    calc
      _ <= T.sum (fun _ => (1 : Real)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp1 : (1 : Real)<=(p : Real) := by
          exact_mod_cast (Finset.mem_Icc.mp hp).1
        simpa using one_div_le_one_div_of_le (by norm_num) hp1
      _ = _ := by simp [T]
  unfold PrimeFactorUnimodality.reciprocalPrimeSumBelow
  change (Nat.primesBelow (Q+1)).sum (fun p => (1 : Real)/(p : Real))<=
    A.sum (fun p => (1 : Real)/(p : Real))+(12+h : Nat)
  linarith only [hfirst,hsum,hnonneg,hT]

theorem crest_reciprocal_square_bound (h Q : Nat) (hQ : 13<=Q) :
    (crestPrimeSet h Q).sum (fun p => (1 : Real)/(p : Real)^2)<=1/12 := by
  apply FiniteField.QuadraticPairEuler.sum_inverse_square_tail 12 Q
    (by omega) (by omega)
  intro p hp
  have hd := Finset.mem_filter.mp hp
  exact Finset.mem_Ico.mpr (And.intro hd.2.2.1 (by have hu:=(Finset.mem_Icc.mp hd.1).2; omega))

theorem crest_product_exponential_lower (h Q : Nat) (hQ : 13<=Q) :
    Real.exp (4*((crestPrimeSet h Q).sum (fun p => (1 : Real)/(p : Real)))-1)<=
      (Finset.Icc 1 Q).prod (crestFactor h) := by
  let A := crestPrimeSet h Q
  have hpoint : forall p, Membership.mem A p ->
      Real.exp (4/(p : Real)-4/(p : Real)^2)<=((p : Real)+1)/((p : Real)-3) := by
    intro p hp
    have hd := (Finset.mem_filter.mp hp).2
    have hp13 : (13 : Real)<=(p : Real) := by exact_mod_cast hd.2.1
    have hlog := FiniteField.QuadraticPairTwistExtrema.log_envelope_lower
      (p : Real) (by linarith only [hp13])
    have he := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (show 0<((p : Real)+1)/((p : Real)-3) from by
      apply div_pos <;> linarith only [hp13])] at he
  have hsquare := crest_reciprocal_square_bound h Q hQ
  have hexp : Real.exp (4*(A.sum (fun p => (1 : Real)/(p : Real)))-1)<=
      Real.exp (A.sum (fun p => 4/(p : Real)-4/(p : Real)^2)) := by
    apply Real.exp_le_exp.mpr
    have hid : A.sum (fun p => 4/(p : Real)-4/(p : Real)^2)=
        4*(A.sum (fun p => (1 : Real)/(p : Real)))-
          4*(A.sum (fun p => (1 : Real)/(p : Real)^2)) := by
      calc
        _ = A.sum (fun p => 4*((1 : Real)/(p : Real))-4*((1 : Real)/(p : Real)^2)) :=
          Finset.sum_congr rfl (fun p _ => by ring)
        _ = _ := by rw [Finset.sum_sub_distrib,<- Finset.mul_sum,<- Finset.mul_sum]
    rw [hid]
    linarith only [hsquare]
  calc
    _ <= Real.exp (A.sum (fun p => 4/(p : Real)-4/(p : Real)^2)) := hexp
    _ = A.prod (fun p => Real.exp (4/(p : Real)-4/(p : Real)^2)) := Real.exp_sum A _
    _ <= A.prod (fun p => ((p : Real)+1)/((p : Real)-3)) := by
      apply real_product_le_of_nonneg
      . intro p _
        exact (Real.exp_pos _).le
      . exact hpoint
    _ = _ := by
      unfold A crestPrimeSet crestFactor
      rw [Finset.prod_filter]

def lowerConstant (h : Nat) : Real :=
  Real.exp (-4*(mertensBudget+(12+h : Nat))-1)

theorem lower_constant_pos (h : Nat) : 0<lowerConstant h := Real.exp_pos _

theorem crest_product_logarithmic_lower (h Q : Nat) (hh : 0<h) (hQ : 13<=Q) :
    lowerConstant h*(Real.log (Q : Real))^4<=
      (Finset.Icc 1 Q).prod (crestFactor h) := by
  have hM := reciprocal_prime_lower Q (by omega)
  have hR := retained_reciprocal_mass h Q hh
  have hS : Real.log (Real.log (Q : Real))-mertensBudget-(12+h : Nat)<=
      (crestPrimeSet h Q).sum (fun p => (1 : Real)/(p : Real)) := by
    linarith only [hM,hR]
  have hlog : 0<Real.log (Q : Real) :=
    Real.log_pos (by exact_mod_cast (show 1<Q from by omega))
  have hpow : Real.exp (4*Real.log (Real.log (Q : Real)))=(Real.log (Q : Real))^4 := by
    have he : 4*Real.log (Real.log (Q : Real))=
        Real.log (Real.log (Q : Real))+Real.log (Real.log (Q : Real))+
          Real.log (Real.log (Q : Real))+Real.log (Real.log (Q : Real)) := by ring
    rw [he,Real.exp_add,Real.exp_add,Real.exp_add,Real.exp_log hlog]
    ring
  have hid : lowerConstant h*(Real.log (Q : Real))^4=
      Real.exp (4*(Real.log (Real.log (Q : Real))-mertensBudget-(12+h : Nat))-1) := by
    unfold lowerConstant
    rw [<- hpow,<- Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.exp (4*(Real.log (Real.log (Q : Real))-mertensBudget-(12+h : Nat))-1) := hid
    _ <= Real.exp (4*((crestPrimeSet h Q).sum (fun p => (1 : Real)/(p : Real)))-1) :=
      Real.exp_le_exp.mpr (by linarith only [hS])
    _ <= _ := crest_product_exponential_lower h Q hQ

theorem integer_packet_sharp_fourth_power (h Q : Nat)
    (hh : 0<h) (heven : Dvd.dvd 2 h) (hQ : 13<=Q) :
    exists a : Nat, a<primePeriod Q /\
      (forall t : Nat, lowerConstant h*(Real.log (Q : Real))^4<=
        actualPacket (h : Int) Q (a+primePeriod Q*t)) /\
      (forall n : Nat, actualPacket (h : Int) Q n<=
        replacementConstant*(Real.log (Q : Real))^4) := by
  have hex := exists_integer_crest_product h Q heven
  let a : Nat := Classical.choose hex
  have ha := Classical.choose_spec hex
  refine Exists.intro a (And.intro ha.1 (And.intro ?_ ?_))
  . intro t
    exact le_trans (crest_product_logarithmic_lower h Q hh hQ) (ha.2 t)
  . intro n
    exact actual_packet_envelope (h : Int) Q n (by omega)

end PrimeFactorOscillations.FiniteFieldIntegerExtrema
