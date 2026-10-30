/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerExtrema
/-!
# Sharp two-cutoff domination and integer frozen likelihood growth

The full actual packet is dominated on every integer by the flat-tail
hybrid times an explicit constant and (log(Q)/log(K))^2. A single compatible
integer residue below the prime period attains the matching logarithmic
power for every 12 <= K <= Q, on its entire arithmetic progression.
All local zero masks, small rows and prime-dividing-shift factors remain.
The quotient equals the exact frozen compensation factor and its denominator
is proved positive before division. No prime recurrence height bound is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldFrozenGrowth
open PrimeFactorOscillations.FiniteFieldIntegerTail
open PrimeFactorOscillations.FiniteFieldIntegerMass
open PrimeFactorOscillations.FiniteFieldIntegerAffine
open PrimeFactorOscillations.FiniteFieldIntegerExtrema
attribute [local instance] Classical.propDecidable

def allTailPrimes (K Q : Nat) : Finset Nat :=
  (Finset.Icc 1 Q).filter (fun p => Nat.Prime p /\ K<p)

def tailPrimeSet (K h Q : Nat) : Finset Nat :=
  (Finset.Icc 1 Q).filter (fun p => Nat.Prime p /\ K<p /\ Not (Dvd.dvd p h))

theorem all_tail_reciprocal_sum (K Q : Nat) (hKQ : K<=Q) :
    (allTailPrimes K Q).sum (fun p => (1 : Real)/(p : Real))+
      PrimeFactorUnimodality.reciprocalPrimeSumBelow (K+1)=
        PrimeFactorUnimodality.reciprocalPrimeSumBelow (Q+1) := by
  have hsub : Nat.primesBelow (K+1)<=Nat.primesBelow (Q+1) := by
    intro p hp
    have hd := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr (And.intro (by omega) hd.2)
  have hid : SDiff.sdiff (Nat.primesBelow (Q+1)) (Nat.primesBelow (K+1))=
      allTailPrimes K Q := by
    apply Finset.ext
    intro p
    constructor
    . intro hp
      have hd := Finset.mem_sdiff.mp hp
      have hs := Nat.mem_primesBelow.mp hd.1
      have h2 := hs.2.two_le
      have hk : K<p := by
        by_contra hn
        apply hd.2
        exact Nat.mem_primesBelow.mpr (And.intro (by omega) hs.2)
      exact Finset.mem_filter.mpr (And.intro
        (Finset.mem_Icc.mpr (And.intro (by omega) (by omega))) (And.intro hs.2 hk))
    . intro hp
      have hd := Finset.mem_filter.mp hp
      have hs := Finset.mem_Icc.mp hd.1
      apply Finset.mem_sdiff.mpr
      refine And.intro (Nat.mem_primesBelow.mpr (And.intro (by omega) hd.2.1)) ?_
      intro hlo
      have hl := Nat.mem_primesBelow.mp hlo
      omega
  have hs := Finset.sum_sdiff (f:=fun p : Nat => (1 : Real)/(p : Real)) hsub
  rw [hid] at hs
  exact hs

theorem tail_reciprocal_upper (K h Q : Nat) (hKQ : K<=Q) :
    (tailPrimeSet K h Q).sum (fun p => (1 : Real)/(p : Real))<=
      PrimeFactorUnimodality.reciprocalPrimeSumBelow (Q+1)-
        PrimeFactorUnimodality.reciprocalPrimeSumBelow (K+1) := by
  have hsub : tailPrimeSet K h Q<=allTailPrimes K Q := by
    intro p hp
    have hd := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr (And.intro hd.1 (And.intro hd.2.1 hd.2.2.1))
  have hb := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => (show (0 : Real)<=1/(p : Real) from by positivity))
  have hs := all_tail_reciprocal_sum K Q hKQ
  linarith only [hb,hs]

theorem tail_reciprocal_missing_mass (K h Q : Nat) (hh : 0<h) (hKQ : K<=Q) :
    PrimeFactorUnimodality.reciprocalPrimeSumBelow (Q+1)-
      PrimeFactorUnimodality.reciprocalPrimeSumBelow (K+1)<=
        (tailPrimeSet K h Q).sum (fun p => (1 : Real)/(p : Real))+(h : Real) := by
  let A := tailPrimeSet K h Q
  let T := Finset.Icc 1 h
  have hsub : allTailPrimes K Q<=Union.union A T := by
    intro p hp
    have hd := Finset.mem_filter.mp hp
    by_cases hdiv : Dvd.dvd p h
    . have hp1 := (Finset.mem_Icc.mp hd.1).1
      exact Finset.mem_union_right A
        (Finset.mem_Icc.mpr (And.intro hp1 (Nat.le_of_dvd hh hdiv)))
    . exact Finset.mem_union_left T
        (Finset.mem_filter.mpr (And.intro hd.1 (And.intro hd.2.1 (And.intro hd.2.2 hdiv))))
  have hfirst := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => (show (0 : Real)<=1/(p : Real) from by positivity))
  have hsum : (Union.union A T).sum (fun p => (1 : Real)/(p : Real))+
      (Inter.inter A T).sum (fun p => (1 : Real)/(p : Real))=
      A.sum (fun p => (1 : Real)/(p : Real))+T.sum (fun p => (1 : Real)/(p : Real)) :=
    Finset.sum_union_inter
  have hnonneg : 0<=(Inter.inter A T).sum (fun p => (1 : Real)/(p : Real)) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hT : T.sum (fun p => (1 : Real)/(p : Real))<=(h : Real) := by
    calc
      _ <= T.sum (fun _ => (1 : Real)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp1 : (1 : Real)<=(p : Real) := by
          exact_mod_cast (Finset.mem_Icc.mp hp).1
        simpa using one_div_le_one_div_of_le (by norm_num) hp1
      _ = _ := by simp [T]
  have hband := all_tail_reciprocal_sum K Q hKQ
  change _<=A.sum (fun p => (1 : Real)/(p : Real))+(h : Real)
  linarith only [hfirst,hsum,hnonneg,hT,hband]

theorem tail_reciprocal_mertens_band (K h Q : Nat)
    (hK : 12<=K) (hKQ : K<=Q) (hh : 0<h) :
    Real.log (Real.log (Q : Real))-Real.log (Real.log (K : Real))-2*mertensBudget-(h : Real)<=
      (tailPrimeSet K h Q).sum (fun p => (1 : Real)/(p : Real)) /\
    (tailPrimeSet K h Q).sum (fun p => (1 : Real)/(p : Real))<=
      Real.log (Real.log (Q : Real))-Real.log (Real.log (K : Real))+2*mertensBudget := by
  have hlQ := reciprocal_prime_lower Q (by omega)
  have huQ := reciprocal_prime_log_bound Q (by omega)
  have hlK := reciprocal_prime_lower K (by omega)
  have huK := reciprocal_prime_log_bound K (by omega)
  have hm := tail_reciprocal_missing_mass K h Q hh hKQ
  have hu := tail_reciprocal_upper K h Q hKQ
  exact And.intro (by linarith only [hlQ,huK,hm]) (by linarith only [huQ,hlK,hu])

theorem tail_reciprocal_square_bound (K h Q : Nat) (hK : 12<=K) (hKQ : K<=Q) :
    (tailPrimeSet K h Q).sum (fun p => (1 : Real)/(p : Real)^2)<=1/(K : Real) := by
  apply FiniteField.QuadraticPairEuler.sum_inverse_square_tail K Q (by omega) hKQ
  intro p hp
  have hd := Finset.mem_filter.mp hp
  exact Finset.mem_Ico.mpr (And.intro (by omega)
    (by have hu:=(Finset.mem_Icc.mp hd.1).2; omega))

def tailLogEnvelope (K h p : Nat) : Real :=
  if Nat.Prime p /\ K<p /\ Not (Dvd.dvd p h) then
    Real.log ((1-2/(p : Real))*(((p : Real)+1)/((p : Real)-3))) else 0

theorem tail_log_at_crest {Q : Nat} (K h : Nat) (hK : 12<=K)
    (q : BoundedModulus Q) (c : ZMod q.val)
    (hrow : crestFactor h q.val<=actualLocal (h : Int) q c) :
    Real.log (1+tailCorrection K (h : Int) q c)=tailLogEnvelope K h q.val := by
  have hcast : (((h : Int) : ZMod q.val)=0) <-> Dvd.dvd q.val h := by
    simpa only [Int.cast_natCast] using (CharP.cast_eq_zero_iff (ZMod q.val) q.val h)
  by_cases hp : Nat.Prime q.val
  . letI : Fact (Nat.Prime q.val) := Fact.mk hp
    by_cases hg : K<q.val /\ Not (((h : Int) : ZMod q.val)=0)
    . have hnd : Not (Dvd.dvd q.val h) := fun hd => hg.2 (hcast.mpr hd)
      have hgn : Nat.Prime q.val /\ K<q.val /\ Not (Dvd.dvd q.val h) :=
        And.intro hp (And.intro hg.1 hnd)
      have h13 : 13<=q.val := by omega
      have hcf : Nat.Prime q.val /\ 13<=q.val /\ Not (Dvd.dvd q.val h) :=
        And.intro hp (And.intro h13 hnd)
      have h5 : 5<=q.val /\ Not (((h : Int) : ZMod q.val)=0) :=
        And.intro (by omega) hg.2
      have hqR : (13 : Real)<=(q.val : Real) := by exact_mod_cast h13
      have hlo := hrow
      simp only [crestFactor,if_pos hcf,actualLocal,dif_pos hp,if_pos h5] at hlo
      have hhi := (trace_free_weight_bounds c (((h : Int) : ZMod q.val)) hg.2
        (by rw [ZMod.card]; exact_mod_cast (show 5<=q.val from by omega))).2
      rw [ZMod.card] at hhi
      have hw : FiniteField.traceFreePairWeight c (((h : Int) : ZMod q.val))=
          ((q.val : Real)+1)/((q.val : Real)-3) := le_antisymm hhi hlo
      have hwpos : 0<FiniteField.traceFreePairWeight c (((h : Int) : ZMod q.val)) := by
        rw [hw]
        apply div_pos <;> linarith only [hqR]
      have hgood := (FiniteField.traceFreePairWeight_pos_iff c
        (((h : Int) : ZMod q.val)) hg.2
        (by rw [ZMod.card]; exact_mod_cast (show 5<=q.val from by omega))).mp hwpos
      have hn : Not (c=-((h : Int) : ZMod q.val)) := by
        intro he
        apply hgood.2
        rw [he]
        ring
      simp only [tailLogEnvelope,if_pos hgn,tailCorrection,dif_pos hp,if_pos hg,
        FiniteField.QuadraticPairTwistLikelihood.localCorrection,
        FiniteField.QuadraticPairTwistLikelihood.admissibilityMask,
        if_neg hgood.1,if_neg hn,ZMod.card,hw]
      congr 1
      ring
    . have hgn : Not (Nat.Prime q.val /\ K<q.val /\ Not (Dvd.dvd q.val h)) := by
        intro he
        apply hg
        refine And.intro he.2.1 ?_
        intro hz
        exact he.2.2 (hcast.mp hz)
      simp only [tailLogEnvelope,if_neg hgn,tailCorrection,dif_pos hp,if_neg hg,
        add_zero,Real.log_one,le_refl]
  . have hgn : Not (Nat.Prime q.val /\ K<q.val /\ Not (Dvd.dvd q.val h)) :=
      fun he => hp he.1
    simp [tailLogEnvelope,tailCorrection,hp,hgn]

theorem tail_log_le_envelope {Q : Nat} (K h : Nat) (hK : 12<=K)
    (q : BoundedModulus Q) (c : ZMod q.val) :
    Real.log (1+tailCorrection K (h : Int) q c)<=tailLogEnvelope K h q.val := by
  have hcast : (((h : Int) : ZMod q.val)=0) <-> Dvd.dvd q.val h := by
    simpa only [Int.cast_natCast] using (CharP.cast_eq_zero_iff (ZMod q.val) q.val h)
  by_cases hp : Nat.Prime q.val
  . letI : Fact (Nat.Prime q.val) := Fact.mk hp
    by_cases hg : K<q.val /\ Not (((h : Int) : ZMod q.val)=0)
    . have hnd : Not (Dvd.dvd q.val h) := fun hd => hg.2 (hcast.mpr hd)
      have hgn : Nat.Prime q.val /\ K<q.val /\ Not (Dvd.dvd q.val h) :=
        And.intro hp (And.intro hg.1 hnd)
      have hqR : (13 : Real)<=(q.val : Real) := by exact_mod_cast (show 13<=q.val from by omega)
      have h0 : 0<(q.val : Real) := by linarith only [hqR]
      have h3 : 0<(q.val : Real)-3 := by linarith only [hqR]
      have hfac : 0<=1-2/(q.val : Real) := by
        apply sub_nonneg.mpr
        apply (div_le_one h0).mpr
        linarith only [hqR]
      have hr1 : 1<=(1-2/(q.val : Real))*(((q.val : Real)+1)/((q.val : Real)-3)) := by
        have hid : (1-2/(q.val : Real))*(((q.val : Real)+1)/((q.val : Real)-3))-1=
            2*((q.val : Real)-1)/((q.val : Real)*((q.val : Real)-3)) := by
          field_simp [ne_of_gt h0,ne_of_gt h3] <;> ring
        have hn : 0<=2*((q.val : Real)-1)/((q.val : Real)*((q.val : Real)-3)) := by
          apply div_nonneg
          . nlinarith only [hqR]
          . positivity
        linarith only [hid,hn]
      have ha := tail_correction_abs_half K (h : Int) (by omega) q c
      have hpos : 0<1+tailCorrection K (h : Int) q c := by
        have hl := (abs_le.mp ha).1
        linarith only [hl]
      rw [tailLogEnvelope,if_pos hgn]
      apply Real.log_le_log hpos
      simp only [tailCorrection,dif_pos hp,if_pos hg,
        FiniteField.QuadraticPairTwistLikelihood.localCorrection,ZMod.card]
      by_cases hc : c=0
      . simpa [hc,FiniteField.traceFreePairWeight_zero,
          FiniteField.QuadraticPairTwistLikelihood.admissibilityMask] using hr1
      . by_cases hn : c=-((h : Int) : ZMod q.val)
        . simpa [hn,FiniteField.traceFreePairWeight_neg_shift,
            FiniteField.QuadraticPairTwistLikelihood.admissibilityMask] using hr1
        . have hu := (trace_free_weight_bounds c (((h : Int) : ZMod q.val)) hg.2
            (by rw [ZMod.card]; exact_mod_cast (show 5<=q.val from by omega))).2
          rw [ZMod.card] at hu
          have hi := mul_le_mul_of_nonneg_left hu hfac
          simp only [FiniteField.QuadraticPairTwistLikelihood.admissibilityMask,if_neg hc,if_neg hn]
          linarith only [hi]
    . have hgn : Not (Nat.Prime q.val /\ K<q.val /\ Not (Dvd.dvd q.val h)) := by
        intro he
        apply hg
        refine And.intro he.2.1 ?_
        intro hz
        exact he.2.2 (hcast.mp hz)
      simp only [tailLogEnvelope,if_neg hgn,tailCorrection,dif_pos hp,if_neg hg,
        add_zero,Real.log_one,le_refl]
  . have hgn : Not (Nat.Prime q.val /\ K<q.val /\ Not (Dvd.dvd q.val h)) :=
      fun he => hp he.1
    simp [tailLogEnvelope,tailCorrection,hp,hgn]

theorem sum_tail_log_envelope (K h Q : Nat) :
    (Finset.Icc 1 Q).attach.sum (fun q => tailLogEnvelope K h q.val)=
      (tailPrimeSet K h Q).sum (fun p =>
        Real.log ((1-2/(p : Real))*(((p : Real)+1)/((p : Real)-3)))) := by
  rw [Finset.sum_attach]
  simp only [tailPrimeSet,Finset.sum_filter,tailLogEnvelope]

theorem envelope_sum_bounds (K h Q : Nat) (hK : 12<=K) (hKQ : K<=Q) :
    2*((tailPrimeSet K h Q).sum (fun p => (1 : Real)/(p : Real)))<=
      (tailPrimeSet K h Q).sum (fun p =>
        Real.log ((1-2/(p : Real))*(((p : Real)+1)/((p : Real)-3)))) /\
    (tailPrimeSet K h Q).sum (fun p =>
        Real.log ((1-2/(p : Real))*(((p : Real)+1)/((p : Real)-3))))<=
      2*((tailPrimeSet K h Q).sum (fun p => (1 : Real)/(p : Real)))+6/(K : Real) := by
  let T := tailPrimeSet K h Q
  have hsmall := tail_reciprocal_square_bound K h Q hK hKQ
  have hlo := Finset.sum_le_sum (fun p (hp : Membership.mem T p) =>
    FiniteField.QuadraticPairTwistExtrema.frozen_ratio_log_lower (p : Real)
      (by have hd:=(Finset.mem_filter.mp hp).2; exact_mod_cast (show 3<p from by omega)))
  have hhi := Finset.sum_le_sum (fun p (hp : Membership.mem T p) =>
    FiniteField.QuadraticPairTwistExtrema.frozen_ratio_log_upper (p : Real)
      (by have hd:=(Finset.mem_filter.mp hp).2; exact_mod_cast (show 13<=p from by omega)))
  have hidlo : T.sum (fun p => 2/(p : Real))=
      2*(T.sum (fun p => (1 : Real)/(p : Real))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hidhi : T.sum (fun p => 2/(p : Real)+6/(p : Real)^2)=
      2*(T.sum (fun p => (1 : Real)/(p : Real)))+
        6*(T.sum (fun p => (1 : Real)/(p : Real)^2)) := by
    rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro p _ <;> ring
  rw [hidlo] at hlo
  rw [hidhi] at hhi
  change T.sum (fun p => (1 : Real)/(p : Real)^2)<=1/(K : Real) at hsmall
  constructor
  . exact hlo
  . change T.sum (fun p => Real.log ((1-2/(p : Real))*(((p : Real)+1)/((p : Real)-3))))<=
      2*(T.sum (fun p => (1 : Real)/(p : Real)))+6/(K : Real)
    have hscaled : 6*(T.sum (fun p => (1 : Real)/(p : Real)^2))<=6/(K : Real) := by
      calc
        _ <= 6*(1/(K : Real)) := mul_le_mul_of_nonneg_left hsmall (by norm_num)
        _ = _ := by ring
    linarith only [hhi,hscaled]

theorem tail_log_sum_le_maximum (K h Q n : Nat) (hK : 12<=K) :
    tailLogSum K (h : Int) Q n<=
      (tailPrimeSet K h Q).sum (fun p =>
        Real.log ((1-2/(p : Real))*(((p : Real)+1)/((p : Real)-3)))) := by
  calc
    _ <= (Finset.Icc 1 Q).attach.sum (fun q => tailLogEnvelope K h q.val) := by
      apply Finset.sum_le_sum
      intro q _
      exact tail_log_le_envelope K h hK q (n : ZMod q.val)
    _ = _ := sum_tail_log_envelope K h Q

theorem tail_log_sum_at_crest (K h Q n : Nat) (hK : 12<=K)
    (hrows : forall q : BoundedModulus Q,
      crestFactor h q.val<=actualLocal (h : Int) q (n : ZMod q.val)) :
    tailLogSum K (h : Int) Q n=
      (tailPrimeSet K h Q).sum (fun p =>
        Real.log ((1-2/(p : Real))*(((p : Real)+1)/((p : Real)-3)))) := by
  calc
    _ = (Finset.Icc 1 Q).attach.sum (fun q => tailLogEnvelope K h q.val) := by
      apply Finset.sum_congr rfl
      intro q _
      exact tail_log_at_crest K h hK q _ (hrows q)
    _ = _ := sum_tail_log_envelope K h Q

theorem tail_log_two_cutoff_upper (K h Q n : Nat)
    (hK : 12<=K) (hKQ : K<=Q) (hh : 0<h) :
    tailLogSum K (h : Int) Q n<=
      2*(Real.log (Real.log (Q : Real))-Real.log (Real.log (K : Real)))+4*mertensBudget+1 := by
  have hfirst := tail_log_sum_le_maximum K h Q n hK
  have henv := (envelope_sum_bounds K h Q hK hKQ).2
  have hm := (tail_reciprocal_mertens_band K h Q hK hKQ hh).2
  have hKR : (12 : Real)<=(K : Real) := by exact_mod_cast hK
  have hsmall : (6 : Real)/(K : Real)<=1 :=
    (div_le_one (by linarith only [hKR])).mpr (by linarith only [hKR])
  linarith only [hfirst,henv,hm,hsmall]

theorem tail_log_two_cutoff_at_crest (K h Q n : Nat)
    (hK : 12<=K) (hKQ : K<=Q) (hh : 0<h)
    (hrows : forall q : BoundedModulus Q,
      crestFactor h q.val<=actualLocal (h : Int) q (n : ZMod q.val)) :
    2*(Real.log (Real.log (Q : Real))-Real.log (Real.log (K : Real)))-
        4*mertensBudget-2*(h : Real)<=tailLogSum K (h : Int) Q n /\
    tailLogSum K (h : Int) Q n<=
      2*(Real.log (Real.log (Q : Real))-Real.log (Real.log (K : Real)))+4*mertensBudget+1 := by
  have hlo := (envelope_sum_bounds K h Q hK hKQ).1
  have hm := (tail_reciprocal_mertens_band K h Q hK hKQ hh).1
  have he := tail_log_sum_at_crest K h Q n hK hrows
  exact And.intro (by linarith only [hlo,hm,he]) (tail_log_two_cutoff_upper K h Q n hK hKQ hh)

theorem full_period_compensation (K Q n : Nat) (h : Int) :
    compensatedPacket K h (primePeriod Q) Q n=actualPacket h Q n := by
  unfold compensatedPacket actualPacket
  apply Finset.prod_congr rfl
  intro q _
  by_cases hp : Nat.Prime q.val
  . have hm : Membership.mem ((Finset.Icc 1 Q).attach.filter (fun r => Nat.Prime r.val)) q :=
      Finset.mem_filter.mpr (And.intro (Finset.mem_attach _ q) hp)
    have hd : Dvd.dvd q.val (primePeriod Q) :=
      Finset.dvd_prod_of_mem (fun r : BoundedModulus Q => r.val) hm
    have hz : ((primePeriod Q) : ZMod q.val)=0 :=
      (CharP.cast_eq_zero_iff (ZMod q.val) q.val (primePeriod Q)).mpr hd
    simp only [compensatedLocal,if_pos hz]
  . simp [compensatedLocal,actualLocal,hybridLocal,hp]

def normalizedRatio (K Q : Nat) : Real := (Real.log (Q : Real)/Real.log (K : Real))^2

def growthLower (h : Nat) : Real := Real.exp (-4*mertensBudget-2*(h : Real))

def growthUpper : Real := Real.exp (4*mertensBudget+1)

theorem growth_lower_pos (h : Nat) : 0<growthLower h := Real.exp_pos _

theorem growth_upper_pos : 0<growthUpper := Real.exp_pos _

theorem normalized_ratio_pos (K Q : Nat) (hK : 12<=K) (hKQ : K<=Q) :
    0<normalizedRatio K Q := by
  unfold normalizedRatio
  apply sq_pos_of_pos
  apply div_pos
  . apply Real.log_pos
    exact_mod_cast (show 1<Q from by omega)
  . apply Real.log_pos
    exact_mod_cast (show 1<K from by omega)

theorem exp_log_cutoff_ratio (K Q : Nat) (hK : 12<=K) (hKQ : K<=Q) :
    Real.exp (2*(Real.log (Real.log (Q : Real))-Real.log (Real.log (K : Real))))=
      normalizedRatio K Q := by
  have hq : 0<Real.log (Q : Real) :=
    Real.log_pos (by exact_mod_cast (show 1<Q from by omega))
  have hk : 0<Real.log (K : Real) :=
    Real.log_pos (by exact_mod_cast (show 1<K from by omega))
  have hid : 2*(Real.log (Real.log (Q : Real))-Real.log (Real.log (K : Real)))=
      (Real.log (Real.log (Q : Real))-Real.log (Real.log (K : Real)))+
      (Real.log (Real.log (Q : Real))-Real.log (Real.log (K : Real))) := by ring
  rw [hid]
  simp only [Real.exp_add,Real.exp_sub,Real.exp_log hq,Real.exp_log hk,normalizedRatio]
  ring

theorem growth_lower_exp_identity (K h Q : Nat) (hK : 12<=K) (hKQ : K<=Q) :
    growthLower h*normalizedRatio K Q=
      Real.exp (2*(Real.log (Real.log (Q : Real))-Real.log (Real.log (K : Real)))-
        4*mertensBudget-2*(h : Real)) := by
  unfold growthLower
  rw [<- exp_log_cutoff_ratio K Q hK hKQ,<- Real.exp_add]
  congr 1
  ring

theorem growth_upper_exp_identity (K Q : Nat) (hK : 12<=K) (hKQ : K<=Q) :
    growthUpper*normalizedRatio K Q=
      Real.exp (2*(Real.log (Real.log (Q : Real))-Real.log (Real.log (K : Real)))+
        4*mertensBudget+1) := by
  unfold growthUpper
  rw [<- exp_log_cutoff_ratio K Q hK hKQ,<- Real.exp_add]
  congr 1
  ring

theorem packet_quotient_eq_exp_tail (K Q n : Nat) (h : Int) (hK : 6<=K)
    (hV : 0<hybridPacket K h Q n) :
    actualPacket h Q n/hybridPacket K h Q n=Real.exp (tailLogSum K h Q n) := by
  rw [full_packet_factorization K h hK Q n]
  field_simp [ne_of_gt hV]

theorem actual_packet_pos_at_crest (h Q n : Nat)
    (hrows : forall q : BoundedModulus Q,
      crestFactor h q.val<=actualLocal (h : Int) q (n : ZMod q.val)) :
    0<actualPacket (h : Int) Q n := by
  unfold actualPacket
  apply Finset.prod_pos
  intro q _
  exact lt_of_lt_of_le (by norm_num : (0 : Real)<1)
    (le_trans (crest_factor_ge_one h q.val) (hrows q))

theorem hybrid_packet_pos_at_crest (K h Q n : Nat) (hK : 6<=K)
    (hrows : forall q : BoundedModulus Q,
      crestFactor h q.val<=actualLocal (h : Int) q (n : ZMod q.val)) :
    0<hybridPacket K (h : Int) Q n := by
  have hU := actual_packet_pos_at_crest h Q n hrows
  have hf := full_packet_factorization K (h : Int) hK Q n
  by_contra hn
  have hle : hybridPacket K (h : Int) Q n<=0 := le_of_not_gt hn
  have hm : hybridPacket K (h : Int) Q n*Real.exp (tailLogSum K (h : Int) Q n)<=0 :=
    mul_nonpos_of_nonpos_of_nonneg hle (Real.exp_pos _).le
  rw [<- hf] at hm
  linarith only [hU,hm]

theorem likelihood_exp_upper (K h Q n : Nat)
    (hK : 12<=K) (hKQ : K<=Q) (hh : 0<h) :
    Real.exp (tailLogSum K (h : Int) Q n)<=growthUpper*normalizedRatio K Q := by
  rw [growth_upper_exp_identity K Q hK hKQ]
  exact Real.exp_le_exp.mpr (tail_log_two_cutoff_upper K h Q n hK hKQ hh)

theorem full_packet_domination (K h Q n : Nat)
    (hK : 12<=K) (hKQ : K<=Q) (hh : 0<h) :
    actualPacket (h : Int) Q n<=
      (growthUpper*normalizedRatio K Q)*hybridPacket K (h : Int) Q n := by
  have hV : 0<=hybridPacket K (h : Int) Q n := by
    unfold hybridPacket
    apply Finset.prod_nonneg
    intro q _
    exact hybrid_local_nonneg K (h : Int) q _
  calc
    _ = hybridPacket K (h : Int) Q n*Real.exp (tailLogSum K (h : Int) Q n) :=
      full_packet_factorization K (h : Int) (by omega) Q n
    _ <= hybridPacket K (h : Int) Q n*(growthUpper*normalizedRatio K Q) :=
      mul_le_mul_of_nonneg_left (likelihood_exp_upper K h Q n hK hKQ hh) hV
    _ = _ := mul_comm _ _

theorem packet_quotient_at_crest (K h Q n : Nat)
    (hK : 12<=K) (hKQ : K<=Q) (hh : 0<h)
    (hrows : forall q : BoundedModulus Q,
      crestFactor h q.val<=actualLocal (h : Int) q (n : ZMod q.val)) :
    0<hybridPacket K (h : Int) Q n /\
      growthLower h*normalizedRatio K Q<=
        actualPacket (h : Int) Q n/hybridPacket K (h : Int) Q n /\
      actualPacket (h : Int) Q n/hybridPacket K (h : Int) Q n<=
        growthUpper*normalizedRatio K Q := by
  have hV := hybrid_packet_pos_at_crest K h Q n (by omega) hrows
  have hb := tail_log_two_cutoff_at_crest K h Q n hK hKQ hh hrows
  have he := packet_quotient_eq_exp_tail K Q n (h : Int) (by omega) hV
  refine And.intro hV (And.intro ?_ ?_)
  . rw [he,growth_lower_exp_identity K h Q hK hKQ]
    exact Real.exp_le_exp.mpr hb.1
  . rw [he]
    exact likelihood_exp_upper K h Q n hK hKQ hh

theorem packet_quotient_eq_frozen (K h Q a t : Nat) (hK : 6<=K)
    (hV : 0<hybridPacket K (h : Int) Q (a+primePeriod Q*t)) :
    actualPacket (h : Int) Q (a+primePeriod Q*t)/
      hybridPacket K (h : Int) Q (a+primePeriod Q*t)=
        Real.exp (frozenLogSum K (h : Int) a (primePeriod Q) Q) := by
  have hf := compensated_frozen_factor K (h : Int) a (primePeriod Q) hK Q t
  rw [full_period_compensation] at hf
  rw [hf]
  field_simp [ne_of_gt hV]

theorem sharp_frozen_packet_ratio (h Q : Nat) (hh : 0<h) (heven : Dvd.dvd 2 h) :
    exists a : Nat, a<primePeriod Q /\
      forall K : Nat, 12<=K -> K<=Q -> forall t : Nat,
        0<hybridPacket K (h : Int) Q (a+primePeriod Q*t) /\
        actualPacket (h : Int) Q (a+primePeriod Q*t)/
          hybridPacket K (h : Int) Q (a+primePeriod Q*t)=
            Real.exp (frozenLogSum K (h : Int) a (primePeriod Q) Q) /\
        growthLower h*normalizedRatio K Q<=
          actualPacket (h : Int) Q (a+primePeriod Q*t)/
            hybridPacket K (h : Int) Q (a+primePeriod Q*t) /\
        actualPacket (h : Int) Q (a+primePeriod Q*t)/
          hybridPacket K (h : Int) Q (a+primePeriod Q*t)<=
            growthUpper*normalizedRatio K Q := by
  have hex := exists_integer_crest_rows h Q heven
  let a : Nat := Classical.choose hex
  have ha := Classical.choose_spec hex
  refine Exists.intro a (And.intro ha.1 ?_)
  intro K hK hKQ t
  have hc := packet_quotient_at_crest K h Q (a+primePeriod Q*t) hK hKQ hh (ha.2 t)
  exact And.intro hc.1 (And.intro
    (packet_quotient_eq_frozen K h Q a t (by omega) hc.1) hc.2)

end PrimeFactorOscillations.FiniteFieldFrozenGrowth
