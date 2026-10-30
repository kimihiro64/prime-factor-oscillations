/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerTail
import PrimeFactorOscillations.Helpers.GenericOddMertens

/-!
# Weighted integer replacement for positive finite-field pair packets

The common actual/hybrid packet envelope is used before estimating their
difference. The unconditional cached Mertens provider supplies the logarithmic
envelope. The full L1 replacement theorem is uniform in the integer interval
origin, shift and cutoff, and retains the exact opening mask, all small-prime
rows and every prime-dividing-shift fallback.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerMass
attribute [local instance] Classical.propDecidable

def mertensBudget : Real :=
  abs Mertens.M+PrimeFactorUnimodality.mertensErrorConstant/Real.log 2

theorem reciprocal_prime_log_bound (Q : Nat) (hQ : 2<=Q) :
    PrimeFactorUnimodality.reciprocalPrimeSumBelow (Q+1)<=
      Real.log (Real.log Q)+mertensBudget := by
  have hu := PrimeFactorUnimodality.reciprocalPrimeSumBelow_upper_of_estimate
    PrimeFactorUnimodality.hasMertensReciprocalPrimeEstimate hQ
  have hl2 : (0 : Real)<Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2<=Real.log (Q : Real) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hQ)
  have he := div_le_div_of_nonneg_left
    PrimeFactorUnimodality.mertensErrorConstant_nonneg hl2 hl
  have hm := le_abs_self Mertens.M
  dsimp only [mertensBudget]
  linarith only [hu,he,hm]

theorem coupled_exp_difference_le (u v B t : Real)
    (hv0 : 0<=v) (hu : u=v*Real.exp t) (huB : u<=B) (hvB : v<=B) :
    abs (u-v)<=B*abs t := by
  have hu0 : 0<=u := by rw [hu]; exact mul_nonneg hv0 (Real.exp_pos _).le
  by_cases ht : 0<=t
  . have he : 1<=Real.exp t := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr ht
    have huv : v<=u := by
      rw [hu]
      nlinarith only [mul_nonneg hv0 (sub_nonneg.mpr he)]
    have hi := Real.add_one_le_exp (-t)
    have hh := mul_le_mul_of_nonneg_left hi hu0
    have hid : u*Real.exp (-t)=v := by
      rw [hu,mul_assoc,<- Real.exp_add]
      simp
    rw [hid] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr huv),abs_of_nonneg ht]
    have hm := mul_le_mul_of_nonneg_right huB ht
    nlinarith only [hh,hm]
  . have ht0 : t<=0 := le_of_not_ge ht
    have he : Real.exp t<=1 := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr ht0
    have huv : u<=v := by
      rw [hu]
      nlinarith only [mul_nonneg hv0 (sub_nonneg.mpr he)]
    have hi := Real.add_one_le_exp t
    have hh := mul_le_mul_of_nonneg_left hi hv0
    rw [<- hu] at hh
    rw [abs_of_nonpos (sub_nonpos.mpr huv),abs_of_nonpos ht0]
    have hm := mul_le_mul_of_nonneg_right hvB (neg_nonneg.mpr ht0)
    nlinarith only [hh,hm]

open PrimeFactorOscillations.FiniteFieldIntegerTail

theorem integer_l1_of_envelope {Q N : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat)
    (U V : Fin N -> Real) (B : Real) (hB : 0<=B)
    (hV : forall j, 0<=V j)
    (hfactor : forall j, U j=V j*Real.exp (tailLogSum K h Q (M+1+j.val)))
    (hUcap : forall j, U j<=B) (hVcap : forall j, V j<=B) :
    (Finset.univ.sum fun j : Fin N => abs (U j-V j)) <=
      B*Real.sqrt (500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real)) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
    (fun _ => (1 : Real)) (fun j => abs (tailLogSum K h Q (M+1+j.val)))
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one,sq_abs] at hc
  have he := tail_log_interval_energy K h hK hKQ hN M
  have hm := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)
  have hs : (Finset.univ.sum fun j : Fin N =>
      abs (tailLogSum K h Q (M+1+j.val)))^2 <=
      500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real) := by
    calc
      _ <= (N : Real)*(Finset.univ.sum fun j : Fin N =>
        (tailLogSum K h Q (M+1+j.val))^2) := hc
      _ <= (N : Real)*(500*((N : Real)+(Q : Real)^2)/(K : Real)) := hm
      _ = _ := by ring
  have hr : 0<=500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real) := by positivity
  have hroot := Real.sq_sqrt hr
  have hnonneg := Real.sqrt_nonneg (500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real))
  have hsum : (Finset.univ.sum fun j : Fin N =>
      abs (tailLogSum K h Q (M+1+j.val))) <=
      Real.sqrt (500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real)) := by
    nlinarith only [hs,hroot,hnonneg]
  calc
    _ <= Finset.univ.sum (fun j : Fin N =>
        B*abs (tailLogSum K h Q (M+1+j.val))) := by
      apply Finset.sum_le_sum
      intro j _
      exact coupled_exp_difference_le (U j) (V j) B _ (hV j)
        (hfactor j) (hUcap j) (hVcap j)
    _ = B*(Finset.univ.sum fun j : Fin N =>
        abs (tailLogSum K h Q (M+1+j.val))) := by rw [Finset.mul_sum]
    _ <= _ := mul_le_mul_of_nonneg_left hsum hB

def integerMask {Q : Nat} (h : Int) (q : BoundedModulus Q) (c : ZMod q.val) : Real :=
  if c=0 then 0 else if c=-(h : ZMod q.val) then 0 else 1

def flatFallback {Q : Nat} (h : Int) (q : BoundedModulus Q) (c : ZMod q.val) : Real :=
  ((q.val : Real)/((q.val : Real)-(if (h : ZMod q.val)=0 then 1 else 2)))*
    integerMask h q c

def actualLocal {Q : Nat} (h : Int) (q : BoundedModulus Q) (c : ZMod q.val) : Real :=
  if hp : Nat.Prime q.val then
    letI : Fact (Nat.Prime q.val) := Fact.mk hp
    if 5<=q.val /\ Not ((h : ZMod q.val)=0)
      then _root_.FiniteField.traceFreePairWeight c (h : ZMod q.val)
      else flatFallback h q c
  else 1

def hybridLocal {Q : Nat} (K : Nat) (h : Int)
    (q : BoundedModulus Q) (c : ZMod q.val) : Real :=
  if Nat.Prime q.val then
    if q.val<=K then actualLocal h q c else flatFallback h q c
  else 1

def actualPacket (h : Int) (Q n : Nat) : Real :=
  (Finset.Icc 1 Q).attach.prod (fun q => actualLocal h q (n : ZMod q.val))

def hybridPacket (K : Nat) (h : Int) (Q n : Nat) : Real :=
  (Finset.Icc 1 Q).attach.prod (fun q => hybridLocal K h q (n : ZMod q.val))

theorem integer_mask_bounds {Q : Nat} (h : Int) (q : BoundedModulus Q)
    (c : ZMod q.val) : 0<=integerMask h q c /\ integerMask h q c<=1 := by
  unfold integerMask
  split_ifs <;> norm_num

theorem flat_fallback_nonneg {Q : Nat} (h : Int) (q : BoundedModulus Q)
    (hq : 2<=q.val) (c : ZMod q.val) : 0<=flatFallback h q c := by
  have hqr : (2 : Real)<=(q.val : Real) := by exact_mod_cast hq
  have hnu : (if (h : ZMod q.val)=0 then (1 : Real) else 2)<=2 := by
    split_ifs <;> norm_num
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg q.val) (by linarith only [hqr,hnu]))
    (integer_mask_bounds h q c).1

theorem trace_free_weight_bounds {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (c h : F) (hh : Not (h=0)) (hq : 5<=(Fintype.card F : Real)) :
    0<=_root_.FiniteField.traceFreePairWeight c h /\
      _root_.FiniteField.traceFreePairWeight c h<=
        ((Fintype.card F : Real)+1)/((Fintype.card F : Real)-3) := by
  have hd : 0<=(Fintype.card F : Real)-3 := by linarith only [hq]
  have hu : 0<=((Fintype.card F : Real)+1)/((Fintype.card F : Real)-3) :=
    div_nonneg (by positivity) hd
  by_cases hc : c=0
  . simp only [hc,_root_.FiniteField.traceFreePairWeight_zero]
    exact And.intro (le_refl _) hu
  . by_cases hn : c=-h
    . simp only [hn,_root_.FiniteField.traceFreePairWeight_neg_shift]
      exact And.intro (le_refl _) hu
    . have hch : Not (c+h=0) := by
        intro hz
        apply hn
        calc
          c=(c+h)-h := by ring
          _ = -h := by rw [hz]; ring
      have hb := _root_.FiniteField.traceFreePairWeight_good_bounds c h hc hch hh hq
      exact And.intro (by linarith only [hb.1]) hb.2

theorem actual_local_nonneg {Q : Nat} (h : Int) (q : BoundedModulus Q)
    (c : ZMod q.val) : 0<=actualLocal h q c := by
  by_cases hp : Nat.Prime q.val
  . letI : Fact (Nat.Prime q.val) := Fact.mk hp
    by_cases hg : 5<=q.val /\ Not ((h : ZMod q.val)=0)
    . simp only [actualLocal,dif_pos hp,if_pos hg]
      apply (trace_free_weight_bounds c (h : ZMod q.val) hg.2 _).1
      rw [ZMod.card]
      exact_mod_cast hg.1
    . simp only [actualLocal,dif_pos hp,if_neg hg]
      exact flat_fallback_nonneg h q hp.two_le c
  . simp [actualLocal,hp]

theorem hybrid_local_nonneg {Q : Nat} (K : Nat) (h : Int)
    (q : BoundedModulus Q) (c : ZMod q.val) : 0<=hybridLocal K h q c := by
  by_cases hp : Nat.Prime q.val
  . by_cases hk : q.val<=K
    . simp only [hybridLocal,if_pos hp,if_pos hk]
      exact actual_local_nonneg h q c
    . simp only [hybridLocal,if_pos hp,if_neg hk]
      exact flat_fallback_nonneg h q hp.two_le c
  . simp [hybridLocal,hp]

theorem full_local_factorization {Q : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (q : BoundedModulus Q) (c : ZMod q.val) :
    actualLocal h q c=hybridLocal K h q c*(1+tailCorrection K h q c) := by
  by_cases hp : Nat.Prime q.val
  . letI : Fact (Nat.Prime q.val) := Fact.mk hp
    by_cases hk : q.val<=K
    . have hn : Not (K<q.val) := by omega
      simp [hybridLocal,tailCorrection,hp,hk,hn]
    . have hlt : K<q.val := by omega
      have h5 : 5<=q.val := by omega
      by_cases hh : (h : ZMod q.val)=0
      . simp [actualLocal,hybridLocal,tailCorrection,hp,hk,hh]
      . have hq7 : (7 : Real)<=(Fintype.card (ZMod q.val) : Real) := by
          rw [ZMod.card]
          exact_mod_cast (show 7<=q.val from by omega)
        have he := _root_.FiniteField.QuadraticPairTwistLikelihood.local_factorization
          c (h : ZMod q.val) hq7
        simpa [actualLocal,hybridLocal,tailCorrection,hp,hk,hlt,hh,h5,
          flatFallback,integerMask,
          _root_.FiniteField.QuadraticPairTwistLikelihood.flatPairWeight,
          _root_.FiniteField.QuadraticPairTwistLikelihood.admissibilityMask,ZMod.card] using he
  . simp [actualLocal,hybridLocal,tailCorrection,hp]

theorem full_packet_factorization (K : Nat) (h : Int) (hK : 6<=K) (Q n : Nat) :
    actualPacket h Q n=hybridPacket K h Q n*Real.exp (tailLogSum K h Q n) := by
  unfold actualPacket hybridPacket
  simp_rw [full_local_factorization K h hK]
  rw [Finset.prod_mul_distrib]
  change _ = _*Real.exp (tailLogSum K h Q n)
  rw [<- tail_ratio_exp_log K h hK Q n]
  rfl

theorem hybrid_packet_nonneg (K : Nat) (h : Int) (Q n : Nat) :
    0<=hybridPacket K h Q n := by
  apply Finset.prod_nonneg
  intro q _
  exact hybrid_local_nonneg K h q _

def smallMultiplier (p : Nat) : Real :=
  (if p=2 then 2 else 1)*(if p=3 then 3 else 1)*(if p=5 then 3 else 1)

def envelopeExponent (p : Nat) : Real :=
  if Nat.Prime p /\ 7<=p then 4/(p : Real)+21/(p : Real)^2 else 0

def localEnvelope (p : Nat) : Real :=
  smallMultiplier p*Real.exp (envelopeExponent p)

def replacementConstant : Real := 18*Real.exp (4+4*mertensBudget)

theorem small_multiplier_ge_one (p : Nat) : 1<=smallMultiplier p := by
  unfold smallMultiplier
  split_ifs <;> norm_num

theorem local_envelope_ge_one (p : Nat) : 1<=localEnvelope p := by
  have hs := small_multiplier_ge_one p
  have hE : 0<=envelopeExponent p := by
    unfold envelopeExponent
    split_ifs <;> positivity
  have he : 1<=Real.exp (envelopeExponent p) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hE
  unfold localEnvelope
  nlinarith only [hs,he,mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr he)]

theorem large_local_scalar_cap (p : Nat) (hp : 7<=p) :
    ((p : Real)+1)/((p : Real)-3)<=Real.exp (4/(p : Real)+21/(p : Real)^2) := by
  have hpr : (7 : Real)<=(p : Real) := by exact_mod_cast hp
  have h0 : Not ((p : Real)=0) := ne_of_gt (by linarith only [hpr])
  have h3 : Not ((p : Real)-3=0) := ne_of_gt (by linarith only [hpr])
  have he : (4/(p : Real)+21/(p : Real)^2)-4/((p : Real)-3)=
      9*((p : Real)-7)/((p : Real)^2*((p : Real)-3)) := by
    field_simp [h0,h3] <;> ring
  have hn : 0<=9*((p : Real)-7)/((p : Real)^2*((p : Real)-3)) :=
    div_nonneg (mul_nonneg (by norm_num) (by linarith only [hpr]))
      (mul_nonneg (sq_nonneg _) (by linarith only [hpr]))
  have hr : ((p : Real)+1)/((p : Real)-3)=1+4/((p : Real)-3) := by
    field_simp [h3] <;> ring
  have hx := Real.add_one_le_exp (4/(p : Real)+21/(p : Real)^2)
  rw [hr]
  linarith only [he,hn,hx]

theorem small_multiplier_product (Q : Nat) (hQ : 6<=Q) :
    (Finset.Icc 1 Q).prod smallMultiplier=18 := by
  have h2 : Membership.mem (Finset.Icc 1 Q) 2 := Finset.mem_Icc.mpr (by omega)
  have h3 : Membership.mem (Finset.Icc 1 Q) 3 := Finset.mem_Icc.mpr (by omega)
  have h5 : Membership.mem (Finset.Icc 1 Q) 5 := Finset.mem_Icc.mpr (by omega)
  unfold smallMultiplier
  simp only [Finset.prod_mul_distrib]
  norm_num [h2,h3,h5]

theorem prime_inverse_sum (Q : Nat) :
    (Finset.Icc 1 Q).sum (fun p => if Nat.Prime p then (1 : Real)/(p : Real) else 0)=
      PrimeFactorUnimodality.reciprocalPrimeSumBelow (Q+1) := by
  rw [<- Finset.sum_filter]
  unfold PrimeFactorUnimodality.reciprocalPrimeSumBelow
  have he : (Finset.Icc 1 Q).filter Nat.Prime=Nat.primesBelow (Q+1) := by
    ext p
    change Membership.mem ((Finset.Icc 1 Q).filter Nat.Prime) p <->
      Membership.mem ((Finset.range (Q+1)).filter Nat.Prime) p
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_range]
    constructor
    . intro hp
      exact And.intro (by omega) hp.2
    . intro hp
      have h2 := hp.2.two_le
      exact And.intro (And.intro (by omega) (by omega)) hp.2
  rw [he]

theorem exponent_sum_bound (Q : Nat) (hQ : 6<=Q) :
    (Finset.Icc 1 Q).sum envelopeExponent <=
      4*PrimeFactorUnimodality.reciprocalPrimeSumBelow (Q+1)+4 := by
  have hp : forall p : Nat, envelopeExponent p <=
      4*(if Nat.Prime p then (1 : Real)/(p : Real) else 0)+
      21*(if 7<=p then (1 : Real)/(p : Real)^2 else 0) := by
    intro p
    by_cases hprime : Nat.Prime p
    . by_cases h7 : 7<=p
      . simp only [envelopeExponent,if_pos (And.intro hprime h7),if_pos hprime,if_pos h7]
        ring_nf
        exact le_refl _
      . simp only [envelopeExponent,if_neg (not_and.mpr (fun _ => h7)),
          if_pos hprime,if_neg h7]
        positivity
    . simp only [envelopeExponent,if_neg (not_and.mpr (fun hh => False.elim (hprime hh))),
        if_neg hprime,zero_mul,add_zero,zero_add]
      split_ifs <;> positivity
  have hs := Finset.sum_le_sum (fun p (_ : Membership.mem (Finset.Icc 1 Q) p) => hp p)
  have ht : (Finset.Icc 1 Q).sum
      (fun p => if 7<=p then (1 : Real)/(p : Real)^2 else 0)<=1/6 := by
    rw [<- Finset.sum_filter]
    have he : (Finset.Icc 1 Q).filter (fun p => 7<=p)=Finset.Ico 7 (Q+1) := by
      ext p
      simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ico]
      omega
    rw [he]
    simpa using _root_.FiniteField.QuadraticPairEuler.sum_inverse_square_tail
      6 Q (by omega) hQ (Finset.Ico 7 (Q+1)) (le_refl _)
  rw [Finset.sum_add_distrib,<- Finset.mul_sum,<- Finset.mul_sum,prime_inverse_sum] at hs
  linarith only [hs,ht]

theorem envelope_product_bound (Q : Nat) (hQ : 6<=Q) :
    (Finset.Icc 1 Q).prod localEnvelope <=
      replacementConstant*(Real.log (Q : Real))^4 := by
  have hs := exponent_sum_bound Q hQ
  have hm := reciprocal_prime_log_bound Q (by omega)
  have hlog : 0<Real.log (Q : Real) := Real.log_pos (by exact_mod_cast (show 1<Q from by omega))
  have heq : Real.exp (4*Real.log (Real.log (Q : Real)))=(Real.log (Q : Real))^4 := by
    rw [show 4*Real.log (Real.log (Q : Real)) =
      Real.log (Real.log (Q : Real))+Real.log (Real.log (Q : Real))+
        Real.log (Real.log (Q : Real))+Real.log (Real.log (Q : Real)) from by ring]
    simp only [Real.exp_add,Real.exp_log hlog]
    ring
  calc
    _ = 18*Real.exp ((Finset.Icc 1 Q).sum envelopeExponent) := by
      unfold localEnvelope
      rw [Finset.prod_mul_distrib,small_multiplier_product Q hQ,Real.exp_sum]
    _ <= 18*Real.exp (4*PrimeFactorUnimodality.reciprocalPrimeSumBelow (Q+1)+4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) (by norm_num)
    _ <= 18*Real.exp (4*(Real.log (Real.log (Q : Real))+mertensBudget)+4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hm])) (by norm_num)
    _ = _ := by
      rw [show 4*(Real.log (Real.log (Q : Real))+mertensBudget)+4 =
        (4+4*mertensBudget)+4*Real.log (Real.log (Q : Real)) from by ring,
        Real.exp_add,heq]
      unfold replacementConstant
      ring

open PrimeFactorOscillations.FiniteFieldIntegerTail

theorem flat_fallback_le_scalar {Q : Nat} (h : Int) (q : BoundedModulus Q)
    (hq : 2<=q.val) (c : ZMod q.val) :
    flatFallback h q c <=
      (q.val : Real)/((q.val : Real)-(if (h : ZMod q.val)=0 then 1 else 2)) := by
  have hqr : (2 : Real)<=(q.val : Real) := by exact_mod_cast hq
  have hnu : (if (h : ZMod q.val)=0 then (1 : Real) else 2)<=2 := by
    split_ifs <;> norm_num
  have hd : 0<=(q.val : Real)/((q.val : Real)-
      (if (h : ZMod q.val)=0 then 1 else 2)) :=
    div_nonneg (Nat.cast_nonneg _) (by linarith only [hqr,hnu])
  unfold flatFallback
  have hb := mul_le_mul_of_nonneg_left (integer_mask_bounds h q c).2 hd
  simpa only [mul_one] using hb

theorem flat_fallback_le_small {Q : Nat} (h : Int) (q : BoundedModulus Q)
    (hsmall : q.val=2 \/ q.val=3 \/ q.val=5) (c : ZMod q.val) :
    flatFallback h q c<=smallMultiplier q.val := by
  have hq : 2<=q.val := by rcases hsmall with h2 | h3 | h5 <;> omega
  have hb := flat_fallback_le_scalar h q hq c
  by_cases hh : (h : ZMod q.val)=0
  . rw [if_pos hh] at hb
    rcases hsmall with h2 | h3 | h5
    all_goals simp_all [smallMultiplier]
    all_goals linarith only [hb]
  . rw [if_neg hh] at hb
    rcases hsmall with h2 | h3 | h5
    all_goals simp_all [smallMultiplier]
    all_goals linarith only [hb]

theorem actual_local_le_small {Q : Nat} (h : Int) (q : BoundedModulus Q)
    (hsmall : q.val=2 \/ q.val=3 \/ q.val=5) (c : ZMod q.val) :
    actualLocal h q c<=smallMultiplier q.val := by
  have hp : Nat.Prime q.val := by
    rcases hsmall with h2 | h3 | h5
    all_goals norm_num [*]
  letI : Fact (Nat.Prime q.val) := Fact.mk hp
  by_cases hg : 5<=q.val /\ Not ((h : ZMod q.val)=0)
  . have h5 : q.val=5 := by rcases hsmall with h2 | h3 | h5 <;> omega
    have hq : (5 : Real)<=(Fintype.card (ZMod q.val) : Real) := by
      norm_num [ZMod.card,h5]
    have hb := (trace_free_weight_bounds c (h : ZMod q.val) hg.2 hq).2
    simp only [actualLocal,dif_pos hp,if_pos hg]
    norm_num [ZMod.card,h5] at hb
    have hs : smallMultiplier q.val=3 := by norm_num [smallMultiplier,h5]
    rw [hs]
    exact hb
  . simp only [actualLocal,dif_pos hp,if_neg hg]
    exact flat_fallback_le_small h q hsmall c

theorem flat_fallback_le_large {Q : Nat} (h : Int) (q : BoundedModulus Q)
    (hq : 7<=q.val) (c : ZMod q.val) :
    flatFallback h q c<=((q.val : Real)+1)/((q.val : Real)-3) := by
  have hqr : (7 : Real)<=(q.val : Real) := by exact_mod_cast hq
  have hb := flat_fallback_le_scalar h q (by omega) c
  have hd : flatFallback h q c<=(q.val : Real)/((q.val : Real)-2) := by
    by_cases hh : (h : ZMod q.val)=0
    . rw [if_pos hh] at hb
      apply le_trans hb
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith only [hqr])
        (show (q.val : Real)-2<=(q.val : Real)-1 from by linarith)
    . rwa [if_neg hh] at hb
  have h2 : Not ((q.val : Real)-2=0) := ne_of_gt (by linarith only [hqr])
  have h3 : Not ((q.val : Real)-3=0) := ne_of_gt (by linarith only [hqr])
  have he : ((q.val : Real)+1)/((q.val : Real)-3)-
      (q.val : Real)/((q.val : Real)-2)=
      2*((q.val : Real)-1)/(((q.val : Real)-3)*((q.val : Real)-2)) := by
    field_simp [h2,h3] <;> ring
  have hn : 0<=2*((q.val : Real)-1)/(((q.val : Real)-3)*((q.val : Real)-2)) :=
    div_nonneg (mul_nonneg (by norm_num) (by linarith only [hqr]))
      (mul_nonneg (by linarith only [hqr]) (by linarith only [hqr]))
  linarith only [hd,he,hn]

theorem actual_local_le_large {Q : Nat} (h : Int) (q : BoundedModulus Q)
    (hp : Nat.Prime q.val) (hq : 7<=q.val) (c : ZMod q.val) :
    actualLocal h q c<=((q.val : Real)+1)/((q.val : Real)-3) := by
  letI : Fact (Nat.Prime q.val) := Fact.mk hp
  by_cases hg : 5<=q.val /\ Not ((h : ZMod q.val)=0)
  . have hF : (5 : Real)<=(Fintype.card (ZMod q.val) : Real) := by
      rw [ZMod.card]
      exact_mod_cast (show 5<=q.val from by omega)
    simp only [actualLocal,dif_pos hp,if_pos hg]
    simpa only [ZMod.card] using (trace_free_weight_bounds c (h : ZMod q.val) hg.2 hF).2
  . simp only [actualLocal,dif_pos hp,if_neg hg]
    exact flat_fallback_le_large h q hq c

theorem actual_local_envelope {Q : Nat} (h : Int) (q : BoundedModulus Q)
    (c : ZMod q.val) : actualLocal h q c<=localEnvelope q.val := by
  by_cases hp : Nat.Prime q.val
  . by_cases h2 : q.val=2
    . have hb := actual_local_le_small h q (Or.inl h2) c
      simpa [localEnvelope,envelopeExponent,h2] using hb
    . by_cases h3 : q.val=3
      . have hb := actual_local_le_small h q (Or.inr (Or.inl h3)) c
        simpa [localEnvelope,envelopeExponent,h3] using hb
      . by_cases h5 : q.val=5
        . have hb := actual_local_le_small h q (Or.inr (Or.inr h5)) c
          simpa [localEnvelope,envelopeExponent,h5] using hb
        . have hn4 : Not (q.val=4) := by intro he; norm_num [he] at hp
          have hn6 : Not (q.val=6) := by intro he; norm_num [he] at hp
          have h7 : 7<=q.val := by have hmin := hp.two_le; omega
          have hb := le_trans (actual_local_le_large h q hp h7 c)
            (large_local_scalar_cap q.val h7)
          simpa only [localEnvelope,smallMultiplier,if_neg h2,if_neg h3,if_neg h5,
            one_mul,envelopeExponent,if_pos (And.intro hp h7)] using hb
  . simpa only [actualLocal,dif_neg hp] using local_envelope_ge_one q.val

theorem hybrid_local_envelope {Q : Nat} (K : Nat) (h : Int) (hK : 6<=K)
    (q : BoundedModulus Q) (c : ZMod q.val) :
    hybridLocal K h q c<=localEnvelope q.val := by
  by_cases hp : Nat.Prime q.val
  . by_cases hk : q.val<=K
    . simp only [hybridLocal,if_pos hp,if_pos hk]
      exact actual_local_envelope h q c
    . have h7 : 7<=q.val := by omega
      have h2 : Not (q.val=2) := by omega
      have h3 : Not (q.val=3) := by omega
      have h5 : Not (q.val=5) := by omega
      have hb := le_trans (flat_fallback_le_large h q h7 c)
        (large_local_scalar_cap q.val h7)
      simpa only [hybridLocal,if_pos hp,if_neg hk,localEnvelope,smallMultiplier,
        if_neg h2,if_neg h3,if_neg h5,one_mul,envelopeExponent,
        if_pos (And.intro hp h7)] using hb
  . simpa only [hybridLocal,if_neg hp] using local_envelope_ge_one q.val

theorem real_product_le_of_nonneg {I : Type*} [DecidableEq I]
    (s : Finset I) (f g : I -> Real) :
    (forall i, Membership.mem s i -> 0<=f i) ->
    (forall i, Membership.mem s i -> f i<=g i) ->
    s.prod f<=s.prod g := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    intro hf hfg
    have hf' : forall i, Membership.mem s i -> 0<=f i :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfg' : forall i, Membership.mem s i -> f i<=g i :=
      fun i hi => hfg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha,Finset.prod_insert ha]
    exact mul_le_mul (hfg a (Finset.mem_insert_self a s)) (ih hf' hfg')
      (Finset.prod_nonneg hf')
      (le_trans (hf a (Finset.mem_insert_self a s)) (hfg a (Finset.mem_insert_self a s)))

theorem actual_packet_envelope (h : Int) (Q n : Nat) (hQ : 6<=Q) :
    actualPacket h Q n<=replacementConstant*(Real.log (Q : Real))^4 := by
  calc
    _ <= (Finset.Icc 1 Q).attach.prod (fun q => localEnvelope q.val) := by
      apply real_product_le_of_nonneg
      . intro q _
        exact actual_local_nonneg h q _
      . intro q _
        exact actual_local_envelope h q _
    _ = (Finset.Icc 1 Q).prod localEnvelope := Finset.prod_attach (Finset.Icc 1 Q) localEnvelope
    _ <= _ := envelope_product_bound Q hQ

theorem hybrid_packet_envelope (K : Nat) (h : Int) (Q n : Nat)
    (hK : 6<=K) (hKQ : K<=Q) :
    hybridPacket K h Q n<=replacementConstant*(Real.log (Q : Real))^4 := by
  calc
    _ <= (Finset.Icc 1 Q).attach.prod (fun q => localEnvelope q.val) := by
      apply real_product_le_of_nonneg
      . intro q _
        exact hybrid_local_nonneg K h q _
      . intro q _
        exact hybrid_local_envelope K h hK q _
    _ = (Finset.Icc 1 Q).prod localEnvelope := Finset.prod_attach (Finset.Icc 1 Q) localEnvelope
    _ <= _ := envelope_product_bound Q (by omega)

theorem integer_packet_l1_replacement {Q N : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat) :
    (Finset.univ.sum fun j : Fin N =>
      abs (actualPacket h Q (M+1+j.val)-hybridPacket K h Q (M+1+j.val))) <=
      replacementConstant*(Real.log (Q : Real))^4*
        Real.sqrt (500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real)) := by
  apply integer_l1_of_envelope K h hK hKQ hN M
    (fun j => actualPacket h Q (M+1+j.val))
    (fun j => hybridPacket K h Q (M+1+j.val))
    (replacementConstant*(Real.log (Q : Real))^4)
  . unfold replacementConstant
    positivity
  . intro j
    exact hybrid_packet_nonneg K h Q _
  . intro j
    exact full_packet_factorization K h hK Q _
  . intro j
    exact actual_packet_envelope h Q _ (by omega)
  . intro j
    exact hybrid_packet_envelope K h Q _ hK hKQ

open PrimeFactorOscillations.FiniteFieldIntegerTail

theorem integer_packet_mass_replacement {Q N : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat) :
    abs ((Finset.univ.sum fun j : Fin N => actualPacket h Q (M+1+j.val))-
      (Finset.univ.sum fun j : Fin N => hybridPacket K h Q (M+1+j.val))) <=
      replacementConstant*(Real.log (Q : Real))^4*
        Real.sqrt (500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real)) := by
  rw [<- Finset.sum_sub_distrib]
  exact le_trans (Finset.abs_sum_le_sum_abs _ _)
    (integer_packet_l1_replacement K h hK hKQ hN M)

theorem weighted_bad_mass_bound {Q N : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat)
    (epsilon : Real) (heps : 0<epsilon) :
    ((tailBadIndices (N:=N) K h Q M epsilon).sum fun j =>
      hybridPacket K h Q (M+1+j.val)) <=
      (replacementConstant*(Real.log (Q : Real))^4)*
        ((500*((N : Real)+(Q : Real)^2)/(K : Real))/epsilon^2) := by
  calc
    _ <= (tailBadIndices (N:=N) K h Q M epsilon).sum
        (fun _ => replacementConstant*(Real.log (Q : Real))^4) := by
      apply Finset.sum_le_sum
      intro j _
      exact hybrid_packet_envelope K h Q _ hK hKQ
    _ = (replacementConstant*(Real.log (Q : Real))^4)*
        ((tailBadIndices (N:=N) K h Q M epsilon).card : Real) := by simp [mul_comm]
    _ <= _ := mul_le_mul_of_nonneg_left
      (tail_bad_card_bound_div K h hK hKQ hN M epsilon heps)
      (by unfold replacementConstant; positivity)

theorem logarithmic_cutoff_l1_replacement {Q N : Nat} (K : Nat) (h : Int)
    (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N) (M : Nat)
    (hcritical : (Q : Real)^2<=3*(N : Real))
    (hlogK : (Real.log (Q : Real))^10<=(K : Real)) :
    (Finset.univ.sum fun j : Fin N =>
      abs (actualPacket h Q (M+1+j.val)-hybridPacket K h Q (M+1+j.val))) <=
      45*replacementConstant*(N : Real)/Real.log (Q : Real) := by
  have hlog : 0<Real.log (Q : Real) :=
    Real.log_pos (by exact_mod_cast (show 1<Q from by omega))
  have hl0 : Not (Real.log (Q : Real)=0) := ne_of_gt hlog
  have hR : 500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real)<=
      2025*(N : Real)^2/(Real.log (Q : Real))^10 := by
    calc
      _ <= 500*(N : Real)*(4*(N : Real))/(K : Real) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith only [hcritical]) (by positivity))
          (Nat.cast_nonneg K)
      _ = 2000*(N : Real)^2/(K : Real) := by ring
      _ <= 2000*(N : Real)^2/(Real.log (Q : Real))^10 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hlog _) hlogK
      _ <= _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg (N : Real)))
        (pow_nonneg hlog.le _)
  have hid : Real.sqrt (2025*(N : Real)^2/(Real.log (Q : Real))^10)=
      45*(N : Real)/(Real.log (Q : Real))^5 := by
    have he : 2025*(N : Real)^2/(Real.log (Q : Real))^10=
        (45*(N : Real)/(Real.log (Q : Real))^5)^2 := by
      field_simp [hl0] <;> ring
    rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg (by positivity)]
  have hs := Real.sqrt_le_sqrt hR
  rw [hid] at hs
  calc
    _ <= replacementConstant*(Real.log (Q : Real))^4*
        Real.sqrt (500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real)) :=
      integer_packet_l1_replacement K h hK hKQ hN M
    _ <= replacementConstant*(Real.log (Q : Real))^4*
        (45*(N : Real)/(Real.log (Q : Real))^5) :=
      mul_le_mul_of_nonneg_left hs (by unfold replacementConstant; positivity)
    _ = _ := by field_simp [hl0] <;> ring

end PrimeFactorOscillations.FiniteFieldIntegerMass
