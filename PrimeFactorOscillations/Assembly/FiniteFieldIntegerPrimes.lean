/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerAffine
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePastWave
/-!
# Extracting actual integer prime pairs from the finite-field packet

The full local zero masks exclude every prime divisor through Q.
The existing deterministic past-prime theorem gives primality on
Q < n <= Q^2. The affine mass comparison therefore supplies a literal
lower bound on the number of sampled integer prime pairs. Its positive
mass hypothesis is retained explicitly and is not asserted here.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerPrimes
open PrimeFactorOscillations.FiniteFieldIntegerTail
open PrimeFactorOscillations.FiniteFieldIntegerMass
open PrimeFactorOscillations.FiniteFieldIntegerAffine
attribute [local instance] Classical.propDecidable

theorem actual_local_zero {Q : Nat} (h : Int) (q : BoundedModulus Q)
    (hp : Nat.Prime q.val) : actualLocal h q 0=0 := by
  letI : Fact (Nat.Prime q.val) := Fact.mk hp
  by_cases hg : 5<=q.val /\ Not ((h : ZMod q.val)=0)
  . simp [actualLocal,hp,hg,_root_.FiniteField.traceFreePairWeight_zero]
  . simp [actualLocal,hp,hg,flatFallback,integerMask]

theorem actual_local_neg_shift {Q : Nat} (h : Int) (q : BoundedModulus Q)
    (hp : Nat.Prime q.val) : actualLocal h q (-(h : ZMod q.val))=0 := by
  letI : Fact (Nat.Prime q.val) := Fact.mk hp
  by_cases hg : 5<=q.val /\ Not ((h : ZMod q.val)=0)
  . simp [actualLocal,hp,hg,_root_.FiniteField.traceFreePairWeight_neg_shift]
  . simp [actualLocal,hp,hg,flatFallback,integerMask]

theorem actual_packet_zero_of_prime_divisor (h : Int) (Q n p : Nat)
    (hp : Nat.Prime p) (hpQ : p<=Q) (hpn : Dvd.dvd p n) :
    actualPacket h Q n=0 := by
  let qp : BoundedModulus Q :=
    Subtype.mk p (Finset.mem_Icc.mpr (And.intro (by have h2:=hp.two_le; omega) hpQ))
  have hpp : (n : ZMod qp.val)=0 :=
    (CharP.cast_eq_zero_iff (ZMod qp.val) qp.val n).mpr hpn
  unfold actualPacket
  apply Finset.prod_eq_zero (Finset.mem_attach _ qp)
  rw [hpp]
  exact actual_local_zero h qp hp

theorem actual_packet_zero_of_shift_divisor (h Q n p : Nat)
    (hp : Nat.Prime p) (hpQ : p<=Q) (hpn : Dvd.dvd p (n+h)) :
    actualPacket (h : Int) Q n=0 := by
  let qp : BoundedModulus Q :=
    Subtype.mk p (Finset.mem_Icc.mpr (And.intro (by have h2:=hp.two_le; omega) hpQ))
  have hpp : ((n+h : Nat) : ZMod qp.val)=0 :=
    (CharP.cast_eq_zero_iff (ZMod qp.val) qp.val (n+h)).mpr hpn
  have hn : (n : ZMod qp.val)=-((h : Int) : ZMod qp.val) := by
    push_cast at hpp
    push_cast
    exact eq_neg_of_add_eq_zero_left hpp
  unfold actualPacket
  apply Finset.prod_eq_zero (Finset.mem_attach _ qp)
  rw [hn]
  exact actual_local_neg_shift (h : Int) qp hp

theorem actual_packet_positive_gives_prime_pair (h Q n : Nat)
    (hQ : 1<=Q) (hQn : Q<n) (hnQ : n+h<=Q*Q)
    (hpos : 0<actualPacket (h : Int) Q n) :
    Nat.Prime n /\ Nat.Prime (n+h) := by
  have hn : n<=Q*Q := by omega
  apply And.intro
  . apply (PrimeFactorOscillations.PrimeClassDeletion.prime_iff_no_past_prime_divisor
      Q n hQ hQn hn).mpr
    intro p hp hpQ hpn
    have hz := actual_packet_zero_of_prime_divisor (h : Int) Q n p hp hpQ hpn
    linarith only [hpos,hz]
  . apply (PrimeFactorOscillations.PrimeClassDeletion.prime_iff_no_past_prime_divisor
      Q (n+h) hQ (by omega) hnQ).mpr
    intro p hp hpQ hpn
    have hz := actual_packet_zero_of_shift_divisor h Q n p hp hpQ hpn
    linarith only [hpos,hz]

def primePairIndices (N h a b M : Nat) : Finset (Fin N) :=
  Finset.univ.filter (fun j =>
    Nat.Prime (a+b*(M+1+j.val)) /\ Nat.Prime (a+b*(M+1+j.val)+h))

theorem actual_mass_le_prime_pair_count {N : Nat} (h Q a b M : Nat)
    (hQ : 6<=Q)
    (hlo : forall j : Fin N, Q<a+b*(M+1+j.val))
    (hhi : forall j : Fin N, a+b*(M+1+j.val)+h<=Q*Q) :
    (Finset.univ.sum fun j : Fin N => actualPacket (h : Int) Q (a+b*(M+1+j.val))) <=
      (replacementConstant*(Real.log (Q : Real))^4)*
        ((primePairIndices N h a b M).card : Real) := by
  let B : Real := replacementConstant*(Real.log (Q : Real))^4
  have hlocal : forall j : Fin N,
      actualPacket (h : Int) Q (a+b*(M+1+j.val)) <=
        if Nat.Prime (a+b*(M+1+j.val)) /\ Nat.Prime (a+b*(M+1+j.val)+h)
          then B else 0 := by
    intro j
    by_cases hp : Nat.Prime (a+b*(M+1+j.val)) /\
      Nat.Prime (a+b*(M+1+j.val)+h)
    . rw [if_pos hp]
      exact actual_packet_envelope (h : Int) Q _ hQ
    . rw [if_neg hp]
      apply le_of_not_gt
      intro hpos
      exact hp (actual_packet_positive_gives_prime_pair h Q _
        (by omega) (hlo j) (hhi j) hpos)
  calc
    _ <= Finset.univ.sum (fun j : Fin N =>
      if Nat.Prime (a+b*(M+1+j.val)) /\ Nat.Prime (a+b*(M+1+j.val)+h)
        then B else 0) := Finset.sum_le_sum (fun j _ => hlocal j)
    _ = B*((primePairIndices N h a b M).card : Real) := by
      rw [<- Finset.sum_filter]
      simp [primePairIndices,mul_comm]
    _ = _ := rfl

theorem compensated_mass_prime_pair_lower_bound {Q N : Nat}
    (K h a b M : Nat) (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N)
    (hlo : forall j : Fin N, Q<a+b*(M+1+j.val))
    (hhi : forall j : Fin N, a+b*(M+1+j.val)+h<=Q*Q) :
    (Finset.univ.sum fun j : Fin N =>
      compensatedPacket K (h : Int) b Q (a+b*(M+1+j.val)))-
      replacementConstant*(Real.log (Q : Real))^4*
        Real.sqrt (500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real)) <=
      (replacementConstant*(Real.log (Q : Real))^4)*
        ((primePairIndices N h a b M).card : Real) := by
  have hm := affine_packet_mass_replacement K (h : Int) a b hK hKQ hN M
  have hl := (abs_le.mp hm).1
  have hu := actual_mass_le_prime_pair_count h Q a b M (by omega) hlo hhi
  linarith only [hl,hu]

theorem prime_pair_of_compensated_mass {Q N : Nat}
    (K h a b M : Nat) (hK : 6<=K) (hKQ : K<=Q) (hN : 0<N)
    (hlo : forall j : Fin N, Q<a+b*(M+1+j.val))
    (hhi : forall j : Fin N, a+b*(M+1+j.val)+h<=Q*Q)
    (hmass : replacementConstant*(Real.log (Q : Real))^4*
        Real.sqrt (500*(N : Real)*((N : Real)+(Q : Real)^2)/(K : Real)) <
      Finset.univ.sum (fun j : Fin N =>
        compensatedPacket K (h : Int) b Q (a+b*(M+1+j.val)))) :
    exists j : Fin N, Nat.Prime (a+b*(M+1+j.val)) /\
      Nat.Prime (a+b*(M+1+j.val)+h) := by
  have hc := compensated_mass_prime_pair_lower_bound
    K h a b M hK hKQ hN hlo hhi
  have hcard : 0<(primePairIndices N h a b M).card := by
    by_contra hn
    have hz : (primePairIndices N h a b M).card=0 := by omega
    rw [hz,Nat.cast_zero,mul_zero] at hc
    linarith only [hc,hmass]
  have hex := Finset.card_pos.mp hcard
  let j : Fin N := Classical.choose hex
  have hj := Classical.choose_spec hex
  exact Exists.intro j (Finset.mem_filter.mp hj).2

end PrimeFactorOscillations.FiniteFieldIntegerPrimes
