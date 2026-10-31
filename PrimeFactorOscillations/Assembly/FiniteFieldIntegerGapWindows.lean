/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerWindowTransfer
import PrimeFactorOscillations.Assembly.LeastRecurringPrimeGap

/-!
# Genuine integer recurrence frames for the coherent pair packet

The least recurring adjacent prime gap supplies unbounded full natural
windows with positive retained packet mass. The same witnesses retain
their actual consecutive prime endpoints and the polylogarithmic core
range. No twin-prime hypothesis or improvement of the bounded-gap
input is introduced.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerGapWindows
attribute [local instance] Classical.propDecidable

open FiniteFieldIntegerTail
open FiniteFieldIntegerMass
open FiniteFieldIntegerExtrema
open FiniteFieldIntegerWindowTransfer
open PrimeProfileRigidity

theorem least_gap_even : Dvd.dvd 2 leastRecurringPrimeGap := by
  let i : Nat := Classical.choose (leastRecurringPrimeGap_exact_above 3)
  have hi : 3 <= i /\ PrimeFactorUnimodality.primeAt (i + 1) =
      PrimeFactorUnimodality.primeAt i + leastRecurringPrimeGap :=
    Classical.choose_spec (leastRecurringPrimeGap_exact_above 3)
  have hpi : 3 <= PrimeFactorUnimodality.primeAt i :=
    le_trans hi.1 (PrimeFactorUnimodality.primeAt_strictMono.id_le i)
  have hp := (PrimeFactorUnimodality.prime_primeAt i).eq_two_or_odd
  have hq := (PrimeFactorUnimodality.prime_primeAt (i + 1)).eq_two_or_odd
  have hlt := PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self i)
  apply Nat.dvd_of_mod_eq_zero
  omega

theorem actual_packet_positive_of_prime_pair (h Q n : Nat) (heven : Dvd.dvd 2 h)
    (hQn : Q < n) (hn : Nat.Prime n) (hnh : Nat.Prime (n + h)) :
    0 < actualPacket (h : Int) Q n := by
  unfold actualPacket
  apply Finset.prod_pos
  intro q _
  by_cases hp : Nat.Prime q.val
  . have hsmall : q.val = 2 -> ((h : Int) : ZMod q.val) = 0 := by
      intro he
      have hd : Dvd.dvd q.val h := by rwa [he]
      simpa only [Int.cast_natCast] using
        (CharP.cast_eq_zero_iff (ZMod q.val) q.val h).mpr hd
    have hcast (P : Nat) (hP : Nat.Prime P) (hQP : Q < P) :
        Not ((P : ZMod q.val) = 0) := by
      intro hz
      have hd := (CharP.cast_eq_zero_iff (ZMod q.val) q.val P).mp hz
      have hqQ := (Finset.mem_Icc.mp q.property).2
      cases (Nat.dvd_prime hP).mp hd with
      | inl he => exact hp.ne_one he
      | inr he => omega
    have hc := hcast n hn hQn
    have hch : Not ((n : ZMod q.val) + ((h : Int) : ZMod q.val) = 0) := by
      intro hz
      apply hcast (n + h) hnh (by omega)
      simpa only [Int.cast_natCast, Nat.cast_add] using hz
    have hlocal := actual_local_ge_one h q hp hsmall (n : ZMod q.val) hc hch
    linarith only [hlocal]
  . simp only [actualLocal, dite_eq_right hp]
    norm_num

theorem core_packet_positive_of_prime_pair (h Q n : Nat) (heven : Dvd.dvd 2 h)
    (hlog : 1 <= Real.log (Q : Real)) (hQn : Q < n)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h)) :
    0 < hybridPacket (preciseCore Q) (h : Int) Q n := by
  have hU := actual_packet_positive_of_prime_pair h Q n heven hQn hn hnh
  have hK := precise_core_ge_six Q hlog
  have hf := full_packet_factorization (preciseCore Q) (h : Int) hK Q n
  by_contra hnot
  have ht := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot)
    (Real.exp_pos (tailLogSum (preciseCore Q) (h : Int) Q n)).le
  rw [<- hf] at ht
  linarith only [hU, ht]

def naturalWindowSize (h Q : Nat) : Nat := Q * Q - h - Q

def naturalWindowPoint (h Q : Nat) (j : Fin (naturalWindowSize h Q)) : Nat :=
  Q + 1 + j.val

def naturalWindowMass (h Q : Nat) : Real :=
  coreWindowMass h Q (naturalWindowPoint h Q) (fun _ => 1)

theorem natural_window_point_range (h Q : Nat) (j : Fin (naturalWindowSize h Q)) :
    Q < naturalWindowPoint h Q j /\ naturalWindowPoint h Q j + h <= Q * Q := by
  have hj := j.isLt
  dsimp [naturalWindowPoint, naturalWindowSize] at *
  omega

theorem natural_window_point_injective (h Q : Nat) :
    Function.Injective (naturalWindowPoint h Q) := by
  intro a b hab
  apply Fin.ext
  dsimp [naturalWindowPoint] at hab
  omega

theorem natural_window_point_iff (h Q n : Nat) :
    (Q < n /\ n + h <= Q * Q) <->
      exists j : Fin (naturalWindowSize h Q), naturalWindowPoint h Q j = n := by
  constructor
  . intro hn
    have hj : n - Q - 1 < naturalWindowSize h Q := by
      dsimp [naturalWindowSize]
      omega
    refine Exists.intro (Fin.mk (n - Q - 1) hj) ?_
    dsimp [naturalWindowPoint]
    omega
  . intro hn
    let j := Classical.choose hn
    have hj := Classical.choose_spec hn
    rw [<- hj]
    exact natural_window_point_range h Q j

theorem natural_window_mass_positive (h Q : Nat) (heven : Dvd.dvd 2 h)
    (hlog : 1 <= Real.log (Q : Real))
    (hp : Nat.Prime (Q + 1)) (hq : Nat.Prime (Q + 1 + h))
    (hhi : Q + 1 + h <= Q * Q) : 0 < naturalWindowMass h Q := by
  have hsize : 0 < naturalWindowSize h Q := by dsimp [naturalWindowSize]; omega
  let j0 : Fin (naturalWindowSize h Q) := Fin.mk 0 hsize
  have hj0 : naturalWindowPoint h Q j0 = Q + 1 := rfl
  have hpos := core_packet_positive_of_prime_pair h Q (Q + 1) heven hlog (by omega) hp hq
  have hsum : hybridPacket (preciseCore Q) (h : Int) Q (Q + 1) <=
      Finset.univ.sum (fun j : Fin (naturalWindowSize h Q) =>
        hybridPacket (preciseCore Q) (h : Int) Q (naturalWindowPoint h Q j)) := by
    rw [<- hj0]
    exact Finset.single_le_sum
      (fun j _ => hybrid_packet_nonneg (preciseCore Q) (h : Int) Q _)
      (Finset.mem_univ j0)
  have ht := hpos.trans_le hsum
  simpa only [naturalWindowMass, coreWindowMass, one_mul] using ht

def leastGapFrame (Q i : Nat) : Prop :=
  And (6 <= Q) (And (1 <= Real.log (Q : Real))
    (And (1 <= Real.log (Real.log (Q : Real)))
      (And (preciseCore Q <= Q) (And (leastRecurringPrimeGap < Q)
        (And (PrimeFactorUnimodality.primeAt i = Q + 1)
          (And (PrimeFactorUnimodality.primeAt (i + 1) = Q + 1 + leastRecurringPrimeGap)
            (0 < naturalWindowMass leastRecurringPrimeGap Q)))))))

theorem unbounded_least_gap_positive_windows (R : Nat) :
    exists Q i : Nat, And (R <= Q) (leastGapFrame Q i) := by
  let Qfit : Nat := Classical.choose eventually_precise_core_fits
  have hfit := Classical.choose_spec eventually_precise_core_fits
  let N : Nat := max (R + 1) (max (Qfit + 1) (leastRecurringPrimeGap + 3))
  let i : Nat := Classical.choose (leastRecurringPrimeGap_exact_above N)
  have hi : N <= i /\ PrimeFactorUnimodality.primeAt (i + 1) =
      PrimeFactorUnimodality.primeAt i + leastRecurringPrimeGap :=
    Classical.choose_spec (leastRecurringPrimeGap_exact_above N)
  let p : Nat := PrimeFactorUnimodality.primeAt i
  let Q : Nat := p - 1
  have hNp : N <= p := le_trans hi.1 (PrimeFactorUnimodality.primeAt_strictMono.id_le i)
  have hR : R + 1 <= p := le_trans (le_max_left _ _) hNp
  have hF : Qfit + 1 <= p := le_trans
    (le_trans (le_max_left _ _) (le_max_right _ _)) hNp
  have hH : leastRecurringPrimeGap + 3 <= p := le_trans
    (le_trans (le_max_right _ _) (le_max_right _ _)) hNp
  have hpQ : p = Q + 1 := by dsimp [Q]; omega
  have hRQ : R <= Q := by omega
  have hFQ : Qfit <= Q := by omega
  have hHQ : leastRecurringPrimeGap < Q := by omega
  have hcore := hfit Q hFQ
  have hip : PrimeFactorUnimodality.primeAt i = Q + 1 := hpQ
  have hiq : PrimeFactorUnimodality.primeAt (i + 1) = Q + 1 + leastRecurringPrimeGap := by
    rw [hi.2, hip]
  have hp : Nat.Prime (Q + 1) := by rw [<- hip]; exact PrimeFactorUnimodality.prime_primeAt i
  have hq : Nat.Prime (Q + 1 + leastRecurringPrimeGap) := by
    rw [<- hiq]
    exact PrimeFactorUnimodality.prime_primeAt (i + 1)
  have hhi : Q + 1 + leastRecurringPrimeGap <= Q * Q := by
    have hh : leastRecurringPrimeGap + 1 <= Q := by omega
    have hQ2 : 2 <= Q := by have ht := hcore.1; omega
    nlinarith only [hh, hQ2]
  have hmass := natural_window_mass_positive leastRecurringPrimeGap Q least_gap_even
    hcore.2.1 hp hq hhi
  exact Exists.intro Q (Exists.intro i (And.intro hRQ (And.intro hcore.1
    (And.intro hcore.2.1 (And.intro hcore.2.2.1 (And.intro hcore.2.2.2
      (And.intro hHQ (And.intro hip (And.intro hiq hmass)))))))))

end PrimeFactorOscillations.FiniteFieldIntegerGapWindows
