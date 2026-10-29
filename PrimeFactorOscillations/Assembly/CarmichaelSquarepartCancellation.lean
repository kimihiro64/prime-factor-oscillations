/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Assembly.CarmichaelNativeLowSector

/-!
# Squarefree companion cancellation on physical windows

The finite square-divisor Mobius expansion preserves the character phases.
Complete-period cancellation gives shortened squarefree progression bounds,
uniformly over every finite prime amplifier. The coupled coprime estimate
keeps its supported Mobius rows and has a harmonic range cost. Its native
cubic square-part character has no remaining nonprincipality assumption.
Squared physical Schwartz windows have a fixed variation budget at every
row rescaling. The remaining native small-square core and full Abel
consumer are still open; these results alone assert no zero-free gain.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelSquarepartCancellation

/-- A square divisor is entirely absorbed by the square part of a squarefree decomposition. -/
theorem square_dvd_square_mul_squarefree_iff (a b d : Nat)
    (ha : Not (a = 0)) (hb : Not (b = 0)) (hsf : Squarefree b) :
    Dvd.dvd (d ^ 2) (a ^ 2 * b) <-> Dvd.dvd d a := by
  constructor
  . intro h
    have hd : Not (d = 0) := by
      intro hz
      have hn : Not (a ^ 2 * b = 0) := mul_ne_zero (pow_ne_zero 2 ha) hb
      apply hn
      simpa only [hz, zero_pow (by decide : Not (2 = 0)), zero_dvd_iff] using h
    apply (Nat.factorization_le_iff_dvd hd ha).mp
    have hf := (Nat.factorization_le_iff_dvd
      (pow_ne_zero 2 hd) (mul_ne_zero (pow_ne_zero 2 ha) hb)).mpr h
    rw [Nat.factorization_mul (pow_ne_zero 2 ha) hb,
      Nat.factorization_pow, Nat.factorization_pow] at hf
    intro p
    have hfp := hf p
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hfp
    have hbp := (Nat.squarefree_iff_factorization_le_one hb).mp hsf p
    omega
  . intro h
    choose k hk using h
    exact Exists.intro (k ^ 2 * b) (by rw [hk]; ring)

private theorem moebius_divisor_sum (a : Nat) (ha : 0 < a) :
    a.divisors.sum (fun d => ArithmeticFunction.moebius d) =
      if a = 1 then 1 else 0 := by
  have hsum :
      a.divisors.sum (fun d => ArithmeticFunction.moebius d) =
        (ArithmeticFunction.moebius *
          (ArithmeticFunction.zeta : ArithmeticFunction Int)) a := by
    rw [ArithmeticFunction.mul_apply]
    rw [Nat.sum_divisorsAntidiagonal (n := a)
      (fun x y : Nat => ArithmeticFunction.moebius x *
        (ArithmeticFunction.zeta : ArithmeticFunction Int) y)]
    apply Finset.sum_congr rfl
    intro d hd
    have hdiv := (Nat.mem_divisors.mp hd).1
    have hd0 : Not (d = 0) := by
      intro hz
      have hz0 : a = 0 := by simpa only [hz, zero_dvd_iff] using hdiv
      omega
    have hdpos : 0 < d := by omega
    have hquot : Not (a / d = 0) :=
      Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd ha hdiv) hdpos)
    have hz : ((ArithmeticFunction.zeta (a / d) : Nat) : Int) = 1 := by
      change ((if a / d = 0 then 0 else 1 : Nat) : Int) = 1
      rw [ite_eq_right hquot, Nat.cast_one]
    change ArithmeticFunction.moebius d =
      ArithmeticFunction.moebius d * ((ArithmeticFunction.zeta (a / d) : Nat) : Int)
    rw [hz, mul_one]
  rw [hsum, ArithmeticFunction.moebius_mul_coe_zeta]
  rfl

private theorem moebius_square_finite_expansion (n N : Nat)
    (hn : 0 < n) (hN : n <= N) :
    (Finset.Icc 1 (Nat.sqrt N)).sum
        (fun d => if Dvd.dvd (d ^ 2) n
          then ArithmeticFunction.moebius d else 0) =
      ArithmeticFunction.moebius n ^ 2 := by
  classical
  choose r hr using Nat.sq_mul_squarefree_of_pos hn
  choose a ha using hr
  have hrpos : 0 < r := ha.1
  have hapos : 0 < a := ha.2.1
  have hprod : a ^ 2 * r = n := ha.2.2.1
  have hsf : Squarefree r := ha.2.2.2
  have ha0 : Not (a = 0) := Nat.ne_of_gt hapos
  have hr0 : Not (r = 0) := Nat.ne_of_gt hrpos
  have hdvd (d : Nat) : Dvd.dvd (d ^ 2) n <-> Dvd.dvd d a := by
    rw [<- hprod]
    exact square_dvd_square_mul_squarefree_iff a r d ha0 hr0 hsf
  have harange : a <= Nat.sqrt N := by
    apply Nat.le_sqrt.mpr
    have hh : a ^ 2 <= a ^ 2 * r := by nlinarith
    nlinarith
  have hsets :
      (Finset.Icc 1 (Nat.sqrt N)).filter (fun d => Dvd.dvd (d ^ 2) n) =
        a.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    . intro hd
      exact And.intro ((hdvd d).mp hd.2) ha0
    . intro hd
      have hd0 : Not (d = 0) := by
        intro hz
        have hz0 : a = 0 := by simpa only [hz, zero_dvd_iff] using hd.1
        exact ha0 hz0
      have hda : d <= a := Nat.le_of_dvd hapos hd.1
      exact And.intro (And.intro (by omega) (hda.trans harange)) ((hdvd d).mpr hd.1)
  have hsfiff : Squarefree n <-> a = 1 := by
    constructor
    . intro hnsf
      by_contra hne
      choose p hp using Nat.exists_prime_and_dvd hne
      choose k hk using hp.2
      have hpdvd : Dvd.dvd (p * p) n := by
        apply Exists.intro (k ^ 2 * r)
        rw [<- hprod, hk]
        ring
      exact (Nat.squarefree_iff_prime_squarefree.mp hnsf) p hp.1 hpdvd
    . intro hone
      rw [<- hprod, hone, one_pow, one_mul]
      exact hsf
  rw [<- Finset.sum_filter, hsets, moebius_divisor_sum a hapos,
    ArithmeticFunction.moebius_sq]
  simp only [hsfiff]


open PrimeFactorOscillations.CarmichaelCompanionCancellation
open PrimeFactorOscillations.CarmichaelCompanionMasks

/-- The squarefree projector at the positive integer stored at index i. -/
def squarefreeWindow (w : Nat -> Complex) (i : Nat) : Complex :=
  (ArithmeticFunction.moebius (i + 1) : Complex) ^ 2 * w i

private theorem moebius_square_complex_expansion (n N : Nat)
    (hn : 0 < n) (hN : n <= N) :
    (Finset.Icc 1 (Nat.sqrt N)).sum
        (fun d => if Dvd.dvd (d ^ 2) n
          then (ArithmeticFunction.moebius d : Complex) else 0) =
      (ArithmeticFunction.moebius n : Complex) ^ 2 := by
  classical
  have hc := congrArg (Int.castRingHom Complex)
    (moebius_square_finite_expansion n N hn hN)
  rw [map_sum, map_pow] at hc
  calc
    _ = (Finset.Icc 1 (Nat.sqrt N)).sum (fun d =>
        (Int.castRingHom Complex)
          (if Dvd.dvd (d ^ 2) n then ArithmeticFunction.moebius d else 0)) := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : Dvd.dvd (d ^ 2) n
      . rw [ite_eq_left hd, ite_eq_left hd]
        rfl
      . rw [ite_eq_right hd, ite_eq_right hd, map_zero]
    _ = _ := hc

/-- Retain the square-divisor Mobius phases in every progression. -/
theorem squarefree_progression_expansion {q : Nat}
    (psi : DirichletCharacter Complex q) (H k N : Nat) (w : Nat -> Complex) :
    weightedMaskedProgression psi H k N (squarefreeWindow w) =
      (Finset.Icc 1 (Nat.sqrt N)).sum (fun d =>
        (ArithmeticFunction.moebius d : Complex) *
          weightedMaskedProgression psi H (Nat.lcm k (d ^ 2)) N w) := by
  classical
  calc
    _ = (Finset.Icc 1 N).sum (fun n =>
        (Finset.Icc 1 (Nat.sqrt N)).sum (fun d =>
          (ArithmeticFunction.moebius d : Complex) *
            (if Dvd.dvd k n then
              divisorWindow (d ^ 2) w (n - 1) * maskedCharacter psi H n else 0))) := by
      unfold weightedMaskedProgression squarefreeWindow
      apply Finset.sum_congr rfl
      intro n hn
      have hidx : n - 1 + 1 = n :=
        Nat.sub_add_cancel (Finset.mem_Icc.mp hn).1
      by_cases hk : Dvd.dvd k n
      . simp only [hidx, ite_eq_left hk, divisorWindow]
        have hm := moebius_square_complex_expansion n N
          (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
        rw [<- hm, Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : Dvd.dvd (d ^ 2) n
        . simp only [ite_eq_left hd]
          ring
        . simp only [ite_eq_right hd, zero_mul, mul_zero]
      . simp only [ite_eq_right hk, mul_zero, Finset.sum_const_zero]
    _ = (Finset.Icc 1 (Nat.sqrt N)).sum (fun d =>
        (ArithmeticFunction.moebius d : Complex) *
          weightedMaskedProgression psi H k N (divisorWindow (d ^ 2) w)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      unfold weightedMaskedProgression
      rw [Finset.mul_sum]
    _ = _ := by simp_rw [progression_divisor_window]

/-- Squarefree character cancellation is uniform in all finite prime amplifiers. -/
theorem squarefree_amplified_progression_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (H k N : Nat) (hH : 0 < H) (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (a : Nat) (ha : 0 < a) (w : Nat -> Complex) :
    norm (weightedMaskedProgression psi H k N
      (squarefreeWindow (amplifiedWindow G a w))) <=
      (Nat.sqrt N : Real) * companionCap q H a N w := by
  rw [squarefree_progression_expansion]
  calc
    _ <= (Finset.Icc 1 (Nat.sqrt N)).sum (fun d =>
        norm ((ArithmeticFunction.moebius d : Complex) *
          weightedMaskedProgression psi H (Nat.lcm k (d ^ 2)) N
            (amplifiedWindow G a w))) := norm_sum_le _ _
    _ <= (Finset.Icc 1 (Nat.sqrt N)).sum (fun _ =>
        companionCap q H a N w) := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul]
      have hm : norm (ArithmeticFunction.moebius d : Complex) <= 1 := by
        calc
          _ = ((abs (ArithmeticFunction.moebius d) : Int) : Real) := by simp
          _ <= 1 := by
            exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      have hb : norm (weightedMaskedProgression psi H (Nat.lcm k (d ^ 2)) N
          (amplifiedWindow G a w)) <= companionCap q H a N w :=
        amplified_progression_bound psi hpsi H (Nat.lcm k (d ^ 2)) N hH G hG a ha w
      calc
        _ <= 1 * companionCap q H a N w :=
          mul_le_mul hm hb (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
    _ = _ := by simp


/-- The original window on the positive multiples of k, still stored from index zero. -/
def dilatedWindow (k : Nat) (w : Nat -> Complex) (i : Nat) : Complex :=
  w (k * (i + 1) - 1)

private theorem sum_multiples (k N : Nat) (hk : 0 < k) (F : Nat -> Complex) :
    (Finset.Icc 1 N).sum (fun n => if Dvd.dvd k n then F n else 0) =
      (Finset.Icc 1 (N / k)).sum (fun t => F (k * t)) := by
  classical
  rw [<- Finset.sum_filter]
  refine Finset.sum_bij (fun n _ => n / k) ?_ ?_ ?_ ?_
  . intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hnmem := Finset.mem_Icc.mp hmem.1
    exact Finset.mem_Icc.mpr (And.intro
      (Nat.div_pos (Nat.le_of_dvd hnmem.1 hmem.2) hk)
      (Nat.div_le_div_right hnmem.2))
  . intro n hn m hm he
    have hnd := (Finset.mem_filter.mp hn).2
    have hmd := (Finset.mem_filter.mp hm).2
    calc
      n = n / k * k := (Nat.div_mul_cancel hnd).symm
      _ = m / k * k := congrArg (fun t : Nat => t * k) he
      _ = m := Nat.div_mul_cancel hmd
  . intro t ht
    have htm := Finset.mem_Icc.mp ht
    have htn : Membership.mem (Finset.Icc 1 N) (t * k) :=
      Finset.mem_Icc.mpr (And.intro (Nat.mul_pos htm.1 hk)
        ((Nat.le_div_iff_mul_le hk).mp htm.2))
    have hdk : Dvd.dvd k (t * k) := Exists.intro t (Nat.mul_comm t k)
    exact Exists.intro (t * k)
      (Exists.intro (Finset.mem_filter.mpr (And.intro htn hdk))
        (Nat.mul_div_cancel t hk))
  . intro n hn
    have hd := (Finset.mem_filter.mp hn).2
    have he : k * (n / k) = n := by
      rw [Nat.mul_comm, Nat.div_mul_cancel hd]
    rw [he]

private theorem squarefreeWindow_apply (w : Nat -> Complex) (i : Nat) :
    squarefreeWindow w i = if Squarefree (i + 1) then w i else 0 := by
  have hm : (ArithmeticFunction.moebius (i + 1) : Complex) ^ 2 =
      if Squarefree (i + 1) then 1 else 0 := by
    by_cases hs : Squarefree (i + 1)
    . rw [ite_eq_left hs]
      have hi : ArithmeticFunction.moebius (i + 1) ^ 2 = 1 := by
        rw [ArithmeticFunction.moebius_sq, ite_eq_left hs]
      exact_mod_cast hi
    . rw [ite_eq_right hs]
      have hi : ArithmeticFunction.moebius (i + 1) ^ 2 = 0 := by
        rw [ArithmeticFunction.moebius_sq, ite_eq_right hs]
      exact_mod_cast hi
  unfold squarefreeWindow
  rw [hm]
  by_cases hs : Squarefree (i + 1)
  . rw [ite_eq_left hs, one_mul, ite_eq_left hs]
  . rw [ite_eq_right hs, zero_mul, ite_eq_right hs]

private theorem squarefree_masked_dilation {q : Nat}
    (psi : DirichletCharacter Complex q) (H k a t : Nat)
    (hk : 0 < k) (ht : 0 < t) (hksf : Squarefree k) (hkH : Nat.Coprime k H)
    (G : Finset Nat) (w : Nat -> Complex) :
    squarefreeWindow (amplifiedWindow G a w) (k * t - 1) *
        maskedCharacter psi H (k * t) =
      psi (k : ZMod q) *
        (squarefreeWindow (amplifiedWindow G (a * k) (dilatedWindow k w)) (t - 1) *
          maskedCharacter psi (H * k) t) := by
  classical
  have hidx : k * t - 1 + 1 = k * t := Nat.sub_add_cancel (Nat.mul_pos hk ht)
  have hit : t - 1 + 1 = t := Nat.sub_add_cancel ht
  rw [squarefreeWindow_apply, squarefreeWindow_apply, hidx, hit]
  by_cases hs : Squarefree t
  . rw [ite_eq_left hs]
    by_cases hc : Nat.Coprime k t
    . have hktsf : Squarefree (k * t) :=
        Nat.squarefree_mul_iff.mpr (And.intro hc (And.intro hksf hs))
      rw [ite_eq_left hktsf]
      by_cases hth : Nat.Coprime t H
      . have hleft : Nat.Coprime (k * t) H :=
          Nat.coprime_mul_iff_left.mpr (And.intro hkH hth)
        have hright : Nat.Coprime t (H * k) :=
          Nat.coprime_mul_iff_right.mpr (And.intro hth hc.symm)
        unfold maskedCharacter
        rw [ite_eq_left hleft, ite_eq_left hright]
        unfold amplifiedWindow dilatedWindow
        simp only [hidx, hit, Nat.mul_assoc, Nat.cast_mul, map_mul]
        ring
      . have hleft : Not (Nat.Coprime (k * t) H) :=
          fun h => hth (Nat.coprime_mul_iff_left.mp h).2
        have hright : Not (Nat.Coprime t (H * k)) :=
          fun h => hth (Nat.coprime_mul_iff_right.mp h).1
        unfold maskedCharacter
        simp only [ite_eq_right hleft, ite_eq_right hright, mul_zero]
    . have hktsf : Not (Squarefree (k * t)) :=
        fun h => hc (Nat.squarefree_mul_iff.mp h).1
      have hright : Not (Nat.Coprime t (H * k)) :=
        fun h => hc (Nat.coprime_mul_iff_right.mp h).2.symm
      rw [ite_eq_right hktsf, zero_mul]
      unfold maskedCharacter
      simp only [ite_eq_right hright, mul_zero]
  . have hktsf : Not (Squarefree (k * t)) :=
      fun h => hs (Nat.squarefree_mul_iff.mp h).2.2
    simp only [ite_eq_right hktsf, ite_eq_right hs, zero_mul, mul_zero]

/-- Rescale the squarefree progression with its exact extra coprimality mask. -/
theorem squarefree_progression_rescale {q : Nat}
    (psi : DirichletCharacter Complex q) (H k N a : Nat) (hk : 0 < k)
    (G : Finset Nat) (w : Nat -> Complex) :
    weightedMaskedProgression psi H k N (squarefreeWindow (amplifiedWindow G a w)) =
      if Squarefree k /\ Nat.Coprime k H then
        psi (k : ZMod q) * weightedMaskedProgression psi (H * k) 1 (N / k)
          (squarefreeWindow (amplifiedWindow G (a * k) (dilatedWindow k w)))
      else 0 := by
  classical
  unfold weightedMaskedProgression
  rw [sum_multiples k N hk]
  by_cases hg : Squarefree k /\ Nat.Coprime k H
  . rw [ite_eq_left hg, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [one_dvd, ite_true]
    exact squarefree_masked_dilation psi H k a t hk
      (Finset.mem_Icc.mp ht).1 hg.1 hg.2 G w
  . rw [ite_eq_right hg]
    apply Finset.sum_eq_zero
    intro t ht
    have htpos : 0 < t := (Finset.mem_Icc.mp ht).1
    have hidx : k * t - 1 + 1 = k * t :=
      Nat.sub_add_cancel (Nat.mul_pos hk htpos)
    by_cases hksf : Squarefree k
    . have hkH : Not (Nat.Coprime k H) := fun h => hg (And.intro hksf h)
      have hktH : Not (Nat.Coprime (k * t) H) :=
        fun h => hkH ((Nat.coprime_mul_iff_left.mp h).1)
      unfold maskedCharacter
      rw [ite_eq_right hktH, mul_zero]
    . have hktsf : Not (Squarefree (k * t)) :=
        fun h => hksf (Nat.squarefree_mul_iff.mp h).2.1
      rw [squarefreeWindow_apply, hidx, ite_eq_right hktsf, zero_mul]

/-- The squarefree estimate uses the shortened length N/k rather than N. -/
theorem squarefree_amplified_rescaled_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (H k N : Nat) (hH : 0 < H) (hk : 0 < k) (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (a : Nat) (ha : 0 < a) (w : Nat -> Complex) :
    norm (weightedMaskedProgression psi H k N
      (squarefreeWindow (amplifiedWindow G a w))) <=
      (Nat.sqrt (N / k) : Real) *
        companionCap q (H * k) (a * k) (N / k) (dilatedWindow k w) := by
  have hb := squarefree_amplified_progression_bound psi hpsi (H * k) 1 (N / k)
    (Nat.mul_pos hH hk) G hG (a * k) (Nat.mul_pos ha hk) (dilatedWindow k w)
  rw [squarefree_progression_rescale psi H k N a hk G w]
  by_cases hg : Squarefree k /\ Nat.Coprime k H
  . rw [ite_eq_left hg, norm_mul]
    calc
      _ <= 1 * ((Nat.sqrt (N / k) : Real) *
          companionCap q (H * k) (a * k) (N / k) (dilatedWindow k w)) :=
        mul_le_mul (psi.norm_le_one _) hb (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  . rw [ite_eq_right hg, norm_zero]
    exact (norm_nonneg _).trans hb


/-- The original squarefree coprime character packet, with both amplifier bases. -/
def squarefreeCompanionPacket {q : Nat} (psi : DirichletCharacter Complex q)
    (G : Finset Nat) (H K a c B C : Nat) (w v : Nat -> Complex) : Complex :=
  weightedCompanionPacket psi H K B C
    (squarefreeWindow (amplifiedWindow G a w))
    (squarefreeWindow (amplifiedWindow G c v))

/-- The shortened row costs after complete-period cancellation in both columns. -/
def squarefreeRowCost (q H K a c B C k : Nat) (w v : Nat -> Complex) : Real :=
  ((Nat.sqrt (B / k) : Real) *
    companionCap q (H * k) (a * k) (B / k) (dilatedWindow k w)) *
  ((Nat.sqrt (C / k) : Real) *
    companionCap q (K * k) (c * k) (C / k) (dilatedWindow k v))

/-- Keep every supported Mobius row; the omitted zero row has coefficient zero. -/
theorem squarefree_coprime_identity {q : Nat}
    (psi : DirichletCharacter Complex q) (G : Finset Nat)
    (H K a c B C : Nat) (w v : Nat -> Complex) :
    squarefreeCompanionPacket psi G H K a c B C w v =
      (Finset.Ioc 0 B).sum (fun k =>
        (ArithmeticFunction.moebius k : Complex) *
          weightedMaskedProgression psi H k B
            (squarefreeWindow (amplifiedWindow G a w)) *
          star (weightedMaskedProgression psi K k C
            (squarefreeWindow (amplifiedWindow G c v)))) := by
  classical
  unfold squarefreeCompanionPacket
  rw [weighted_coprime_companion_identity]
  have hsets : Finset.range (B + 1) = insert 0 (Finset.Ioc 0 B) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hsets, Finset.sum_insert (by simp)]
  have hz : (ArithmeticFunction.moebius 0 : Complex) = 0 := by simp
  rw [hz, zero_mul, zero_mul, zero_add]

/-- Both squarefree columns cancel before the supported row costs are summed. -/
theorem squarefree_coprime_row_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (G : Finset Nat) (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (H K a c B C : Nat) (hH : 0 < H) (hK : 0 < K)
    (ha : 0 < a) (hc : 0 < c) (w v : Nat -> Complex) :
    norm (squarefreeCompanionPacket psi G H K a c B C w v) <=
      (Finset.Ioc 0 B).sum (fun k => squarefreeRowCost q H K a c B C k w v) := by
  rw [squarefree_coprime_identity]
  calc
    _ <= (Finset.Ioc 0 B).sum (fun k =>
        norm ((ArithmeticFunction.moebius k : Complex) *
          weightedMaskedProgression psi H k B
            (squarefreeWindow (amplifiedWindow G a w)) *
          star (weightedMaskedProgression psi K k C
            (squarefreeWindow (amplifiedWindow G c v))))) := norm_sum_le _ _
    _ <= _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : 0 < k := (Finset.mem_Ioc.mp hk).1
      have hl := squarefree_amplified_rescaled_bound psi hpsi H k B hH hkpos G hG a ha w
      have hr := squarefree_amplified_rescaled_bound psi hpsi K k C hK hkpos G hG c hc v
      have hm : norm (ArithmeticFunction.moebius k : Complex) <= 1 := by
        calc
          _ = ((abs (ArithmeticFunction.moebius k) : Int) : Real) := by simp
          _ <= 1 := by
            exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
      rw [norm_mul, norm_mul, norm_star]
      unfold squarefreeRowCost
      have hml : norm (ArithmeticFunction.moebius k : Complex) *
          norm (weightedMaskedProgression psi H k B
            (squarefreeWindow (amplifiedWindow G a w))) <=
          (Nat.sqrt (B / k) : Real) *
            companionCap q (H * k) (a * k) (B / k) (dilatedWindow k w) := by
        calc
          _ <= 1 * ((Nat.sqrt (B / k) : Real) *
              companionCap q (H * k) (a * k) (B / k) (dilatedWindow k w)) :=
            mul_le_mul hm hl (norm_nonneg _) (by norm_num)
          _ = _ := one_mul _
      exact mul_le_mul hml hr (norm_nonneg _) ((norm_nonneg _).trans hl)

/-- Apply the coupled estimate to the actual native square-part character. -/
theorem cubic_squarepart_row_bound {q : Nat}
    (hq : 0 < q) (chi : DirichletCharacter Complex q) (hchi : chi ^ 3 = 1)
    (G : Finset Nat) (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (H K a c B C : Nat) (hH : 0 < H) (hK : 0 < K)
    (ha : 0 < a) (hc : 0 < c) (w v : Nat -> Complex) :
    norm (squarefreeCompanionPacket (OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2))
      G H K a c B C w v) <=
      (Finset.Ioc 0 B).sum (fun k =>
        squarefreeRowCost (q * 3) H K a c B C k w v) := by
  let : NeZero (q * 3) := NeZero.mk (by omega)
  have hpow : (chi ^ 2) ^ 3 = 1 := by
    calc
      _ = (chi ^ 3) ^ 2 := by simp only [<- pow_mul]
      _ = 1 := by rw [hchi, one_pow]
  exact squarefree_coprime_row_bound
    (OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2))
    (cubic_companion_ne_one (chi ^ 2) hpow) G hG H K a c B C hH hK ha hc w v


private theorem sqrt_divisor_pair_bound (B C k : Nat) (hk : 0 < k) :
    (Nat.sqrt (B / k) : Real) * (Nat.sqrt (C / k) : Real) <=
      Real.sqrt ((B : Real) * (C : Real)) * (1 / (k : Real)) := by
  let s := Nat.sqrt (B / k)
  let t := Nat.sqrt (C / k)
  have hs : s * s * k <= B :=
    (Nat.mul_le_mul_right k (Nat.sqrt_le (B / k))).trans (Nat.div_mul_le_self B k)
  have ht : t * t * k <= C :=
    (Nat.mul_le_mul_right k (Nat.sqrt_le (C / k))).trans (Nat.div_mul_le_self C k)
  have hp : (s * t * k) ^ 2 <= B * C := by
    calc
      _ = (s * s * k) * (t * t * k) := by ring
      _ <= _ := Nat.mul_le_mul hs ht
  have hpR : ((s : Real) * (t : Real) * (k : Real)) ^ 2 <=
      (B : Real) * (C : Real) := by exact_mod_cast hp
  have hrad : 0 <= (B : Real) * (C : Real) := by positivity
  have hsqrt := Real.sq_sqrt hrad
  have hsqrt0 := Real.sqrt_nonneg ((B : Real) * (C : Real))
  have hmul : (s : Real) * (t : Real) * (k : Real) <=
      Real.sqrt ((B : Real) * (C : Real)) := by
    have hh : 0 <= (s : Real) * (t : Real) * (k : Real) := by positivity
    nlinarith
  have hkR : 0 < (k : Real) := Nat.cast_pos.mpr hk
  have he :
      (Real.sqrt ((B : Real) * (C : Real)) * (1 / (k : Real))) * (k : Real) =
        Real.sqrt ((B : Real) * (C : Real)) := by
    field_simp
  change (s : Real) * (t : Real) <= _
  by_contra h
  have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge h) hkR
  rw [he] at hlt
  exact not_lt_of_ge hmul hlt

/-- The complete supported shortened-length cost is only a harmonic factor. -/
theorem squarefree_divisor_cost_bound (B C : Nat) :
    (Finset.Ioc 0 B).sum (fun k =>
      (Nat.sqrt (B / k) : Real) * (Nat.sqrt (C / k) : Real)) <=
        Real.sqrt ((B : Real) * (C : Real)) * harmonicPrefix B := by
  unfold harmonicPrefix
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact sqrt_divisor_pair_bound B C k (Finset.mem_Ioc.mp hk).1

/-- The coupled squarefree packet is bounded by sqrt(B*C), one harmonic factor and explicit caps. -/
theorem squarefree_coprime_harmonic_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (G : Finset Nat) (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (H K a c B C : Nat) (hH : 0 < H) (hK : 0 < K)
    (ha : 0 < a) (hc : 0 < c) (w v : Nat -> Complex)
    (L R : Real) (hL : 0 <= L) (hR : 0 <= R)
    (hleft : forall k, Membership.mem (Finset.Ioc 0 B) k ->
      companionCap q (H * k) (a * k) (B / k) (dilatedWindow k w) <= L)
    (hright : forall k, Membership.mem (Finset.Ioc 0 B) k ->
      companionCap q (K * k) (c * k) (C / k) (dilatedWindow k v) <= R) :
    norm (squarefreeCompanionPacket psi G H K a c B C w v) <=
      L * R * Real.sqrt ((B : Real) * (C : Real)) * harmonicPrefix B := by
  calc
    _ <= (Finset.Ioc 0 B).sum (fun k => squarefreeRowCost q H K a c B C k w v) :=
      squarefree_coprime_row_bound psi hpsi G hG H K a c B C hH hK ha hc w v
    _ <= (Finset.Ioc 0 B).sum (fun k =>
        ((Nat.sqrt (B / k) : Real) * (Nat.sqrt (C / k) : Real)) * (L * R)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hcapR : 0 <= companionCap q (K * k) (c * k) (C / k)
          (dilatedWindow k v) := by
        unfold companionCap windowVariation
        positivity
      have hcaps :
          companionCap q (H * k) (a * k) (B / k) (dilatedWindow k w) *
            companionCap q (K * k) (c * k) (C / k) (dilatedWindow k v) <= L * R :=
        mul_le_mul (hleft k hk) (hright k hk) hcapR hL
      unfold squarefreeRowCost
      calc
        _ = ((Nat.sqrt (B / k) : Real) * (Nat.sqrt (C / k) : Real)) *
            (companionCap q (H * k) (a * k) (B / k) (dilatedWindow k w) *
              companionCap q (K * k) (c * k) (C / k) (dilatedWindow k v)) := by ring
        _ <= _ := mul_le_mul_of_nonneg_left hcaps (by positivity)
    _ = ((Finset.Ioc 0 B).sum (fun k =>
        (Nat.sqrt (B / k) : Real) * (Nat.sqrt (C / k) : Real))) * (L * R) := by
      rw [Finset.sum_mul]
    _ <= (Real.sqrt ((B : Real) * (C : Real)) * harmonicPrefix B) * (L * R) :=
      mul_le_mul_of_nonneg_right (squarefree_divisor_cost_bound B C) (mul_nonneg hL hR)
    _ = _ := by ring


/-- The native square-part input, with its physical scale retained exactly. -/
def squaredWindow (f : Real -> Complex) (A D : Nat) (i : Nat) : Complex :=
  f (((A * (i + 1) ^ 2 : Nat) : Real) / (D : Real))

/-- A fixed Schwartz seminorm budget for every physical square-part rescaling. -/
def squareWindowBudget (f : SchwartzMap Real Complex) : Real :=
  (SchwartzMap.seminorm Real 0 0) f +
    8 * (CarmichaelNativeLowSector.schwartzLipschitzConstant f : Real)

/-- No variation hypothesis remains for the actual squared Schwartz window. -/
theorem squared_window_variation (f : SchwartzMap Real Complex)
    (A D N : Nat) (hD : 0 < D) (hcap : A * N ^ 2 <= 4 * D) :
    windowVariation (squaredWindow f A D) N <= squareWindowBudget f := by
  let L := CarmichaelNativeLowSector.schwartzLipschitzConstant f
  have hLip : LipschitzWith L f := CarmichaelNativeLowSector.schwartz_lipschitz f
  have hL : 0 <= (L : Real) := L.coe_nonneg
  have hDR : 0 < (D : Real) := Nat.cast_pos.mpr hD
  let c : Real := (A : Real) / (D : Real)
  have hc : 0 <= c := div_nonneg (Nat.cast_nonneg _) (le_of_lt hDR)
  have hbound (x : Real) : norm (f x) <= (SchwartzMap.seminorm Real 0 0) f := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.norm_iteratedFDeriv_le_seminorm Real f 0 x
  have hend : norm (squaredWindow f A D (N - 1)) <=
      (SchwartzMap.seminorm Real 0 0) f :=
    hbound (((A * (N - 1 + 1) ^ 2 : Nat) : Real) / (D : Real))
  have hscale : ((A : Real) * (N : Real) ^ 2) / (D : Real) <= 4 := by
    have hi : (A : Real) * (N : Real) ^ 2 <= 4 * (D : Real) := by exact_mod_cast hcap
    have he : (((A : Real) * (N : Real) ^ 2) / (D : Real)) * (D : Real) =
        (A : Real) * (N : Real) ^ 2 := by field_simp [ne_of_gt hDR]
    nlinarith
  have hinc : forall i, Membership.mem (Finset.range (N - 1)) i ->
      norm (squaredWindow f A D (i + 1) - squaredWindow f A D i) <=
        2 * (L : Real) * c * (N : Real) := by
    intro i hi
    have hiN : i + 2 <= N := by
      have hh := Finset.mem_range.mp hi
      omega
    have hiR : (i : Real) + 2 <= (N : Real) := by exact_mod_cast hiN
    let x : Real := ((A * ((i + 1) + 1) ^ 2 : Nat) : Real) / (D : Real)
    let y : Real := ((A * (i + 1) ^ 2 : Nat) : Real) / (D : Real)
    have hdiff : x - y = c * (2 * (i : Real) + 3) := by
      dsimp only [x, y, c]
      push_cast
      ring
    have hdiff0 : 0 <= x - y := by
      rw [hdiff]
      positivity
    have hstep : x - y <= 2 * c * (N : Real) := by
      rw [hdiff]
      have hlinear : 2 * (i : Real) + 3 <= 2 * (N : Real) := by linarith
      calc
        _ <= c * (2 * (N : Real)) := mul_le_mul_of_nonneg_left hlinear hc
        _ = _ := by ring
    have hn := hLip.norm_sub_le x y
    rw [Real.norm_eq_abs, abs_of_nonneg hdiff0] at hn
    calc
      _ <= (L : Real) * (x - y) := hn
      _ <= (L : Real) * (2 * c * (N : Real)) := mul_le_mul_of_nonneg_left hstep hL
      _ = _ := by ring
  have hsum : (Finset.range (N - 1)).sum (fun i =>
      norm (squaredWindow f A D (i + 1) - squaredWindow f A D i)) <= 8 * (L : Real) := by
    have hconst : 0 <= 2 * (L : Real) * c * (N : Real) := by positivity
    calc
      _ <= (Finset.range (N - 1)).sum (fun _ => 2 * (L : Real) * c * (N : Real)) :=
        Finset.sum_le_sum hinc
      _ = ((N - 1 : Nat) : Real) * (2 * (L : Real) * c * (N : Real)) := by simp
      _ <= (N : Real) * (2 * (L : Real) * c * (N : Real)) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le N 1)) hconst
      _ = 2 * (L : Real) * (((A : Real) * (N : Real) ^ 2) / (D : Real)) := by
        dsimp only [c]
        ring
      _ <= 2 * (L : Real) * 4 := mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by ring
  exact add_le_add hend hsum

/-- Dilation changes the square coefficient by k squared and keeps the original window. -/
theorem squared_window_dilate (f : Real -> Complex) (A D k : Nat) (hk : 0 < k) :
    dilatedWindow k (squaredWindow f A D) = squaredWindow f (A * k ^ 2) D := by
  funext i
  have hi : k * (i + 1) - 1 + 1 = k * (i + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos hk (Nat.succ_pos i))
  unfold dilatedWindow squaredWindow
  rw [hi]
  have he : A * (k * (i + 1)) ^ 2 = (A * k ^ 2) * (i + 1) ^ 2 := by ring
  rw [he]

/-- Every supported coprime row has the same physical Schwartz budget. -/
theorem squared_window_rescaled_variation (f : SchwartzMap Real Complex)
    (A D B k : Nat) (hD : 0 < D) (hk : 0 < k) (hcap : A * B ^ 2 <= 4 * D) :
    windowVariation (dilatedWindow k (squaredWindow f A D)) (B / k) <=
      squareWindowBudget f := by
  rw [squared_window_dilate f A D k hk]
  apply squared_window_variation f (A * k ^ 2) D (B / k) hD
  have hbk := Nat.div_mul_le_self B k
  calc
    _ = A * (((B / k) * k) * ((B / k) * k)) := by ring
    _ <= A * (B * B) := Nat.mul_le_mul_left A (Nat.mul_le_mul hbk hbk)
    _ = A * B ^ 2 := by ring
    _ <= _ := hcap


/-- The actual square-part companion is nonprincipal for every Dirichlet character. -/
theorem squarepart_companion_ne_one {q : Nat} (chi : DirichletCharacter Complex q) :
    Not (OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2) = 1) := by
  have heven : (chi ^ 2) (-1 : ZMod q) = 1 := by
    rw [pow_two, MulChar.mul_apply, <- map_mul]
    have he : (-1 : ZMod q) * (-1) = 1 := by ring
    rw [he, map_one]
  have hcop : IsCoprime (-1 : Int) ((q * 3 : Nat) : Int) :=
    Exists.intro (-1) (Exists.intro 0 (by ring))
  have hbase :
      OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2) (-1) =
        (chi ^ 2) (-1) * OAI.ShortDraftHeckeBridge.chiMinusThree (-1) := by
    simp only [OAI.ShortDraftHeckeBridge.baseChangeChar, MulChar.mul_apply]
    have hl := DirichletCharacter.changeLevel_eq_cast_of_dvd' (chi ^ 2)
      (show Dvd.dvd q (q * 3) from Exists.intro 3 rfl) hcop
    have hr := DirichletCharacter.changeLevel_eq_cast_of_dvd'
      OAI.ShortDraftHeckeBridge.chiMinusThree
      (show Dvd.dvd 3 (q * 3) from Exists.intro q (Nat.mul_comm q 3)) hcop
    simp only [Int.cast_neg, Int.cast_one] at hl hr
    rw [hl, hr]
  have heps : OAI.ShortDraftHeckeBridge.chiMinusThree (-1 : ZMod 3) = -1 := by
    have hcast : (2 : ZMod 3) = -1 := by decide
    rw [<- hcast]
    exact OAI.ShortDraftHeckeBridge.chiMinusThree_mod_two 2 (by decide)
  have hvalue : OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2) (-1) = -1 := by
    rw [hbase, heven, heps, one_mul]
  intro h
  rw [h, MulChar.one_apply (isUnit_one.neg)] at hvalue
  norm_num at hvalue

set_option maxHeartbeats 800000 in
/-- An unconditional square-root companion mean with all physical and subpower costs discharged. -/
theorem squared_squarepart_subpower (eps : Real) (heps : 0 < eps) :
    exists Ceps : Real, 0 < Ceps /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
      (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H K a c B C A E D : Nat), 0 < H -> 0 < K -> 0 < a -> 0 < c -> 0 < D ->
      A * B ^ 2 <= 4 * D -> E * C ^ 2 <= 4 * D ->
      forall (f g : SchwartzMap Real Complex),
      norm (squarefreeCompanionPacket (OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2))
        G H K a c B C (squaredWindow f A D) (squaredWindow g E D)) <=
        Ceps * (((q * 3 : Nat) : Real) ^ 2) * squareWindowBudget f * squareWindowBudget g *
          (((H + K + a + c + 1) * (B + C + 1) : Nat) : Real) ^ eps *
            Real.sqrt ((B : Real) * (C : Real)) := by
  choose Cd hCd hd using QuadraticDivisorMean.divisor_card_subpower
    (eps / 8) (by linarith)
  choose Ch hCh hh using CarmichaelNativeLowSector.harmonic_subpower
    (eps / 10) (by linarith)
  refine Exists.intro (Cd ^ 4 * Ch ^ 5) (And.intro (by positivity) ?_)
  intro q inst chi G hG H K a c B C A E D hH hK ha hc hD hAB hEC f g
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let : NeZero (q * 3) := NeZero.mk (by omega)
  let X : Nat := (H + K + a + c + 1) * (B + C + 1)
  let Q : Real := ((q * 3 : Nat) : Real)
  let t : Real := harmonicPrefix X
  have hX : 0 < X := by dsimp only [X]; positivity
  have hXR : 0 < (X : Real) := Nat.cast_pos.mpr hX
  have hsize : B + C + 1 <= X := by
    dsimp only [X]
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (B + C + 1)
      (show 1 <= H + K + a + c + 1 by omega)
  have hBX : B <= X := (show B <= B + C + 1 by omega).trans hsize
  have hCX : C <= X := (show C <= B + C + 1 by omega).trans hsize
  have hnk (n k : Nat) (hn : n <= H + K + a + c + 1) (hk : k <= B) :
      n * k <= X :=
    Nat.mul_le_mul hn (hk.trans (by omega))
  let M : Real := Cd * (X : Real) ^ (eps / 8)
  have hM : 0 <= M := by dsimp only [M]; positivity
  have hdiv (n : Nat) (hn : 0 < n) (hnX : n <= X) :
      (n.divisors.card : Real) <= M :=
    (hd n hn).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hnX) (by linarith))
      (le_of_lt hCd))
  have ht : t <= Ch * (X : Real) ^ (eps / 10) := hh X
  have ht0 : 0 <= t :=
    Finset.sum_nonneg (fun _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hf0 : 0 <= squareWindowBudget f := by
    unfold squareWindowBudget
    exact add_nonneg (NonnegHomClass.apply_nonneg _ _)
      (mul_nonneg (by norm_num)
        (CarmichaelNativeLowSector.schwartzLipschitzConstant f).coe_nonneg)
  have hg0 : 0 <= squareWindowBudget g := by
    unfold squareWindowBudget
    exact add_nonneg (NonnegHomClass.apply_nonneg _ _)
      (mul_nonneg (by norm_num)
        (CarmichaelNativeLowSector.schwartzLipschitzConstant g).coe_nonneg)
  let Lcap : Real := M * t ^ 2 * squareWindowBudget f * (M * Q)
  let Rcap : Real := M * t ^ 2 * squareWindowBudget g * (M * Q)
  have hLcap : 0 <= Lcap := by dsimp only [Lcap, Q]; positivity
  have hRcap : 0 <= Rcap := by dsimp only [Rcap, Q]; positivity
  have hleft : forall k, Membership.mem (Finset.Ioc 0 B) k ->
      companionCap (q * 3) (H * k) (a * k) (B / k)
        (dilatedWindow k (squaredWindow f A D)) <= Lcap := by
    intro k hk
    have hkpos := (Finset.mem_Ioc.mp hk).1
    have hkB := (Finset.mem_Ioc.mp hk).2
    exact CarmichaelNativeLowSector.cap_bound (q * 3) (H * k) (a * k) (B / k) X
      (dilatedWindow k (squaredWindow f A D)) M (squareWindowBudget f) hM hf0
      ((Nat.div_le_self B k).trans hBX)
      (hdiv (a * k) (Nat.mul_pos ha hkpos) (hnk a k (by omega) hkB))
      (hdiv (H * k) (Nat.mul_pos hH hkpos) (hnk H k (by omega) hkB))
      (squared_window_rescaled_variation f A D B k hD hkpos hAB)
  have hright : forall k, Membership.mem (Finset.Ioc 0 B) k ->
      companionCap (q * 3) (K * k) (c * k) (C / k)
        (dilatedWindow k (squaredWindow g E D)) <= Rcap := by
    intro k hk
    have hkpos := (Finset.mem_Ioc.mp hk).1
    have hkB := (Finset.mem_Ioc.mp hk).2
    exact CarmichaelNativeLowSector.cap_bound (q * 3) (K * k) (c * k) (C / k) X
      (dilatedWindow k (squaredWindow g E D)) M (squareWindowBudget g) hM hg0
      ((Nat.div_le_self C k).trans hCX)
      (hdiv (c * k) (Nat.mul_pos hc hkpos) (hnk c k (by omega) hkB))
      (hdiv (K * k) (Nat.mul_pos hK hkpos) (hnk K k (by omega) hkB))
      (squared_window_rescaled_variation g E D C k hD hkpos hEC)
  have hpacket := squarefree_coprime_harmonic_bound
    (OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2)) (squarepart_companion_ne_one chi)
    G hG H K a c B C hH hK ha hc
    (squaredWindow f A D) (squaredWindow g E D)
    Lcap Rcap hLcap hRcap hleft hright
  have hHB : harmonicPrefix B <= t :=
    CarmichaelNativeLowSector.harmonic_prefix_mono hBX
  have hbase : norm (squarefreeCompanionPacket
      (OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2))
      G H K a c B C (squaredWindow f A D) (squaredWindow g E D)) <=
      Q ^ 2 * M ^ 4 * squareWindowBudget f * squareWindowBudget g *
        t ^ 5 * Real.sqrt ((B : Real) * (C : Real)) := by
    calc
      _ <= Lcap * Rcap * Real.sqrt ((B : Real) * (C : Real)) * harmonicPrefix B := hpacket
      _ <= Lcap * Rcap * Real.sqrt ((B : Real) * (C : Real)) * t :=
        mul_le_mul_of_nonneg_left hHB (by positivity)
      _ = _ := by dsimp only [Lcap, Rcap]; ring
  have ht5 : t ^ 5 <= (Ch * (X : Real) ^ (eps / 10)) ^ 5 := by gcongr
  have he4 : ((X : Real) ^ (eps / 8)) ^ 4 = (X : Real) ^ (eps / 2) := by
    rw [<- Real.rpow_natCast _ 4, <- Real.rpow_mul (le_of_lt hXR)]
    congr 1
    norm_num <;> ring
  have he5 : ((X : Real) ^ (eps / 10)) ^ 5 = (X : Real) ^ (eps / 2) := by
    rw [<- Real.rpow_natCast _ 5, <- Real.rpow_mul (le_of_lt hXR)]
    congr 1
    norm_num <;> ring
  have hmass : M ^ 4 * t ^ 5 <= Cd ^ 4 * Ch ^ 5 * (X : Real) ^ eps := by
    calc
      _ <= M ^ 4 * (Ch * (X : Real) ^ (eps / 10)) ^ 5 :=
        mul_le_mul_of_nonneg_left ht5 (pow_nonneg hM _)
      _ = Cd ^ 4 * Ch ^ 5 *
          ((X : Real) ^ (eps / 2) * (X : Real) ^ (eps / 2)) := by
        dsimp only [M]
        rw [mul_pow, mul_pow, he4, he5]
        ring
      _ = _ := by
        rw [<- Real.rpow_add hXR, show eps / 2 + eps / 2 = eps by ring]
  calc
    _ <= Q ^ 2 * M ^ 4 * squareWindowBudget f * squareWindowBudget g *
        t ^ 5 * Real.sqrt ((B : Real) * (C : Real)) := hbase
    _ = (Q ^ 2 * squareWindowBudget f * squareWindowBudget g *
        Real.sqrt ((B : Real) * (C : Real))) * (M ^ 4 * t ^ 5) := by ring
    _ <= (Q ^ 2 * squareWindowBudget f * squareWindowBudget g *
        Real.sqrt ((B : Real) * (C : Real))) *
        (Cd ^ 4 * Ch ^ 5 * (X : Real) ^ eps) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by dsimp only [Q, X]; ring

end PrimeFactorOscillations.CarmichaelSquarepartCancellation
