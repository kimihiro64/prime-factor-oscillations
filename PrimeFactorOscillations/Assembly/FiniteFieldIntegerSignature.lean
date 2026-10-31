/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticCharacter
import PrimeFactorOscillations.Helpers.QRHPrimePrefix

/-!
# Finite-field quadratic signatures determine bounded integer prime pairs

A prime divisor of odd valuation supplies a constructive CRT witness for
nonprincipality, without requiring its coefficient to be smaller than it.
The installed uniform Dirichlet-character estimate then bounds the signed
quadratic correlation. The reciprocal-prime main term is retained.

The final finite certificate states exactly when a prime band distinguishes
two actual bounded-gap integer prime pairs. It is a return-map rigidity
statement; it does not assert a new supply of prime pairs or improve a
zero-free exponent.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

open IntegerQuadraticCharacter
open QuadraticCarrierPacket IntegerQuadraticSieve

theorem numerator_kernel_mul_numerators (D E : Int) (n : Nat) :
    numeratorKernel (D * E) n = numeratorKernel D n * numeratorKernel E n := by
  by_cases hn : Odd n
  . simp only [numeratorKernel, ite_eq_left hn, jacobiSym.mul_left, Int.cast_mul]
  . simp only [numeratorKernel, ite_eq_right hn, zero_mul]

theorem exists_coprime_prime_factor_witness (h P : Nat)
    (hh : 0 < h) (hP : Nat.Prime P) (hP2 : 2 < P)
    (hPh : Nat.Coprime P h) :
    exists u : Nat, And
      (numeratorKernel ((h : Int) * (P : Int)) u = -1)
      (numeratorKernel (-((h : Int) * (P : Int))) u = -1) := by
  have : Fact (Nat.Prime P) := Fact.mk hP
  have : NeZero P := NeZero.mk hP.ne_zero
  have hPo : Odd P := hP.odd_of_ne_two (by omega)
  have hchar : Not (ringChar (ZMod P) = 2) := by
    simpa only [ringChar.eq (ZMod P) P] using (show Not (P = 2) by omega)
  let a : ZMod P := Classical.choose (quadraticChar_exists_neg_one hchar)
  have ha : (quadraticChar (ZMod P)) a = -1 :=
    Classical.choose_spec (quadraticChar_exists_neg_one hchar)
  have hP4 : Nat.Coprime P 4 := by
    have ht := Nat.coprime_two_right.mpr hPo
    simpa only [show (2 : Nat) ^ 2 = 4 by norm_num] using
      (Nat.coprime_pow_right_iff (by decide : 0 < (2 : Nat)) P 2).mpr ht
  have hco : Nat.Coprime (4 * h) P :=
    Nat.coprime_mul_iff_left.mpr (And.intro hP4.symm hPh.symm)
  let w := Nat.chineseRemainder hco 1 a.val
  let u : Nat := w.val
  have huMod : u % (4 * h) = 1 := by
    have ht := w.property.1
    change u % (4 * h) = 1 % (4 * h) at ht
    simpa only [Nat.mod_eq_of_lt (show 1 < 4 * h by omega)] using ht
  have hu4 : u % 4 = 1 := by
    calc
      _ = (u % (4 * h)) % 4 :=
        (Nat.mod_mod_of_dvd u (dvd_mul_right 4 h)).symm
      _ = 1 := by rw [huMod]
  have hu : Odd u := by
    apply Nat.odd_iff.mpr
    calc
      _ = (u % 4) % 2 := (Nat.mod_mod_of_dvd u (by decide : Dvd.dvd (2 : Nat) 4)).symm
      _ = 1 := by rw [hu4]
  have huCast : (u : ZMod P) = a := by
    have ht : (u : ZMod P) = (a.val : ZMod P) :=
      (ZMod.natCast_eq_natCast_iff u a.val P).mpr w.property.2
    exact ht.trans (ZMod.natCast_zmod_val a)
  have hhJacobi : jacobiSym (h : Int) u = 1 := by
    have ht := jacobiSym.mod_right' h hu
    rw [huMod, jacobiSym.one_right] at ht
    exact ht
  have hpJacobi : jacobiSym (P : Int) u = -1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hPo hu4,
      <- jacobiSym.legendreSym.to_jacobiSym P (u : Int)]
    simpa only [legendreSym, Int.cast_natCast, huCast] using ha
  have hneg : jacobiSym (-1) u = 1 := by
    have ht := jacobiSym.mod_right (-1 : Int) hu
    simpa only [Int.natAbs_neg, Int.natAbs_one, Nat.mul_one, hu4,
      jacobiSym.one_right] using ht
  have hprod : jacobiSym ((h : Int) * (P : Int)) u = -1 := by
    rw [jacobiSym.mul_left, hhJacobi, hpJacobi]
    norm_num
  have hprodneg : jacobiSym (-((h : Int) * (P : Int))) u = -1 := by
    rw [show -((h : Int) * (P : Int)) = (-1) * ((h : Int) * (P : Int)) by ring,
      jacobiSym.mul_left, hneg, hprod]
    norm_num
  refine Exists.intro u (And.intro ?_ ?_)
  . simp only [numeratorKernel, ite_eq_left hu, hprod, Int.cast_neg, Int.cast_one]
  . simp only [numeratorKernel, ite_eq_left hu, hprodneg, Int.cast_neg, Int.cast_one]

theorem numerator_character_ne_one_of_coprime_prime_factor (h P : Nat)
    (hh : 0 < h) (hP : Nat.Prime P) (hP2 : 2 < P)
    (hPh : Nat.Coprime P h)
    (D : Int) (hD : Not (D = 0))
    (hSign : Or (D = (h : Int) * (P : Int))
      (D = -((h : Int) * (P : Int)))) :
    Not (numeratorCharacter D hD = 1) := by
  choose u hu using exists_coprime_prime_factor_witness h P hh hP hP2 hPh
  apply character_ne_one_of_neg_one (numeratorCharacter D hD) (u : ZMod (4 * D.natAbs))
  rw [numerator_character_natCast]
  cases hSign with
  | inl hs => simpa only [hs] using hu.1
  | inr hs => simpa only [hs] using hu.2

def reciprocalBand (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun p => 1 / (p : Real))

def separationScore (D : Int) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum
    (fun p => (1 / (p : Real)) * (1 - (numeratorKernel D p).re))

theorem separation_score_identity (D : Int) (Y X : Nat) :
    separationScore D Y X = reciprocalBand Y X -
      (Finset.sum ((Finset.Ico Y X).filter Nat.Prime)
        (fun p => HSMul.hSMul (1 / (p : Real)) (numeratorKernel D p))).re := by
  simp [separationScore, reciprocalBand, mul_sub, Finset.sum_sub_distrib]

theorem exists_uniform_separation_score_lower :
    exists C : Real, And (0 < C)
      (forall h P : Nat, 0 < h -> Nat.Prime P -> 2 < P -> Nat.Coprime P h ->
        forall D : Int,
          Or (D = (h : Int) * (P : Int)) (D = -((h : Int) * (P : Int))) ->
        forall Y X : Nat, 1 <= Y ->
          reciprocalBand Y X -
            C * (3 + Real.log ((4 * h * P : Nat) : Real)) ^ 2 *
              (Y : Real) ^ (-1 / 32 : Real) <= separationScore D Y X) := by
  choose C hCpos hC using QRH.exists_primeCharacter_reciprocal_tail_bound
  refine Exists.intro C (And.intro hCpos ?_)
  intro h P hh hP hP2 hPh D hSign Y X hY
  have hAbs : D.natAbs = h * P := by
    cases hSign with
    | inl hs => simp only [hs, Int.natAbs_mul, Int.natAbs_natCast]
    | inr hs => simp only [hs, Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast]
  have hprod : 0 < h * P := Nat.mul_pos hh hP.pos
  have hD : Not (D = 0) := by
    intro hz
    rw [hz, Int.natAbs_zero] at hAbs
    omega
  have : NeZero (4 * D.natAbs) := NeZero.mk (by
    apply ne_of_gt
    apply Nat.mul_pos (by decide : 0 < (4 : Nat))
    rw [hAbs]
    exact hprod)
  have hn := numerator_character_ne_one_of_coprime_prime_factor h P hh hP hP2 hPh
    D hD hSign
  have ht := hC (numeratorCharacter D hD) hn Y X hY
  simp only [numerator_character_natCast] at ht
  have hlevel : 4 * D.natAbs = 4 * h * P := by rw [hAbs, Nat.mul_assoc]
  rw [hlevel] at ht
  rw [separation_score_identity]
  have hr := Complex.re_le_norm
    (Finset.sum ((Finset.Ico Y X).filter Nat.Prime)
      (fun p => HSMul.hSMul (1 / (p : Real)) (numeratorKernel D p)))
  linarith only [hr, ht]


theorem endpoint_coefficient_coprime (h k P R : Nat)
    (hh : 0 < h) (hk : 0 < k) (hP : Nat.Prime P) (hR : Nat.Prime R)
    (hhP : h < P) (hkP : k < P) (hPR : Not (P = R)) :
    Nat.Coprime P (h * k * R) := by
  have hPh := Nat.coprime_of_lt_prime (ne_of_gt hh) hhP hP
  have hPk := Nat.coprime_of_lt_prime (ne_of_gt hk) hkP hP
  have hPr : Nat.Coprime P R := by
    apply hP.coprime_iff_not_dvd.mpr
    intro hd
    cases (Nat.dvd_prime hR).mp hd with
    | inl he => exact hP.ne_one he
    | inr he => exact hPR he
  exact Nat.coprime_mul_iff_right.mpr
    (And.intro (Nat.coprime_mul_iff_right.mpr (And.intro hPh hPk)) hPr)

theorem positive_kernel_square_on_prime (h P p : Nat)
    (hh : 0 < h) (hP : Nat.Prime P) (hp : Nat.Prime p)
    (hp2 : 2 < p) (hhp : h < p) (hpP : p < P) :
    numeratorKernel ((h : Int) * (P : Int)) p ^ 2 = 1 := by
  have : Fact (Nat.Prime p) := Fact.mk hp
  have hhn : Not ((h : ZMod p) = 0) := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff h p).mp hz
    exact (Nat.not_dvd_of_pos_of_lt hh hhp) hd
  have hPn : Not ((P : ZMod p) = 0) := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff P p).mp hz
    cases (Nat.dvd_prime hP).mp hd with
    | inl he => exact hp.ne_one he
    | inr he => omega
  have hn : Not ((((h : Int) * (P : Int)) : ZMod p) = 0) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using mul_ne_zero hhn hPn
  rw [numerator_kernel_prime _ p (by omega)]
  exact_mod_cast quadraticChar_sq_one hn

theorem separation_score_zero_of_matching (D E : Int) (Y X : Nat)
    (hsq : forall p, Membership.mem ((Finset.Ico Y X).filter Nat.Prime) p ->
      numeratorKernel D p ^ 2 = 1)
    (hmatch : forall p, Membership.mem ((Finset.Ico Y X).filter Nat.Prime) p ->
      numeratorKernel D p = numeratorKernel E p) :
    separationScore (D * E) Y X = 0 := by
  unfold separationScore
  apply Finset.sum_eq_zero
  intro p hp
  have he : numeratorKernel (D * E) p = 1 := by
    rw [numerator_kernel_mul_numerators, <- hmatch p hp, <- pow_two, hsq p hp]
  simp only [he, Complex.one_re, sub_self, mul_zero]

theorem exists_finite_endpoint_signature_separation :
    exists C : Real, And (0 < C)
      (forall h k P R Y X : Nat,
        0 < h -> 0 < k -> Nat.Prime P -> Nat.Prime R -> Not (P = R) ->
        h < Y -> k < Y -> 2 < Y -> X <= P -> X <= R ->
        C * (3 + Real.log ((4 * (h * k * R) * P : Nat) : Real)) ^ 2 *
          (Y : Real) ^ (-1 / 32 : Real) < reciprocalBand Y X ->
        exists p : Nat, And (Membership.mem ((Finset.Ico Y X).filter Nat.Prime) p)
          (Not (numeratorKernel ((h : Int) * (P : Int)) p =
            numeratorKernel ((k : Int) * (R : Int)) p))) := by
  classical
  choose C hCpos hC using exists_uniform_separation_score_lower
  refine Exists.intro C (And.intro hCpos ?_)
  intro h k P R Y X hh hk hP hR hPR hhY hkY hY hXP hXR hmargin
  by_cases hYX : X <= Y
  . have hempty : reciprocalBand Y X = 0 := by
      simp [reciprocalBand, Finset.Ico_eq_empty_of_le hYX]
    rw [hempty] at hmargin
    have hn : 0 <= C * (3 + Real.log ((4 * (h * k * R) * P : Nat) : Real)) ^ 2 *
        (Y : Real) ^ (-1 / 32 : Real) := by positivity
    linarith only [hmargin, hn]
  have hYXP : Y < P := lt_of_lt_of_le (lt_of_not_ge hYX) hXP
  have hco := endpoint_coefficient_coprime h k P R hh hk hP hR
    (hhY.trans hYXP) (hkY.trans hYXP) hPR
  let D : Int := ((h * k * R : Nat) : Int) * (P : Int)
  have hhkR : 0 < h * k * R := Nat.mul_pos (Nat.mul_pos hh hk) hR.pos
  have hlow := hC (h * k * R) P hhkR hP (by omega) hco D (Or.inl rfl) Y X (by omega)
  have hD : D = ((h : Int) * (P : Int)) * ((k : Int) * (R : Int)) := by
    dsimp [D]
    ring
  by_contra hnone
  push Not at hnone
  have hz : separationScore D Y X = 0 := by
    rw [hD]
    apply separation_score_zero_of_matching _ _ Y X
    . intro p hp
      have ht := Finset.mem_filter.mp hp
      have hi := Finset.mem_Ico.mp ht.1
      exact positive_kernel_square_on_prime h P p hh hP ht.2
        (lt_of_lt_of_le hY hi.1) (hhY.trans_le hi.1) (hi.2.trans_le hXP)
    . exact hnone
  rw [hz] at hlow
  linarith only [hlow, hmargin]


theorem endpoint_cost_le_uniform (C : Real) (h k P R H T Y : Nat)
    (hC : 0 <= C) (hh : 0 < h) (hk : 0 < k) (hP : 0 < P) (hR : 0 < R)
    (hhH : h <= H) (hkH : k <= H) (hPT : P <= T) (hRT : R <= T) :
    C * (3 + Real.log ((4 * (h * k * R) * P : Nat) : Real)) ^ 2 *
        (Y : Real) ^ (-1 / 32 : Real) <=
      C * (3 + Real.log ((4 * H * H * T * T : Nat) : Real)) ^ 2 *
        (Y : Real) ^ (-1 / 32 : Real) := by
  have hlevel : 4 * (h * k * R) * P <= 4 * H * H * T * T := by
    calc
      _ = 4 * ((h * k) * (R * P)) := by ring
      _ <= 4 * ((H * H) * (T * T)) :=
        Nat.mul_le_mul_left 4 (Nat.mul_le_mul
          (Nat.mul_le_mul hhH hkH) (Nat.mul_le_mul hRT hPT))
      _ = _ := by ring
  have hpos : 0 < 4 * (h * k * R) * P := by positivity
  have hposR : (0 : Real) < ((4 * (h * k * R) * P : Nat) : Real) := by
    exact_mod_cast hpos
  have hlog := Real.log_le_log hposR (Nat.cast_le.mpr hlevel)
  have hone : (1 : Real) <= ((4 * (h * k * R) * P : Nat) : Real) := by
    exact_mod_cast (show 1 <= 4 * (h * k * R) * P from hpos)
  have hnon : 0 <= 3 + Real.log ((4 * (h * k * R) * P : Nat) : Real) := by
    have hl := Real.log_nonneg hone
    linarith only [hl]
  have hsum : 0 <= (3 + Real.log ((4 * H * H * T * T : Nat) : Real)) +
      (3 + Real.log ((4 * (h * k * R) * P : Nat) : Real)) := by
    linarith only [hlog, hnon]
  have hdiff : 0 <= (3 + Real.log ((4 * H * H * T * T : Nat) : Real)) -
      (3 + Real.log ((4 * (h * k * R) * P : Nat) : Real)) := by
    linarith only [hlog]
  have hmul := mul_nonneg hdiff hsum
  have hsq : (3 + Real.log ((4 * (h * k * R) * P : Nat) : Real)) ^ 2 <=
      (3 + Real.log ((4 * H * H * T * T : Nat) : Real)) ^ 2 := by
    nlinarith only [hmul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC)
    (Real.rpow_nonneg (Nat.cast_nonneg Y) _)

theorem exists_finite_prime_pair_signature_rigidity :
    exists C : Real, And (0 < C)
      (forall H T n m h k Y X : Nat,
        Nat.Prime n -> Nat.Prime (n + h) -> Nat.Prime m -> Nat.Prime (m + k) ->
        0 < h -> 0 < k -> h <= H -> k <= H -> H < Y -> 2 < Y ->
        X <= n -> X <= m -> n + h <= T -> m + k <= T ->
        C * (3 + Real.log ((4 * H * H * T * T : Nat) : Real)) ^ 2 *
          (Y : Real) ^ (-1 / 32 : Real) < reciprocalBand Y X ->
        (forall p : Nat, Membership.mem ((Finset.Ico Y X).filter Nat.Prime) p ->
          And
            (numeratorKernel ((h : Int) * (n : Int)) p =
              numeratorKernel ((k : Int) * (m : Int)) p)
            (numeratorKernel ((h : Int) * ((n + h : Nat) : Int)) p =
              numeratorKernel ((k : Int) * ((m + k : Nat) : Int)) p)) ->
        And (n = m) (h = k)) := by
  classical
  choose C hCpos hC using exists_finite_endpoint_signature_separation
  refine Exists.intro C (And.intro hCpos ?_)
  intro H T n m h k Y X hn hnh hm hmk hh hk hhH hkH hHY hY hXn hXm hnT hmT hmargin hmatch
  have hhY : h < Y := hhH.trans_lt hHY
  have hkY : k < Y := hkH.trans_lt hHY
  have hn0 : 0 < n := hn.pos
  have hm0 : 0 < m := hm.pos
  have hnSmall : n <= T := by omega
  have hmSmall : m <= T := by omega
  have hnm : n = m := by
    by_contra hne
    have he := endpoint_cost_le_uniform C h k n m H T Y hCpos.le
      hh hk hn0 hm0 hhH hkH hnSmall hmSmall
    choose p hp using hC h k n m Y X hh hk hn hm hne hhY hkY hY
      hXn hXm (he.trans_lt hmargin)
    exact hp.2 ((hmatch p hp.1).1)
  subst m
  have hhk : h = k := by
    by_contra hne
    have hend : Not (n + h = n + k) := by omega
    have he := endpoint_cost_le_uniform C h k (n + h) (n + k) H T Y hCpos.le
      hh hk hnh.pos hmk.pos hhH hkH hnT hmT
    choose p hp using hC h k (n + h) (n + k) Y X hh hk hnh hmk hend hhY hkY hY
      (by omega) (by omega) (he.trans_lt hmargin)
    exact hp.2 ((hmatch p hp.1).2)
  exact And.intro rfl hhk

end PrimeFactorOscillations.FiniteFieldIntegerSignature
