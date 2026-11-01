/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeArithmeticAgreement

/-!
# The exceptional half-agreement neighborhood

A fixed actual prime pair has only square-root many half-agreeing candidate
pairs up to a given upper endpoint. The independent field limit is taken
first for each fixed comparison; no moving-endpoint estimate is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open IntegerQuadraticCharacter

theorem native_half_agreement_endpoint_localization (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hneq : Not (And (n = m) (h = k)))
    (hrate : nativeAgreementRate n h m k = 1 / 2) :
    Or (And (m <= h * n) (IsSquare (h * n * k * m)))
      (m + k <= h * (n + h)) := by
  classical
  have hn0 := hn.pos
  have hm0 := hm.pos
  have hh1 : 1 <= h := by omega
  have hA : 0 < h * n := Nat.mul_pos hh hn.pos
  have hB : 0 < h * (n + h) := Nat.mul_pos hh hnh.pos
  have hA2 : 2 <= h * n := hn.two_le.trans (by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right n hh1)
  have hB2 : 2 <= h * (n + h) := hnh.two_le.trans (by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (n + h) hh1)
  have hfirst (hs : IsSquare (h * k * n * m)) : m <= h * n := by
    by_contra hlarge
    have hAm : h * n < m := by omega
    have hm2 : 2 < m := by omega
    have hcopA : Nat.Coprime m (h * n) :=
      hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hA hAm)
    have hcopQ : Nat.Coprime m (m + k) :=
      (Nat.coprime_primes hm hmk).mpr (by omega)
    have hcopK : Nat.Coprime m k := Nat.coprime_self_add_right.mp hcopQ
    have hD : Not (((h * k * n * m : Nat) : Int) = 0) := by
      exact_mod_cast (ne_of_gt (show 0 < h * k * n * m by positivity))
    have hprincipal := (numerator_character_nat_eq_one_iff_isSquare
      (h * k * n * m) (by positivity) hD).mpr hs
    have hsign : ((h * k * n * m : Nat) : Int) =
        ((h * n * k : Nat) : Int) * (m : Int) := by
      push_cast
      ring
    have hnon := numerator_character_ne_one_of_coprime_prime_factor
      (h * n * k) m (by positivity) hm hm2 (hcopA.mul_right hcopK)
      ((h * k * n * m : Nat) : Int) hD (Or.inl hsign)
    exact hnon hprincipal
  have hsecond (hs : IsSquare (h * k * (n + h) * (m + k))) :
      m + k <= h * (n + h) := by
    by_contra hlarge
    have hBq : h * (n + h) < m + k := by omega
    have hq2 : 2 < m + k := by omega
    have hcopB : Nat.Coprime (m + k) (h * (n + h)) :=
      hmk.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hB hBq)
    have hcopK : Nat.Coprime (m + k) k :=
      hmk.coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt hk (by have hp := hm.pos; omega))
    have hD : Not (((h * k * (n + h) * (m + k) : Nat) : Int) = 0) := by
      exact_mod_cast (ne_of_gt (show 0 < h * k * (n + h) * (m + k) by positivity))
    have hprincipal := (numerator_character_nat_eq_one_iff_isSquare
      (h * k * (n + h) * (m + k)) (by positivity) hD).mpr hs
    have hsign : ((h * k * (n + h) * (m + k) : Nat) : Int) =
        ((h * (n + h) * k : Nat) : Int) * ((m + k : Nat) : Int) := by
      push_cast
      ring
    have hnon := numerator_character_ne_one_of_coprime_prime_factor
      (h * (n + h) * k) (m + k) (by positivity) hmk hq2 (hcopB.mul_right hcopK)
      ((h * k * (n + h) * (m + k) : Nat) : Int) hD (Or.inl hsign)
    exact hnon hprincipal
  rcases (native_agreement_arithmetic_classification
    n h m k hn hnh hm hmk hh hk hneq).1.mp hrate with hs | hs
  . refine Or.inl (And.intro (hfirst hs) ?_)
    have hid : h * n * k * m = h * k * n * m := by ring
    rw [hid]
    exact hs
  . exact Or.inr (hsecond hs)

def nativeHalfAgreementPairs (n h Y : Nat) : Finset (Prod Nat Nat) := by
  classical
  exact (Finset.product (Finset.range (Y + 1)) (Finset.range (Y + 1))).filter
    (fun pair => Nat.Prime pair.1 /\ Nat.Prime pair.2 /\ pair.1 < pair.2 /\
      Not (And (pair.1 = n) (pair.2 = n + h)) /\
      nativeAgreementRate n h pair.1 (pair.2 - pair.1) = 1 / 2)

theorem native_exceptional_agreement_count_bound (n h Y : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h)) (hh : 0 < h) :
    (nativeHalfAgreementPairs n h Y).card <=
      (h * n + 1) * (Nat.sqrt ((h * n) ^ 2 * Y) + 1) +
        (h * (n + h) + 1) ^ 2 := by
  classical
  let A := h * n
  let B := h * (n + h)
  let S := nativeHalfAgreementPairs n h Y
  let V : Prod Nat Nat -> Nat := fun pair => A * (pair.2 - pair.1) * pair.1
  let L := S.filter (fun pair => And (pair.1 <= A) (IsSquare (V pair)))
  let U := S.filter (fun pair => pair.2 <= B)
  let R := Nat.sqrt (A ^ 2 * Y)
  let T := Finset.product (Finset.range (A + 1)) (Finset.range (R + 1))
  let f : Prod Nat Nat -> Prod Nat Nat := fun pair =>
    Prod.mk pair.1 (Nat.sqrt (V pair))
  have hA : 0 < A := Nat.mul_pos hh hn.pos
  have hroot (N : Nat) (hs : IsSquare N) :
      Nat.sqrt N * Nat.sqrt N = N := by
    choose s hs using hs
    rw [hs, Nat.sqrt_eq]
  have hcover : S.card <= (Union.union L U).card := by
    apply Finset.card_le_card
    intro pair hp
    have hd := Finset.mem_filter.mp hp
    have hsum : pair.1 + (pair.2 - pair.1) = pair.2 := by omega
    have hupper : Nat.Prime (pair.1 + (pair.2 - pair.1)) := by
      rw [hsum]
      exact hd.2.2.1
    have hneq : Not (And (n = pair.1) (h = pair.2 - pair.1)) := by
      intro he
      apply hd.2.2.2.2.1
      constructor <;> omega
    have hloc := native_half_agreement_endpoint_localization n h pair.1
      (pair.2 - pair.1) hn hnh hd.2.1 hupper hh (by omega) hneq hd.2.2.2.2.2
    change Or (And (pair.1 <= A) (IsSquare (V pair)))
      (pair.1 + (pair.2 - pair.1) <= B) at hloc
    rw [hsum] at hloc
    apply Finset.mem_union.mpr
    rcases hloc with hl | hu
    . exact Or.inl (Finset.mem_filter.mpr (And.intro hp hl))
    . exact Or.inr (Finset.mem_filter.mpr (And.intro hp hu))
  have hmap : Set.MapsTo f (L : Set (Prod Nat Nat)) (T : Set (Prod Nat Nat)) := by
    intro pair hp
    have hl := Finset.mem_filter.mp hp
    have hd := Finset.mem_filter.mp hl.1
    have hY : pair.2 <= Y := by
      have hy := Finset.mem_range.mp (Finset.mem_product.mp hd.1).2
      omega
    have hkY : pair.2 - pair.1 <= Y := by omega
    have hval : V pair <= A ^ 2 * Y := by
      change A * (pair.2 - pair.1) * pair.1 <= A ^ 2 * Y
      calc
        A * (pair.2 - pair.1) * pair.1 = (A * pair.1) * (pair.2 - pair.1) := by ring
        _ <= (A * A) * Y :=
          Nat.mul_le_mul (Nat.mul_le_mul_left A hl.2.1) hkY
        _ = A ^ 2 * Y := by ring
    have hs : Nat.sqrt (V pair) <= R := Nat.sqrt_le_sqrt hval
    apply Finset.mem_product.mpr
    constructor
    . apply Finset.mem_range.mpr
      change pair.1 < A + 1
      omega
    . apply Finset.mem_range.mpr
      change Nat.sqrt (V pair) < R + 1
      omega
  have hinj : Set.InjOn f (L : Set (Prod Nat Nat)) := by
    intro u hu v hv heq
    have hm : u.1 = v.1 :=
      @congrArg (Prod Nat Nat) Nat (f u) (f v) Prod.fst heq
    have hs : Nat.sqrt (V u) = Nat.sqrt (V v) :=
      @congrArg (Prod Nat Nat) Nat (f u) (f v) Prod.snd heq
    have hlu := Finset.mem_filter.mp hu
    have hlv := Finset.mem_filter.mp hv
    have hdu := Finset.mem_filter.mp hlu.1
    have hdv := Finset.mem_filter.mp hlv.1
    have hval : V u = V v := by
      rw [<- hroot (V u) hlu.2.2, <- hroot (V v) hlv.2.2, hs]
    change A * (u.2 - u.1) * u.1 = A * (v.2 - v.1) * v.1 at hval
    rw [hm] at hval
    have hmul : (A * v.1) * (u.2 - v.1) = (A * v.1) * (v.2 - v.1) := by
      calc
        (A * v.1) * (u.2 - v.1) = A * (u.2 - v.1) * v.1 := by ring
        _ = A * (v.2 - v.1) * v.1 := hval
        _ = (A * v.1) * (v.2 - v.1) := by ring
    have hk := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hA hdv.2.1.pos) hmul
    apply Prod.ext hm
    have hluq := hdu.2.2.2.1
    have hlvq := hdv.2.2.2.1
    omega
  have hleft : L.card <= (A + 1) * (R + 1) := by
    calc
      L.card <= T.card := Finset.card_le_card_of_injOn f hmap hinj
      _ = (A + 1) * (R + 1) := by
        exact (Finset.card_product (Finset.range (A + 1)) (Finset.range (R + 1))).trans
          (by simp only [Finset.card_range])
  have hright : U.card <= (B + 1) ^ 2 := by
    calc
      U.card <= (Finset.product (Finset.range (B + 1)) (Finset.range (B + 1))).card := by
        apply Finset.card_le_card
        intro pair hp
        have hu := Finset.mem_filter.mp hp
        have hd := Finset.mem_filter.mp hu.1
        have hlt := hd.2.2.2.1
        apply Finset.mem_product.mpr
        exact And.intro (Finset.mem_range.mpr (by omega))
          (Finset.mem_range.mpr (by omega))
      _ = (B + 1) ^ 2 := by
        exact (Finset.card_product (Finset.range (B + 1)) (Finset.range (B + 1))).trans
          (by simp only [Finset.card_range, pow_two])
  change S.card <= (A + 1) * (R + 1) + (B + 1) ^ 2
  exact (hcover.trans (Finset.card_union_le L U)).trans (Nat.add_le_add hleft hright)

end PrimeFactorOscillations.FiniteFieldIntegerSignature
