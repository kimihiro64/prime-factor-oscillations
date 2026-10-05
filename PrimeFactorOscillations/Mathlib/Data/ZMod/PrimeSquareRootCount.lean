/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import PrimeFactorOscillations.Mathlib.Data.Int.PrimeSquareRoot

/-!
# Counting square roots modulo prime squares

Regular targets have at most two roots modulo an odd prime square. Zero has
at most p roots modulo p^2, and every target has at most p roots for odd p.
The Chinese remainder map bounds root counts over coprime products. These
finite counts retain singular roots, as needed by squarefree divisibility
estimates for quadratic forms.
-/

set_option autoImplicit false

namespace ZMod

/-- A regular square has at most its two signed roots modulo an odd prime square. -/
theorem card_regular_sq_roots_prime_sq_le_two
    (p : Nat) [Fact (Nat.Prime p)] (a : Int)
    (htwo : Not (p = 2)) (hunit : Not (Dvd.dvd (p : Int) a)) :
    (Finset.univ.filter fun x : ZMod (p ^ 2) =>
      x ^ 2 = (a : ZMod (p ^ 2)) ^ 2).card <= 2 := by
  classical
  have hsub :
      (Finset.univ.filter fun x : ZMod (p ^ 2) =>
        x ^ 2 = (a : ZMod (p ^ 2)) ^ 2) <=
      ({(a : ZMod (p ^ 2)), -(a : ZMod (p ^ 2))} : Finset (ZMod (p ^ 2))) := by
    intro x hx
    have hs := (Finset.mem_filter.mp hx).2
    have hz : (((x.val : Int) ^ 2 - a ^ 2 : Int) : ZMod (p ^ 2)) = 0 := by
      simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast, ZMod.natCast_val,
        ZMod.intCast_cast, ZMod.cast_id]
        using sub_eq_zero.mpr hs
    have hd : Dvd.dvd ((p : Int) ^ 2) ((x.val : Int) ^ 2 - a ^ 2) := by
      simpa only [Int.natCast_pow] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).mp hz
    have he := (Int.nat_prime_sq_dvd_sq_sub_sq_iff
      (Fact.out : Nat.Prime p) htwo hunit).mp hd
    cases he with
    | inl hm =>
        have hz' : (((x.val : Int) - a : Int) : ZMod (p ^ 2)) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).mpr
            (by simpa only [Int.natCast_pow] using hm)
        have hx' : x - (a : ZMod (p ^ 2)) = 0 := by
          simpa only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_val,
            ZMod.intCast_cast, ZMod.cast_id] using hz'
        exact Finset.mem_insert.mpr (Or.inl (sub_eq_zero.mp hx'))
    | inr hp =>
        have hz' : (((x.val : Int) + a : Int) : ZMod (p ^ 2)) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).mpr
            (by simpa only [Int.natCast_pow] using hp)
        have hx' : x + (a : ZMod (p ^ 2)) = 0 := by
          simpa only [Int.cast_add, Int.cast_natCast, ZMod.natCast_val,
            ZMod.intCast_cast, ZMod.cast_id] using hz'
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton.mpr (eq_neg_of_add_eq_zero_left hx')))
  calc
    _ <= ({(a : ZMod (p ^ 2)), -(a : ZMod (p ^ 2))} :
        Finset (ZMod (p ^ 2))).card := Finset.card_le_card hsub
    _ <= ({-(a : ZMod (p ^ 2))} : Finset (ZMod (p ^ 2))).card + 1 :=
      Finset.card_insert_le _ _
    _ = 2 := by simp

/-- Every root of zero modulo a prime square is a multiple of the prime. -/
theorem card_zero_sq_roots_prime_sq_le (p : Nat) [Fact (Nat.Prime p)] :
    (Finset.univ.filter fun x : ZMod (p ^ 2) => x ^ 2 = 0).card <= p := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hsub :
      (Finset.univ.filter fun x : ZMod (p ^ 2) => x ^ 2 = 0) <=
      (Finset.range p).image (fun j : Nat => ((p * j : Nat) : ZMod (p ^ 2))) := by
    intro x hx
    have hz : ((x.val ^ 2 : Nat) : ZMod (p ^ 2)) = 0 := by
      simpa only [Nat.cast_pow, ZMod.natCast_val, ZMod.cast_id]
        using (Finset.mem_filter.mp hx).2
    have hd2 : Dvd.dvd (p ^ 2) (x.val ^ 2) :=
      (ZMod.natCast_eq_zero_iff _ (p ^ 2)).mp hz
    have hpp : Dvd.dvd p (p ^ 2) := by
      exact Exists.intro p (by ring1)
    have hd : Dvd.dvd p x.val := hp.dvd_of_dvd_pow (dvd_trans hpp hd2)
    cases hd with
    | intro j hj =>
        have hjlt : j < p := by
          have hv := ZMod.val_lt x
          rw [hj, pow_two] at hv
          exact Nat.lt_of_mul_lt_mul_left hv
        refine Finset.mem_image.mpr (Exists.intro j (And.intro
          (Finset.mem_range.mpr hjlt) ?_))
        simp only [<- hj, ZMod.natCast_val, ZMod.cast_id]
  calc
    _ <= ((Finset.range p).image
        (fun j : Nat => ((p * j : Nat) : ZMod (p ^ 2)))).card :=
      Finset.card_le_card hsub
    _ <= (Finset.range p).card := Finset.card_image_le
    _ = p := Finset.card_range p

/-- A unit target has at most two square roots modulo an odd prime square. -/
theorem card_unit_sq_roots_prime_sq_le_two
    (p : Nat) [Fact (Nat.Prime p)] (n : Int)
    (htwo : Not (p = 2)) (hunit : Not (Dvd.dvd (p : Int) n)) :
    (Finset.univ.filter fun x : ZMod (p ^ 2) =>
      x ^ 2 = (n : ZMod (p ^ 2))).card <= 2 := by
  classical
  by_cases hempty : (Finset.univ.filter fun x : ZMod (p ^ 2) =>
      x ^ 2 = (n : ZMod (p ^ 2))) = Finset.empty
  case pos =>
    rw [hempty]
    exact Nat.zero_le 2
  case neg =>
    have hn := Finset.nonempty_iff_ne_empty.mpr hempty
    cases hn with
    | intro a ha =>
        have haeq := (Finset.mem_filter.mp ha).2
        have hz : (((a.val : Int) ^ 2 - n : Int) : ZMod (p ^ 2)) = 0 := by
          simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast,
            ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id]
            using sub_eq_zero.mpr haeq
        have hd2 : Dvd.dvd ((p : Int) ^ 2) ((a.val : Int) ^ 2 - n) := by
          simpa only [Int.natCast_pow] using
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).mp hz
        have haunit : Not (Dvd.dvd (p : Int) (a.val : Int)) := by
          intro hpa
          apply hunit
          have hpp : Dvd.dvd (p : Int) ((p : Int) ^ 2) :=
            Exists.intro (p : Int) (by ring1)
          have hsquare : Dvd.dvd (p : Int) ((a.val : Int) ^ 2) := by
            simpa only [pow_two] using dvd_mul_of_dvd_left hpa (a.val : Int)
          have hd := dvd_sub hsquare (dvd_trans hpp hd2)
          have hid : (a.val : Int) ^ 2 - ((a.val : Int) ^ 2 - n) = n := by ring1
          rwa [hid] at hd
        have hbound := card_regular_sq_roots_prime_sq_le_two p (a.val : Int)
          htwo haunit
        simpa only [Int.cast_natCast, ZMod.natCast_val, ZMod.intCast_cast,
          ZMod.cast_id, haeq] using hbound

/-- Every target has at most p square roots modulo the square of an odd prime p. -/
theorem card_sq_roots_prime_sq_le
    (p : Nat) [Fact (Nat.Prime p)] (n : Int) (htwo : Not (p = 2)) :
    (Finset.univ.filter fun x : ZMod (p ^ 2) =>
      x ^ 2 = (n : ZMod (p ^ 2))).card <= p := by
  classical
  have hp : Nat.Prime p := Fact.out
  by_cases hunit : Not (Dvd.dvd (p : Int) n)
  case pos =>
    exact (card_unit_sq_roots_prime_sq_le_two p n htwo hunit).trans hp.two_le
  case neg =>
    have hn : Dvd.dvd (p : Int) n := Classical.byContradiction hunit
    by_cases hz : (n : ZMod (p ^ 2)) = 0
    case pos =>
      simpa only [hz] using card_zero_sq_roots_prime_sq_le p
    case neg =>
      have hempty : (Finset.univ.filter fun x : ZMod (p ^ 2) =>
          x ^ 2 = (n : ZMod (p ^ 2))) = Finset.empty := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        have haeq := (Finset.mem_filter.mp ha).2
        have hcast : (((a.val : Int) ^ 2 - n : Int) : ZMod (p ^ 2)) = 0 := by
          simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast,
            ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id]
            using sub_eq_zero.mpr haeq
        have hd2 : Dvd.dvd ((p : Int) ^ 2) ((a.val : Int) ^ 2 - n) := by
          simpa only [Int.natCast_pow] using
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).mp hcast
        have hpp : Dvd.dvd (p : Int) ((p : Int) ^ 2) :=
          Exists.intro (p : Int) (by ring1)
        have hsq : Dvd.dvd (p : Int) ((a.val : Int) ^ 2) := by
          simpa only [sub_add_cancel] using dvd_add (dvd_trans hpp hd2) hn
        have ha : Dvd.dvd (p : Int) (a.val : Int) :=
          (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hsq
        have hs2 : Dvd.dvd ((p : Int) ^ 2) ((a.val : Int) ^ 2) := by
          cases ha with
          | intro k hk => exact Exists.intro (k ^ 2) (by rw [hk]; ring1)
        have hn2 := dvd_sub hs2 hd2
        have hid : (a.val : Int) ^ 2 - ((a.val : Int) ^ 2 - n) = n := by ring1
        rw [hid] at hn2
        apply hz
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd n (p ^ 2)).mpr
          (by simpa only [Int.natCast_pow] using hn2)
      rw [hempty]
      exact Nat.zero_le p

/-- The Chinese remainder map bounds root counts over coprime moduli. -/
theorem card_sq_roots_mul_le (m n : Nat) [NeZero m] [NeZero n]
    (a : Int) (hcop : Nat.Coprime m n) :
    (Finset.univ.filter fun x : ZMod (m * n) => x ^ 2 = (a : ZMod (m * n))).card <=
      (Finset.univ.filter fun x : ZMod m => x ^ 2 = (a : ZMod m)).card *
      (Finset.univ.filter fun x : ZMod n => x ^ 2 = (a : ZMod n)).card := by
  classical
  let e := ZMod.chineseRemainder hcop
  have hsub :
      (Finset.univ.filter fun x : ZMod (m * n) =>
        x ^ 2 = (a : ZMod (m * n))).image e <=
      (Finset.univ.filter fun x : ZMod m => x ^ 2 = (a : ZMod m)).product
      (Finset.univ.filter fun x : ZMod n => x ^ 2 = (a : ZMod n)) := by
    intro z hz
    cases Finset.mem_image.mp hz with
    | intro x hx =>
        cases hx with
        | intro hx hzx =>
            subst z
            have he := congrArg e (Finset.mem_filter.mp hx).2
            have he' : (e x) ^ 2 = (a : Prod (ZMod m) (ZMod n)) := by
              simpa only [map_pow, map_intCast] using he
            apply Finset.mem_product.mpr
            refine And.intro (Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) ?_))
              (Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) ?_))
            case refine_1 => exact congrArg Prod.fst he'
            case refine_2 => exact congrArg Prod.snd he'
  calc
    _ = ((Finset.univ.filter fun x : ZMod (m * n) =>
        x ^ 2 = (a : ZMod (m * n))).image e).card :=
      (Finset.card_image_of_injective _ e.injective).symm
    _ <= ((Finset.univ.filter fun x : ZMod m => x ^ 2 = (a : ZMod m)).product
      (Finset.univ.filter fun x : ZMod n => x ^ 2 = (a : ZMod n))).card :=
      Finset.card_le_card hsub
    _ = _ := Finset.card_product _ _

end ZMod
