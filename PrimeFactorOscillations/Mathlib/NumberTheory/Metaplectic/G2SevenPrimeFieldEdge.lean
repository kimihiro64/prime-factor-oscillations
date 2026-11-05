/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.Complex
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenFermatPrimeEdge

/-!
# The primary Fermat-septic edge without character witnesses

Every admissible order occurs among complex characters of a finite field.
The split case then uses the full primary packet; the remaining residue
classes use the already proved exact chart count. The prime two is explicit.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Metaplectic.CharacterRoots

theorem complex_character_of_order_exists
    (F : Type*) [Field F] [Fintype F] (n : Nat)
    (hdiv : Dvd.dvd n (Fintype.card F - 1)) :
    Exists fun chi : MulChar F Complex => orderOf chi = n := by
  classical
  have hsize : 0 < Fintype.card F - 1 :=
    Nat.sub_pos_of_lt Fintype.one_lt_card
  have hcard : Nat.card (Units F) = Fintype.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have hexp : Not (Monoid.exponent (Units F) = 0) := by
    rw [IsCyclic.exponent_eq_card, hcard]
    exact Nat.ne_of_gt hsize
  have : NeZero (Monoid.exponent (Units F)) := NeZero.mk hexp
  let : HasEnoughRootsOfUnity Complex (Monoid.exponent (Units F)) :=
    { prim := Exists.intro _ (Complex.isPrimitiveRoot_exp _ hexp)
      cyc := rootsOfUnity.isCyclic Complex _ }
  let e : MulEquiv (MulChar F Complex) (Units F) :=
    Classical.choice (MulChar.mulEquiv_units F Complex)
  have hgen : Exists fun g : Units F => orderOf g = Nat.card (Units F) :=
    IsCyclic.exists_ofOrder_eq_natCard
  cases hgen with
  | intro g hg =>
    cases hdiv with
    | intro k hk =>
      have hkne : Not (k = 0) := by
        intro hzero
        rw [hzero, mul_zero] at hk
        exact Nat.ne_of_gt hsize hk
      have hkd : Dvd.dvd k (orderOf g) := by
        rw [hg, hcard, hk]
        exact Exists.intro n (by ring)
      have hpower : orderOf (g ^ k) = n := by
        rw [orderOf_pow' g hkne, Nat.gcd_eq_right hkd, hg, hcard, hk]
        exact Nat.mul_div_cancel n (Nat.pos_of_ne_zero hkne)
      apply Exists.intro (e.symm (g ^ k))
      exact (e.symm.orderOf_eq (g ^ k)).trans hpower

end Metaplectic.CharacterRoots

namespace Metaplectic.G2Seven.Fermat

/-- The complete primary cubic edge for every prime p at least three. -/
theorem prime_field_primary_cubic_edge
    (p : Nat) [Fact p.Prime] (hp : 3 <= p)
    (rho : Real) (hrho : 0 < rho) (hrhosq : rho ^ 2 = (p : Real)) :
    74088 * rho <=
      (30 * rho - abs ((chartCount (ZMod p) : Real) - (p : Real) - 1)) ^ 3 := by
  classical
  have hpne : Not (p = 0) := (Fact.out : Nat.Prime p).ne_zero
  have : NeZero p := NeZero.mk hpne
  have hcard : Fintype.card (ZMod p) = p := by simp
  by_cases hmod : p % 7 = 1
  . have hd : Dvd.dvd 7 (Fintype.card (ZMod p) - 1) := by
      rw [hcard]
      refine Exists.intro (p / 7) ?_
      have ht := Nat.mod_add_div p 7
      rw [hmod] at ht
      omega
    cases Metaplectic.CharacterRoots.complex_character_of_order_exists
        (ZMod p) 7 hd with
    | intro chi hchi =>
      let z : Complex := Complex.exp (2 * (Real.pi : Complex) * Complex.I / 7)
      have hz : IsPrimitiveRoot z 7 := Complex.isPrimitiveRoot_exp 7 (by decide)
      let w : Complex := Complex.exp (2 * (Real.pi : Complex) * Complex.I / p)
      have hw : IsPrimitiveRoot w p := Complex.isPrimitiveRoot_exp p hpne
      let psi : AddChar (ZMod p) Complex := AddChar.zmodChar p hw.pow_eq_one
      have hpsi : psi.IsPrimitive :=
        AddChar.zmodChar_primitive_of_primitive_root p hw
      exact prime_chart_primary_cubic_edge p hcard hmod chi hchi psi hpsi z hz
        rho hrho hrhosq
  . have hN : chartCount (ZMod p) = p + 1 := by
      have ht := chart_count_of_card_mod_ne_one (F := ZMod p)
        (by simpa only [hcard] using hmod)
      simpa only [hcard] using ht
    have hpR : 3 <= (p : Real) := by exact_mod_cast hp
    have hconstant : 74088 <= 27000 * (p : Real) := by nlinarith [hpR]
    have hraw : 74088 * rho <= (30 * rho) ^ 3 := by
      calc
        74088 * rho <= (27000 * (p : Real)) * rho :=
          mul_le_mul_of_nonneg_right hconstant (le_of_lt hrho)
        _ = (30 * rho) ^ 3 := by rw [<- hrhosq]; ring
    simpa [hN] using hraw

/-- The stronger constant has a genuine exception at the prime two. -/
theorem prime_field_primary_cubic_edge_fails_two
    (rho : Real) (hrho : 0 < rho) (hrhosq : rho ^ 2 = 2) :
    Not (74088 * rho <=
      (30 * rho - abs ((chartCount (ZMod 2) : Real) - 2 - 1)) ^ 3) := by
  have hN : chartCount (ZMod 2) = 3 := by
    have ht := chart_count_of_card_mod_ne_one (F := ZMod 2) (by norm_num)
    simpa using ht
  have hscale : (30 * rho) ^ 3 = 54000 * rho := by
    calc
      (30 * rho) ^ 3 = 27000 * rho ^ 2 * rho := by ring
      _ = 54000 * rho := by rw [hrhosq]; ring
  have hraw : Not (74088 * rho <= (30 * rho) ^ 3) := by
    rw [hscale]
    nlinarith [hrho]
  have hzero : (chartCount (ZMod 2) : Real) - 2 - 1 = 0 := by
    rw [hN]
    norm_num
  simpa only [hzero, abs_zero, sub_zero] using hraw

end Metaplectic.G2Seven.Fermat
