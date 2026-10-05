/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

/-!
# A residue lower bound for a repeated prime factor

If a prime square is one modulo a modulus, divisibility by that prime
forces the remaining cofactor into the product's residue class. A size
bound below the least nonnegative residue then excludes the repeated
factor. The final specialization retains the exact dyadic endpoints.
-/

set_option autoImplicit false

namespace Nat

/-- A product residue bounds the quotient that would remain after a repeated factor. -/
theorem not_dvd_of_mul_mod_of_square_mod_one
    {p m modulus residue : Nat}
    (hsquare : (p * p) % modulus = 1)
    (hproduct : (p * m) % modulus = residue)
    (hsmall : m < residue * p) : Not (Dvd.dvd p m) := by
  intro hdiv
  cases hdiv with
  | intro a ha =>
    have hresidue : a % modulus = residue := by
      rw [ha, <- Nat.mul_assoc, Nat.mul_mod, hsquare, Nat.one_mul,
        Nat.mod_mod] at hproduct
      exact hproduct
    have haLarge : residue <= a := by
      rw [<- hresidue]
      exact Nat.mod_le _ _
    have hmLarge : residue * p <= m := by
      rw [ha, Nat.mul_comm residue p]
      exact Nat.mul_le_mul_left p haLarge
    exact Nat.not_lt_of_ge hmLarge hsmall

/-- The square of a prime above three is one modulo twenty-four. -/
theorem Prime.square_mod_twentyFour {p : Nat} (hp : p.Prime) (hgt : 3 < p) :
    (p * p) % 24 = 1 := by
  have hcoprime : p.Coprime 24 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hdiv
    have hle : p <= 24 := Nat.le_of_dvd (by decide) hdiv
    have hfinite : forall q : Fin 25,
        q.val.Prime -> 3 < q.val -> Not (Dvd.dvd q.val 24) := by decide
    exact hfinite (Fin.mk p (Nat.lt_succ_of_le hle)) hp hgt hdiv
  have hmod : (p % 24).Coprime 24 := by
    change Nat.gcd (p % 24) 24 = 1
    rw [<- Nat.gcd_rec]
    exact hcoprime.symm
  have hlt : p % 24 < 24 := Nat.mod_lt p (by decide)
  have hfinite : forall q : Fin 24,
      q.val.Coprime 24 -> (q.val * q.val) % 24 = 1 := by decide
  rw [Nat.mul_mod]
  exact hfinite (Fin.mk (p % 24) hlt) hmod

/-- Residue seventeen forces a repeated prime's quotient to be at least seventeen. -/
theorem Prime.coprime_of_mul_mod_twentyFour_eq_seventeen
    {p m : Nat} (hp : p.Prime) (hgt : 3 < p)
    (hproduct : (p * m) % 24 = 17) (hsmall : m < 17 * p) :
    p.Coprime m :=
  hp.coprime_iff_not_dvd.mpr
    (not_dvd_of_mul_mod_of_square_mod_one (hp.square_mod_twentyFour hgt)
      hproduct hsmall)

/-- The product residue excludes a shared prime in the stated balanced norm block. -/
theorem Prime.coprime_of_product_residue_of_balanced_block
    {p m U V : Nat} (hp : p.Prime) (hgt : 3 < p)
    (hproduct : (p * m) % 840 = 377)
    (hpLower : U < p) (hmUpper : m <= 2 * V) (hbalanced : 2 * V <= 17 * U) :
    p.Coprime m := by
  have hmod : (p * m) % 24 = 17 := by
    have h := congrArg (fun n : Nat => n % 24) hproduct
    norm_num [Nat.mod_mod_of_dvd _ (by decide : Dvd.dvd 24 840)] at h
    exact h
  apply hp.coprime_of_mul_mod_twentyFour_eq_seventeen hgt hmod
  exact hmUpper.trans_lt (hbalanced.trans_lt (Nat.mul_lt_mul_of_pos_left hpLower (by decide)))

/-- A common divisor of coprime affine shifts divides the cofactor difference. -/
theorem dvd_sub_of_dvd_mul_add_of_coprime
    {d b c k1 k2 : Nat} (hbc : b.Coprime c)
    (h1 : Dvd.dvd d (b * k1 + c)) (h2 : Dvd.dvd d (b * k2 + c)) :
    Dvd.dvd d (k2 - k1) := by
  have hdb : d.Coprime b :=
    Nat.Coprime.of_dvd_left h1
      ((Nat.coprime_mul_left_add_right b c k1).mpr hbc).symm
  have hdiff : Dvd.dvd d ((b * k2 + c) - (b * k1 + c)) :=
    Nat.dvd_sub h2 h1
  rw [Nat.add_sub_add_right, <- Nat.mul_sub_left_distrib] at hdiff
  exact hdb.dvd_of_dvd_mul_left hdiff

/-- The gcd of two coprime affine shifts divides their cofactor difference. -/
theorem gcd_mul_add_dvd_sub_of_coprime
    {b c k1 k2 : Nat} (hbc : b.Coprime c) :
    Dvd.dvd (Nat.gcd (b * k1 + c) (b * k2 + c)) (k2 - k1) :=
  dvd_sub_of_dvd_mul_add_of_coprime hbc
    (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)


end Nat
