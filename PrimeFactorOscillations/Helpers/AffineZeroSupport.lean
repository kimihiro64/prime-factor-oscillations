import PrimeFactorOscillations.Definitions.AffineSumFamily

/-! # Finite support of zero outputs in a fixed affine family -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.AffineSumFamily
open scoped Classical

theorem zero_value_sum_bound (F : AffineSumFamily) (a b : Nat)
    (hz : F.value a b = 0) :
    a + b <= Finset.univ.sum (fun i : Fin F.arity => (F.shift i).natAbs) := by
  have hprod : Finset.univ.prod (fun i : Fin F.arity =>
      F.coeff i * ((a : Int) + b) + F.shift i) = 0 := by
    simpa only [value, eval, Int.cast_id] using hz
  choose i hi using Finset.prod_eq_zero_iff.mp hprod
  have hc : (1 : Int) <= F.coeff i := F.coeff_pos i
  have hab : (0 : Int) <= (a : Int) + b := add_nonneg (Int.natCast_nonneg a) (Int.natCast_nonneg b)
  have hmul : (a : Int) + b <= F.coeff i * ((a : Int) + b) :=
    le_mul_of_one_le_left hab hc
  have hd : -F.shift i <= ((F.shift i).natAbs : Int) := by
    have h : -F.shift i <= ((-F.shift i).natAbs : Int) := Int.le_natAbs
    simpa only [Int.natAbs_neg] using h
  have hlocal : a + b <= (F.shift i).natAbs := by
    have hR : (a : Int) + b <= ((F.shift i).natAbs : Int) := by linarith [hi.2]
    exact_mod_cast hR
  exact hlocal.trans (Finset.single_le_sum
    (fun j _ => Nat.zero_le (F.shift j).natAbs) (Finset.mem_univ i))

end PrimeFactorOscillations.AffineSumFamily
