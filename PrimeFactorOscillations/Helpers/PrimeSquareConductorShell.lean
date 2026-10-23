/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimePowerReturnAllPrimes

/-!
# The full prime-square return shell

The actual kernel of the p-th power map modulo p squared is enumerated by
all last-layer returns, retaining the complete signed unit reference.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimePowerReturnSpectrum

open scoped BigOperators

theorem prime_square_kernel_card (p : Nat) [NeZero p] (hp : Nat.Prime p) :
    Fintype.card (powerKernel (p ^ 2) p) = p := by
  letI : IsCyclic (Units (ZMod (p ^ 2))) := by
    by_cases hp2 : p = 2
    { subst p
      exact ZMod.isCyclic_units_four }
    { exact ZMod.isCyclic_units_of_prime_pow p hp hp2 2 }
  rw [power_kernel_card, Nat.totient_prime_pow_succ hp 1, pow_one]
  exact Nat.gcd_eq_right (dvd_mul_right p (p - 1))

def primeSquareReturnEquiv (p : Nat) [NeZero p] (hp : Nat.Prime p) :
    Equiv (Fin p) (powerKernel (p ^ 2) p) := by
  let f : Fin p -> powerKernel (p ^ 2) p := lastLayerReturn p 0 p (dvd_refl p)
  have hinj : Function.Injective f := by
    intro i j hij
    have hval := congrArg (fun u : powerKernel (p ^ 2) p =>
      (u.val : ZMod (p ^ 2))) hij
    change ((lastLayerReturn p 0 p (dvd_refl p) i).val : ZMod (p ^ 2)) =
      ((lastLayerReturn p 0 p (dvd_refl p) j).val : ZMod (p ^ 2)) at hval
    rw [last_layer_return_value, last_layer_return_value] at hval
    have hprod : ((p * i.val : Nat) : ZMod (p ^ 2)) =
        ((p * j.val : Nat) : ZMod (p ^ 2)) := by
      have hcancel := add_left_cancel hval
      simpa only [lastLayer, Nat.zero_add, pow_one, Nat.cast_mul] using hcancel
    have hi : p * i.val < p ^ 2 := by
      simpa only [pow_two] using (Nat.mul_lt_mul_of_pos_left i.isLt hp.pos)
    have hj : p * j.val < p ^ 2 := by
      simpa only [pow_two] using (Nat.mul_lt_mul_of_pos_left j.isLt hp.pos)
    have heq := congrArg (fun x : ZMod (p ^ 2) => x.val) hprod
    rw [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at heq
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hp.pos heq)
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  refine And.intro hinj ?_
  rw [Fintype.card_fin, prime_square_kernel_card p hp]

theorem prime_square_return_equiv_value (p : Nat) [NeZero p] (hp : Nat.Prime p)
    (j : Fin p) :
    ((primeSquareReturnEquiv p hp j).val : ZMod (p ^ 2)) =
      1 + (p : ZMod (p ^ 2)) * (j.val : ZMod (p ^ 2)) := by
  change ((lastLayerReturn p 0 p (dvd_refl p) j).val : ZMod (p ^ 2)) = _
  rw [last_layer_return_value]
  simp only [lastLayer, Nat.zero_add, pow_one]

theorem prime_square_return_geometric (p h : Nat) [NeZero p] (hp : Nat.Prime p) :
    returnTransform (p ^ 2) p h =
      ZMod.stdAddChar (h : ZMod (p ^ 2)) *
        Finset.univ.sum (fun j : Fin p =>
          ZMod.stdAddChar ((h : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) ^ j.val) := by
  classical
  calc
    _ = Finset.univ.sum (fun j : Fin p => ZMod.stdAddChar
        ((h : ZMod (p ^ 2)) *
          (1 + (p : ZMod (p ^ 2)) * (j.val : ZMod (p ^ 2))))) := by
      have he := _root_.Equiv.sum_comp (primeSquareReturnEquiv p hp)
        (fun u : powerKernel (p ^ 2) p =>
          ZMod.stdAddChar ((h : ZMod (p ^ 2)) * (u.val : ZMod (p ^ 2))))
      simpa only [returnTransform, prime_square_return_equiv_value] using he.symm
    _ = Finset.univ.sum (fun j : Fin p =>
        ZMod.stdAddChar (h : ZMod (p ^ 2)) *
          ZMod.stdAddChar ((h : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) ^ j.val) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show (h : ZMod (p ^ 2)) *
          (1 + (p : ZMod (p ^ 2)) * (j.val : ZMod (p ^ 2))) =
        (h : ZMod (p ^ 2)) + (j.val : ZMod (p ^ 2)) *
          ((h : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) by ring,
        AddChar.map_add_eq_mul]
      have he := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := p ^ 2)) j.val
        ((h : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)))
      exact congrArg (fun w : Complex => ZMod.stdAddChar (h : ZMod (p ^ 2)) * w)
        (by simpa only [nsmul_eq_mul] using he)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem prime_square_phase_one_iff (p h : Nat) [NeZero p] :
    ZMod.stdAddChar (h : ZMod (p ^ 2)) = 1 <-> Dvd.dvd (p ^ 2) h := by
  constructor
  { intro hz
    have hzero : (h : ZMod (p ^ 2)) = 0 := by
      apply ZMod.injective_stdAddChar
      simpa only [AddChar.map_zero_eq_one] using hz
    exact (CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2) h).mp hzero }
  { intro hd
    rw [(CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2) h).mpr hd,
      AddChar.map_zero_eq_one] }

theorem prime_square_phase_pow (p h : Nat) [NeZero p] (hd : Dvd.dvd p h) :
    ZMod.stdAddChar (h : ZMod (p ^ 2)) ^ p = 1 := by
  rw [<- AddChar.map_nsmul_eq_pow]
  have hzero : HSMul.hSMul p (h : ZMod (p ^ 2)) = 0 := by
    rw [nsmul_eq_mul, <- Nat.cast_mul]
    apply (CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2) (p * h)).mpr
    rw [pow_two]
    exact Nat.mul_dvd_mul_left p hd
  rw [hzero, AddChar.map_zero_eq_one]

theorem prime_square_return_ratio_one_iff (p h : Nat) [NeZero p] (hp : Nat.Prime p) :
    ZMod.stdAddChar ((h : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) = 1 <->
      Dvd.dvd p h := by
  rw [<- Nat.cast_mul, prime_square_phase_one_iff, pow_two, mul_comm h p,
    Nat.mul_dvd_mul_iff_left hp.pos]

theorem prime_square_return_formula (p h : Nat) [NeZero p] (hp : Nat.Prime p) :
    returnTransform (p ^ 2) p h =
      if Dvd.dvd p h then (p : Complex) * ZMod.stdAddChar (h : ZMod (p ^ 2))
      else 0 := by
  rw [prime_square_return_geometric p h hp]
  by_cases hd : Dvd.dvd p h
  { rw [if_pos hd, (prime_square_return_ratio_one_iff p h hp).mpr hd]
    simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, mul_comm] }
  { rw [if_neg hd]
    let z : Complex := ZMod.stdAddChar ((h : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)))
    have hnz : Not (z = 1) := fun hz =>
      hd ((prime_square_return_ratio_one_iff p h hp).mp hz)
    have hpow : z ^ p = 1 := by
      have he := prime_square_phase_pow p (h * p) (dvd_mul_left p h)
      simpa only [Nat.cast_mul] using he
    have hg := geom_sum_mul z p
    rw [hpow, sub_self] at hg
    have hs : Finset.univ.sum (fun j : Fin p => z ^ j.val) = 0 := by
      rw [Fin.sum_univ_eq_sum_range]
      exact (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hnz)
    change ZMod.stdAddChar (h : ZMod (p ^ 2)) *
      Finset.univ.sum (fun j : Fin p => z ^ j.val) = 0
    rw [hs, mul_zero] }

theorem prime_square_unit_reference (p h : Nat) [NeZero p] (hp : Nat.Prime p) :
    LPF.lpfRamanujanSum (q := p ^ 2) h =
      (if Dvd.dvd (p ^ 2) h then ((p ^ 2 : Nat) : Complex) else 0) -
      (if Dvd.dvd p h then (p : Complex) else 0) := by
  have hqp : p ^ 2 / p = p := by
    rw [pow_two, Nat.mul_div_cancel p hp.pos]
  have hd : Dvd.dvd (p ^ 2) (p * h) <-> Dvd.dvd p h := by
    rw [pow_two, Nat.mul_dvd_mul_iff_left hp.pos]
  have hm : ArithmeticFunction.moebius (p ^ 2) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by decide)]
    rfl
  rw [LPF.lpfRamanujanSum_divisor_mask, Nat.divisors_prime_pow hp 2, Finset.sum_map]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Function.Embedding.coeFn_mk, pow_zero, pow_one,
    ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime hp,
    hm, Int.cast_one, Int.cast_neg, Int.cast_zero, zero_mul, one_mul,
    Nat.div_one, hqp, hd, zero_add, add_zero, neg_one_mul, sub_eq_add_neg]

theorem prime_square_unit_card (p : Nat) [NeZero p] (hp : Nat.Prime p) :
    Fintype.card (Units (ZMod (p ^ 2))) = p * (p - 1) := by
  rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp 1, pow_one]

theorem prime_square_centered_formula (p h : Nat) [NeZero p] (hp : Nat.Prime p) :
    centeredTransform (p ^ 2) p h =
      if Dvd.dvd (p ^ 2) h then 0
      else if Dvd.dvd p h then
        (p : Complex) ^ 2 *
          (((p - 1 : Nat) : Complex) * ZMod.stdAddChar (h : ZMod (p ^ 2)) + 1)
      else 0 := by
  unfold centeredTransform
  rw [prime_square_unit_card p hp, prime_square_kernel_card p hp,
    prime_square_return_formula p h hp, prime_square_unit_reference p h hp]
  by_cases h2 : Dvd.dvd (p ^ 2) h
  { have hd : Dvd.dvd p h :=
      dvd_trans (dvd_pow_self p (by decide : Not (2 = 0))) h2
    have hx : (h : ZMod (p ^ 2)) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2) h).mpr h2
    simp only [if_pos h2, if_pos hd, hx, AddChar.map_zero_eq_one,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    ring }
  { by_cases hd : Dvd.dvd p h
    { simp only [if_neg h2, if_pos hd, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_sub hp.one_lt.le, Nat.cast_one]
      ring }
    { simp only [if_neg h2, if_neg hd, sub_self, mul_zero] } }

theorem prime_square_odd_phase_nonzero (p h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2)) :
    Not (((p - 1 : Nat) : Complex) * ZMod.stdAddChar (h : ZMod (p ^ 2)) + 1 = 0) := by
  intro hz
  have heq : ((p - 1 : Nat) : Complex) * ZMod.stdAddChar (h : ZMod (p ^ 2)) = -1 := by
    simpa only [add_sub_cancel_right, zero_sub] using
      congrArg (fun z : Complex => z - 1) hz
  have hn := congrArg norm heq
  have hr : ((p - 1 : Nat) : Real) = 1 := by
    simpa only [norm_mul, Complex.norm_natCast, AddChar.norm_apply, mul_one,
      norm_neg, norm_one] using hn
  have hnat : p - 1 = 1 := by exact_mod_cast hr
  apply hp2
  have hple := hp.two_le
  omega

theorem prime_square_centered_nonzero_iff (p h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2)) :
    Not (centeredTransform (p ^ 2) p h = 0) <->
      And (Dvd.dvd p h) (Not (Dvd.dvd (p ^ 2) h)) := by
  rw [prime_square_centered_formula p h hp]
  by_cases h2 : Dvd.dvd (p ^ 2) h
  { simp [h2] }
  { by_cases hd : Dvd.dvd p h
    { simp only [if_neg h2, if_pos hd]
      constructor
      { intro _
        exact And.intro hd h2 }
      { intro _
        apply mul_ne_zero
        { exact pow_ne_zero 2 (by exact_mod_cast hp.ne_zero) }
        { exact prime_square_odd_phase_nonzero p h hp hp2 } } }
    { simp [h2, hd] } }

theorem prime_square_two_zero (h : Nat) :
    centeredTransform (2 ^ 2) 2 h = 0 := by
  rw [prime_square_centered_formula 2 h Nat.prime_two]
  simp only [show (2 : Nat) ^ 2 = 4 by decide, show (2 : Nat) - 1 = 1 by decide,
    Nat.cast_one, one_mul]
  by_cases h4 : Dvd.dvd 4 h
  { rw [if_pos h4] }
  { by_cases h2 : Dvd.dvd 2 h
    { have hzpow : ZMod.stdAddChar (h : ZMod 4) ^ 2 = 1 :=
        prime_square_phase_pow 2 h h2
      have hnz : Not (ZMod.stdAddChar (h : ZMod 4) = 1) := fun hz =>
        h4 ((prime_square_phase_one_iff 2 h).mp hz)
      have hf : (ZMod.stdAddChar (h : ZMod 4) - 1) *
          (ZMod.stdAddChar (h : ZMod 4) + 1) = 0 := by
        calc
          _ = ZMod.stdAddChar (h : ZMod 4) ^ 2 - 1 := by ring
          _ = 0 := by rw [hzpow, sub_self]
      have hzsum : ZMod.stdAddChar (h : ZMod 4) + 1 = 0 :=
        (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hnz)
      rw [if_neg h4, if_pos h2, hzsum, mul_zero] }
    { rw [if_neg h4, if_neg h2] } }

theorem prime_square_centered_all_primes (p h : Nat) [NeZero p] (hp : Nat.Prime p) :
    Not (centeredTransform (p ^ 2) p h = 0) <->
      And (Not (p = 2)) (And (Dvd.dvd p h) (Not (Dvd.dvd (p ^ 2) h))) := by
  by_cases hp2 : p = 2
  { subst p
    rw [prime_square_two_zero]
    simp }
  { rw [prime_square_centered_nonzero_iff p h hp hp2]
    simp only [hp2, not_false_eq_true, true_and] }

end PrimeFactorOscillations.PrimePowerReturnSpectrum
