/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeConstantBounds

/-! # Uniform positive cubic coprime character packets

The full cubic rational character quotient is retained at every divisor.
Its exact local factors keep the prime two and all phase-dependent signs.
The existing reciprocal-square budget supplies a positive uniform lower
bound on the complete finite product, without a growing-modulus loss.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianCoprimeCubicWeight (h : Nat) : ArithmeticFunction Complex :=
  (LPF.lpfRationalFunction.ppow 3).pmul (LPF.lpfRamanujanFunction h)

def hamiltonianCoprimeCubicSum (h : Nat) : ArithmeticFunction Complex :=
  hamiltonianCoprimeCubicWeight h * (ArithmeticFunction.zeta : ArithmeticFunction Complex)

def hamiltonianCoprimeCubicLocal (p h : Nat) : Real :=
  if Dvd.dvd p h then 1 - 1 / ((p : Real) - 1) ^ 2
  else 1 + 1 / ((p : Real) - 1) ^ 3

def hamiltonianCoprimeOddPrimeFactors (n : Nat) : Finset Nat :=
  n.primeFactors.filter (fun p => Not (p = 2))

theorem hamiltonian_coprime_cubic_weight_multiplicative (h : Nat) :
    (hamiltonianCoprimeCubicWeight h).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.pmul
    LPF.lpfRationalFunction_multiplicative.ppow (LPF.lpfRamanujanFunction_multiplicative h)

theorem hamiltonian_coprime_cubic_sum_multiplicative (h : Nat) :
    (hamiltonianCoprimeCubicSum h).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.mul (hamiltonian_coprime_cubic_weight_multiplicative h)
    ArithmeticFunction.isMultiplicative_zeta.natCast

theorem hamiltonian_coprime_cubic_weight_apply (h q : Nat) :
    hamiltonianCoprimeCubicWeight h q =
      ((ArithmeticFunction.moebius q : Complex) / (q.totient : Complex)) ^ 3 *
        LPF.lpfRamanujanFunction h q := by
  rw [hamiltonianCoprimeCubicWeight, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.ppow_apply (by decide : 0 < 3), LPF.lpfRationalFunction_apply]
  rfl

theorem hamiltonian_coprime_cubic_sum_apply (h n : Nat) :
    hamiltonianCoprimeCubicSum h n =
      n.divisors.sum (fun q => hamiltonianCoprimeCubicWeight h q) :=
  ArithmeticFunction.coe_mul_zeta_apply

theorem hamiltonian_coprime_cubic_prime_power (h p a : Nat)
    (hp : Nat.Prime p) (ha : 0 < a) :
    hamiltonianCoprimeCubicSum h (p ^ a) =
      (hamiltonianCoprimeCubicLocal p h : Complex) := by
  rw [hamiltonian_coprime_cubic_sum_apply, Nat.sum_divisors_prime_pow hp]
  have hSubset : ({0, 1} : Finset Nat) <= Finset.range (a + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    apply Finset.mem_range.mpr
    omega
  have hTail (k : Nat) (hk : Membership.mem (Finset.range (a + 1)) k)
      (hNot : Not (Membership.mem ({0, 1} : Finset Nat) k)) :
      hamiltonianCoprimeCubicWeight h (p ^ k) = 0 := by
    have hk2 : 2 <= k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hNot
      omega
    rw [hamiltonian_coprime_cubic_weight_apply h (p ^ k),
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega),
      ite_eq_right (by omega : Not (k = 1))]
    simp
  have hPrime0 : Not ((p : Complex) - 1 = 0) := by
    apply sub_ne_zero.mpr
    exact_mod_cast hp.ne_one
  have hPrimeReal0 : Not ((p : Real) - 1 = 0) := by
    apply sub_ne_zero.mpr
    exact_mod_cast hp.ne_one
  calc
    _ = ({0, 1} : Finset Nat).sum (fun k => hamiltonianCoprimeCubicWeight h (p ^ k)) :=
      (Finset.sum_subset hSubset hTail).symm
    _ = hamiltonianCoprimeCubicWeight h 1 + hamiltonianCoprimeCubicWeight h p := by simp
    _ = _ := by
      rw [hamiltonian_coprime_cubic_weight_apply h 1,
        hamiltonian_coprime_cubic_weight_apply h p]
      haveI : NeZero p := NeZero.mk hp.ne_zero
      have hOne : LPF.lpfRamanujanSum (q := 1) h = 1 := by
        rw [LPF.lpfRamanujanSum_divisors]
        simp
      simp only [LPF.lpfRamanujanFunction_eq_sum]
      rw [hOne, LPF.lpfRamanujanSum_prime hp]
      simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.totient_one,
        Nat.cast_one, one_div, ArithmeticFunction.moebius_apply_prime hp,
        Int.cast_neg, Nat.totient_prime hp]
      rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
      unfold hamiltonianCoprimeCubicLocal
      by_cases hDiv : Dvd.dvd p h
      case pos =>
        simp only [hDiv, ite_true, Complex.ofReal_sub, Complex.ofReal_one,
          Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
        field_simp [hPrime0, hPrimeReal0]
        ring
      case neg =>
        simp only [hDiv, ite_false, Complex.ofReal_add, Complex.ofReal_one,
          Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_natCast]
        field_simp [hPrime0, hPrimeReal0]

theorem hamiltonian_coprime_cubic_finite_product (h n : Nat) (hn : 0 < n) :
    hamiltonianCoprimeCubicSum h n =
      Complex.ofReal (n.primeFactors.prod (fun p => hamiltonianCoprimeCubicLocal p h)) := by
  have hFactor := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    (hamiltonianCoprimeCubicSum h) (hamiltonian_coprime_cubic_sum_multiplicative h)
    (ne_of_gt hn)
  change hamiltonianCoprimeCubicSum h n =
    n.factorization.support.prod
      (fun p => hamiltonianCoprimeCubicSum h (p ^ n.factorization p)) at hFactor
  rw [Nat.support_factorization] at hFactor
  rw [hFactor, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have hPrime := Nat.prime_of_mem_primeFactors hp
  have hSupport : Membership.mem n.factorization.support p := by
    simpa only [Nat.support_factorization] using hp
  have hExp : 0 < n.factorization p := by
    have hNonzero := Finsupp.mem_support_iff.mp hSupport
    omega
  exact hamiltonian_coprime_cubic_prime_power h p _ hPrime hExp

theorem hamiltonian_coprime_odd_prime_filter_data (n p : Nat) [NeZero n]
    (hp : Membership.mem (hamiltonianCoprimeOddPrimeFactors n) p) :
    Odd p /\ 3 <= p /\ p <= n := by
  have hFilter := Finset.mem_filter.mp hp
  have hData := Nat.mem_primeFactors.mp hFilter.1
  exact And.intro (hData.1.odd_of_ne_two hFilter.2)
    (And.intro (by have h := hData.1.two_le; omega)
      (Nat.le_of_dvd (NeZero.pos n) hData.2.1))

theorem hamiltonian_coprime_odd_prime_filter_square_budget (n : Nat) [NeZero n] :
    (hamiltonianCoprimeOddPrimeFactors n).sum
      (fun p => 1 / ((p : Real) - 1) ^ 2) <= 1 / 2 := by
  let S := hamiltonianCoprimeOddPrimeFactors n
  let g := fun p : Nat => (p - 3) / 2
  have hRel (p : Nat) (hp : Membership.mem S p) : p = 2 * g p + 3 := by
    have hData := hamiltonian_coprime_odd_prime_filter_data n p hp
    choose k hk using hData.1
    dsimp only [g]
    omega
  have hInj : Set.InjOn g (S : Set Nat) := by
    intro p hp q hq hEq
    have hP := hRel p hp
    have hQ := hRel q hq
    omega
  have hSubset : S.image g <= Finset.range n := by
    intro k hk
    choose p hp hEq using Finset.mem_image.mp hk
    have hData := hamiltonian_coprime_odd_prime_filter_data n p hp
    have hP := hRel p hp
    apply Finset.mem_range.mpr
    omega
  have hMapped :
      S.sum (fun p => 1 / ((g p + 1 : Nat) : Real) ^ 2) =
        (S.image g).sum (fun k => 1 / ((k + 1 : Nat) : Real) ^ 2) :=
    (Finset.sum_image (f := fun k : Nat => 1 / ((k + 1 : Nat) : Real) ^ 2) hInj).symm
  have hSubsetSum := Finset.sum_le_sum_of_subset_of_nonneg hSubset
    (fun k hk hNot => show (0 : Real) <= 1 / ((k + 1 : Nat) : Real) ^ 2 by positivity)
  have hSumBound : S.sum (fun p => 1 / ((g p + 1 : Nat) : Real) ^ 2) <= 2 := by
    rw [hMapped]
    exact hSubsetSum.trans (hamiltonian_reciprocal_square_finite_bound n)
  calc
    _ <= S.sum (fun p => (1 / 4 : Real) / ((g p + 1 : Nat) : Real) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      have hData := hamiltonian_coprime_odd_prime_filter_data n p hp
      simpa only [Nat.mul_one, pow_one] using
        hamiltonian_odd_reciprocal_power_budget p 1 hData.1 hData.2.1 (by norm_num)
    _ = (1 / 4 : Real) * S.sum (fun p => 1 / ((g p + 1 : Nat) : Real) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ <= (1 / 4 : Real) * 2 :=
      mul_le_mul_of_nonneg_left hSumBound (by norm_num)
    _ = _ := by norm_num

theorem hamiltonian_coprime_cubic_local_lower (n h p : Nat) [NeZero n]
    (hParity : Odd n \/ Odd h) (hp : Membership.mem n.primeFactors p) :
    0 <= (if p = 2 then (0 : Real) else 1 / ((p : Real) - 1) ^ 2) /\
    (if p = 2 then (0 : Real) else 1 / ((p : Real) - 1) ^ 2) <= 1 /\
    1 - (if p = 2 then (0 : Real) else 1 / ((p : Real) - 1) ^ 2) <=
      hamiltonianCoprimeCubicLocal p h := by
  have hPrime := Nat.prime_of_mem_primeFactors hp
  by_cases hTwo : p = 2
  case pos =>
    subst p
    have hOddH : Odd h := by
      rcases hParity with hOddN | hOddH
      case inl =>
        have hDiv := (Nat.mem_primeFactors.mp hp).2.1
        choose k hk using hDiv
        have hEven : Even n := Exists.intro k (by omega)
        exact False.elim ((Nat.not_even_iff_odd.mpr hOddN) hEven)
      case inr => exact hOddH
    have hNotDiv : Not (Dvd.dvd 2 h) := by
      intro hDiv
      choose k hk using hDiv
      have hEven : Even h := Exists.intro k (by omega)
      exact (Nat.not_even_iff_odd.mpr hOddH) hEven
    norm_num [hamiltonianCoprimeCubicLocal, hNotDiv]
  case neg =>
    have hP3 : (3 : Real) <= (p : Real) := by
      have h : 3 <= p := by have h := hPrime.two_le; omega
      exact_mod_cast h
    have hOne : 1 <= (p : Real) - 1 := by linarith only [hP3]
    have hPower := hamiltonian_one_le_power ((p : Real) - 1) hOne 2
    have hInv := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hPower
    have h0 : 0 <= 1 / ((p : Real) - 1) ^ 2 := by positivity
    refine And.intro (by simpa only [hTwo, ite_false] using h0)
      (And.intro (by simpa only [hTwo, ite_false, one_div_one] using hInv) ?_)
    simp only [hTwo, ite_false, hamiltonianCoprimeCubicLocal]
    split_ifs
    next => exact le_refl _
    next =>
      have hCube0 : 0 <= 1 / ((p : Real) - 1) ^ 3 := by positivity
      linarith only [h0, hCube0]

theorem hamiltonian_coprime_cubic_packet_lower (n h : Nat) [NeZero n]
    (hParity : Odd n \/ Odd h) :
    1 / 2 <= (hamiltonianCoprimeCubicSum h n).re := by
  let u := fun p : Nat => if p = 2 then (0 : Real) else 1 / ((p : Real) - 1) ^ 2
  have hU : forall p, Membership.mem n.primeFactors p -> 0 <= u p /\ u p <= 1 := by
    intro p hp
    have hData := hamiltonian_coprime_cubic_local_lower n h p hParity hp
    exact And.intro hData.1 hData.2.1
  have hSum : n.primeFactors.sum u <= 1 / 2 := by
    have hFilter : n.primeFactors.sum u =
        (hamiltonianCoprimeOddPrimeFactors n).sum
          (fun p => 1 / ((p : Real) - 1) ^ 2) := by
      rw [hamiltonianCoprimeOddPrimeFactors, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hTwo : p = 2 <;> simp [u, hTwo]
    rw [hFilter]
    exact hamiltonian_coprime_odd_prime_filter_square_budget n
  have hBase := (Finset.prod_one_sub_linear_error_bounds n.primeFactors u hU).1
  have hProd (S : Finset Nat) :
      S <= n.primeFactors ->
      S.prod (fun p => 1 - u p) <= S.prod (fun p => hamiltonianCoprimeCubicLocal p h) := by
    induction S using Finset.induction_on with
    | empty => intro hS; simp only [Finset.prod_empty, le_refl]
    | @insert p S hp ih =>
      intro hS
      have hP := hS (Finset.mem_insert_self p S)
      have hSubset : S <= n.primeFactors := fun q hq => hS (Finset.mem_insert_of_mem hq)
      have hData := hamiltonian_coprime_cubic_local_lower n h p hParity hP
      have hFactor0 : 0 <= 1 - u p := sub_nonneg.mpr (hU p hP).2
      have hLocal0 : 0 <= hamiltonianCoprimeCubicLocal p h :=
        hFactor0.trans hData.2.2
      rw [Finset.prod_insert hp, Finset.prod_insert hp]
      exact mul_le_mul hData.2.2 (ih hSubset)
        (Finset.prod_nonneg (fun q hq => sub_nonneg.mpr (hU q (hSubset hq)).2)) hLocal0
  have hCompare := hProd n.primeFactors (le_refl _)
  have hProduct : (hamiltonianCoprimeCubicSum h n).re =
      n.primeFactors.prod (fun p => hamiltonianCoprimeCubicLocal p h) := by
    have h := congrArg Complex.re (hamiltonian_coprime_cubic_finite_product h n (NeZero.pos n))
    simpa only [Complex.ofReal_re] using h
  rw [hProduct]
  linarith only [hBase, hSum, hCompare]

end PrimeFactorOscillations
