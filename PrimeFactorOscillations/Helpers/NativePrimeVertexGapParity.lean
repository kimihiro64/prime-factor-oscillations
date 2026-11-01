/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NativePrimeVertexGapGeometry
import PrimeFactorOscillations.Mathlib.Data.Nat.SquareProductSupport

/-! # Exact parity readout for the independent vertex/gap coordinates

The square part is canceled with a positivity certificate. The remaining
finite odd support is tested by full squareclass independence.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_gap_power_parity_factorization
    (S : Finset (Sum Nat (Prod Nat Nat)))
    (n : Sum Nat (Prod Nat Nat) -> Nat) :
    S.prod (fun x => nativeVertexGapValue x ^ n x) =
      (S.prod (fun x => nativeVertexGapValue x ^ (n x / 2))) ^ 2 *
        (S.filter (fun x => n x % 2 = 1)).prod nativeVertexGapValue := by
  classical
  have hpow : forall x : Sum Nat (Prod Nat Nat),
      nativeVertexGapValue x ^ n x =
        (nativeVertexGapValue x ^ (n x / 2)) ^ 2 *
          (if n x % 2 = 1 then nativeVertexGapValue x else 1) := by
    intro x
    have he : n x = n x / 2 * 2 + n x % 2 := by omega
    calc
      _ = nativeVertexGapValue x ^ (n x / 2 * 2 + n x % 2) := congrArg _ he
      _ = (nativeVertexGapValue x ^ (n x / 2)) ^ 2 *
          (if n x % 2 = 1 then nativeVertexGapValue x else 1) := by
        rw [pow_add, pow_mul]
        have hrem : Or (n x % 2 = 0) (n x % 2 = 1) := by omega
        cases hrem with
        | inl hz => simp [hz]
        | inr ho => simp [ho]
  calc
    _ = S.prod (fun x => (nativeVertexGapValue x ^ (n x / 2)) ^ 2 *
        (if n x % 2 = 1 then nativeVertexGapValue x else 1)) :=
      Finset.prod_congr rfl (fun x _ => hpow x)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow, <- Finset.prod_filter]

theorem native_gap_square_power_product_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (S : Finset (Sum Nat (Prod Nat Nat))) (hS : S <= nativeVertexGapBasis P)
    (n : Sum Nat (Prod Nat Nat) -> Nat) :
    IsSquare (S.prod (fun x => nativeVertexGapValue x ^ n x)) <->
      forall x : Sum Nat (Prod Nat Nat), Membership.mem S x -> n x % 2 = 0 := by
  classical
  let C := S.prod (fun x => nativeVertexGapValue x ^ (n x / 2))
  let R := S.filter (fun x => n x % 2 = 1)
  have hC : 0 < C := Finset.prod_pos (fun x hx =>
    pow_pos (native_gap_basis_value_positive P hP x (hS hx)) _)
  constructor
  case mp =>
    intro hsq
    rw [native_gap_power_parity_factorization S n] at hsq
    have hsq' : IsSquare ((C * C) * R.prod nativeVertexGapValue) := by
      simpa only [C, R, pow_two] using hsq
    have hR : IsSquare (R.prod nativeVertexGapValue) := by
      have hh := Nat.isSquare_mul_trans_of_pos (a := 1) (b := C * C)
        (c := R.prod nativeVertexGapValue) (Nat.mul_pos hC hC)
        (Exists.intro C (by simp)) hsq'
      simpa only [one_mul] using hh
    have hRempty : R = {} := hind R
      (Finset.mem_powerset.mpr ((Finset.filter_subset _ _).trans hS)) hR
    intro x hx
    have hnot : Not (n x % 2 = 1) := by
      intro ho
      have hm : Membership.mem R x := Finset.mem_filter.mpr (And.intro hx ho)
      rw [hRempty] at hm
      exact Finset.notMem_empty x hm
    omega
  case mpr =>
    intro heven
    have hRempty : R = {} := by
      refine Finset.Subset.antisymm ?_ (by intro x hx; simp at hx)
      intro x hx
      exfalso
      have hh := Finset.mem_filter.mp hx
      have hz := heven x hh.1
      omega
    rw [native_gap_power_parity_factorization S n]
    change IsSquare (C ^ 2 * R.prod nativeVertexGapValue)
    rw [hRempty]
    simp only [Finset.prod_empty, mul_one]
    exact Exists.intro C (pow_two C)

end PrimeFactorOscillations.FiniteFieldIntegerSignature
