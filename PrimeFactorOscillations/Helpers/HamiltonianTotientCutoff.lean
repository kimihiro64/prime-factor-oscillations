/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMertensProduct
import PrimeFactorOscillations.Helpers.HamiltonianTotientEuler

/-! # The finite small-prime and large-prime totient cutoff

The actual prime-factor support is split at an arbitrary real cutoff.
The full large-prime product is retained; the small product is compared
with the cached classical Mertens product.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_totient_euler_factor_ge_one (p : Nat) (hp : 2 <= p) :
    1 <= hamiltonianTotientEulerFactor p := by
  have hpR : (2 : Real) <= (p : Real) := by exact_mod_cast hp
  have hDen : 0 < (p : Real) - 1 := by linarith only [hpR]
  have hNe : Not ((p : Real) - 1 = 0) := ne_of_gt hDen
  apply (mul_le_mul_iff_of_pos_right hDen).mp
  have hCancel : hamiltonianTotientEulerFactor p * ((p : Real) - 1) = (p : Real) := by
    unfold hamiltonianTotientEulerFactor
    field_simp
  rw [hCancel, one_mul]
  linarith only [hpR]

theorem hamiltonian_nonnegative_subset_product
    (T P : Finset Nat) (f : Nat -> Real) (hSub : P <= T)
    (hOne : forall p, Membership.mem T p -> 1 <= f p) :
    P.prod f <= T.prod f := by
  have hGeneral : forall V : Finset Nat, forall U : Finset Nat, U <= V ->
      (forall p, Membership.mem V p -> 1 <= f p) -> U.prod f <= V.prod f := by
    intro V
    induction V using Finset.induction_on with
    | empty =>
        intro U hUV hV
        have hU : U = EmptyCollection.emptyCollection := by
          apply Finset.ext
          intro p
          constructor
          case mp =>
            intro hp
            exact False.elim (by simpa using hUV hp)
          case mpr =>
            intro hp
            exact False.elim (by simpa using hp)
        rw [hU]
    | @insert p V hp ih =>
        intro U hUV hV
        have hVp (q : Nat) (hq : Membership.mem V q) : 1 <= f q :=
          hV q (Finset.mem_insert_of_mem hq)
        have hpOne : 1 <= f p := hV p (Finset.mem_insert_self p V)
        have hpNonneg : 0 <= f p := le_trans (by norm_num) hpOne
        rw [Finset.prod_insert hp]
        by_cases hpU : Membership.mem U p
        case pos =>
          have hErase : U.erase p <= V := by
            intro q hq
            have h := Finset.mem_erase.mp hq
            have hMem := Finset.mem_insert.mp (hUV h.2)
            exact hMem.resolve_left h.1
          rw [<- Finset.mul_prod_erase U f hpU]
          exact mul_le_mul_of_nonneg_left (ih (U.erase p) hErase hVp) hpNonneg
        case neg =>
          have hUV' : U <= V := by
            intro q hq
            have h := Finset.mem_insert.mp (hUV hq)
            rcases h with hEq | hMem
            case inl =>
              exact False.elim (hpU (by simpa only [hEq] using hq))
            case inr => exact hMem
          have hVNonneg : 0 <= V.prod f :=
            Finset.prod_nonneg (fun q hq => le_trans (by norm_num) (hVp q hq))
          have hScale := mul_le_mul_of_nonneg_right hpOne hVNonneg
          rw [one_mul] at hScale
          exact (ih U hUV' hVp).trans hScale
  exact hGeneral T P hSub hOne

theorem hamiltonian_mertens_product_positive (x : Real) :
    0 < hamiltonianMertensProduct x := by
  unfold hamiltonianMertensProduct
  apply Finset.prod_pos
  intro p hp
  have hPrime := (Finset.mem_filter.mp hp).2
  have hpR : (2 : Real) <= (p : Real) := by exact_mod_cast hPrime.two_le
  have hInv : 1 / (p : Real) <= 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2) hpR
  linarith only [hInv]

theorem hamiltonian_mertens_reciprocal_euler_product (x : Real) :
    1 / hamiltonianMertensProduct x =
      ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).prod hamiltonianTotientEulerFactor := by
  unfold hamiltonianMertensProduct
  calc
    _ = ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).prod
        (fun p => 1 / (1 - 1 / (p : Real))) := by
      rw [Finset.prod_div_distrib]
      simp
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      have hPrime := (Finset.mem_filter.mp hp).2
      have hpR : (2 : Real) <= (p : Real) := by exact_mod_cast hPrime.two_le
      have hpPos : 0 < (p : Real) := by linarith only [hpR]
      have hDen : 0 < (p : Real) - 1 := by linarith only [hpR]
      have hPNe : Not ((p : Real) = 0) := ne_of_gt hpPos
      have hDNe : Not ((p : Real) - 1 = 0) := ne_of_gt hDen
      unfold hamiltonianTotientEulerFactor
      field_simp
      <;> ring

theorem hamiltonian_totient_small_prime_product (P : Finset Nat) (Y : Real)
    (hP : forall p, Membership.mem P p -> Nat.Prime p /\ (p : Real) <= Y) :
    P.prod hamiltonianTotientEulerFactor <= 1 / hamiltonianMertensProduct Y := by
  rw [hamiltonian_mertens_reciprocal_euler_product]
  apply hamiltonian_nonnegative_subset_product
  case hSub =>
    intro p hp
    have h := hP p hp
    exact Finset.mem_filter.mpr (And.intro
      (Finset.mem_Ioc.mpr (And.intro h.1.pos (Nat.le_floor h.2))) h.1)
  case hOne =>
    intro p hp
    exact hamiltonian_totient_euler_factor_ge_one p
      (Finset.mem_filter.mp hp).2.two_le

theorem hamiltonian_totient_finite_cutoff (n : Nat) (hn : 0 < n) (Y : Real) (hY : 4 <= Y) :
    (n : Real) / (n.totient : Real) <=
      (1 / hamiltonianMertensProduct Y) *
        Real.exp (2 * Real.log (n : Real) / (Y * Real.log Y)) := by
  let P := n.primeFactors.filter (fun p : Nat => (p : Real) <= Y)
  let Q := n.primeFactors.filter (fun p : Nat => Y < (p : Real))
  have hSplit : n.primeFactors.prod hamiltonianTotientEulerFactor =
      P.prod hamiltonianTotientEulerFactor * Q.prod hamiltonianTotientEulerFactor := by
    dsimp [P, Q]
    rw [Finset.prod_filter, Finset.prod_filter, <- Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    by_cases h : (p : Real) <= Y
    case pos => simp [h, not_lt_of_ge h]
    case neg => simp [h, lt_of_not_ge h]
  have hP (p : Nat) (hp : Membership.mem P p) : Nat.Prime p /\ (p : Real) <= Y := by
    have h := Finset.mem_filter.mp hp
    exact And.intro (Nat.prime_of_mem_primeFactors h.1) h.2
  have hQ (p : Nat) (hp : Membership.mem Q p) :
      Nat.Prime p /\ Y <= (p : Real) /\ Dvd.dvd p n := by
    have h := Finset.mem_filter.mp hp
    exact And.intro (Nat.prime_of_mem_primeFactors h.1)
      (And.intro h.2.le (Nat.dvd_of_mem_primeFactors h.1))
  rw [hamiltonian_totient_euler_product n hn, hSplit]
  exact mul_le_mul (hamiltonian_totient_small_prime_product P Y hP)
    (hamiltonian_totient_large_prime_product Q n Y hn hY hQ)
    (Finset.prod_nonneg (fun p hp =>
      (hamiltonian_totient_euler_factor_positive p (hQ p hp).1.two_le).le))
    (one_div_nonneg.mpr (hamiltonian_mertens_product_positive Y).le)

end PrimeFactorOscillations
