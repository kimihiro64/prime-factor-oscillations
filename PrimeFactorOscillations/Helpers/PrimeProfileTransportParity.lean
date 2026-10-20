/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileTransportComparison

/-!
# The even lattice of bounded prime-profile transport

After localization removes the exceptional prime two from both transported
sets, their equal cardinalities force an even integer transport sum.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

theorem prime_prefix_transport_even_of_cost_le
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C)
    (hsmall : 2 < (PrimeFactorUnimodality.primeAt n : Real) - C) :
    exists K : Nat,
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) = 2 * (K : Real) := by
  let s := (Finset.range (n + 1)).image e
  let u := Finset.range (n + 1)
  let E := s \ u
  let L := u \ s
  have hcard : s.card = u.card := Finset.card_image_iff.mpr
    (fun _ _ _ _ h => e.injective h)
  have hEL : E.card = L.card := Finset.card_sdiff_comm hcard
  have hlocal := prime_prefix_coordinates_localized_of_cost_le e t n C ht hC hcost
  have hEodd : forall j, Membership.mem E j ->
      PrimeFactorUnimodality.primeAt j % 2 = 1 := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).2
    change Not (Membership.mem (Finset.range (n + 1)) j) at hn
    rw [Finset.mem_range] at hn
    have hidx : n <= j := by omega
    have hpq : (PrimeFactorUnimodality.primeAt n : Real) <=
        PrimeFactorUnimodality.primeAt j := by
      exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone hidx
    have hbigR : (2 : Real) < PrimeFactorUnimodality.primeAt j := by
      linarith only [hsmall, hC0, hpq]
    have hbig : 2 < PrimeFactorUnimodality.primeAt j := by exact_mod_cast hbigR
    have hodd := (PrimeFactorUnimodality.prime_primeAt j).eq_two_or_odd
    omega
  have hLodd : forall j, Membership.mem L j ->
      PrimeFactorUnimodality.primeAt j % 2 = 1 := by
    intro j hj
    have hbound := hlocal.2 j hj
    have hbigR : (2 : Real) < PrimeFactorUnimodality.primeAt j := by
      linarith only [hsmall, hbound]
    have hbig : 2 < PrimeFactorUnimodality.primeAt j := by exact_mod_cast hbigR
    have hodd := (PrimeFactorUnimodality.prime_primeAt j).eq_two_or_odd
    omega
  let A := E.sum PrimeFactorUnimodality.primeAt
  let B := L.sum PrimeFactorUnimodality.primeAt
  have hcancel : (A : Real) - (B : Real) =
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1) := by
    change ((E.sum PrimeFactorUnimodality.primeAt : Nat) : Real) -
      ((L.sum PrimeFactorUnimodality.primeAt : Nat) : Real) = _
    rw [Nat.cast_sum, Nat.cast_sum]
    have hid := @Finset.sum_sdiff_sub_sum_sdiff Nat Real u s inferInstance inferInstance
      (fun j => (PrimeFactorUnimodality.primeAt j : Real))
    change E.sum (fun j => (PrimeFactorUnimodality.primeAt j : Real)) -
        L.sum (fun j => (PrimeFactorUnimodality.primeAt j : Real)) =
      s.sum (fun j => (PrimeFactorUnimodality.primeAt j : Real)) -
        u.sum (fun j => (PrimeFactorUnimodality.primeAt j : Real)) at hid
    rw [hid]
    dsimp only [s, u]
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    rfl
  have hABR : (B : Real) <= A := by
    have hn := prime_prefix_transport_nonneg e n
    rw [<- hcancel] at hn
    exact sub_nonneg.mp hn
  have hAB : B <= A := by exact_mod_cast hABR
  have he := Finset.exists_nat_sum_sub_sum_eq_twice E L
    PrimeFactorUnimodality.primeAt hEL hEodd hLodd
  let K := Classical.choose he
  have hK : A - B = 2 * K := Classical.choose_spec he
  have hcast : ((A - B : Nat) : Real) = 2 * (K : Real) := by exact_mod_cast hK
  rw [Nat.cast_sub hAB] at hcast
  exact Exists.intro K (hcancel.symm.trans hcast)

end PrimeFactorOscillations.PrimeProfileRigidity
