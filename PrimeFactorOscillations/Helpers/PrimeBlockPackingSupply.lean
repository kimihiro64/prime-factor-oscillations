/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeCountingLocation
import PrimeFactorOscillations.Helpers.QRHSquarefreePrimePairs

/-!
# PNT supply for the native packing blocks

The existing unconditional theta PNT supplies both actual adjacent prime
blocks. The external height may be any natural Y at least 4*N.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

/-- The actual prime-block cardinal controls its exact theta increment. -/
theorem primeBlock_theta_sub_le_card_mul_log
    (a b Y : Nat) (hab : a <= b) (hbY : b <= Y) :
    Chebyshev.theta (b : Real) - Chebyshev.theta (a : Real) <=
      ((primeBlockSet a b).card : Real) * Real.log (Y : Real) := by
  classical
  have hSet (n : Nat) : Nat.primesLE n = Nat.primesBelow (n + 1) := by
    apply Finset.ext
    intro p
    constructor
    . intro hp
      have h := Nat.mem_primesLE.mp hp
      exact Nat.mem_primesBelow.mpr (And.intro (by omega) h.2)
    . intro hp
      have h := Nat.mem_primesBelow.mp hp
      exact Nat.mem_primesLE.mpr (And.intro (by omega) h.2)
  have hTheta (n : Nat) : Chebyshev.theta (n : Real) =
      Finset.sum (Nat.primesBelow (n + 1)) (fun p => Real.log (p : Real)) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, hSet n]
  have hsub : forall p : Nat, Membership.mem (Nat.primesBelow (a + 1)) p ->
      Membership.mem (Nat.primesBelow (b + 1)) p := by
    intro p hp
    have h := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr (And.intro (by omega) h.2)
  have hSum : Finset.sum (primeBlockSet a b) (fun p => Real.log (p : Real)) =
      Chebyshev.theta (b : Real) - Chebyshev.theta (a : Real) := by
    rw [hTheta b, hTheta a]
    exact eq_sub_iff_add_eq.mpr (Finset.sum_sdiff hsub)
  rw [<- hSum]
  calc
    Finset.sum (primeBlockSet a b) (fun p => Real.log (p : Real)) <=
        Finset.sum (primeBlockSet a b) (fun _ => Real.log (Y : Real)) := by
      apply Finset.sum_le_sum
      intro p hp
      have h := (mem_primeBlockSet_iff a b p).mp hp
      exact Real.log_le_log (by exact_mod_cast h.1.pos)
        (by exact_mod_cast h.2.2.trans hbY)
    _ = ((primeBlockSet a b).card : Real) * Real.log (Y : Real) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Both quarter blocks have a uniform positive prime supply below Y. -/
theorem eventually_primeQuarterBlock_supply :
    Filter.Eventually (fun N : Nat => 1 <= N /\
      forall Y : Nat, 4 * N <= Y ->
        (N : Real) <= 2 * ((primeBlockSet (2 * N) (3 * N)).card : Real) *
          Real.log (Y : Real) /\
        (N : Real) <= 2 * ((primeBlockSet (3 * N) (4 * N)).card : Real) *
          Real.log (Y : Real)) Filter.atTop := by
  have hLower := tendsto_primeProfile_theta_ratio.eventually
    (lt_mem_nhds (by norm_num : (15 / 16 : Real) < 1))
  have hUpper := tendsto_primeProfile_theta_ratio.eventually
    (gt_mem_nhds (by norm_num : (1 : Real) < 17 / 16))
  have hBand : Filter.Eventually (fun n : Nat =>
      (15 / 16 : Real) * n <= Chebyshev.theta (n : Real) /\
        Chebyshev.theta (n : Real) <= (17 / 16 : Real) * n) Filter.atTop := by
    filter_upwards [hLower, hUpper, Filter.eventually_ge_atTop (1 : Nat)]
      with n hl hu hn
    have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
    have hn0 : Not ((n : Real) = 0) := ne_of_gt hnR
    have hcancel : Chebyshev.theta (n : Real) / (n : Real) * n =
        Chebyshev.theta (n : Real) := by field_simp
    have hLo := mul_lt_mul_of_pos_right hl hnR
    have hHi := mul_lt_mul_of_pos_right hu hnR
    rw [hcancel] at hLo hHi
    exact And.intro hLo.le hHi.le
  choose N0 hN0 using hBand.exists_forall_of_atTop
  filter_upwards [Filter.eventually_ge_atTop (max N0 1)] with N hN
  have hN1 : 1 <= N := (le_max_right _ _).trans hN
  have hNbase : N0 <= N := (le_max_left _ _).trans hN
  refine And.intro hN1 ?_
  intro Y hY
  have h2 := hN0 (2 * N) (by omega)
  have h3 := hN0 (3 * N) (by omega)
  have h4 := hN0 (4 * N) (by omega)
  have hA := primeBlock_theta_sub_le_card_mul_log (2 * N) (3 * N) Y
    (by omega) (by omega)
  have hB := primeBlock_theta_sub_le_card_mul_log (3 * N) (4 * N) Y
    (by omega) hY
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h2 h3 h4 hA hB
  have hNR : 0 <= (N : Real) := Nat.cast_nonneg N
  exact And.intro (by nlinarith only [hA, h2.2, h3.1, hNR])
    (by nlinarith only [hB, h3.2, h4.1, hNR])

end PrimeFactorOscillations.QRH
