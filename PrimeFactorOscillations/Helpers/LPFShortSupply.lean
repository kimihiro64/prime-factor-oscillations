/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFShortSource
import PrimeFactorOscillations.Helpers.LPFSubwindowTransfer

/-!
# Complete short-window defect bound

The retained supply is 67/1024 at M >= 2^20. Both proper-prime-power
positions, the source exceptional set and the complete cross-overlap
absorption enter this one-step bound. Growth is only floor(7M/6);
the corresponding asymptotic defect-growth reserve is 5/48.
No entry theorem for the seed {2} is asserted here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem exists_fullStep_dense_short_normalized_power_log_bound :
    exists C eta : Real, And (0 < C) (And (0 < eta)
      (Filter.Eventually (fun M : Nat =>
        forall S : Finset Nat,
        let E := ((SDiff.sdiff (inputPrimePrefix M) S).card : Real)
        E <= eta * ((M : Real) / Real.log (M : Real)) ->
        ((SDiff.sdiff (inputPrimePrefix (7 * M / 6)) (fullStep S)).card : Real) <=
          (17 / 16 : Real) * E + C * (M : Real) ^ (79 / 80 : Real) +
            (8192 / 67 : Real) * eta * Real.log (M : Real))
        Filter.atTop)) := by
  choose C hC hSupply using exists_short_primeTarget_supply_low_cutoff
  choose eta hEta hRec using exists_dense_fullStep_subwindow_row_normalized_recurrence
    (67 / 1024 : Real) (by norm_num)
  refine Exists.intro C (Exists.intro eta (And.intro hC (And.intro hEta ?_)))
  filter_upwards [hRec, Filter.eventually_ge_atTop (2 ^ 20 : Nat)] with M hStep hM
  intro S
  dsimp only
  intro hE
  choose Z hZ hGood using hSupply M hM
  have h := hStep (7 * M / 6) (by omega) S Z hE hGood
  have hCoeff : 8 * eta / (67 / 1024 : Real) = (8192 / 67 : Real) * eta := by ring
  rw [hCoeff] at h
  nlinarith only [h, hZ]

end PrimeFactorOscillations.LPF
