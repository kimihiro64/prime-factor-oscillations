import PrimeFactorOscillations.Proof.Lower.PositivePowerWindows
import PrimeFactorOscillations.Proof.Upper.UpperBound

/-! # Sharp quantitative transfer to attained reversal maxima -/

set_option autoImplicit false

namespace PrimeFactorOscillations

/-- Reusable sharp transfer with exact attained maxima and the maintained upper bound.
The positive-power supply assumption is explicit and cannot be replaced by infinitude. -/
theorem both_reversal_bounds_of_quantitative_prime_windows (H : Nat)
    (delta a : Real) (hd : 0 < delta) (ha : 0 < a)
    (haH : a < 1 / ((H : Real) + 1))
    (hsupply : Filter.Eventually (fun N : Nat =>
      (N : Real) ^ delta <=
        (((Finset.Ioc N (2 * N)).filter (fun n =>
          2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card)).card : Real))
      Filter.atTop) :
    forall epsilon : Real, 0 < epsilon ->
      exists K : Nat, 1 <= K /\ forall k : Nat, K <= k ->
        ReversalBoundsAt (ordinaryDensity k) k a epsilon /\
        ReversalBoundsAt (genericOddDensity k) k a epsilon := by
  choose K0 hK0 using both_reversal_supply_of_positive_power_windows H delta a hd ha haH hsupply
  intro epsilon he
  choose K1 hK1 using both_reversalNumbers_eventually_upper epsilon he
  refine Exists.intro (max K0 K1) (And.intro ?_ ?_)
  next => have h4 := hK0.1; omega
  next =>
    intro k hk
    choose m hm hOrd hGen using hK0.2 k ((le_max_left K0 K1).trans hk)
    have hupper := hK1.2 k ((le_max_right K0 K1).trans hk)
    choose NO hNO using hupper.1
    choose NG hNG using hupper.2
    have hmNO : m <= NO := hNO.1.2 m hOrd
    have hmNG : m <= NG := hNG.1.2 m hGen
    have hloO : Real.exp (Real.exp (a * k)) <= (NO : Real) :=
      hm.trans (by exact_mod_cast hmNO)
    have hloG : Real.exp (Real.exp (a * k)) <= (NG : Real) :=
      hm.trans (by exact_mod_cast hmNG)
    exact And.intro (Exists.intro NO (And.intro hNO.1 (And.intro hloO hNO.2)))
      (Exists.intro NG (And.intro hNG.1 (And.intro hloG hNG.2)))

end PrimeFactorOscillations
