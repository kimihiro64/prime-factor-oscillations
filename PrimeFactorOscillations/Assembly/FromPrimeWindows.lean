import PrimeFactorOscillations.Proof.Lower.FromPrimeWindows
import PrimeFactorOscillations.Proof.Upper.UpperBound

/-! # Exact headline reduction from quantitative prime windows -/

namespace PrimeFactorOscillations

/-- Exact headline assembly, retaining the sole unverified analytic supply input. -/
theorem doubleExponentialReversalBounds_of_prime_windows (H : Nat)
    (hsupply : Filter.Eventually (fun N : Nat =>
      (N : Real) ^ ((1 : Real) / 3) <=
        (((Finset.Ioc N (2 * N)).filter (fun n =>
          2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card)).card : Real))
      Filter.atTop) : DoubleExponentialReversalBounds := by
  choose a ha K0 hK0 using both_double_exp_reversal_supply_of_prime_windows H hsupply
  refine Exists.intro a (And.intro ha ?_)
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
