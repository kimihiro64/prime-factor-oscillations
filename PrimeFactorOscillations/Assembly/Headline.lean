import PrimeFactorOscillations.Assembly.QuantitativePrimeWindows
import PrimeFactorOscillations.Proof.PrimeClusters.WindowCount

/-! # Unconditional double-exponential reversal bounds -/

set_option autoImplicit false

namespace PrimeFactorOscillations

/-- Both canonical density sequences have attained finite reversal maxima,
with one positive lower coefficient and upper coefficient 1/3 + epsilon. -/
theorem doubleExponentialReversalBounds : DoubleExponentialReversalBounds := by
  refine Exists.intro ((1 : Real) / 602) (And.intro (by norm_num) ?_)
  exact both_reversal_bounds_of_quantitative_prime_windows
    600 ((1 : Real) / 3) ((1 : Real) / 602)
    (by norm_num) (by norm_num) (by norm_num)
    PrimeGaps.eventually_many_prime_windows_600

end PrimeFactorOscillations
