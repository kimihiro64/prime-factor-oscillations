import PrimeFactorOscillations.Proof.Upper.FiniteMaximum
import PrimeFactorOscillations.Proof.Upper.UniformTail

set_option autoImplicit false

/-!
# The upper half of the headline oscillation theorem

For both named families, the separated strict reversal count is a genuinely
attained finite maximum and obeys the stated double-exponential upper bound.
The matching double-exponential lower bound remains a separate open target.
-/

namespace PrimeFactorOscillations

/-- Unconditional upper bound, with all maxima and asymptotic quantifiers explicit. -/
theorem both_reversalNumbers_eventually_upper (epsilon : Real) (he : 0 < epsilon) :
    exists K : Nat, 2 <= K /\ forall k : Nat, K <= k ->
      (exists N : Nat, HasReversalNumber (ordinaryDensity k) N /\
        (N : Real) <= Real.exp (Real.exp (((1 : Real) / 3 + epsilon) * k))) /\
      (exists N : Nat, HasReversalNumber (genericOddDensity k) N /\
        (N : Real) <= Real.exp (Real.exp (((1 : Real) / 3 + epsilon) * k))) := by
  choose K hK using both_densities_eventually_strict_tail epsilon he
  refine Exists.intro K (And.intro hK.1 ?_)
  intro k hk
  have htail := hK.2 k hk
  choose No hNo using exists_reversalNumber_of_tail (ordinaryDensity k)
    (upperCutoffIndex epsilon k) (fun i hi => le_of_lt (htail.2 i hi).1)
  choose Ng hNg using exists_reversalNumber_of_tail (genericOddDensity k)
    (upperCutoffIndex epsilon k) (fun i hi => le_of_lt (htail.2 i hi).2)
  have ho : (No : Real) <= upperCutoffIndex epsilon k := by exact_mod_cast hNo.2
  have hg : (Ng : Real) <= upperCutoffIndex epsilon k := by exact_mod_cast hNg.2
  exact And.intro
    (Exists.intro No (And.intro hNo.1 (ho.trans htail.1)))
    (Exists.intro Ng (And.intro hNg.1 (hg.trans htail.1)))

end PrimeFactorOscillations
