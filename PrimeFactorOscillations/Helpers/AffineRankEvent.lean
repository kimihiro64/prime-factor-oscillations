import PrimeFactorOscillations.Definitions.AffineSumFamily
import PrimeFactorOscillations.Definitions.RealLocalDensity

/-! # Exact affine rank-event interpretation away from zero -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.AffineSumFamily
open scoped Classical

theorem isKthDistinctPrimeFactor_iff (F : AffineSumFamily)
    (a b k p : Nat) (hp : Nat.Prime p) (hvalue : Not (F.value a b = 0)) :
    PrimeFactorUnimodality.IsKthDistinctPrimeFactor (F.value a b).natAbs k p <->
      Dvd.dvd (p : Int) (F.value a b) /\
        (((Finset.range p).filter Nat.Prime).filter
          (fun l : Nat => Dvd.dvd (l : Int) (F.value a b))).card = k - 1 := by
  have hz : Not ((F.value a b).natAbs = 0) := by
    simpa only [Int.natAbs_eq_zero] using hvalue
  have hfilter :
      ((F.value a b).natAbs.primeFactors.filter (fun l => l < p)) =
      ((Finset.range p).filter Nat.Prime).filter
        (fun l : Nat => Dvd.dvd (l : Int) (F.value a b)) := by
    apply Finset.ext
    intro l
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_range,
      ne_eq, hz, not_false_eq_true, true_and, Int.natCast_dvd, and_assoc, and_comm]
  simp only [PrimeFactorUnimodality.IsKthDistinctPrimeFactor, hfilter, hp, ne_eq, hz,
    not_false_eq_true, true_and, Int.natCast_dvd]

end PrimeFactorOscillations.AffineSumFamily
