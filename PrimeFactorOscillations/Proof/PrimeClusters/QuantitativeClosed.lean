import BombieriVinogradov.Assembly.PrimeCountingConversion.Main
import PrimeFactorOscillations.Proof.PrimeClusters.CuberootCount
import PrimeFactorOscillations.Proof.PrimeClusters.PositiveWitness

set_option autoImplicit false

/-! # QuantitativeClosed in the quantitative prime-cluster count -/

namespace PrimeGaps

theorem eventually_many_prime_cluster_shifts_105
    (h : Fin 105 -> Nat) (hadm : GPYSieveS1.IsAdmissible h) :
    Filter.Eventually (fun N : Nat =>
      (N : Real) ^ ((1 : Real) / 3) <=
        (((Finset.Ioc N (2 * N)).filter (fun n =>
          2 <= (Finset.univ.filter (fun i : Fin 105 => Nat.Prime (n + h i))).card)).card :
            Real)) Filter.atTop := by
  choose theta ht0 ht delta hd0 hd F hF hsupp hmargin using
    exists_positive_smooth_margin_105
  exact eventually_cuberoot_prime_cluster_count (by norm_num) h hadm F hF hsupp
    theta delta ht0 ht hd0 hd
    (_root_.BombieriVinogradov.hasLevelOfDistribution
      BombieriVinogradov.PrimeCountingConversion.weighted_to_prime_counting ht) hmargin

end PrimeGaps
