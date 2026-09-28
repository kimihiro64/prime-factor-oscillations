import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Pow.PowerLogCount
import PrimeFactorOscillations.Proof.PrimeClusters.PowerLogBound
import PrimeFactorOscillations.Proof.PrimeClusters.ScaleCount
import PrimeGapsTheory.NumberTheory.Compatibility

set_option autoImplicit false

/-! # CuberootCount in the quantitative prime-cluster count -/

open Filter

namespace PrimeGaps

theorem eventually_cuberoot_prime_cluster_count {k : Nat} (hk : 2 <= k)
    (h : Fin k -> Nat) (hadm : GPYSieveS1.IsAdmissible h)
    (F : EuclideanSpace Real (Fin k) -> Real)
    (hF : ContDiff Real (Top.top : ENat) F)
    (hsupp : Set.Subset (Function.support F) (EuclideanSpace.scaledStdSimplex k 1))
    (theta delta : Real) (ht0 : 0 < theta) (ht : theta < 1 / 2)
    (hd0 : 0 < delta) (hd : delta < theta / 2)
    (hLD : Nat.HasLevelOfDistribution Set.univ theta 1)
    (hmargin : 0 <
      (theta / 2 - delta) *
        Finset.univ.sum (fun m => J m ((MainProp.canonMemLp F hF hsupp).toLp F)) -
          norm ((MainProp.canonMemLp F hF hsupp).toLp F) ^ 2) :
    Filter.Eventually (fun N : Nat =>
      (N : Real) ^ ((1 : Real) / 3) <=
        (((Finset.Ioc N (2 * N)).filter (fun n =>
          2 <= (Finset.univ.filter (fun i : Fin k => Nat.Prime (n + h i))).card)).card :
            Real)) Filter.atTop := by
  classical
  let G := fun N : Nat => ((Finset.Ioc N (2 * N)).filter (fun n =>
    2 <= (Finset.univ.filter (fun i : Fin k => Nat.Prime (n + h i))).card)).card
  let alpha := theta / 2 - delta
  let gamma := alpha *
      Finset.univ.sum (fun m => J m ((MainProp.canonMemLp F hF hsupp).toLp F)) -
        norm ((MainProp.canonMemLp F hF hsupp).toLp F) ^ 2
  have ha : 0 < alpha := by dsimp [alpha]; linarith
  have haThird : alpha < 1 / 3 := by dsimp [alpha]; linarith
  have ha1 : alpha <= 1 := by linarith
  have hg : 0 < gamma := hmargin
  choose C hC Ns hscale using exists_uniform_scale_count_bound hk h hadm F hF hsupp
    theta delta ht0 ht hd0 hd hLD hmargin
  let K := C * (MaynardSmoothY.Fmax F + 1)
  let A := 2 * ((k : Real) - 1) * K ^ 2 / gamma
  apply Real.eventually_cuberoot_le_of_power_log_bound G A alpha (6 * k + 2) haThird
  have hcast : Tendsto (fun N : Nat => (N : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlogs : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  filter_upwards [hcast.eventually_ge_atTop Ns, lem_W_size,
    hlogs.eventually_ge_atTop 1, hlogs.eventually_ge_atTop (1 / alpha),
    Filter.eventually_ge_atTop 2] with N hNs hW hlog1 hlogAlpha hN2
  have hNpos : (0 : Real) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog0 : 0 <= Real.log (N : Real) := by linarith
  have hloglog0 : 0 <= Real.log (Real.log (N : Real)) := Real.log_nonneg hlog1
  have hloglog : Real.log (Real.log (N : Real)) <= Real.log (N : Real) :=
    Real.log_le_self hlog0
  have hWlog : (sieveModulus N : Real) <= Real.log (N : Real) ^ 2 := by
    apply hW.trans
    gcongr
  have hprod := mul_le_mul_of_nonneg_left hlogAlpha ha.le
  have hunit : alpha * (1 / alpha) = 1 := by field_simp
  rw [hunit] at hprod
  have hlogR : 1 <= Real.log ((N : Real) ^ alpha) := by
    rw [Real.log_rpow hNpos]
    exact hprod
  choose v hv using hadm.2.exists_zmod_gcd_eq_one N
  have hc := hscale N hNs v hv
  exact power_log_bound_of_scale_count k N (sieveModulus N) (G N) alpha gamma K
    hk hN2 W_pos ha ha1 hg hlogR hWlog hc

end PrimeGaps
