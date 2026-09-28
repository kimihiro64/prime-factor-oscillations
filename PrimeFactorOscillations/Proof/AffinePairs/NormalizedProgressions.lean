import PrimeFactorOscillations.Proof.AffinePairs.FixedProgressions

/-! # Normalized prime frequencies in a fixed reduced residue class -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

/-- Reduced residue probabilities converge uniformly over the classes of each
fixed positive modulus. Every normalization uses the actual prime count. -/
theorem eventually_prime_progression_probability_close
    (q : Nat) (hq : 1 <= q) (epsilon : Real) (he : 0 < epsilon) :
    exists K : Nat, forall N : Nat, K <= N -> forall a : Units (ZMod q),
      abs ((Real.primeCountingZMod (N : Real) q a : Real) /
        (Nat.primeCounting N : Real) - 1 / (q.totient : Real)) < epsilon := by
  choose C hC X0 hX0 using fixed_progression_prime_error q hq 2 (by norm_num)
  choose KP hKP using eventually_primeCounting_lower
  choose KB hKB using exists_nat_gt X0
  have hlog : Filter.Eventually (fun N : Nat =>
      max 1 (2 * C / epsilon + 1) <= Real.log (N : Real)) Filter.atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (max 1 (2 * C / epsilon + 1)))
  choose KL hKL using Filter.eventually_atTop.mp hlog
  refine Exists.intro (max 3 (max KP (max KB KL))) ?_
  intro N hN a
  let L : Real := Real.log (N : Real)
  let n : Real := Nat.primeCounting N
  let u : Real := Real.primeCountingZMod (N : Real) q a
  let f : Real := q.totient
  have hN3 : (3 : Real) <= N := by exact_mod_cast (show 3 <= N by omega)
  have hNp : (0 : Real) < N := by linarith only [hN3]
  have hL1 : 1 <= L := (le_max_left 1 _).trans (hKL N (by omega))
  have hL : 0 < L := by linarith only [hL1]
  have hsmall : 2 * C / epsilon + 1 <= L :=
    (le_max_right 1 _).trans (hKL N (by omega))
  have hscaled := mul_lt_mul_of_pos_right
    (show 2 * C / epsilon < L by linarith only [hsmall]) he
  have hc : (2 * C / epsilon) * epsilon = 2 * C := by field_simp [ne_of_gt he]
  rw [hc] at hscaled
  have htarget : 2 * C / L < epsilon := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hL.le
    have hcL : (2 * C / L) * L = 2 * C := by field_simp [ne_of_gt hL]
    rw [hcL] at hm
    nlinarith only [hscaled, hm]
  have hprime := hKP N (by omega)
  have hn : 0 < n := hprime.2
  have hf : 0 < f := by
    dsimp only [f]
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hX : X0 <= (N : Real) :=
    hKB.le.trans (by exact_mod_cast (show KB <= N by omega))
  have herror : abs (u - n / f) <= C * (N : Real) / L ^ 2 := by
    simpa only [u, n, f, L, BombieriVinogradov.primeCounting, pi,
      Nat.floor_natCast, Real.rpow_two] using hX0 (N : Real) hX a
  have hrepr : u / n - 1 / f = (u - n / f) / n := by
    field_simp [ne_of_gt hn, ne_of_gt hf]
  have hden : 0 < (N : Real) / (2 * L) := div_pos hNp (by linarith only [hL])
  have hnum : 0 <= C * (N : Real) / L ^ 2 := by positivity
  change abs (u / n - 1 / f) < epsilon
  calc
    _ = abs (u - n / f) / n := by rw [hrepr, abs_div, abs_of_pos hn]
    _ <= (C * (N : Real) / L ^ 2) / n :=
      div_le_div_of_nonneg_right herror hn.le
    _ <= (C * (N : Real) / L ^ 2) / ((N : Real) / (2 * L)) :=
      div_le_div_of_nonneg_left hnum hden hprime.1
    _ = 2 * C / L := by field_simp [ne_of_gt hNp, ne_of_gt hL]
    _ < epsilon := htarget

/-- The fixed-modulus prime probability limit used by the ordered pair
ensemble. The modulus is fixed before the input-size limit. -/
theorem tendsto_prime_progression_probability
    (q : Nat) (hq : 1 <= q) (a : Units (ZMod q)) :
    Filter.Tendsto (fun N : Nat =>
      (Real.primeCountingZMod (N : Real) q a : Real) / (Nat.primeCounting N : Real))
      Filter.atTop (nhds (1 / (q.totient : Real))) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon he
  choose K hK using eventually_prime_progression_probability_close q hq epsilon he
  refine Exists.intro K ?_
  intro N hN
  simpa only [Real.dist_eq] using hK N hN a

end PrimeFactorOscillations
