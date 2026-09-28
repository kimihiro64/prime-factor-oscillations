import PrimeGapsTheory.Sieve.Common.S2mEvalAssembly

set_option autoImplicit false

/-! # PowerLogBound in the quantitative prime-cluster count -/

namespace PrimeGaps

theorem power_log_bound_of_scale_count
    (k N W G : Nat) (alpha gamma K : Real)
    (hk : 2 <= k) (hN : 2 <= N) (hW : 0 < W)
    (ha : 0 < alpha) (ha1 : alpha <= 1) (hg : 0 < gamma)
    (hlogR : 1 <= Real.log ((N : Real) ^ alpha))
    (hWlog : (W : Real) <= Real.log (N : Real) ^ 2)
    (hc : mainScale k N ((N : Real) ^ alpha) W * gamma / 2 <=
      (G : Real) * (((k : Real) - 1) *
        (K * (N : Real) ^ alpha * Real.log ((N : Real) ^ alpha) ^ (2 * k)) ^ 2)) :
    (N : Real) <= (2 * ((k : Real) - 1) * K ^ 2 / gamma) *
      (G : Real) * (N : Real) ^ (2 * alpha) *
        Real.log (N : Real) ^ (6 * k + 2) := by
  let R := (N : Real) ^ alpha
  let A := 2 * ((k : Real) - 1) * K ^ 2 / gamma
  have hNpos : (0 : Real) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : Real) <= N := by exact_mod_cast (by omega : 1 <= N)
  have hWR : (0 : Real) < W := Nat.cast_pos.mpr hW
  have hWp : 0 < (W : Real) ^ (k + 1) := pow_pos hWR _
  have hphi : (1 : Real) <= W.totient := by
    exact_mod_cast (Nat.totient_pos.mpr hW)
  have hphi0 : (0 : Real) <= W.totient := Nat.cast_nonneg _
  have hp : (1 : Real) ^ k <= (W.totient : Real) ^ k := by gcongr
  have hl : (1 : Real) ^ k <= Real.log R ^ k := by gcongr
  simp only [one_pow] at hp hl
  have hnum : (N : Real) <=
      (W.totient : Real) ^ k * (N : Real) * Real.log R ^ k := by
    calc
      _ <= (W.totient : Real) ^ k * (N : Real) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg N)
      _ <= _ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hl
          (mul_nonneg (pow_nonneg hphi0 _) (Nat.cast_nonneg N))
  have hscale : (N : Real) / (W : Real) ^ (k + 1) <= mainScale k N R W :=
    div_le_div_of_nonneg_right hnum hWp.le
  have hlow := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hscale hg.le) (show (0 : Real) <= 2 by norm_num)
  have hboth := hlow.trans hc
  have hfactor : 0 <= 2 * (W : Real) ^ (k + 1) / gamma := by positivity
  have hprod := mul_le_mul_of_nonneg_right hboth hfactor
  have hleft :
      ((N : Real) / (W : Real) ^ (k + 1) * gamma / 2) *
        (2 * (W : Real) ^ (k + 1) / gamma) = N := by
    field_simp
  have hright :
      ((G : Real) * (((k : Real) - 1) * (K * R * Real.log R ^ (2 * k)) ^ 2)) *
        (2 * (W : Real) ^ (k + 1) / gamma) =
      A * (G : Real) * R ^ 2 * (Real.log R ^ (2 * k)) ^ 2 *
        (W : Real) ^ (k + 1) := by
    dsimp [A]
    ring
  rw [hleft] at hprod
  change (N : Real) <=
    ((G : Real) * (((k : Real) - 1) * (K * R * Real.log R ^ (2 * k)) ^ 2)) *
      (2 * (W : Real) ^ (k + 1) / gamma) at hprod
  rw [hright] at hprod
  have hlogN : 0 <= Real.log (N : Real) := Real.log_nonneg hN1
  have hlogR0 : 0 <= Real.log R := by linarith
  have hlogCmp : Real.log R <= Real.log (N : Real) := by
    change Real.log ((N : Real) ^ alpha) <= Real.log (N : Real)
    rw [Real.log_rpow hNpos]
    nlinarith
  have hpoly : (Real.log R ^ (2 * k)) ^ 2 * (W : Real) ^ (k + 1) <=
      Real.log (N : Real) ^ (6 * k + 2) := by
    calc
      _ <= (Real.log (N : Real) ^ (2 * k)) ^ 2 *
          (Real.log (N : Real) ^ 2) ^ (k + 1) := by gcongr
      _ = _ := by
        rw [<- pow_mul, <- pow_mul, <- pow_add]
        congr 1
        omega
  have hkR : 0 <= (k : Real) - 1 := by
    have hk' : (2 : Real) <= k := by exact_mod_cast hk
    linarith
  have hA : 0 <= A := by dsimp [A]; positivity
  have hR2 : R ^ 2 = (N : Real) ^ (2 * alpha) := by
    change ((N : Real) ^ alpha) ^ 2 = (N : Real) ^ (2 * alpha)
    rw [show 2 * alpha = alpha * (2 : Real) by ring, Real.rpow_mul hNpos.le,
      Real.rpow_two]
  calc
    (N : Real) <= A * (G : Real) * R ^ 2 *
        ((Real.log R ^ (2 * k)) ^ 2 * (W : Real) ^ (k + 1)) := by
      simpa only [mul_assoc] using hprod
    _ <= A * (G : Real) * R ^ 2 * Real.log (N : Real) ^ (6 * k + 2) :=
      mul_le_mul_of_nonneg_left hpoly
        (mul_nonneg (mul_nonneg hA (Nat.cast_nonneg _)) (sq_nonneg _))
    _ = _ := by rw [hR2]

end PrimeGaps
