/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/WeightedPrimePowerTail.lean. Apache-2.0.
Original source lines 25-177 and208-236; proof bodies unchanged.
-/
import PrimeFactorOscillations.Helpers.Robin1984.Equivalence.RobinLemmaTwo

/-!
# Exact prime-square tail input for the RH negative envelope

Retains the root substitution, integrability and lower comparison from the
pinned source; unused upper-comparison and scalar corollaries are omitted.
-/

namespace Robin1984

noncomputable section

open MeasureTheory Set

theorem robinRealWeight_rpow_pullback
    (n k : Nat) (hk : 0 < k) {u : Real} (hu : 1 < u) :
    (k : Real) * u^((k : Real) - 1) * robinRealWeight n (u^(k : Real)) =
      Inv.inv (k : Real) * robinRealWeight (k * n) u := by
  have huPos : 0 < u := lt_trans Real.zero_lt_one hu
  have hkPos : (0 : Real) < k := by exact_mod_cast hk
  have hPowers : u^((k : Real) - 1) * (u^(k : Real))^(-(n : Real) - 1) =
      u^(-((k : Real) * n) - 1) := by
    rw [<- Real.rpow_mul huPos.le, <- Real.rpow_add huPos]
    congr 1
    ring
  unfold robinRealWeight
  rw [Real.log_rpow huPos]
  simp only [Nat.cast_mul]
  calc
    _ = (k : Real) * (u^((k : Real) - 1) * (u^(k : Real))^(-(n : Real) - 1)) *
        (((n : Real) * ((k : Real) * Real.log u) + 1) / ((k : Real) * Real.log u)^2) := by ring
    _ = _ := by
      rw [hPowers]
      field_simp [hkPos.ne', (Real.log_pos hu).ne'] <;> ring

/-- Exact change of variable for an arbitrary root-scale integrand. -/
theorem integral_root_mul_robinRealWeight
    (g : Real -> Real) (n k : Nat) (hk : 0 < k) {x : Real} (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (fun t : Real =>
        g (t^(Inv.inv (k : Real))) * robinRealWeight n t) =
      Inv.inv (k : Real) * integral (volume.restrict (Ioi (x^(Inv.inv (k : Real)))))
        (fun u : Real => g u * robinRealWeight (k * n) u) := by
  have hkPos : (0 : Real) < k := by exact_mod_cast hk
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hRoot : 1 < x^(Inv.inv (k : Real)) := Real.one_lt_rpow hx (inv_pos.mpr hkPos)
  have hChange := integral_comp_rpow_Ioi_of_pos'
    (g := fun t : Real => g (t^(Inv.inv (k : Real))) * robinRealWeight n t)
    hkPos hxPos.le
  rw [<- hChange, <- integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  have huOne : 1 < u := lt_trans hRoot hu
  have huPos : 0 < u := lt_trans Real.zero_lt_one huOne
  have hRootBack : (u^(k : Real))^(Inv.inv (k : Real)) = u := by
    rw [<- Real.rpow_mul huPos.le]
    have hCancel : (k : Real) * Inv.inv (k : Real) = 1 := by field_simp
    rw [hCancel, Real.rpow_one]
  rw [smul_eq_mul, hRootBack]
  calc
    _ = g u * ((k : Real) * u^((k : Real) - 1) * robinRealWeight n (u^(k : Real))) := by ring
    _ = _ := by rw [robinRealWeight_rpow_pullback n k hk huOne]; ring

theorem integrableOn_rpow_mul_robinRealWeight
    {n : Nat} {r x : Real} (hx : 1 < x) (hr : r < n) :
    IntegrableOn (fun t : Real => t^r * robinRealWeight n t) (Ioi x) := by
  have hRaw := (integrableOn_cpow_mul_robinRealWeight (rho := (r : Complex)) hx hr).norm
  apply IntegrableOn.congr_fun hRaw _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans Real.zero_lt_one (lt_trans hx ht)),
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (robinRealWeight_nonneg (lt_trans hx ht))]
  rfl

theorem integral_rpow_mul_robinRealWeight
    (n : Nat) (r : Real) {x : Real} (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (fun t : Real => t^r * robinRealWeight n t) =
      (robinZeroKernel n (r : Complex) x).re := by
  have hEq : robinZeroKernel n (r : Complex) x =
      ((integral (volume.restrict (Ioi x)) (fun t : Real => t^r * robinRealWeight n t) : Real) : Complex) := by
    rw [robinZeroKernel_eq_integral_cpow_weight n (r : Complex) hx, <- integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (lt_trans Real.zero_lt_one (lt_trans hx ht)).le]
  rw [hEq, Complex.ofReal_re]

theorem inv_nat_lt_nat_of_two_le
    {n k : Nat} (hn : 1 <= n) (hk : 2 <= k) : Inv.inv (k : Real) < n := by
  have hkGt : (1 : Real) < k := by exact_mod_cast (show 1 < k by omega)
  have hnReal : (1 : Real) <= n := by exact_mod_cast hn
  have hInv : Inv.inv (k : Real) < 1 := by
    simpa only [one_div, inv_one] using one_div_lt_one_div_of_lt Real.zero_lt_one hkGt
  exact lt_of_lt_of_le hInv hnReal

theorem integrableOn_psi_root_mul_robinRealWeight
    {n k : Nat} (hn : 1 <= n) (hk : 2 <= k) {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real =>
      Chebyshev.psi (t^(Inv.inv (k : Real))) * robinRealWeight n t) (Ioi x) := by
  have hMain := integrableOn_rpow_mul_robinRealWeight hx (inv_nat_lt_nat_of_two_le hn hk)
  have hPsiMeas : Measurable (fun t : Real => Chebyshev.psi (t^(Inv.inv (k : Real)))) :=
    Chebyshev.psi_mono.measurable.comp (by fun_prop)
  have hWeightMeas : Measurable (robinRealWeight n) := by unfold robinRealWeight; fun_prop
  apply Integrable.mono' (hMain.const_mul (Real.log 4 + 4))
    (hPsiMeas.mul hWeightMeas).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htOne : 1 < t := lt_trans hx ht
  have htNonneg : 0 <= t := le_of_lt (lt_trans Real.zero_lt_one htOne)
  have hWeight := robinRealWeight_nonneg (n := n) htOne
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Chebyshev.psi_nonneg _) hWeight)]
  calc
    _ <= ((Real.log 4 + 4) * t^(Inv.inv (k : Real))) * robinRealWeight n t :=
      mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg htNonneg _)) hWeight
    _ = _ := by ring

/-- Each complete root-scale prime-power tail is an elementary real-power
kernel plus a weighted psi error whose bound is already proved. -/
theorem integral_psi_root_mul_robinRealWeight_eq
    {n k : Nat} (hn : 1 <= n) (hk : 2 <= k) {x : Real} (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (fun t : Real =>
        Chebyshev.psi (t^(Inv.inv (k : Real))) * robinRealWeight n t) =
      (robinZeroKernel n ((Inv.inv (k : Real)) : Complex) x).re +
        Inv.inv (k : Real) * robinPsiWeightedErrorIntegral (k * n) (x^(Inv.inv (k : Real))) := by
  have hPsi := integrableOn_psi_root_mul_robinRealWeight hn hk hx
  have hMain := integrableOn_rpow_mul_robinRealWeight hx (inv_nat_lt_nat_of_two_le hn hk)
  have hError : IntegrableOn (fun t : Real =>
      (Chebyshev.psi (t^(Inv.inv (k : Real))) - t^(Inv.inv (k : Real))) * robinRealWeight n t) (Ioi x) := by
    apply IntegrableOn.congr_fun (hPsi.sub hMain) _ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.sub_apply]
    ring
  calc
    _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
        t^(Inv.inv (k : Real)) * robinRealWeight n t) +
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Chebyshev.psi (t^(Inv.inv (k : Real))) - t^(Inv.inv (k : Real))) * robinRealWeight n t) := by
      rw [<- integral_add hMain hError]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      ring
    _ = _ := by
      rw [integral_rpow_mul_robinRealWeight n _ hx,
        integral_root_mul_robinRealWeight (fun u : Real => Chebyshev.psi u - u) n k (by omega) hx]
      simp only [Complex.ofReal_inv, robinPsiWeightedErrorIntegral]

def robinPrimePowerWeightedTail (n : Nat) (x : Real) : Real :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    (Chebyshev.psi t - Chebyshev.theta t) * robinRealWeight n t)

theorem integrableOn_robinPrimePowerWeightedTail
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real =>
      (Chebyshev.psi t - Chebyshev.theta t) * robinRealWeight n t) (Ioi x) := by
  have hTwo := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (2 : Nat)) hx
  have hThree := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (3 : Nat)) hx
  have hFive := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (5 : Nat)) hx
  have hWeightMeas : Measurable (robinRealWeight n) := by unfold robinRealWeight; fun_prop
  apply Integrable.mono' ((hTwo.add hThree).add hFive)
    (((Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable).mul hWeightMeas).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hWeight := robinRealWeight_nonneg (n := n) (lt_trans hx ht)
  dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t)) hWeight)]
  simpa only [add_mul, Nat.cast_ofNat] using
    mul_le_mul_of_nonneg_right (Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi t) hWeight

theorem three_root_integrals_le_robinPrimePowerWeightedTail
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (fun t : Real => Chebyshev.psi (t^(Inv.inv (2 : Real))) * robinRealWeight n t) +
      integral (volume.restrict (Ioi x)) (fun t : Real => Chebyshev.psi (t^(Inv.inv (3 : Real))) * robinRealWeight n t) +
      integral (volume.restrict (Ioi x)) (fun t : Real => Chebyshev.psi (t^(Inv.inv (7 : Real))) * robinRealWeight n t) <=
        robinPrimePowerWeightedTail n x := by
  have hTwo := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (2 : Nat)) hx
  have hThree := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (3 : Nat)) hx
  have hSeven := integrableOn_psi_root_mul_robinRealWeight hn (by norm_num : 2 <= (7 : Nat)) hx
  have hAdd := integral_add (hTwo.add hThree) hSeven
  simp only [Pi.add_apply] at hAdd
  rw [integral_add hTwo hThree] at hAdd
  norm_num at hAdd
  norm_num
  have hMono : integral (volume.restrict (Ioi x)) (fun t : Real =>
      Chebyshev.psi (t^(Inv.inv (2 : Real))) * robinRealWeight n t +
      Chebyshev.psi (t^(Inv.inv (3 : Real))) * robinRealWeight n t +
      Chebyshev.psi (t^(Inv.inv (7 : Real))) * robinRealWeight n t) <=
      robinPrimePowerWeightedTail n x := by
    unfold robinPrimePowerWeightedTail
    apply integral_mono_ae ((hTwo.add hThree).add hSeven) (integrableOn_robinPrimePowerWeightedTail hn hx)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp only [Pi.add_apply]
    have htNonneg : 0 <= t := le_of_lt (lt_trans Real.zero_lt_one (lt_trans hx ht))
    simpa only [add_mul, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_right (Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi htNonneg)
        (robinRealWeight_nonneg (n := n) (lt_trans hx ht))
  norm_num at hMono
  exact hAdd.symm.trans_le hMono

end

end Robin1984
