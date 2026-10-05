/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/Equivalence/WeightedKernelBounds.lean
Original source lines 27-92. Apache-2.0.
Statements and proof bodies retained; only the required declaration block is selected.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.RobinWeightedIntegral

/-!
# Signed real-power kernel recurrence

Part of the written RH negative-envelope argument.
-/

namespace Robin1984

noncomputable section

open MeasureTheory Set

theorem robinCpowLogTail_ofReal_eq
    (a : Real) (k : Nat) {x : Real} (hx : 1 < x) :
    robinCpowLogTail (a : Complex) k x =
      ((integral (volume.restrict (Ioi x)) (fun t : Real =>
        t^(a - 1) * Inv.inv ((Real.log t)^k)) : Real) : Complex) := by
  unfold robinCpowLogTail
  rw [<- integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have htPos : 0 < t := lt_trans Real.zero_lt_one (lt_trans hx ht)
  rw [Complex.ofReal_mul, Complex.ofReal_cpow htPos.le]
  push_cast
  rfl

theorem robinCpowLogTail_ofReal_re_nonneg
    (a : Real) (k : Nat) {x : Real} (hx : 1 < x) :
    0 <= (robinCpowLogTail (a : Complex) k x).re := by
  rw [robinCpowLogTail_ofReal_eq a k hx, Complex.ofReal_re]
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  have htOne : 1 < t := lt_trans hx ht
  have htPos : 0 < t := lt_trans Real.zero_lt_one htOne
  exact mul_nonneg (Real.rpow_nonneg htPos.le _)
    (inv_nonneg.mpr (pow_nonneg (Real.log_pos htOne).le k))

theorem robinCpowLogTail_ofReal_re_le
    {a : Real} (ha : a < 0) (k : Nat) {x : Real} (hx : 1 < x) :
    (robinCpowLogTail (a : Complex) k x).re <=
      (-x^a / a) * Inv.inv ((Real.log x)^k) := by
  exact (Complex.re_le_norm _).trans
    (norm_robinCpowLogTail_le hx (show (a : Complex).re < 0 from ha) k)

theorem robinCpowLogTail_ofReal_recurrence
    {a : Real} (ha : a < 0) (k : Nat) {x : Real} (hx : 1 < x) :
    (robinCpowLogTail (a : Complex) k x).re =
      -Inv.inv a * x^a * Inv.inv ((Real.log x)^k) +
        ((k : Real) * Inv.inv a) * (robinCpowLogTail (a : Complex) (k + 1) x).re := by
  have hRaw := robinCpowLogTail_recurrence hx (show (a : Complex).re < 0 from ha) k
  have hPow : (x : Complex)^(a : Complex) = ((x^a : Real) : Complex) :=
    (Complex.ofReal_cpow (lt_trans Real.zero_lt_one hx).le a).symm
  rw [hPow, <- Complex.ofReal_inv] at hRaw
  have hRe := congrArg Complex.re hRaw
  simpa only [Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul, sub_zero, neg_zero,
    zero_add, add_zero] using hRe

/-- The signed next logarithmic tail is retained before taking any bound. -/
theorem robinZeroKernel_ofReal_eq_main_add_signed_tail
    (n : Nat) {r : Real} (hr : r < n) {x : Real} (hx : 1 < x) :
    (robinZeroKernel n (r : Complex) x).re =
      -(n : Real) * Inv.inv (r - n) * x^(r - n) * Inv.inv (Real.log x) +
        ((n : Real) * Inv.inv (r - n) + 1) *
          (robinCpowLogTail ((r - n : Real) : Complex) 2 x).re := by
  have hKernel := robinZeroKernel_eq_nat_mul_tail_one_add_tail_two
    (n := n) (rho := (r : Complex)) hx (show (r : Complex).re < n from hr)
  have hCast : (r : Complex) - (n : Complex) = ((r - n : Real) : Complex) := by push_cast; rfl
  rw [hCast] at hKernel
  have hKernelRe := congrArg Complex.re hKernel
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] at hKernelRe
  have hRec := robinCpowLogTail_ofReal_recurrence (show r - n < 0 by linarith) 1 hx
  simp only [Nat.cast_one, pow_one, one_mul] at hRec
  rw [hKernelRe, hRec]
  ring

end

end Robin1984
