/-
Compatibility inputs for the maintained Robin1984 source port.
Licensed under Apache-2.0; see the repository LICENSE.
RS_prime.L and meisselMertensConstant preserve the definitions from PNT
f8f58c749d6cde8a641348fcd5e4702993651cd6, RosserSchoenfeldPrime.lean,
blob 61f6dbce0abfb6eaf0798aeccee36b5b5818af54, lines 626-627 and 811.
The summand sign proof is adapted from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee,
MertensWeightedBound.lean, blob a75ddf611ab6815ad4c79f1d727a14ea7f9c2ea6, lines 24-33.
No source compiler version is inferred from the 4.34.0 execution environment.
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.PrimeReciprocalTail
import VendorPrimeNumberTheoremAnd.Mertens

/-!
# Canonical inputs for the Nicolas source port

Identifies the original Rosser--Schoenfeld constant with the cached Mertens
constant and proves nonnegativity of the exact finite Euler-product remainder.
The source definitions and their attribution are retained in the header.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Set

namespace RS_prime

noncomputable def L (f : Real -> Real) : Real :=
  2 * f 2 / Real.log 2 -
    integral (volume.restrict (Ioi 2))
      (fun y : Real => (Chebyshev.theta y - y) *
        deriv (fun t : Real => f t / Real.log t) y)

end RS_prime

noncomputable def meisselMertensConstant : Real :=
  -Real.log (Real.log 2) + RS_prime.L (fun x : Real => 1 / x)

namespace RS_prime

private theorem deriv_inv_div_log_eq_neg_kernel {t : Real} (ht : 1 < t) :
    deriv (fun s : Real => 1 / s / Real.log s) t =
      -(1 + Real.log t) / (t ^ 2 * (Real.log t) ^ 2) := by
  have htPos : 0 < t := lt_trans (by norm_num) ht
  have hLog : 0 < Real.log t := Real.log_pos ht
  have hDeriv := deriv_fun_inv''
    (t.hasDerivAt_mul_log htPos.ne').differentiableAt
    (mul_ne_zero htPos.ne' hLog.ne')
  have hMulDeriv :
      deriv (fun s : Real => s * Real.log s) t = 1 + Real.log t := by
    have hMul := (hasDerivAt_id t).mul (Real.hasDerivAt_log htPos.ne')
    have hMulValue := hMul.deriv
    have hFun : (id * Real.log : Real -> Real) =
        (fun s : Real => s * Real.log s) := by
      funext s
      rfl
    rw [hFun] at hMulValue
    simp only [id_eq, one_mul] at hMulValue
    rw [hMulValue]
    field_simp [htPos.ne']
    ring
  simp only [div_div, fun s : Real => one_div (s * Real.log s), hDeriv, hMulDeriv]
  field_simp [htPos.ne', hLog.ne']

theorem meisselMertensConstant_eq_mertensM :
    meisselMertensConstant = Mertens.M := by
  have hIntegral :
      integral (volume.restrict (Ioi (2 : Real)))
        (fun t : Real => (Chebyshev.theta t - t) *
          deriv (fun s : Real => 1 / s / Real.log s) t) =
      -integral (volume.restrict (Ioi (2 : Real)))
        (fun t : Real => (Chebyshev.theta t - t) * (1 + Real.log t) /
          (t ^ 2 * (Real.log t) ^ 2)) := by
    rw [<- integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [deriv_inv_div_log_eq_neg_kernel (lt_trans (by norm_num) ht)]
    ring
  have hM := PrimeFactorOscillations.mertensConstant_eq_thetaError_integral
  unfold meisselMertensConstant L
  change -Real.log (Real.log 2) +
      (2 * (1 / (2 : Real)) / Real.log 2 -
        integral (volume.restrict (Ioi (2 : Real)))
          (fun t : Real => (Chebyshev.theta t - t) *
            deriv (fun s : Real => 1 / s / Real.log s) t)) = Mertens.M
  rw [hIntegral]
  norm_num
  simpa only [one_div, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hM.symm

end RS_prime

namespace Robin1984

private theorem mertens_summand_nonpos (p : Nat) : Mertens.M_eq_summand p <= 0 := by
  classical
  unfold Mertens.M_eq_summand
  split_ifs with hp
  . have hpOne : (1 : Real) < p := by exact_mod_cast hp.one_lt
    have hpPos : (0 : Real) < p := by linarith
    have hFrac : (1 : Real) / p < 1 := (div_lt_one hpPos).mpr hpOne
    have hLog := Real.log_le_sub_one_of_pos (by linarith : (0 : Real) < 1 - 1 / p)
    linarith
  . exact le_rfl

private theorem mertens_summand_tsum_eq_euler :
    tsum Mertens.M_eq_summand = Mertens.M - Real.eulerMascheroniConstant := by
  have hTotal := Mertens.tsum_M_eq_summand_eq
  run_tac
    let gamma := String.singleton (Char.ofNat 947)
    let declaration := Lean.Name.str
      (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Mertens") gamma)
      "eq_eulerMascheroni"
    let total := Lean.mkIdent (Lean.Name.mkSimple "hTotal")
    let proofSyntax <- `(tactic| simpa only [($(Lean.mkIdent declaration))] using $total)
    Lean.Elab.Tactic.evalTactic proofSyntax

/-- The omitted nonpositive prime-logarithm terms give a nonnegative remainder
for this exact finite prefix, including its excluded zero index. -/
theorem nicolasMertensSummandRemainder_nonneg (x : Real) :
    0 <= Finset.sum (Finset.Ioc 0 (Nat.floor x)) Mertens.M_eq_summand -
      (Mertens.M - Real.eulerMascheroniConstant) := by
  have hSum := Mertens.M_eq_summable.neg.sum_le_tsum
    (Finset.Ioc 0 (Nat.floor x)) (fun p _ => neg_nonneg.mpr (mertens_summand_nonpos p))
  rw [Finset.sum_neg_distrib, tsum_neg, mertens_summand_tsum_eq_euler] at hSum
  linarith

end Robin1984
