/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPrimeProductCriterion

/-!
# The Eisenstein norm profile and its corrected Nicolas criterion

The local law is that of a^2-a*b+b^2 for uniformly distributed ordered
integer pairs. Its finite Euler product is the ordinary inverse Mertens
product times the truncated character product for chi modulo 3.
Retaining that character correction gives an exact ordinary-RH criterion.
No assertion about the sign of the uncorrected profile is made here.
The residue-count interpretation and the evaluation of L(1,chi) are supplied
in the accompanying ordinary proof; the finite identities and RH transfer
below are kernel-checked for the explicitly defined local law and constant.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations
open Filter Robin1984

def eisensteinPrimeCharacter (p : Nat) : Real :=
  if p % 3 = 0 then 0 else if p % 3 = 1 then 1 else -1

def eisensteinNormLocalProbability (p : Nat) : Real :=
  if p % 3 = 0 then 1 / (p : Real)
  else if p % 3 = 1 then 2 / (p : Real) - 1 / (p : Real) ^ 2
  else 1 / (p : Real) ^ 2

theorem eisensteinNormLocalProbability_complement {p : Nat} (hp : 0 < p) :
    1 - eisensteinNormLocalProbability p =
      (1 - 1 / (p : Real)) * (1 - eisensteinPrimeCharacter p / (p : Real)) := by
  have hp0 : Not ((p : Real) = 0) := by exact_mod_cast hp.ne'
  unfold eisensteinNormLocalProbability eisensteinPrimeCharacter
  split_ifs <;> field_simp <;> ring

theorem eisensteinPrimeCharacter_le_one (p : Nat) :
    eisensteinPrimeCharacter p <= 1 := by
  unfold eisensteinPrimeCharacter
  split_ifs <;> norm_num

theorem eisensteinCharacterFactor_pos {p : Nat} (hp : Nat.Prime p) :
    0 < 1 - eisensteinPrimeCharacter p / (p : Real) := by
  have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : Real) < p := by linarith
  have hle := div_le_div_of_nonneg_right (eisensteinPrimeCharacter_le_one p) hp0.le
  have hlt : (1 : Real) / p < 1 := (div_lt_one hp0).mpr hp1
  linarith

theorem eisensteinNormComplement_pos {p : Nat} (hp : Nat.Prime p) :
    0 < 1 - eisensteinNormLocalProbability p := by
  rw [eisensteinNormLocalProbability_complement hp.pos]
  have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : Real) < p := by linarith
  exact mul_pos (sub_pos.mpr ((div_lt_one hp0).mpr hp1))
    (eisensteinCharacterFactor_pos hp)

def eisensteinNormEulerProduct (N : Nat) : Real :=
  (Nat.primesLE N).prod (fun p => (1 - eisensteinNormLocalProbability p) ^ (-1 : Int))

def eisensteinCharacterProduct (N : Nat) : Real :=
  (Nat.primesLE N).prod (fun p => (1 - eisensteinPrimeCharacter p / (p : Real)) ^ (-1 : Int))

def eisensteinLValue : Real := Real.pi / (3 * Real.sqrt 3)

def eisensteinNormConstant : Real :=
  Real.exp Real.eulerMascheroniConstant * eisensteinLValue

theorem eisensteinLValue_pos : 0 < eisensteinLValue := by
  unfold eisensteinLValue
  positivity

theorem eisensteinNormConstant_pos : 0 < eisensteinNormConstant :=
  mul_pos (Real.exp_pos _) eisensteinLValue_pos

theorem eisensteinCharacterProduct_pos (N : Nat) : 0 < eisensteinCharacterProduct N := by
  apply Finset.prod_pos
  intro p hp
  exact zpow_pos (eisensteinCharacterFactor_pos (Nat.mem_primesLE.mp hp).2) _

theorem eisensteinNormEulerProduct_pos (N : Nat) : 0 < eisensteinNormEulerProduct N := by
  apply Finset.prod_pos
  intro p hp
  exact zpow_pos (eisensteinNormComplement_pos (Nat.mem_primesLE.mp hp).2) _

theorem eisensteinNormEulerProduct_factorization (N : Nat) :
    eisensteinNormEulerProduct N =
      eisensteinCharacterProduct N / nicolasMertensProduct (N : Real) := by
  classical
  unfold eisensteinNormEulerProduct eisensteinCharacterProduct nicolasMertensProduct
  rw [Nat.floor_natCast, <- Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [eisensteinNormLocalProbability_complement (Nat.mem_primesLE.mp hp).2.pos]
  simp only [zpow_neg_one, mul_inv_rev, div_eq_mul_inv]

def eisensteinCharacterCorrection (N : Nat) : Real :=
  Real.log eisensteinLValue - Real.log (eisensteinCharacterProduct N)

def eisensteinNormLogError (N : Nat) : Real :=
  Real.log eisensteinNormConstant + Real.log (Real.log (Chebyshev.theta (N : Real))) -
    Real.log (eisensteinNormEulerProduct N)

/-- The character tail is retained exactly, without a GRH or tail-size premise. -/
theorem eisensteinNormLogError_corrected (N : Nat)
    (hTheta : 1 < Chebyshev.theta (N : Real)) :
    eisensteinNormLogError N - eisensteinCharacterCorrection N =
      nicolasLogMertensOscillation (N : Real) := by
  unfold eisensteinNormLogError eisensteinCharacterCorrection
  rw [eisensteinNormEulerProduct_factorization,
    Real.log_div (eisensteinCharacterProduct_pos N).ne'
      (Robin1984.nicolasMertensProduct_pos (N : Real)).ne']
  unfold eisensteinNormConstant nicolasLogMertensOscillation nicolasFunction
  rw [Real.log_mul (Real.exp_pos _).ne' eisensteinLValue_pos.ne',
    Real.log_mul (mul_pos (Real.exp_pos _) (Real.log_pos hTheta)).ne'
      (Robin1984.nicolasMertensProduct_pos (N : Real)).ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.log_pos hTheta).ne', Real.log_exp]
  ring

theorem riemannHypothesis_iff_eventually_eisensteinNormLogError_lt_correction :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      eisensteinNormLogError N < eisensteinCharacterCorrection N) atTop := by
  rw [riemannHypothesis_iff_eventually_nicolasLog_nat_neg]
  apply Filter.eventually_congr
  filter_upwards [tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1] with N hTheta
  rw [<- eisensteinNormLogError_corrected N hTheta, sub_lt_zero]

def eisensteinNormCorrectedProduct (N : Nat) : Real :=
  eisensteinLValue / eisensteinCharacterProduct N * eisensteinNormEulerProduct N

theorem eisensteinNormCorrectedProduct_exact (N : Nat) :
    eisensteinNormCorrectedProduct N =
      eisensteinLValue / nicolasMertensProduct (N : Real) := by
  unfold eisensteinNormCorrectedProduct
  rw [eisensteinNormEulerProduct_factorization]
  field_simp [(eisensteinCharacterProduct_pos N).ne']

theorem eisensteinNormCorrectedProduct_criterion (N : Nat)
    (hTheta : 1 < Chebyshev.theta (N : Real)) :
    eisensteinNormConstant * Real.log (Chebyshev.theta (N : Real)) <
      eisensteinNormCorrectedProduct N <->
      nicolasLogMertensOscillation (N : Real) < 0 := by
  rw [eisensteinNormCorrectedProduct_exact, eisensteinNormConstant]
  have hM := Robin1984.nicolasMertensProduct_pos (N : Real)
  have hL := eisensteinLValue_pos
  have hf := nicolasFunction_pos_of_theta_gt_one hTheta
  have hAlgebra : Real.exp Real.eulerMascheroniConstant * eisensteinLValue *
      Real.log (Chebyshev.theta (N : Real)) * nicolasMertensProduct (N : Real) =
      eisensteinLValue * nicolasFunction (N : Real) := by unfold nicolasFunction; ring
  have hCancel : (eisensteinLValue / nicolasMertensProduct (N : Real)) *
      nicolasMertensProduct (N : Real) = eisensteinLValue := by field_simp
  have hIff : Real.exp Real.eulerMascheroniConstant * eisensteinLValue *
      Real.log (Chebyshev.theta (N : Real)) <
        eisensteinLValue / nicolasMertensProduct (N : Real) <->
        nicolasFunction (N : Real) < 1 := by
    constructor
    . intro h
      have hm := mul_lt_mul_of_pos_right h hM
      rw [hAlgebra, hCancel] at hm
      nlinarith only [hm, hL]
    . intro h
      by_contra hNot
      have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hNot) hM.le
      rw [hAlgebra, hCancel] at hm
      nlinarith only [hm, hL, h]
  rw [hIff]
  change nicolasFunction (N : Real) < 1 <-> Real.log (nicolasFunction (N : Real)) < 0
  calc
    _ <-> Real.exp (Real.log (nicolasFunction (N : Real))) < Real.exp 0 := by
      rw [Real.exp_log hf, Real.exp_zero]
    _ <-> _ := Real.exp_lt_exp

theorem riemannHypothesis_iff_eventually_eisensteinNormCorrectedProduct :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      eisensteinNormConstant * Real.log (Chebyshev.theta (N : Real)) <
        eisensteinNormCorrectedProduct N) atTop := by
  rw [riemannHypothesis_iff_eventually_nicolasLog_nat_neg]
  apply Filter.eventually_congr
  filter_upwards [tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1] with N hTheta
  exact (eisensteinNormCorrectedProduct_criterion N hTheta).symm

def eisensteinNormPowerDiscrepancy (N : Nat) : Real :=
  (N : Real) * Real.log N *
    (eisensteinNormLogError N - eisensteinCharacterCorrection N)

theorem eisensteinNormPowerDiscrepancy_exact (N : Nat)
    (hTheta : 1 < Chebyshev.theta (N : Real)) :
    eisensteinNormPowerDiscrepancy N =
      (N : Real) * Real.log N * nicolasLogMertensOscillation (N : Real) := by
  rw [eisensteinNormPowerDiscrepancy, eisensteinNormLogError_corrected N hTheta]

end PrimeFactorOscillations
