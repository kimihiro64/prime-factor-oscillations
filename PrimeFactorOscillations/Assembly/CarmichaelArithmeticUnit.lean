/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelMovingWindow
import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeDivisorKernel
import PrimeFactorOscillations.Assembly.DetectorPackets.RationalInverseLine

/-!
# Arithmetic spatial unit and the native inverse coefficients

The spatial argument u=1 is distinct from the ideal index I=1, the origin
u=0 and the additive Fourier frequency zero. Its compensated value retains
the complete signed ideal coefficients. Rational Mobius reconstruction must
also retain the plain companion and the outer rational coprime correction.
No new estimate of the Abel unit C_G or zero-free boundary is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelArithmeticUnit
open OAI OAI.SevenEighths
open scoped Classical
local notation "Eis" => ConcretePrimeRowBridge.O

variable (F : Finset (Ideal Eis))
variable (hFpos : forall I, Membership.mem F I -> Not (I = Bot.bot))
variable (hFgood : forall I, Membership.mem F I ->
  forall P, Membership.mem (UniqueFactorizationMonoid.normalizedFactors I) P ->
    Not (Membership.mem P ConcretePrimeRowBridge.goodLambda))

private theorem ideal_row_at_one (I : Ideal Eis) :
    ConcretePrimeRowBridge.idealSexticRow F hFpos hFgood I 1 = 1 := by
  unfold ConcretePrimeRowBridge.idealSexticRow
    ActualEisensteinCubic.finiteSquarefreeRow
  apply Finset.prod_eq_one
  intro i _
  simp only [map_one]

theorem compensated_native_unit_value {q : Nat} (chi : DirichletCharacter Complex q)
    (WA WB : Nat -> Complex) (c : Complex) :
    ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WA 1 -
      c * ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WB 1 =
      F.sum (fun I => ShortDraftHeckeBridge.baseChangeWeight chi I *
        (WA (Ideal.absNorm I) - c * WB (Ideal.absNorm I))) := by
  rw [<- CarmichaelMovingWindow.idealRowSum_compensation F hFpos hFgood chi WA WB c 1]
  unfold ConcretePrimeRowBridge.idealRowSum
  simp_rw [ideal_row_at_one F hFpos hFgood, mul_one]

private theorem companion_inverse {r : Nat} (psi : DirichletCharacter Complex r) :
    ShortDraftHeckeBridge.invCharAF psi *
        toArithmeticFunction (fun n : Nat => psi (n : ZMod r)) = 1 := by
  classical
  ext n
  by_cases hn : n = 0
  . subst n
    simp
  have hFactor :
      (ShortDraftHeckeBridge.invCharAF psi *
        toArithmeticFunction (fun k : Nat => psi (k : ZMod r))) n =
      psi (n : ZMod r) *
        (((ArithmeticFunction.moebius *
          (ArithmeticFunction.zeta : ArithmeticFunction Int)) n : Int) : Complex) := by
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
      Int.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hMem := Nat.mem_divisorsAntidiagonal.mp hp
    have hprod : Not (p.1 * p.2 = 0) := by
      rw [hMem.1]
      exact hn
    have ha := (mul_ne_zero_iff.mp hprod).1
    have hb := (mul_ne_zero_iff.mp hprod).2
    have hz :
        (ArithmeticFunction.zeta : ArithmeticFunction Int) p.2 = 1 := by
      change ((ArithmeticFunction.zeta p.2 : Nat) : Int) = 1
      simp only [ArithmeticFunction.zeta_apply, ite_eq_right hb, Nat.cast_one]
    have hpsi :
        psi (p.1 : ZMod r) * psi (p.2 : ZMod r) = psi (n : ZMod r) := by
      rw [<- map_mul, <- Nat.cast_mul, hMem.1]
    rw [ShortDraftHeckeBridge.invCharAF_apply psi ha]
    change psi (p.1 : ZMod r) * (ArithmeticFunction.moebius p.1 : Complex) *
        (if p.2 = 0 then 0 else psi (p.2 : ZMod r)) =
      psi (n : ZMod r) *
        ((ArithmeticFunction.moebius p.1 *
          (ArithmeticFunction.zeta : ArithmeticFunction Int) p.2 : Int) : Complex)
    rw [ite_eq_right hb, hz, mul_one, <- hpsi]
    ring
  rw [hFactor]
  have hOne := congrArg (fun f : ArithmeticFunction Int => ((f n : Int) : Complex))
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [hOne]
  by_cases h1 : n = 1
  . subst n
    simp
  . simp only [ArithmeticFunction.one_apply, ite_eq_right h1, Int.cast_zero, mul_zero]

theorem normFiber_companion_recovery {q : Nat} (chi : DirichletCharacter Complex q)
    (n : Nat) :
    LSeries.convolution
        (ShortDraftHeckeBridge.normFiberCoeff (ShortDraftHeckeBridge.baseChangeWeight chi))
        (fun k : Nat => ShortDraftHeckeBridge.baseChangeChar chi (k : ZMod (q * 3))) n =
      chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex) := by
  classical
  let psi := ShortDraftHeckeBridge.baseChangeChar chi
  let f := ShortDraftHeckeBridge.normFiberCoeff (ShortDraftHeckeBridge.baseChangeWeight chi)
  have hAF : toArithmeticFunction f = ShortDraftHeckeBridge.pairAF chi psi := by
    ext k
    by_cases hk : k = 0
    . subst k
      simp [toArithmeticFunction]
    . change (if k = 0 then 0 else f k) = ShortDraftHeckeBridge.pairAF chi psi k
      rw [ite_eq_right hk, ShortDraftHeckeBridge.pairAF_eq_pairInverseCoeff]
      exact ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff chi k hk
  have hConv :
      LSeries.convolution f (fun k : Nat => psi (k : ZMod (q * 3))) n =
      (toArithmeticFunction f *
        toArithmeticFunction (fun k : Nat => psi (k : ZMod (q * 3)))) n := by
    rw [LSeries.convolution_def, ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl
    intro p hp
    have hMem := Nat.mem_divisorsAntidiagonal.mp hp
    have hprod : Not (p.1 * p.2 = 0) := by
      rw [hMem.1]
      exact hMem.2
    have ha := (mul_ne_zero_iff.mp hprod).1
    have hb := (mul_ne_zero_iff.mp hprod).2
    change f p.1 * psi (p.2 : ZMod (q * 3)) =
      (if p.1 = 0 then 0 else f p.1) *
        (if p.2 = 0 then 0 else psi (p.2 : ZMod (q * 3)))
    rw [ite_eq_right ha, ite_eq_right hb]
  change LSeries.convolution f (fun k : Nat => psi (k : ZMod (q * 3))) n = _
  rw [hConv, hAF]
  change (ShortDraftHeckeBridge.invCharAF chi * ShortDraftHeckeBridge.invCharAF psi *
    toArithmeticFunction (fun k : Nat => psi (k : ZMod (q * 3)))) n = _
  rw [mul_assoc, companion_inverse, mul_one]
  by_cases hn : n = 0
  . subst n
    simp
  . exact ShortDraftHeckeBridge.invCharAF_apply chi hn

def normCompanionAmplitude {q : Nat} (S : Finset Nat)
    (chi : DirichletCharacter Complex q) (W : Nat -> Complex) (d : Nat) : Complex :=
  S.sum (fun n => if Dvd.dvd d n then
    n.divisorsAntidiagonal.sum (fun p =>
      ShortDraftHeckeBridge.normFiberCoeff (ShortDraftHeckeBridge.baseChangeWeight chi) p.1 *
        ShortDraftHeckeBridge.baseChangeChar chi (p.2 : ZMod (q * 3)) * W n)
    else 0)

private theorem normCompanionAmplitude_eq {q : Nat} (S : Finset Nat)
    (chi : DirichletCharacter Complex q) (W : Nat -> Complex) (d : Nat) :
    normCompanionAmplitude S chi W d =
      CoprimeDivisorKernel.amplitude S
        (fun n => chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex) * W n) d := by
  unfold normCompanionAmplitude CoprimeDivisorKernel.amplitude
  apply Finset.sum_congr rfl
  intro n _
  by_cases hd : Dvd.dvd d n
  . simp only [ite_eq_left hd]
    rw [<- Finset.sum_mul]
    have hRec := normFiber_companion_recovery chi n
    rw [LSeries.convolution_def] at hRec
    exact congrArg (fun z : Complex => z * W n) hRec
  . simp only [ite_eq_right hd]

theorem compensated_coprime_unit {q : Nat} (S : Finset Nat) (N : Nat)
    (hs : forall n, Membership.mem S n -> And (0 < n) (n <= N))
    (chi : DirichletCharacter Complex q) (WA WB : Nat -> Complex) (c : Complex) :
    let a : Nat -> Complex := fun n =>
      chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex) * (WA n - c * WB n)
    (S.sum (fun n => S.sum (fun m =>
      if Nat.Coprime n m then a n * star (a m) else 0))).re =
      (Finset.range (N + 1)).sum (fun d => (ArithmeticFunction.moebius d : Real) *
        norm (normCompanionAmplitude S chi (fun n => WA n - c * WB n) d) ^ 2) := by
  dsimp only
  simpa only [normCompanionAmplitude_eq] using
    CoprimeDivisorKernel.coprime_energy_real S
      (fun n => chi (n : ZMod q) * (ArithmeticFunction.moebius n : Complex) *
        (WA n - c * WB n)) N hs

end PrimeFactorOscillations.CarmichaelArithmeticUnit
