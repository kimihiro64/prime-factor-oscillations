/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.Mellin.ExponentialSmoothing
import PrimeFactorOscillations.Assembly.CarmichaelDirichletProduct
import PrimeFactorOscillations.Helpers.DirichletCompensatedProbe

/-!
# Physical quartic reference and native spectrum symmetry

Proves the physical change of variables with its derivative factor and the
inverse-character multiplicity symmetry. Convergence hypotheses remain explicit.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CarmichaelWindowTransfer

open MeasureTheory
open CarmichaelIntegralSpectrum CarmichaelCorrelationSpectrum

theorem trivialOnKernel_inv_iff {q : Nat} [NeZero q]
    (T : Finset Nat.Primes) (chi : DirichletCharacter Complex q) :
    trivialOnKernel T (Inv.inv chi) <-> trivialOnKernel T chi := by
  constructor
  . intro h g
    have hh := h g
    change (Inv.inv chi) (g.val : ZMod q) = 1 at hh
    rw [<- MulChar.star_apply'] at hh
    have he := congrArg star hh
    change chi (g.val : ZMod q) = 1
    simpa only [star_star, star_one] using he
  . intro h g
    change (Inv.inv chi) (g.val : ZMod q) = 1
    rw [<- MulChar.star_apply']
    have hh := h g
    change chi (g.val : ZMod q) = 1 at hh
    rw [hh, star_one]

theorem multiplicity_inv {q : Nat} [NeZero q]
    (S : Finset Nat.Primes) (chi : DirichletCharacter Complex q) :
    multiplicity S (Inv.inv chi) = multiplicity S chi := by
  classical
  simp only [CarmichaelIntegralSpectrum.multiplicity, trivialOnKernel_inv_iff]

def quarticPhysicalReference (F : Real -> Complex) (T : Real) : Complex :=
  (T : Complex) ^ (-3 : Complex) * F (T ^ 4)

def quarticPhysicalProbe (F : Real -> Complex) (T : Real) : Complex :=
  F T - quarticPhysicalReference F T

theorem quarticPhysicalReference_mellin (F : Real -> Complex) (s : Complex) :
    mellin (quarticPhysicalReference F) (-s) =
      HSMul.hSMul ((4 : Real) ^ (-1 : Int))
        (mellin F (-DirichletCompensatedProbe.quarticMap s)) := by
  have hp := mellin_comp_rpow F (-s + (-3 : Complex)) (4 : Real)
  have hpow : (fun T : Real => F (T ^ (4 : Real))) =
      (fun T : Real => F (T ^ 4)) := by
    funext T
    exact congrArg F (Real.rpow_natCast T 4)
  rw [hpow] at hp
  have he : (-s + (-3 : Complex)) / (4 : Complex) =
      -DirichletCompensatedProbe.quarticMap s := by
    dsimp [DirichletCompensatedProbe.quarticMap]
    ring
  have hc := mellin_cpow_smul (fun T : Real => F (T ^ 4)) (-s) (-3 : Complex)
  simp only [smul_eq_mul] at hc
  change mellin (fun T : Real => (T : Complex) ^ (-3 : Complex) * F (T ^ 4)) (-s) = _
  rw [hc]
  simpa only [Complex.ofReal_ofNat, abs_of_pos (by norm_num :
    (0 : Real) < 4), he, zpow_neg_one] using hp

theorem quarticPhysicalReference_convergent (F : Real -> Complex) (s : Complex)
    (hF : MellinConvergent F (-DirichletCompensatedProbe.quarticMap s)) :
    MellinConvergent (quarticPhysicalReference F) (-s) := by
  have he : (-s + (-3 : Complex)) / (4 : Complex) =
      -DirichletCompensatedProbe.quarticMap s := by
    dsimp [DirichletCompensatedProbe.quarticMap]
    ring
  have hr : MellinConvergent (fun T : Real => F (T ^ (4 : Real)))
      (-s + (-3 : Complex)) :=
    (MellinConvergent.comp_rpow (by norm_num : Not ((4 : Real) = 0))).2
      (by simpa only [Complex.ofReal_ofNat, he] using hF)
  have hpow : (fun T : Real => F (T ^ (4 : Real))) =
      (fun T : Real => F (T ^ 4)) := by
    funext T
    exact congrArg F (Real.rpow_natCast T 4)
  rw [hpow] at hr
  have hc := (MellinConvergent.cpow_smul (f := fun T : Real => F (T ^ 4))
    (s := -s) (a := (-3 : Complex))).2 hr
  change MellinConvergent (fun T : Real =>
    (T : Complex) ^ (-3 : Complex) * F (T ^ 4)) (-s)
  simpa only [smul_eq_mul] using hc

theorem quarticPhysicalProbe_mellin (F : Real -> Complex) (s : Complex)
    (hF : MellinConvergent F (-s))
    (hRef : MellinConvergent F (-DirichletCompensatedProbe.quarticMap s)) :
    mellin (quarticPhysicalProbe F) (-s) =
      mellin F (-s) - HSMul.hSMul ((4 : Real) ^ (-1 : Int))
        (mellin F (-DirichletCompensatedProbe.quarticMap s)) := by
  have hSub := (hasMellin_sub hF (quarticPhysicalReference_convergent F s hRef)).2
  change mellin (quarticPhysicalProbe F) (-s) = _ at hSub
  rw [quarticPhysicalReference_mellin] at hSub
  exact hSub

end PrimeFactorOscillations.CarmichaelWindowTransfer
