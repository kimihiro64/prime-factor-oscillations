/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.CarmichaelPowerTrace
import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResidueDecoding

/-!
# Sharp certification of actual zeta multiplicities

The full compensated residue is an integer lattice point. One sufficiently
accurate complex observation identifies both the target and reference orders,
with no RH or multiplicity cap. A larger accuracy scale still identifies the
target order modulo the compensation power.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

open DirichletCompensatedProbe

theorem zetaCanonicalPowerResidue_eq_integerCode (d : Nat) (rho : Complex) :
    zetaCanonicalPowerResidue (d : Real) rho =
      Complex.integerResidueCode d rho
        (analyticOrderNatAt riemannZeta rho : Int)
        (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) : Int) := by
  simp [zetaCanonicalPowerResidue, Complex.integerResidueCode]

theorem zeta_power_readout_certifies_orders
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (d : Nat) (hd : 2 <= d) (rho : Complex)
    (hRe : 0 < rho.re /\ rho.re < 1) (hIm : Not (rho.im = 0))
    (hHeight : (d : Real) * ((d : Real) - 1) <= abs rho.im)
    (r observation : Complex)
    (hr : Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) (d : Real) s)
      (nhdsWithin rho (Set.compl {rho})) (nhds r))
    (A B : Nat)
    (hActual : norm (r - observation) * norm (rho + (d : Complex) - 1) <
      (d : Real) * ((d : Real) - 1) / 2)
    (hCandidate : norm (Complex.integerResidueCode d rho (A : Int) (B : Int) - observation) *
      norm (rho + (d : Complex) - 1) < (d : Real) * ((d : Real) - 1) / 2) :
    analyticOrderNatAt riemannZeta rho = A /\
      analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) = B := by
  have hdR : (1 : Real) < d := by exact_mod_cast (by omega : 1 < d)
  have hden : Not (rho + (d : Complex) - 1 = 0) := by
    intro he
    apply hIm
    simpa using congrArg Complex.im he
  have hEq := zeta_power_readout_residue_eq G hG (d : Real) hdR rho hRe hIm r hr
  rw [zetaCanonicalPowerResidue_eq_integerCode] at hEq
  rw [hEq] at hActual
  have h := Complex.integerResidueCode_unique_of_half_error d hd rho hHeight
    (analyticOrderNatAt riemannZeta rho : Int)
    (analyticOrderNatAt riemannZeta (powerMap (d : Real) rho) : Int)
    (A : Int) (B : Int) observation hden hActual hCandidate
  exact And.intro (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem zeta_power_readout_certifies_order_mod
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (d : Nat) (hd : 2 <= d) (rho : Complex)
    (hRe : 0 < rho.re /\ rho.re < 1) (hIm : Not (rho.im = 0))
    (r observation : Complex)
    (hr : Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) (d : Real) s)
      (nhdsWithin rho (Set.compl {rho})) (nhds r))
    (A B : Nat)
    (hSmall : (norm (r - observation) +
      norm (Complex.integerResidueCode d rho (A : Int) (B : Int) - observation)) *
        norm (rho + (d : Complex) - 1) < abs rho.im) :
    analyticOrderNatAt riemannZeta rho % d = A % d := by
  have hdR : (1 : Real) < d := by exact_mod_cast (by omega : 1 < d)
  have hden : Not (rho + (d : Complex) - 1 = 0) := by
    intro he
    apply hIm
    simpa using congrArg Complex.im he
  let M := analyticOrderNatAt riemannZeta rho
  let N := analyticOrderNatAt riemannZeta (powerMap (d : Real) rho)
  have hEq := zeta_power_readout_residue_eq G hG (d : Real) hdR rho hRe hIm r hr
  rw [zetaCanonicalPowerResidue_eq_integerCode] at hEq
  change r = Complex.integerResidueCode d rho (M : Int) (N : Int) at hEq
  rw [hEq] at hSmall
  have ht :
      norm (Complex.integerResidueCode d rho (M : Int) (N : Int) -
        Complex.integerResidueCode d rho (A : Int) (B : Int)) <=
      norm (Complex.integerResidueCode d rho (M : Int) (N : Int) - observation) +
        norm (Complex.integerResidueCode d rho (A : Int) (B : Int) - observation) := by
    calc
      _ = norm ((Complex.integerResidueCode d rho (M : Int) (N : Int) - observation) +
          (observation - Complex.integerResidueCode d rho (A : Int) (B : Int))) := by
        congr 1
        ring
      _ <= _ := by
        simpa only [norm_sub_rev observation (Complex.integerResidueCode d rho (A : Int) (B : Int))]
          using norm_add_le
            (Complex.integerResidueCode d rho (M : Int) (N : Int) - observation)
            (observation - Complex.integerResidueCode d rho (A : Int) (B : Int))
  have hp := (mul_le_mul_of_nonneg_right ht (norm_nonneg (rho + (d : Complex) - 1))).trans_lt hSmall
  rw [Complex.integerResidueCode_sub] at hp
  have hrel := Complex.integerResidueCode_small_forces_relation d rho
    ((M : Int) - (A : Int)) ((N : Int) - (B : Int)) hden hp
  have heInt : (M : Int) + (d : Int) * (B : Int) =
      (A : Int) + (d : Int) * (N : Int) := by
    linear_combination hrel
  have heNat : M + d * B = A + d * N := by exact_mod_cast heInt
  have hmod := congrArg (fun n : Nat => n % d) heNat
  simpa [Nat.add_mod, Nat.mul_mod] using hmod

end PrimeFactorOscillations.CarmichaelWeightedSignal

end
