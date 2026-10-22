/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.XiZeroMultiplicity

/-!
# Unconditional regrouping by distinct complex zero and analytic multiplicity

The finite value-fiber equivalence is reused, without frequency projection
or RH. Any absolutely summable canonical zero series is regrouped exactly.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

abbrev XiDistinctZero := {z : Complex // Complex.riemannXi z = 0}

noncomputable def xiDistinctZeroLift (p : RiemannXiDivisorZeroIndex) : XiDistinctZero :=
  Subtype.mk (riemannXiDivisorZeroValue p) (riemannXiDivisorZeroValue_eq_zero p)

theorem xiDistinctZero_ne_zero (z : XiDistinctZero) : Not (z.val = 0) := by
  intro hz
  have h := z.property
  rw [hz, Complex.riemannXi_zero] at h
  norm_num at h

noncomputable def xiDistinctZeroFiberEquiv (z : XiDistinctZero) :
    Equiv {p : RiemannXiDivisorZeroIndex // xiDistinctZeroLift p = z}
      (Fin (xiZeroMultiplicity z.val)) := by
  refine Equiv.trans ?_ (xiZeroFiberEquiv z.val (xiDistinctZero_ne_zero z))
  refine Equiv.mk (fun p => Subtype.mk p.val ?_) (fun p => Subtype.mk p.val ?_) ?_ ?_
  . exact congrArg (fun w : XiDistinctZero => w.val) p.property
  . exact Subtype.ext p.property
  . intro p
    rfl
  . intro p
    rfl

theorem xiDistinctZero_fiber_sum (f : Complex -> Complex) (z : XiDistinctZero) :
    tsum (fun p : {p : RiemannXiDivisorZeroIndex // xiDistinctZeroLift p = z} =>
      f (riemannXiDivisorZeroValue p.val)) =
      (xiZeroMultiplicity z.val : Complex) * f z.val := by
  classical
  let F := {p : RiemannXiDivisorZeroIndex // xiDistinctZeroLift p = z}
  let e : Equiv F (Fin (xiZeroMultiplicity z.val)) := xiDistinctZeroFiberEquiv z
  letI : Fintype F := Fintype.ofEquiv (Fin (xiZeroMultiplicity z.val)) e.symm
  have hCard : Fintype.card F = xiZeroMultiplicity z.val := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  have hPoint (p : F) : f (riemannXiDivisorZeroValue p.val) = f z.val :=
    congrArg f (congrArg (fun w : XiDistinctZero => w.val) p.property)
  change tsum (fun p : F => f (riemannXiDivisorZeroValue p.val)) = _
  rw [tsum_fintype]
  calc
    _ = Finset.sum Finset.univ (fun _ : F => f z.val) :=
      Finset.sum_congr rfl (fun p _ => hPoint p)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hCard]

theorem xiDistinctZero_weighted_hasSum
    (f : Complex -> Complex)
    (hf : Summable (fun p : RiemannXiDivisorZeroIndex => f (riemannXiDivisorZeroValue p))) :
    HasSum (fun z : XiDistinctZero => (xiZeroMultiplicity z.val : Complex) * f z.val)
      (tsum (fun p : RiemannXiDivisorZeroIndex => f (riemannXiDivisorZeroValue p))) := by
  have hGroup := hf.hasSum.tsum_fiberwise xiDistinctZeroLift
  change HasSum (fun z : XiDistinctZero =>
    tsum (fun p : {p : RiemannXiDivisorZeroIndex // xiDistinctZeroLift p = z} =>
      f (riemannXiDivisorZeroValue p.val))) _ at hGroup
  convert hGroup using 1
  funext z
  exact (xiDistinctZero_fiber_sum f z).symm

end PrimeFactorOscillations.PrimeClassDeletion
