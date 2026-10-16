/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.NicolasSpectralPsi

/-!
# Multiplicity fibers of the xi-zero index

Canonical divisor-zero indices retain analytic multiplicities. Reflection identifies finite frequency fibers.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Robin1984

/-- The nonnegative divisor order of xi, retaining analytic multiplicity. -/
def xiZeroMultiplicity (z : Complex) : Nat :=
  ((MeromorphicOn.divisor Complex.riemannXi Set.univ) z).toNat

/-- The canonical zero index has exactly one index for each unit of divisor order. -/
def xiZeroFiberEquiv (z : Complex) (hz : Not (z = 0)) :
    Equiv {p : RiemannXiDivisorZeroIndex // riemannXiDivisorZeroValue p = z}
      (Fin (xiZeroMultiplicity z)) := by
  refine Equiv.mk (fun p => ?_) (fun k => ?_) ?_ ?_
  . exact Fin.cast (congrArg xiZeroMultiplicity p.property) p.val.val.snd
  . exact Subtype.mk (Subtype.mk (Sigma.mk z k) hz) rfl
  . intro p
    cases p with
    | mk p hp =>
      cases p with
      | mk q hq =>
        cases q with
        | mk w k =>
          change w = z at hp
          subst z
          rfl
  . intro k
    rfl

theorem card_xiZeroFiber (z : Complex) (hz : Not (z = 0)) :
    Nat.card {p : RiemannXiDivisorZeroIndex // riemannXiDivisorZeroValue p = z} =
      xiZeroMultiplicity z := by
  calc
    _ = Nat.card (Fin (xiZeroMultiplicity z)) := Nat.card_congr (xiZeroFiberEquiv z hz)
    _ = _ := by simp

/-- Under RH a frequency fiber is precisely the divisor multiplicity at that zero. -/
theorem card_xiZeroFrequencyFiber (hRH : RiemannHypothesis) (w : Real) :
    Nat.card {p : RiemannXiDivisorZeroIndex // (riemannXiDivisorZeroValue p).im = w} =
      xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I) := by
  let z : Complex := (1 / 2 : Complex) + (w : Complex) * Complex.I
  have hz : Not (z = 0) := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [z] at hr
  have hp : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).im = w <-> riemannXiDivisorZeroValue p = z := by
    intro p
    constructor
    . intro h
      apply Complex.ext
      . simpa [z] using riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p
      . simpa [z] using h
    . intro h
      have hi := congrArg Complex.im h
      simpa [z] using hi
  have hs : (fun p : RiemannXiDivisorZeroIndex => (riemannXiDivisorZeroValue p).im = w) =
      (fun p : RiemannXiDivisorZeroIndex => riemannXiDivisorZeroValue p = z) := by
    funext p
    exact propext (hp p)
  change Nat.card (Subtype (fun p : RiemannXiDivisorZeroIndex =>
    (riemannXiDivisorZeroValue p).im = w)) = xiZeroMultiplicity z
  rw [hs]
  exact card_xiZeroFiber z hz

/-- The functional equation preserves the full analytic multiplicity. -/
theorem xiZeroMultiplicity_one_sub (z : Complex) :
    xiZeroMultiplicity (1 - z) = xiZeroMultiplicity z := by
  have hAnalytic : AnalyticOnNhd Complex Complex.riemannXi Set.univ :=
    fun s _ => Complex.differentiable_riemannXi.analyticAt s
  have hMap : AnalyticAt Complex (fun s : Complex => 1 - s) z :=
    analyticAt_const.sub analyticAt_id
  have hDeriv : HasDerivAt (fun s : Complex => 1 - s) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : Complex)
  have hOrder := analyticOrderAt_comp_of_deriv_ne_zero (f := Complex.riemannXi) hMap
    (by rw [hDeriv.deriv]; norm_num)
  have hFunction : Function.comp Complex.riemannXi (fun s : Complex => 1 - s) = Complex.riemannXi := by
    funext s
    exact Complex.riemannXi_one_sub s
  rw [hFunction] at hOrder
  unfold xiZeroMultiplicity
  rw [MeromorphicOn.divisor_apply hAnalytic.meromorphicOn (Set.mem_univ (1 - z)),
    MeromorphicOn.divisor_apply hAnalytic.meromorphicOn (Set.mem_univ z),
    (hAnalytic (1 - z) (Set.mem_univ _)).meromorphicOrderAt_eq,
    (hAnalytic z (Set.mem_univ _)).meromorphicOrderAt_eq, hOrder]

theorem xiZeroMultiplicity_frequency_neg (w : Real) :
    xiZeroMultiplicity ((1 / 2 : Complex) + ((-w : Real) : Complex) * Complex.I) =
      xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I) := by
  have h := xiZeroMultiplicity_one_sub ((1 / 2 : Complex) + (w : Complex) * Complex.I)
  have hPoint : (1 : Complex) - ((1 / 2 : Complex) + (w : Complex) * Complex.I) =
      (1 / 2 : Complex) + ((-w : Real) : Complex) * Complex.I := by
    push_cast
    ring
  rw [hPoint] at h
  exact h

theorem card_xiZeroFrequencyFiber_neg (hRH : RiemannHypothesis) (w : Real) :
    Nat.card {p : RiemannXiDivisorZeroIndex // (riemannXiDivisorZeroValue p).im = -w} =
      Nat.card {p : RiemannXiDivisorZeroIndex // (riemannXiDivisorZeroValue p).im = w} := by
  rw [card_xiZeroFrequencyFiber hRH (-w), card_xiZeroFrequencyFiber hRH w]
  exact xiZeroMultiplicity_frequency_neg w

def xiZeroFrequencyFiberEquiv (hRH : RiemannHypothesis) (w : Real) :
    Equiv {p : RiemannXiDivisorZeroIndex // (riemannXiDivisorZeroValue p).im = w}
      (Fin (xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I))) := by
  let z : Complex := (1 / 2 : Complex) + (w : Complex) * Complex.I
  have hz : Not (z = 0) := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [z] at hr
  refine Equiv.trans ?_ (xiZeroFiberEquiv z hz)
  refine Equiv.mk (fun p => Subtype.mk p.val ?_) (fun p => Subtype.mk p.val ?_) ?_ ?_
  . apply Complex.ext
    . simpa [z] using riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p.val
    . simpa [z] using p.property
  . have h := congrArg Complex.im p.property
    simpa [z] using h
  . intro p
    apply Subtype.ext
    rfl
  . intro p
    apply Subtype.ext
    rfl

/-- A frequency-filtered zero sum is exactly multiplicity times its coefficient. -/
theorem tsum_xiZeroFrequencyFiber_const (hRH : RiemannHypothesis) (w : Real) (c : Complex) :
    tsum (fun p : RiemannXiDivisorZeroIndex =>
      if (riemannXiDivisorZeroValue p).im = w then c else 0) =
        (xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I) : Complex) * c := by
  classical
  let s : Set RiemannXiDivisorZeroIndex := fun p => (riemannXiDivisorZeroValue p).im = w
  let e : Equiv s
      (Fin (xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I))) :=
    xiZeroFrequencyFiberEquiv hRH w
  letI : Fintype s := Fintype.ofEquiv
    (Fin (xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I))) e.symm
  have hCard : Fintype.card s =
      xiZeroMultiplicity ((1 / 2 : Complex) + (w : Complex) * Complex.I) := by
    rw [<- Nat.card_eq_fintype_card]
    exact card_xiZeroFrequencyFiber hRH w
  have hSub := tsum_subtype s (fun _ : RiemannXiDivisorZeroIndex => c)
  calc
    _ = tsum (fun _ : s => c) := by
      rw [hSub]
      apply tsum_congr
      intro p
      rfl
    _ = (Fintype.card s : Complex) * c := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = _ := by rw [hCard]

end PrimeFactorOscillations
