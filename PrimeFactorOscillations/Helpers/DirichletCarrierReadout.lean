/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.DirichletPacketMellin
import PrimeFactorOscillations.Helpers.UniformCarrierCoefficients

/-!
# Dirichlet Carrier Readout

End-to-end probability carrier construction, Mellin continuation and unconditional Dirichlet zero readout.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.DirichletCarrierReadout

open DirichletPacketMellin MeasureTheory

def packetMellin (a : Nat -> Complex) (s : Complex) : Complex :=
  s * integral (volume.restrict (Set.Ioi (1 : Real)))
    (fun t : Real => (Finset.Icc 1 (Nat.floor t)).sum a *
      (t : Complex) ^ (-(s + 1)))

theorem correction_abscissa_of_power_error {q : Nat}
    (chi : DirichletCharacter Complex q) (d : Nat) (hd : 2 <= d)
    (a : Nat -> Complex) (C : Real)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - coefficient chi n) <= C / (n : Real) ^ (d - 1)) :
    LSeries.abscissaOfAbsConv (fun n => a n - coefficient chi n) <=
      (((2 : Real) - (d : Real)) : EReal) := by
  have h := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
    (f := fun n => a n - coefficient chi n)
    (x := -(((d - 1 : Nat) : Real))) (Exists.intro C (by
      intro n hn
      have hp : (n : Real) ^ (-(((d - 1 : Nat) : Real))) =
          1 / (n : Real) ^ (d - 1) := by
        rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast, one_div]
      simpa only [hp, div_eq_mul_inv, one_div, one_mul] using herror n hn))
  rw [<- EReal.coe_one, <- EReal.coe_add] at h
  have heq : -(((d - 1 : Nat) : Real)) + 1 = 2 - (d : Real) := by
    rw [Nat.cast_sub (by omega : 1 <= d), Nat.cast_one]
    ring
  rw [heq, EReal.coe_sub] at h
  norm_num at h
  exact h

theorem analyticOnNhd_power_correction {q : Nat}
    (chi : DirichletCharacter Complex q) (d : Nat) (hd : 2 <= d)
    (a : Nat -> Complex) (C : Real)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - coefficient chi n) <= C / (n : Real) ^ (d - 1)) :
    AnalyticOnNhd Complex (correction chi a)
      {s : Complex | 2 - (d : Real) < s.re} := by
  have hA := correction_abscissa_of_power_error chi d hd a C herror
  intro s hs
  apply LSeries_analyticOnNhd (fun n => a n - coefficient chi n) s
  exact hA.trans_lt (by exact_mod_cast hs)

theorem weak_error_of_power_error {q : Nat}
    (chi : DirichletCharacter Complex q) (d : Nat) (hd : 2 <= d)
    (a : Nat -> Complex) (C : Real) (hC : 0 <= C)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - coefficient chi n) <= C / (n : Real) ^ (d - 1)) :
    forall n : Nat, Not (n = 0) ->
      norm (a n - coefficient chi n) <= C / (n : Real) := by
  intro n hn
  have hnPos : (0 : Real) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : Real) <= n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hPow : (n : Real) <= (n : Real) ^ (d - 1) := by
    calc
      (n : Real) = (n : Real) ^ 1 := by simp
      _ <= (n : Real) ^ (d - 1) := by gcongr <;> first | exact hn1 | omega
  exact (herror n hn).trans (div_le_div_of_nonneg_left hC hnPos hPow)

/-- No RH, GRH, or zero-free-strip hypothesis enters the probability data,
the Mellin continuation, or the Dirichlet zero test. -/
theorem exists_unconditional_dirichlet_readout :
    exists n0 : Nat, exists C : Real, 100 <= n0 /\ 0 < C /\
      forall d : Nat, 2 <= d ->
      forall (q : Nat) [NeZero q], forall chi : DirichletCharacter Complex q,
      exists a : Nat -> Complex,
        (forall n : Nat, Not (n = 0) ->
          norm (a n - coefficient chi n) <= C / (n : Real) ^ (d - 1)) /\
        (forall n : Nat, n0 <= n ->
          exists O : UniformCarrier.CoefficientObservation d n (coefficient chi n)
            (coefficient_norm_le_nat chi n), a n = O.value) /\
        (forall n : Nat, n < n0 -> a n = coefficient chi n) /\
        MeromorphicOn (continuation chi a)
          {s : Complex | 2 - (d : Real) < s.re /\ Not (s = 1)} /\
        (forall s : Complex, 2 < s.re -> continuation chi a s = packetMellin a s) /\
        (forall rho : Complex, 2 - (d : Real) < rho.re -> Not (rho = 1) ->
          (meromorphicOrderAt (continuation chi a) rho = -1 <->
            DirichletCharacter.LFunction chi rho = 0)) := by
  choose n0 C hn0 hC hData using UniformCarrier.exists_probability_coefficients
  refine Exists.intro n0 (Exists.intro C (And.intro hn0 (And.intro hC ?_)))
  intro d hd q inst chi
  choose a hError hObserved hSmall using hData d hd (coefficient chi) (coefficient_norm_le_nat chi)
  have hCorrection := analyticOnNhd_power_correction chi d hd a C hError
  refine Exists.intro a ?_
  refine And.intro hError (And.intro hObserved (And.intro hSmall ?_))
  refine And.intro ?_ (And.intro ?_ ?_)
  . intro s hs
    have hL := (DirichletZeroReadout.analyticOnNhd_LFunction_off_one chi) s
      (Set.mem_compl_singleton_iff.mpr hs.2)
    let H : Complex -> Complex := fun z => -logDeriv (DirichletCharacter.LFunction chi) z
    have hH : MeromorphicAt H s := by
      dsimp [H]
      exact hL.meromorphicAt.logDeriv.neg
    change MeromorphicAt (H + correction chi a) s
    exact hH.add (hCorrection s hs.1).meromorphicAt
  . intro s hs
    exact mellin_identity chi a C hC.le (weak_error_of_power_error chi d hd a C hC.le hError) s hs
  . intro rho hr hOne
    exact DirichletZeroReadout.readout_order_iff_zero chi rho hOne (correction chi a)
      (hCorrection rho hr)

end PrimeFactorOscillations.DirichletCarrierReadout
