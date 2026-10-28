/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicCarrierAnalytic
import PrimeFactorOscillations.Helpers.CubicCarrierMellin
import PrimeFactorOscillations.Helpers.CubicInfiniteLaplace

/-!
# Actual infinite reciprocal Gaussian coefficient packet

The four signed Gaussian sums form the actual carrier-profile series on the
positive physical axis. Its convergent Mellin transform is the previously
proved nonvanishing carrier multiplier times the full Dirichlet series. All
complex coefficients are retained. Summability at the evaluated s and at 2
is explicit; the character comparison supplies it initially on Re(s)>1.
The analytic nonzero multiplier preserves meromorphic order on 1/2<Re(s)<1.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CubicInfiniteWindow
open MeasureTheory
open OAI OAI.SevenEighths.ProbeRadialMellin
open CubicReciprocalGaussian CubicCompensatedWindow CubicInfiniteLaplace

def rate (i : Fin 4) : Real := paperConstant * scales i

theorem rate_pos (i : Fin 4) : 0 < rate i :=
  mul_pos paperConstant_pos (scales_pos i)

def directMultiplier (s : Complex) : Complex :=
  Finset.univ.sum (fun i : Fin 4 =>
    coefficients i * ((rate i : Complex) ^ (-s) * Complex.Gamma s))

def windowLaplace (a : Nat -> Complex) (t : Real) : Complex :=
  Finset.univ.sum (fun i : Fin 4 => coefficients i * laplace a (rate i) t)

private theorem finite_hasMellin (S : Finset (Fin 4))
    (f : Fin 4 -> Real -> Complex) (m : Fin 4 -> Complex) (s : Complex)
    (hf : forall i : Fin 4, HasMellin (f i) s (m i)) :
    HasMellin (fun t : Real => S.sum (fun i => f i t)) s (S.sum m) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [HasMellin, MellinConvergent, IntegrableOn, mellin]
  | @insert i S hi ih =>
    have hh := hasMellin_add (hf i).1 ih.1
    rw [(hf i).2, ih.2] at hh
    simpa only [Finset.sum_insert hi] using hh

theorem directMultiplier_eq_carrierMultiplier (s : Complex) (hs : 0 < s.re) :
    directMultiplier s = CubicCarrierMellin.carrierMultiplier s := by
  have hk (i : Fin 4) :
      HasMellin (fun t : Real => coefficients i * expWindow (rate i * t)) s
        (coefficients i * ((rate i : Complex) ^ (-s) * Complex.Gamma s)) := by
    have hc : MellinConvergent (fun t : Real => expWindow (rate i * t)) s :=
      (MellinConvergent.comp_mul_left (rate_pos i)).2
        (expWindow_convergent s hs)
    have hm := mellin_comp_mul_left expWindow s (rate_pos i)
    rw [expWindow_mellin s hs] at hm
    have hh := hasMellin_const_smul hc (coefficients i)
    simpa only [smul_eq_mul, hm] using hh
  have hh := finite_hasMellin Finset.univ
    (fun i t => coefficients i * expWindow (rate i * t))
    (fun i => coefficients i * ((rate i : Complex) ^ (-s) * Complex.Gamma s)) s hk
  have he : (fun t : Real => Finset.univ.sum (fun i : Fin 4 =>
        coefficients i * expWindow (rate i * t))) = carrierProfile := by
    funext t
    unfold carrierProfile
    apply Finset.sum_congr rfl
    intro i hi
    unfold expWindow rate
    congr 1
    congr 1
    push_cast
    ring
  rw [he] at hh
  exact hh.2.symm.trans (CubicCarrierMellin.carrierProfile_hasMellin s hs).2

theorem windowLaplace_hasSum (a : Nat -> Complex) (ha0 : a 0 = 0)
    (ha2 : LSeriesSummable a 2) (t : Real) (ht : 0 < t) :
    HasSum (fun n : Nat => a n * carrierProfile ((n : Real) * t))
      (windowLaplace a t) := by
  classical
  have hfin (S : Finset (Fin 4)) :
      HasSum (fun n : Nat => S.sum (fun i =>
          coefficients i * (a n *
            ((Real.exp (-(rate i * (n : Real)) * t) : Real) : Complex))))
        (S.sum (fun i => coefficients i * laplace a (rate i) t)) := by
    induction S using Finset.induction_on with
    | empty =>
      have hz : HasSum (fun _ : Nat => (0 : Complex)) 0 := hasSum_zero
      simpa only [Finset.sum_empty] using hz
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact ((laplace_summable a ha0 ha2 (rate i) t (rate_pos i) ht).hasSum.mul_left
        (coefficients i)).add ih
  have he (n : Nat) :
      a n * carrierProfile ((n : Real) * t) =
        Finset.univ.sum (fun i : Fin 4 =>
          coefficients i * (a n *
            ((Real.exp (-(rate i * (n : Real)) * t) : Real) : Complex))) := by
    unfold carrierProfile
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hexp : Complex.exp
        (-((paperConstant * scales i : Real) : Complex) *
          (((n : Real) * t : Real) : Complex)) =
        ((Real.exp (-(rate i * (n : Real)) * t) : Real) : Complex) := by
      rw [Complex.ofReal_exp]
      congr 1
      dsimp [rate]
      push_cast
      ring
    rw [hexp]
    ring
  change HasSum (fun n : Nat => a n * carrierProfile ((n : Real) * t))
    (Finset.univ.sum (fun i : Fin 4 => coefficients i * laplace a (rate i) t))
  simpa only [<- he] using hfin Finset.univ

theorem windowLaplace_hasMellin (a : Nat -> Complex) (ha0 : a 0 = 0)
    (ha2 : LSeriesSummable a 2) (s : Complex) (hs : 0 < s.re)
    (ha : LSeriesSummable a s) :
    HasMellin (windowLaplace a) s
      (CubicCarrierMellin.carrierMultiplier s * LSeries a s) := by
  have hk (i : Fin 4) :
      HasMellin (fun t : Real => coefficients i * laplace a (rate i) t) s
        (coefficients i *
          ((rate i : Complex) ^ (-s) * Complex.Gamma s * LSeries a s)) := by
    have hp := laplace_hasMellin a ha0 ha2 (rate i) (rate_pos i) s hs ha
    have hh := hasMellin_const_smul hp.1 (coefficients i)
    simpa only [smul_eq_mul, hp.2] using hh
  have hh := finite_hasMellin Finset.univ
    (fun i t => coefficients i * laplace a (rate i) t)
    (fun i => coefficients i *
      ((rate i : Complex) ^ (-s) * Complex.Gamma s * LSeries a s)) s hk
  have hd : HasMellin (windowLaplace a) s (directMultiplier s * LSeries a s) := by
    convert hh using 1
    . rfl
    . unfold directMultiplier
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
  rw [directMultiplier_eq_carrierMultiplier s hs] at hd
  exact hd

theorem carrierMultiplier_order_mul (D : Complex -> Complex) (rho : Complex)
    (hD : MeromorphicAt D rho) (hs : (1 / 2 : Real) < rho.re) (hs1 : rho.re < 1) :
    meromorphicOrderAt (fun s : Complex =>
      CubicCarrierMellin.carrierMultiplier s * D s) rho =
        meromorphicOrderAt D rho := by
  have hA := CubicCarrierAnalytic.carrierMultiplier_analyticAt rho (by linarith)
  have hn := CubicCarrierMellin.carrierMultiplier_ne_zero rho hs hs1
  have hOrder : meromorphicOrderAt CubicCarrierMellin.carrierMultiplier rho = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hA.meromorphicAt).mp
      (Exists.intro (CubicCarrierMellin.carrierMultiplier rho)
        (And.intro hn (hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)))
  change meromorphicOrderAt (CubicCarrierMellin.carrierMultiplier * D) rho = _
  rw [meromorphicOrderAt_mul hA.meromorphicAt hD, hOrder, zero_add]

end PrimeFactorOscillations.CubicInfiniteWindow
