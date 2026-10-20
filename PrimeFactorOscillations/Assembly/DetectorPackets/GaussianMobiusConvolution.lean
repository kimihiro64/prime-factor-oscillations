/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianMobiusDivisors

/-!
# GaussianMobiusConvolution

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Exact two-cutoff decomposition on the Gaussian ideal packet

The finite rectangle retains both Mobius signs. Its long-long and short-short
pieces are combined before taking squared norms.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianMobiusConvolution
open GaussianMobiusDivisors UniqueFactorizationMonoid
open scoped Classical

theorem cofactor_ne_zero {I A : Ideal G} (hI : Not (I = 0))
    (hA : Dvd.dvd A I) : Not (cofactor I A = 0) := by
  intro h
  have hs := cofactor_spec hA
  rw [h, mul_zero] at hs
  exact hI hs.symm

theorem cofactor_dvd {I A : Ideal G} (hA : Dvd.dvd A I) :
    Dvd.dvd (cofactor I A) I := by
  refine Exists.intro A ?_
  rw [mul_comm, cofactor_spec hA]

theorem mul_dvd_iff_cofactor {I A B : Ideal G} (hI : Not (I = 0))
    (hA : Dvd.dvd A I) :
    Dvd.dvd (A * B) I <-> Dvd.dvd B (cofactor I A) := by
  have hA0 := divisor_ne_zero hI ((mem_divisors hI).mpr hA)
  constructor
  . intro h
    choose C hC using h
    refine Exists.intro C ?_
    apply (mul_right_inj' hA0).mp
    calc
      A * cofactor I A = I := cofactor_spec hA
      _ = (A * B) * C := hC
      _ = A * (B * C) := mul_assoc A B C
  . intro h
    choose C hC using h
    refine Exists.intro C ?_
    calc
      I = A * cofactor I A := (cofactor_spec hA).symm
      _ = A * (B * C) := congrArg (fun T => A * T) hC
      _ = (A * B) * C := (mul_assoc A B C).symm

theorem cofactor_eq_one_iff {I A : Ideal G} (hI : Not (I = 0))
    (hA : Dvd.dvd A I) : cofactor I A = 1 <-> A = I := by
  have hA0 := divisor_ne_zero hI ((mem_divisors hI).mpr hA)
  constructor
  . intro h
    simpa only [h, mul_one] using cofactor_spec hA
  . intro h
    apply (mul_right_inj' hA0).mp
    rw [cofactor_spec hA, mul_one]
    exact h.symm

def pairCoeff (I A B : Ideal G) : Complex :=
  if Dvd.dvd (A * B) I then (moebius A : Complex) * (moebius B : Complex) else 0

theorem pairCoeff_symm (I A B : Ideal G) :
    pairCoeff I A B = pairCoeff I B A := by
  unfold pairCoeff
  rw [mul_comm A B, mul_comm (moebius A : Complex) (moebius B : Complex)]

theorem row_sum (I : Ideal G) (hI : Not (I = 0)) (A : Ideal G)
    (hA : Membership.mem (divisors I) A) :
    (divisors I).sum (fun B => pairCoeff I A B) =
      if A = I then (moebius A : Complex) else 0 := by
  classical
  have hAI := (mem_divisors hI).mp hA
  have hT0 := cofactor_ne_zero hI hAI
  let f : Ideal G -> Complex := fun B =>
    if Dvd.dvd B (cofactor I A) then (moebius B : Complex) else 0
  have hs :
      (divisors (cofactor I A)).sum f = (divisors I).sum f := by
    apply Finset.sum_subset
    . intro B hB
      apply (mem_divisors hI).mpr
      exact dvd_trans ((mem_divisors hT0).mp hB) (cofactor_dvd hAI)
    . intro B _ hB
      have hn : Not (Dvd.dvd B (cofactor I A)) := by
        intro hd
        exact hB ((mem_divisors hT0).mpr hd)
      exact ite_eq_right hn
  have hf :
      (divisors I).sum f = if cofactor I A = 1 then 1 else 0 := by
    rw [<-hs]
    calc
      _ = (divisors (cofactor I A)).sum (fun B => (moebius B : Complex)) := by
        apply Finset.sum_congr rfl
        intro B hB
        exact ite_eq_left ((mem_divisors hT0).mp hB)
      _ = if cofactor I A = 1 then 1 else 0 :=
        sum_mobius_divisors (cofactor I A) hT0
  calc
    _ = (moebius A : Complex) * (divisors I).sum f := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      have he := mul_dvd_iff_cofactor hI hAI (B := B)
      by_cases hd : Dvd.dvd B (cofactor I A)
      . simp only [pairCoeff, ite_eq_left (he.mpr hd), ite_eq_left hd]
      . simp only [pairCoeff, ite_eq_right (fun h => hd (he.mp h)),
          ite_eq_right hd, mul_zero]
    _ = if A = I then (moebius A : Complex) else 0 := by
      rw [hf]
      by_cases h : A = I
      . rw [ite_eq_left ((cofactor_eq_one_iff hI hAI).mpr h), mul_one,
          ite_eq_left h]
      . rw [ite_eq_right (fun ht => h ((cofactor_eq_one_iff hI hAI).mp ht)),
          mul_zero, ite_eq_right h]

def rectangle (I : Ideal G) (f g : Ideal G -> Complex) : Complex :=
  (divisors I).sum (fun A =>
    (divisors I).sum (fun B => pairCoeff I A B * f A * g B))

theorem rectangle_symm (I : Ideal G) (f g : Ideal G -> Complex) :
    rectangle I f g = rectangle I g f := by
  classical
  unfold rectangle
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro A _
  rw [pairCoeff_symm I A B]
  ring

theorem rectangle_one_right (I : Ideal G) (hI : Not (I = 0))
    (f : Ideal G -> Complex) :
    rectangle I f (fun _ => 1) = (moebius I : Complex) * f I := by
  classical
  unfold rectangle
  simp only [mul_one]
  have hs :
      (divisors I).sum (fun A =>
        (divisors I).sum (fun B => pairCoeff I A B * f A)) =
      (divisors I).sum (fun A =>
        ((divisors I).sum (fun B => pairCoeff I A B)) * f A) := by
    apply Finset.sum_congr rfl
    intro A _
    exact (Finset.sum_mul _ _ _).symm
  rw [hs]
  rw [Finset.sum_eq_single I]
  . rw [row_sum I hI I ((mem_divisors hI).mpr dvd_rfl), ite_eq_left rfl]
  . intro A hA hne
    rw [row_sum I hI A hA, ite_eq_right hne, zero_mul]
  . intro hn
    exact False.elim (hn ((mem_divisors hI).mpr dvd_rfl))

theorem rectangle_one_left (I : Ideal G) (hI : Not (I = 0))
    (g : Ideal G -> Complex) :
    rectangle I (fun _ => 1) g = (moebius I : Complex) * g I := by
  rw [rectangle_symm, rectangle_one_right I hI]

theorem rectangle_complement (I : Ideal G) (f g : Ideal G -> Complex) :
    rectangle I (fun A => 1 - f A) (fun B => 1 - g B) =
      rectangle I (fun _ => 1) (fun _ => 1) -
      rectangle I f (fun _ => 1) - rectangle I (fun _ => 1) g +
      rectangle I f g := by
  have ht (A B : Ideal G) :
      pairCoeff I A B * (1 - f A) * (1 - g B) =
        pairCoeff I A B - pairCoeff I A B * f A -
        pairCoeff I A B * g B + pairCoeff I A B * f A * g B := by ring
  simp only [rectangle, ht, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_one]

theorem two_weight_identity (I : Ideal G) (hI : Not (I = 0))
    (f g : Ideal G -> Complex) :
    (moebius I : Complex) =
      (moebius I : Complex) * f I + (moebius I : Complex) * g I -
      rectangle I f g +
      rectangle I (fun A => 1 - f A) (fun B => 1 - g B) := by
  rw [rectangle_complement, rectangle_one_right I hI,
    rectangle_one_right I hI, rectangle_one_left I hI, mul_one]
  ring

def low (U : Nat) (A : Ideal G) : Complex :=
  if Ideal.absNorm A <= U then 1 else 0

def high (U : Nat) (A : Ideal G) : Complex :=
  1 - low U A

theorem long_identity (I : Ideal G) (hI : Not (I = 0)) (U V : Nat)
    (hU : U < Ideal.absNorm I) (hV : V < Ideal.absNorm I) :
    (moebius I : Complex) =
      -rectangle I (low U) (low V) + rectangle I (high U) (high V) := by
  have hu : low U I = 0 := ite_eq_right (Nat.not_le.mpr hU)
  have hv : low V I = 0 := ite_eq_right (Nat.not_le.mpr hV)
  have hh := two_weight_identity I hI (low U) (low V)
  change (moebius I : Complex) = -rectangle I (low U) (low V) +
    rectangle I (fun A => 1 - low U A) (fun B => 1 - low V B)
  simpa only [hu, hv, mul_zero, zero_add, zero_sub] using hh

theorem long_packet_split (S : Finset (Ideal G)) (U V : Nat)
    (K : Ideal G -> Complex)
    (hS : forall I, Membership.mem S I ->
      And (Not (I = 0)) (And (U < Ideal.absNorm I) (V < Ideal.absNorm I))) :
    S.sum (fun I => (moebius I : Complex) * K I) =
      -(S.sum (fun I => rectangle I (low U) (low V) * K I)) +
      S.sum (fun I => rectangle I (high U) (high V) * K I) := by
  calc
    _ = S.sum (fun I =>
        -(rectangle I (low U) (low V) * K I) +
          rectangle I (high U) (high V) * K I) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [long_identity I (hS I hI).1 U V (hS I hI).2.1 (hS I hI).2.2]
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem normSq_signed_split (x y : Complex) :
    Complex.normSq (-x + y) =
      Complex.normSq x + Complex.normSq y -
        2 * (x.re * y.re + x.im * y.im) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.neg_re,
    Complex.add_im, Complex.neg_im]
  ring

theorem long_packet_energy (S : Finset (Ideal G)) (U V : Nat)
    (K : Ideal G -> Complex)
    (hS : forall I, Membership.mem S I ->
      And (Not (I = 0)) (And (U < Ideal.absNorm I) (V < Ideal.absNorm I))) :
    Complex.normSq (S.sum (fun I => (moebius I : Complex) * K I)) =
      Complex.normSq (S.sum (fun I => rectangle I (low U) (low V) * K I)) +
      Complex.normSq (S.sum (fun I => rectangle I (high U) (high V) * K I)) -
      2 * (
        (S.sum (fun I => rectangle I (low U) (low V) * K I)).re *
          (S.sum (fun I => rectangle I (high U) (high V) * K I)).re +
        (S.sum (fun I => rectangle I (low U) (low V) * K I)).im *
          (S.sum (fun I => rectangle I (high U) (high V) * K I)).im) := by
  rw [long_packet_split S U V K hS, normSq_signed_split]

theorem packet_eq_squarefree (S : Finset (Ideal G)) (K : Ideal G -> Complex) :
    S.sum (fun I => (moebius I : Complex) * K I) =
      (S.filter Squarefree).sum (fun I => (moebius I : Complex) * K I) := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro I hI hn
  have hs : Not (Squarefree I) := by
    intro h
    exact hn (Finset.mem_filter.mpr (And.intro hI h))
  rw [moebius_of_not_squarefree hs, Int.cast_zero, zero_mul]

theorem pair_twist (I A B : Ideal G) (hAB : Dvd.dvd (A * B) I)
    (phi : MonoidHom (Ideal G) Complex) :
    (moebius A : Complex) * (moebius B : Complex) * phi I =
      ((moebius A : Complex) * phi A) * ((moebius B : Complex) * phi B) *
        phi (cofactor I (A * B)) := by
  have hp : phi A * phi B * phi (cofactor I (A * B)) = phi I := by
    rw [<-map_mul, <-map_mul, cofactor_spec hAB]
  calc
    _ = (moebius A : Complex) * (moebius B : Complex) *
        (phi A * phi B * phi (cofactor I (A * B))) := by rw [hp]
    _ = _ := by ring

theorem long_packet_moment {R : Type} (rows : Finset R)
    (S : Finset (Ideal G)) (U V : Nat) (K : R -> Ideal G -> Complex)
    (w : R -> Real)
    (hS : forall I, Membership.mem S I ->
      And (Not (I = 0)) (And (U < Ideal.absNorm I) (V < Ideal.absNorm I))) :
    let lo : R -> Complex := fun r =>
      S.sum (fun I => rectangle I (low U) (low V) * K r I)
    let hi : R -> Complex := fun r =>
      S.sum (fun I => rectangle I (high U) (high V) * K r I)
    rows.sum (fun r => w r * Complex.normSq
      (S.sum (fun I => (moebius I : Complex) * K r I))) =
      rows.sum (fun r => w r * Complex.normSq (lo r)) +
      rows.sum (fun r => w r * Complex.normSq (hi r)) -
      2 * rows.sum (fun r => w r *
        ((lo r).re * (hi r).re + (lo r).im * (hi r).im)) := by
  dsimp only
  have ht (r : R) :
      w r * Complex.normSq (S.sum (fun I => (moebius I : Complex) * K r I)) =
        w r * Complex.normSq
          (S.sum (fun I => rectangle I (low U) (low V) * K r I)) +
        w r * Complex.normSq
          (S.sum (fun I => rectangle I (high U) (high V) * K r I)) -
        2 * (w r * (
          (S.sum (fun I => rectangle I (low U) (low V) * K r I)).re *
            (S.sum (fun I => rectangle I (high U) (high V) * K r I)).re +
          (S.sum (fun I => rectangle I (low U) (low V) * K r I)).im *
            (S.sum (fun I => rectangle I (high U) (high V) * K r I)).im)) := by
    rw [long_packet_energy S U V (K r) hS]
    ring
  simp only [ht, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

end PrimeFactorOscillations.GaussianMobiusConvolution
