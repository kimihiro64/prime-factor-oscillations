/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Tactic.Positivity
import PrimeFactorOscillations.Proof.DetectorPackets.DepletedMobius

/-!
# DepletedMobiusBound

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.DepletedMobius

def smoothMass (h N : Nat) (alpha : Real) : Real :=
  (Finset.Ioc 0 N).sum (fun d =>
    if SupportedOn h d then 1 / (d : Real) ^ alpha else 0)

theorem floor_rpow_le {alpha : Real} (halpha : 0 <= alpha) (N d : Nat)
    (hd : 0 < d) :
    ((N / d : Nat) : Real) ^ alpha <=
      (N : Real) ^ alpha / (d : Real) ^ alpha := by
  have hdpos : 0 < (d : Real) := by exact_mod_cast hd
  have hf : ((N / d : Nat) : Real) <= (N : Real) / (d : Real) := by
    have hm : ((N / d : Nat) : Real) * (d : Real) <= (N : Real) := by
      exact_mod_cast Nat.div_mul_le_self N d
    calc
      _ = (((N / d : Nat) : Real) * (d : Real)) / (d : Real) := by field_simp
      _ <= _ := div_le_div_of_nonneg_right hm hdpos.le
  have hb := Real.rpow_le_rpow (Nat.cast_nonneg (N / d)) hf halpha
  rwa [Real.div_rpow (Nat.cast_nonneg N) (Nat.cast_nonneg d)] at hb

theorem depleted_prefix_norm_le {R : Type*} [NormedField R]
    (h N : Nat) (eta : Nat -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n)
    (hnorm : forall n : Nat, norm (eta n) <= 1)
    (alpha C : Real) (halpha : 0 <= alpha) (hC : 0 <= C)
    (hbase : forall n : Nat, norm (mertensPrefix eta n) <= C * (n : Real) ^ alpha) :
    norm (depletedPrefix h eta N) <= C * (N : Real) ^ alpha * smoothMass h N alpha := by
  rw [prefix_depletion_identity h eta heta N]
  apply (norm_sum_le _ _).trans
  calc
    _ <= (Finset.Ioc 0 N).sum (fun d =>
        C * (N : Real) ^ alpha *
          (if SupportedOn h d then 1 / (d : Real) ^ alpha else 0)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
      by_cases hs : SupportedOn h d
      . rw [ite_eq_left hs, ite_eq_left hs, norm_mul]
        calc
          _ <= 1 * (C * ((N / d : Nat) : Real) ^ alpha) :=
            mul_le_mul (hnorm d) (hbase (N / d)) (norm_nonneg _) (by positivity)
          _ <= C * ((N : Real) ^ alpha / (d : Real) ^ alpha) := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_left (floor_rpow_le halpha N d hdpos) hC
          _ = _ := by ring
      . simp only [ite_eq_right hs, norm_zero, mul_zero, le_refl]
    _ = _ := by rw [smoothMass, Finset.mul_sum]

def decayHom (alpha : Real) : MonoidHom Nat Real where
  toFun n := 1 / (n : Real) ^ alpha
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n),
      one_div, mul_inv_rev]
    ring

theorem decayHom_nonneg (alpha : Real) (n : Nat) : 0 <= decayHom alpha n := by
  change 0 <= 1 / (n : Real) ^ alpha
  positivity

theorem decayHom_prime_norm_lt {alpha : Real} (halpha : 0 < alpha)
    {p : Nat} (hp : Nat.Prime p) : norm (decayHom alpha p) < 1 := by
  change norm (1 / (p : Real) ^ alpha) < 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), one_div,
    <- Real.rpow_neg (Nat.cast_nonneg p) alpha]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt)
    (neg_lt_zero.mpr halpha)

def eulerMask (h : Nat) (alpha : Real) : Real :=
  h.primeFactors.prod (fun p => Inv.inv (1 - 1 / (p : Real) ^ alpha))

theorem supported_mem_factored (h d : Nat) (hh : Not (h = 0))
    (hd : SupportedOn h d) :
    Membership.mem (Nat.factoredNumbers h.primeFactors) d := by
  apply Nat.mem_factoredNumbers_iff_primeFactors_subset.mpr
  refine And.intro hd.1 ?_
  intro p hp
  have hpd := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr (And.intro hpd.1 (And.intro (hd.2 p hpd.1 hpd.2.1) hh))

theorem smoothMass_le_eulerMask (h N : Nat) (hh : Not (h = 0))
    {alpha : Real} (halpha : 0 < alpha) :
    smoothMass h N alpha <= eulerMask h alpha := by
  let F := {d : Nat // Membership.mem (Nat.factoredNumbers h.primeFactors) d}
  let S := (Finset.Ioc 0 N).filter (SupportedOn h)
  let incl : {d : Nat // Membership.mem S d} -> F := fun d =>
    Subtype.mk d.val (supported_mem_factored h d.val hh (Finset.mem_filter.mp d.property).2)
  let T : Finset F := S.attach.image incl
  have hsumT : T.sum (fun x => decayHom alpha x.val) =
      S.sum (fun d => decayHom alpha d) := by
    dsimp only [T]
    rw [Finset.sum_image]
    . simpa only [incl] using Finset.sum_attach S (fun d => decayHom alpha d)
    . intro a _ b _ heq
      exact Subtype.ext (congrArg (fun x : F => x.val) heq)
  have hEuler := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := decayHom alpha) (fun hp => decayHom_prime_norm_lt halpha hp) h.primeFactors
  have hsummable : Summable (fun x : F => decayHom alpha x.val) := hEuler.1.of_norm
  have hfilter : h.primeFactors.filter Nat.Prime = h.primeFactors :=
    Finset.filter_eq_self.mpr (fun p hp => (Nat.mem_primeFactors.mp hp).1)
  have heuler : (tsum (fun x : F => decayHom alpha x.val)) = eulerMask h alpha := by
    simpa only [hfilter, eulerMask, decayHom, MonoidHom.coe_mk, OneHom.coe_mk] using
      hEuler.2.tsum_eq
  calc
    _ = S.sum (fun d => decayHom alpha d) := by
      simp only [smoothMass, S, Finset.sum_filter, decayHom, MonoidHom.coe_mk, OneHom.coe_mk]
    _ = T.sum (fun x => decayHom alpha x.val) := hsumT.symm
    _ <= tsum (fun x : F => decayHom alpha x.val) :=
      Summable.sum_le_tsum T (fun x _ => decayHom_nonneg alpha x.val) hsummable
    _ = _ := heuler

theorem depleted_prefix_euler_bound {R : Type*} [NormedField R]
    (h N : Nat) (hh : Not (h = 0)) (eta : Nat -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n)
    (hnorm : forall n : Nat, norm (eta n) <= 1)
    (alpha C : Real) (halpha : 0 < alpha) (hC : 0 <= C)
    (hbase : forall n : Nat, norm (mertensPrefix eta n) <= C * (n : Real) ^ alpha) :
    norm (depletedPrefix h eta N) <= C * (N : Real) ^ alpha * eulerMask h alpha :=
  (depleted_prefix_norm_le h N eta heta hnorm alpha C halpha.le hC hbase).trans
    (mul_le_mul_of_nonneg_left (smoothMass_le_eulerMask h N hh halpha) (by positivity))

end PrimeFactorOscillations.DepletedMobius
