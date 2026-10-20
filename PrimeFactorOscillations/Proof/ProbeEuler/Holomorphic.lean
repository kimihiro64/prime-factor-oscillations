/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.NumberTheory.DirichletL.PrimeRows.SelectedHolomorphic

/-!
# Analytic ramified and selected corrections

Extends the actual ramified product and compensated local replacements along
analytic paths. The explicit denominator estimates hold in the stated region
without assuming RH or an improved zero-free strip.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.RamifiedHolomorphicContinuation
open OAI OAI.SevenEighths OAI.SevenEighths.ProbeEuler
open OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.ConcretePrimeRowBridge
open OAI.SevenEighths.ProbePrimePower OAI.SevenEighths.ProbePhysical
open OAI.SevenEighths.ProbeRow OAI.SevenEighths.ProbeHighRowFamily
open OAI.SevenEighths.HeckeInverseAmplification
open OAI.CanonicalQuadraticSieve OAI.CanonicalRowCompletion
local notation "O" => OAI.ActualEisensteinCubic.O
abbrev SourcePrime := OAI.SmoothMobiusCorrection.PrimeIdeal
abbrev SourceCharacter := OAI.SevenEighths.HeckeFamily.Character

theorem extended_denominators (Q : Real) (A eta v x z : Complex)
    (hQ : 4 <= Q) (hA : norm A <= 1) (heta : norm eta <= 1) (hv : norm v <= 1)
    (hx : (3 / 4 : Real) <= x.re) (hz : (33 / 200 : Real) <= z.re) :
    Not (1 - coordR Q A x z = 0) /\
      Not (1 - coordV Q z = 0) /\ Not (1 - coordD Q eta v x = 0) := by
  have hQ0 : 0 < Q := by linarith
  have hR : norm (coordR Q A x z) <= 1 / 2 :=
    (coordR_norm_le Q hQ0 A x z hA).trans (rpow_le_half Q _ hQ (by linarith))
  have hV : norm (coordV Q z) <= 1 / 2 := second_region_V_half Q hQ z hz
  have hD : norm (coordD Q eta v x) <= 1 / 2 :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans
      (rpow_le_half Q _ hQ (by linarith))
  exact And.intro (ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR)
    (And.intro (ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV)
      (ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD))

theorem ramifiedClosed_extended_differentiableAt
    (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (eta a rho : Complex) (X W Z : Complex -> Complex) (t : Complex)
    (hQ : (4 : Real) <= Ideal.absNorm (Ideal.span {p})) (ha : norm a <= 1)
    (hX : DifferentiableAt Complex X t) (hW : DifferentiableAt Complex W t)
    (hZ : DifferentiableAt Complex Z t)
    (hx : (3 / 4 : Real) <= (X t).re) (hz : (33 / 200 : Real) <= (Z t).re)
    (j : Nat) :
    DifferentiableAt Complex
      (fun y => ramifiedClosed p hp hg eta a rho (X y) (W y) (Z y) j) t := by
  have hA : norm (a ^ 2) <= 1 := by
    rw [pow_two, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg a) ha).trans ha
  have hd := extended_denominators _ (a ^ 2) 0 0 (X t) (Z t) hQ hA
    (by norm_num) (by norm_num) hx hz
  exact ramifiedClosed_differentiableAt p hp hg eta a rho X W Z t
    hX hW hZ hd.2.1 hd.1 j

theorem ramifiedCorrection_extended_differentiableAt
    (eta : SourceCharacter) (u : FreeRow) (P : SourcePrime) (hs : Supported P.val)
    (hQ : (4 : Real) <= P.val.absNorm) (X W Z : Complex -> Complex) (t : Complex)
    (hX : DifferentiableAt Complex X t) (hW : DifferentiableAt Complex W t)
    (hZ : DifferentiableAt Complex Z t)
    (hx : (3 / 4 : Real) <= (X t).re) (hz : (33 / 200 : Real) <= (Z t).re) :
    DifferentiableAt Complex
      (fun y => ramifiedCorrection eta u P hs (X y) (W y) (Z y)) t := by
  let : (Ideal.span {primaryGenerator P.val} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_extended_differentiableAt
  . simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  . exact actualACube_norm_le eta _
  . exact hX
  . exact hW
  . exact hZ
  . exact hx
  . exact hz

theorem ramifiedCorrection_extended_analyticOnNhd
    (eta : SourceCharacter) (u : FreeRow) (P : SourcePrime) (hs : Supported P.val)
    (hQ : (4 : Real) <= P.val.absNorm)
    (X W Z : Complex -> Complex) (U : Set Complex) (hU : IsOpen U)
    (hX : AnalyticOnNhd Complex X U) (hW : AnalyticOnNhd Complex W U)
    (hZ : AnalyticOnNhd Complex Z U)
    (hRe : forall t, Membership.mem U t ->
      (3 / 4 : Real) <= (X t).re /\ (33 / 200 : Real) <= (Z t).re) :
    AnalyticOnNhd Complex
      (fun t => ramifiedCorrection eta u P hs (X t) (W t) (Z t)) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro t ht
  exact (ramifiedCorrection_extended_differentiableAt eta u P hs hQ X W Z t
    (hX t ht).differentiableAt (hW t ht).differentiableAt (hZ t ht).differentiableAt
    (hRe t ht).1 (hRe t ht).2).differentiableWithinAt

theorem ramifiedProduct_extended_analyticOnNhd
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (eta : SourceCharacter) (u : FreeRow)
    (X W Z : Complex -> Complex) (U : Set Complex) (hU : IsOpen U)
    (hX : AnalyticOnNhd Complex X U) (hW : AnalyticOnNhd Complex W U)
    (hZ : AnalyticOnNhd Complex Z U)
    (hRe : forall t, Membership.mem U t ->
      (3 / 4 : Real) <= (X t).re /\ (33 / 200 : Real) <= (Z t).re) :
    AnalyticOnNhd Complex
      (fun t => ramifiedProduct S hS eta u (X t) (W t) (Z t)) U := by
  unfold ramifiedProduct
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact ramifiedCorrection_extended_analyticOnNhd eta u P.val _
    (by exact_mod_cast (hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2))
    X W Z U hU hX hW hZ hRe

theorem continuedMarkedLocal_extended_analyticOnNhd
    (eta : SourceCharacter) (u : FreeRow) (P : SourcePrime) (hs : Supported P.val)
    (hQ : (4 : Real) <= P.val.absNorm)
    (X W Z : Complex -> Complex) (U : Set Complex) (hU : IsOpen U)
    (hX : AnalyticOnNhd Complex X U) (hW : AnalyticOnNhd Complex W U)
    (hZ : AnalyticOnNhd Complex Z U)
    (hRe : forall t, Membership.mem U t ->
      (3 / 4 : Real) <= (X t).re /\ (33 / 200 : Real) <= (Z t).re) :
    AnalyticOnNhd Complex
      (fun t => continuedMarkedLocal eta u P hs (X t) (W t) (Z t)) U := by
  have hRAM : AnalyticOnNhd Complex
      (fun t => ramifiedCorrection eta u P hs (X t) (W t) (Z t)) U :=
    ramifiedCorrection_extended_analyticOnNhd eta u P hs hQ X W Z U hU hX hW hZ hRe
  have hQ0 : (0 : Real) < P.val.absNorm := by linarith
  intro t ht
  have hcv0 : AnalyticAt Complex (coordV (P.val.absNorm : Real)) (Z t) :=
    (coordV_differentiable _ hQ0).analyticAt (Z t)
  have hcv : AnalyticAt Complex
      (fun y => coordV (P.val.absNorm : Real) (Z y)) t := by
    apply AnalyticAt.comp (g := coordV (P.val.absNorm : Real)) (f := Z) (x := t)
    . exact hcv0
    . exact hZ t ht
  have hden := extended_denominators (P.val.absNorm : Real) 0 0 0 (X t) (Z t)
    hQ (by norm_num) (by norm_num) (by norm_num) (hRe t ht).1 (hRe t ht).2
  have hquot : AnalyticAt Complex (fun y =>
      (ramifiedCorrection eta u P hs (X y) (W y) (Z y) - 1) /
        (1 - coordV (P.val.absNorm : Real) (Z y))) t := by
    apply AnalyticAt.div
    . apply AnalyticAt.sub
      . exact hRAM t ht
      . fun_prop
    . apply AnalyticAt.sub
      . fun_prop
      . exact hcv
    . exact hden.2.1
  have heq : Filter.EventuallyEq (nhds t)
      (fun y => (ramifiedCorrection eta u P hs (X y) (W y) (Z y) - 1) /
        (1 - coordV (P.val.absNorm : Real) (Z y)))
      (fun y => continuedMarkedLocal eta u P hs (X y) (W y) (Z y)) := by
    have hmem : Filter.Eventually (fun y => Membership.mem U y) (nhds t) :=
      hU.mem_nhds ht
    apply hmem.mono
    intro y hy
    have hd := extended_denominators (P.val.absNorm : Real) 0 0 0 (X y) (Z y)
      hQ (by norm_num) (by norm_num) (by norm_num) (hRe y hy).1 (hRe y hy).2
    exact (continuedMarkedLocal_eq_quotient eta u P hs (X y) (W y) (Z y) hd.2.1).symm
  exact hquot.congr heq

theorem continuedCompensatedLocal_extended_analyticOnNhd
    (eta : SourceCharacter) (u : FreeRow) (P : SourcePrime) (hs : Supported P.val)
    (hQ : (4 : Real) <= P.val.absNorm)
    (X W Z : Complex -> Complex) (U : Set Complex) (hU : IsOpen U)
    (hX : AnalyticOnNhd Complex X U) (hW : AnalyticOnNhd Complex W U)
    (hZ : AnalyticOnNhd Complex Z U)
    (hRe : forall t, Membership.mem U t ->
      (3 / 4 : Real) <= (X t).re /\ (33 / 200 : Real) <= (Z t).re) :
    AnalyticOnNhd Complex (fun t =>
      continuedCompensatedLocal eta u P hs (X t) (W t) (Z t)
        (star (OAI.SevenEighths.HeckeFamily.idealCoeff eta P.val) *
          (P.val.absNorm : Complex) ^ (X t))
        ((P.val.absNorm : Complex) ^ (-W t))) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro t ht
  have hQ0 : (0 : Real) < P.val.absNorm := by linarith
  have hQc : Not ((P.val.absNorm : Complex) = 0) := by exact_mod_cast (ne_of_gt hQ0)
  have hM : DifferentiableAt Complex
      (fun y => continuedMarkedLocal eta u P hs (X y) (W y) (Z y)) t :=
    (continuedMarkedLocal_extended_analyticOnNhd eta u P hs hQ X W Z U
      hU hX hW hZ hRe t ht).differentiableAt
  have hD : DifferentiableAt Complex (fun y =>
      coordD (P.val.absNorm : Real) (OAI.SevenEighths.HeckeFamily.idealCoeff eta P.val)
        (idealRowHom u.val P.val) (X y)) t := by
    apply DifferentiableAt.comp (f := X)
      (g := coordD (P.val.absNorm : Real)
        (OAI.SevenEighths.HeckeFamily.idealCoeff eta P.val) (idealRowHom u.val P.val)) t
    . exact (coordD_differentiable (P.val.absNorm : Real) hQ0
        (OAI.SevenEighths.HeckeFamily.idealCoeff eta P.val)
        (idealRowHom u.val P.val)).differentiableAt
    . exact (hX t ht).differentiableAt
  have hVW : DifferentiableAt Complex
      (fun y => coordW (P.val.absNorm : Real) (idealRowHom u.val P.val) (W y)) t := by
    apply DifferentiableAt.comp (f := W)
      (g := coordW (P.val.absNorm : Real) (idealRowHom u.val P.val)) t
    . exact (coordW_differentiable (P.val.absNorm : Real) hQ0
        (idealRowHom u.val P.val)).differentiableAt
    . exact (hW t ht).differentiableAt
  have hV : DifferentiableAt Complex
      (fun y => coordV (P.val.absNorm : Real) (Z y)) t := by
    apply DifferentiableAt.comp (f := Z) (g := coordV (P.val.absNorm : Real)) t
    . exact (coordV_differentiable (P.val.absNorm : Real) hQ0).differentiableAt
    . exact (hZ t ht).differentiableAt
  have hB : DifferentiableAt Complex (fun y =>
      star (OAI.SevenEighths.HeckeFamily.idealCoeff eta P.val) *
        (P.val.absNorm : Complex) ^ (X y)) t := by
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.const_cpow
    . exact (hX t ht).differentiableAt
    . exact Or.inl hQc
  have hq : DifferentiableAt Complex
      (fun y => (P.val.absNorm : Complex) ^ (-W y)) t := by
    apply DifferentiableAt.const_cpow
    . apply DifferentiableAt.neg
      exact (hW t ht).differentiableAt
    . exact Or.inl hQc
  have hd := extended_denominators (P.val.absNorm : Real) 0
    (OAI.SevenEighths.HeckeFamily.idealCoeff eta P.val)
    (idealRowHom u.val P.val) (X t) (Z t) hQ (by norm_num)
    (OAI.SevenEighths.HeckeFamily.idealCoeff_norm_le_one eta _)
    (idealRowHom_norm u.val _) (hRe t ht).1 (hRe t ht).2
  have hnD : Not (1 - coordD (P.val.absNorm : Real)
      (OAI.SevenEighths.HeckeFamily.idealCoeff eta P.val)
      (idealRowHom u.val P.val) (X t) = 0) := hd.2.2
  have hfull : DifferentiableAt Complex (fun y =>
      continuedCompensatedLocal eta u P hs (X y) (W y) (Z y)
        (star (OAI.SevenEighths.HeckeFamily.idealCoeff eta P.val) *
          (P.val.absNorm : Complex) ^ (X y))
        ((P.val.absNorm : Complex) ^ (-W y))) t := by
    unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
    fun_prop (disch := assumption)
  exact hfull.differentiableWithinAt

end PrimeFactorOscillations.RamifiedHolomorphicContinuation
