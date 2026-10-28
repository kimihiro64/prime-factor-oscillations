/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Command
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.DirichletEvenGaussPhase

/-!
# Exact norm-coordinate finite Fourier packet

The split norm transform retains the joint cubic/sextic phase and the
principal isotropic-line correction. No arithmetic moment estimate is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CubicNormFourier

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def hyperbolicTransform (chi : MulChar F Complex) (psi : AddChar F Complex)
    (u v : F) : Complex :=
  Finset.univ.sum (fun x : F => Finset.univ.sum (fun y : F =>
    chi (x * y) * psi (u * x + v * y)))

omit [DecidableEq F] in
theorem hyperbolic_factor (chi : MulChar F Complex) (psi : AddChar F Complex)
    (u v : F) :
    hyperbolicTransform chi psi u v =
      gaussSum chi (psi.mulShift u) * gaussSum chi (psi.mulShift v) := by
  have he (x y : F) :
      chi (x * y) * psi (u * x + v * y) =
        (chi x * psi (u * x)) * (chi y * psi (v * y)) := by
    rw [map_mul, AddChar.map_add_eq_mul]
    ring
  unfold hyperbolicTransform
  simp_rw [he]
  rw [<- Finset.sum_mul_sum]
  rfl

theorem hyperbolic_nonprincipal (chi : MulChar F Complex) (psi : AddChar F Complex)
    (hchi : Not (chi = 1)) (u v : F) :
    hyperbolicTransform chi psi u v =
      gaussSum chi psi ^ 2 * (Inv.inv chi) (u * v) := by
  rw [hyperbolic_factor,
    OAI.ShortDraftLocal.gaussSum_mulShift_any chi psi hchi u,
    OAI.ShortDraftLocal.gaussSum_mulShift_any chi psi hchi v, map_mul]
  ring

theorem principal_gauss_shift (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (u : F) :
    gaussSum (1 : MulChar F Complex) (psi.mulShift u) =
      if u = 0 then (Fintype.card F : Complex) - 1 else -1 := by
  by_cases hu : u = 0
  . have hz : psi.mulShift 0 = 1 := by
      ext x
      change psi ((0 : F) * x) = 1
      simp
    rw [ite_eq_left hu, hu, hz, gaussSum_one_one, Nat.card_eq_fintype_card,
      Fintype.card_units]
    rw [Nat.cast_sub (show 1 <= Fintype.card F from Fintype.card_pos), Nat.cast_one]
  . rw [ite_eq_right hu]
    exact gaussSum_one_left (hpsi hu)

theorem hyperbolic_principal (psi : AddChar F Complex) (hpsi : psi.IsPrimitive)
    (u v : F) :
    hyperbolicTransform (1 : MulChar F Complex) psi u v =
      1 - (Fintype.card F : Complex) * (if u * v = 0 then 1 else 0) +
        (Fintype.card F : Complex) * ((Fintype.card F : Complex) - 1) *
          (if And (u = 0) (v = 0) then 1 else 0) := by
  rw [hyperbolic_factor, principal_gauss_shift psi hpsi,
    principal_gauss_shift psi hpsi]
  by_cases hu : u = 0 <;> by_cases hv : v = 0 <;>
    simp [hu, hv, mul_eq_zero]
  all_goals ring

def splitEquiv (r s : F) (hrs : Not (r = s)) : Equiv (Prod F F) (Prod F F) where
  toFun z := Prod.mk (z.1 + z.2 * r) (z.1 + z.2 * s)
  invFun z := Prod.mk ((r * z.2 - s * z.1) / (r - s)) ((z.1 - z.2) / (r - s))
  left_inv := by
    intro z
    apply Prod.ext <;> dsimp <;> field_simp [sub_ne_zero.mpr hrs] <;> ring
  right_inv := by
    intro z
    apply Prod.ext <;> dsimp <;> field_simp [sub_ne_zero.mpr hrs] <;> ring

def normForm (a b : F) : F := a ^ 2 - a * b + b ^ 2

def traceForm (a b c d : F) : F := a * d + b * c - b * d

omit [Fintype F] [DecidableEq F] in
theorem norm_split (r s : F) (hSum : r + s = -1) (hProd : r * s = 1)
    (a b : F) :
    normForm a b = (a + b * r) * (a + b * s) := by
  calc
    _ = a ^ 2 + a * b * (r + s) + b ^ 2 * (r * s) := by
      rw [hSum, hProd]
      dsimp [normForm]
      ring
    _ = _ := by ring

omit [Fintype F] [DecidableEq F] in
theorem trace_split (r s : F) (hSum : r + s = -1) (a b c d : F) :
    (a + b * r) * (c + d * r) - (a + b * s) * (c + d * s) =
      (r - s) * traceForm a b c d := by
  calc
    _ = (r - s) * (a * d + b * c + b * d * (r + s)) := by ring
    _ = _ := by rw [hSum]; dsimp [traceForm]; ring

def normTransform (chi : MulChar F Complex) (psi : AddChar F Complex)
    (c d : F) : Complex :=
  Finset.univ.sum (fun z : Prod F F =>
    chi (normForm z.1 z.2) * psi (traceForm z.1 z.2 c d))

omit [DecidableEq F] in
theorem norm_hyperbolic (r s : F) (hrs : Not (r = s))
    (hSum : r + s = -1) (hProd : r * s = 1)
    (chi : MulChar F Complex) (psi : AddChar F Complex) (c d : F) :
    normTransform chi psi c d =
      hyperbolicTransform chi psi ((c + d * r) / (r - s))
        (-((c + d * s) / (r - s))) := by
  let U := (c + d * r) / (r - s)
  let V := -((c + d * s) / (r - s))
  have hdelta : Not (r - s = 0) := sub_ne_zero.mpr hrs
  have he (a b : F) : traceForm a b c d =
      U * (a + b * r) + V * (a + b * s) := by
    dsimp [U, V]
    field_simp [hdelta]
    linear_combination -(trace_split r s hSum a b c d)
  have h := Fintype.sum_equiv (splitEquiv r s hrs)
    (fun z : Prod F F => chi (normForm z.1 z.2) * psi (traceForm z.1 z.2 c d))
    (fun z : Prod F F => chi (z.1 * z.2) * psi (U * z.1 + V * z.2))
    (by
      intro z
      change chi (normForm z.1 z.2) * psi (traceForm z.1 z.2 c d) =
        chi ((z.1 + z.2 * r) * (z.1 + z.2 * s)) *
          psi (U * (z.1 + z.2 * r) + V * (z.1 + z.2 * s))
      rw [norm_split r s hSum hProd, he])
  change normTransform chi psi c d = hyperbolicTransform chi psi U V
  unfold normTransform
  rw [h, Fintype.sum_prod_type]
  rfl

omit [Fintype F] [DecidableEq F] in
theorem difference_sq (r s : F) (hSum : r + s = -1) (hProd : r * s = 1) :
    (r - s) ^ 2 = -(3 : F) := by
  calc
    _ = (r + s) ^ 2 - 4 * (r * s) := by ring
    _ = _ := by rw [hSum, hProd]; ring

omit [Fintype F] [DecidableEq F] in
theorem three_ne_zero (r s : F) (hrs : Not (r = s))
    (hSum : r + s = -1) (hProd : r * s = 1) :
    Not ((3 : F) = 0) := by
  intro h3
  have hn := pow_ne_zero 2 (sub_ne_zero.mpr hrs)
  rw [difference_sq r s hSum hProd, h3, neg_zero] at hn
  exact hn rfl

omit [Fintype F] [DecidableEq F] in
theorem split_dual_norm (r s : F) (hrs : Not (r = s))
    (hSum : r + s = -1) (hProd : r * s = 1) (c d : F) :
    ((c + d * r) / (r - s)) * (-((c + d * s) / (r - s))) =
      normForm c d / 3 := by
  calc
    _ = -((c + d * r) * (c + d * s)) / (r - s) ^ 2 := by
      field_simp [sub_ne_zero.mpr hrs]
    _ = _ := by
      rw [<- norm_split r s hSum hProd, difference_sq r s hSum hProd]
      rw [neg_div_neg_eq]

omit [Fintype F] [DecidableEq F] in
theorem inverse_norm_div_three (r s : F) (hrs : Not (r = s))
    (hSum : r + s = -1) (hProd : r * s = 1)
    (chi : MulChar F Complex) (c d : F) :
    (Inv.inv chi) (normForm c d / 3) =
      chi 3 * (Inv.inv chi) (normForm c d) := by
  have h3 := three_ne_zero r s hrs hSum hProd
  have hc := congrArg (fun f : MulChar F Complex => f (3 : F)) (mul_inv_cancel chi)
  change chi 3 * (Inv.inv chi) 3 = (1 : MulChar F Complex) 3 at hc
  rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr h3)] at hc
  have he : (normForm c d / 3) * (3 : F) = normForm c d := by
    field_simp [h3]
  have hm := congrArg (fun x : F => (@Inv.inv (MulChar F Complex) inferInstance chi) x) he
  rw [map_mul] at hm
  calc
    _ = (Inv.inv chi) (normForm c d / 3) * 1 := by ring
    _ = chi 3 * ((Inv.inv chi) (normForm c d / 3) * (Inv.inv chi) 3) := by
      rw [<- hc]
      ring
    _ = _ := by rw [hm]

theorem norm_nonprincipal (r s : F) (hrs : Not (r = s))
    (hSum : r + s = -1) (hProd : r * s = 1)
    (chi : MulChar F Complex) (psi : AddChar F Complex)
    (hchi : Not (chi = 1)) (c d : F) :
    normTransform chi psi c d =
      chi 3 * gaussSum chi psi ^ 2 * (Inv.inv chi) (normForm c d) := by
  rw [norm_hyperbolic r s hrs hSum hProd,
    hyperbolic_nonprincipal chi psi hchi,
    split_dual_norm r s hrs hSum hProd,
    inverse_norm_div_three r s hrs hSum hProd]
  ring

theorem norm_principal (r s : F) (hrs : Not (r = s))
    (hSum : r + s = -1) (hProd : r * s = 1)
    (psi : AddChar F Complex) (hpsi : psi.IsPrimitive) (c d : F) :
    normTransform (1 : MulChar F Complex) psi c d =
      1 - (Fintype.card F : Complex) * (if normForm c d = 0 then 1 else 0) +
        (Fintype.card F : Complex) * ((Fintype.card F : Complex) - 1) *
          (if And (c = 0) (d = 0) then 1 else 0) := by
  let U := (c + d * r) / (r - s)
  let V := -((c + d * s) / (r - s))
  have hdelta : Not (r - s = 0) := sub_ne_zero.mpr hrs
  have h3 := three_ne_zero r s hrs hSum hProd
  have hZero : U * V = 0 <-> normForm c d = 0 := by
    change ((c + d * r) / (r - s)) * (-((c + d * s) / (r - s))) = 0 <-> _
    rw [split_dual_norm r s hrs hSum hProd]
    simp [h3]
  have hBoth : And (U = 0) (V = 0) <-> And (c = 0) (d = 0) := by
    constructor
    . intro h
      have hU : c + d * r = 0 := (div_eq_zero_iff.mp h.1).resolve_right hdelta
      have hV : c + d * s = 0 :=
        (div_eq_zero_iff.mp (neg_eq_zero.mp h.2)).resolve_right hdelta
      have hD : d * (r - s) = 0 := by linear_combination hU - hV
      have hd : d = 0 := (mul_eq_zero.mp hD).resolve_right hdelta
      have hc : c = 0 := by simpa only [hd, zero_mul, add_zero] using hU
      exact And.intro hc hd
    . intro h
      simp [U, V, h.1, h.2]
  rw [norm_hyperbolic r s hrs hSum hProd]
  simpa only [hZero, hBoth] using (hyperbolic_principal psi hpsi U V)

end PrimeFactorOscillations.CubicNormFourier
