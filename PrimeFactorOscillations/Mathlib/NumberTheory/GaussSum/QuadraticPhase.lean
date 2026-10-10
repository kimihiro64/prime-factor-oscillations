/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Quadratic phases and coprime root-cusp sums

Exact finite-field evaluations of quadratic additive phases and their quartic
cusp weights. The square-fiber identity, character identification, discriminant
phase and zero frequencies are retained. These are finite algebraic identities;
no global mean-square estimate or character-sum bound is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace MulChar

variable {F : Type*} [Field F] [Fintype F]

/-- Nontrivial quadratic characters on a finite field are unique. -/
theorem quadraticCharacter_unique (delta eta : MulChar F Complex)
    (hd : Not (delta = 1)) (he : Not (eta = 1))
    (hd2 : delta ^ 2 = 1) (he2 : eta ^ 2 = 1) : delta = eta := by
  classical
  let g : Units F := Classical.choose (@IsCyclic.exists_generator (Units F) _ _)
  have hg := Classical.choose_spec (@IsCyclic.exists_generator (Units F) _ _)
  have generator_value (rho : MulChar F Complex) (hr : Not (rho = 1))
      (hr2 : rho ^ 2 = 1) : rho g = -1 := by
    have hnot : Not (rho g = 1) := by
      intro h
      apply hr
      apply MulChar.ext
      intro x
      have hx := (Submonoid.mem_powers_iff x g).mp
        (mem_powers_iff_mem_zpowers.mpr (hg x))
      let n := Classical.choose hx
      have hn : g ^ n = x := Classical.choose_spec hx
      rw [MulChar.one_apply_coe, <- hn, Units.val_pow_eq_pow_val, map_pow, h, one_pow]
    have hs : rho g ^ 2 = 1 := by
      rw [<- MulChar.pow_apply_coe, hr2, MulChar.one_apply_coe]
    exact (sq_eq_one_iff.mp hs).resolve_left hnot
  have hdg := generator_value delta hd hd2
  have heg := generator_value eta he he2
  apply MulChar.ext
  intro x
  have hx := (Submonoid.mem_powers_iff x g).mp
    (mem_powers_iff_mem_zpowers.mpr (hg x))
  let n := Classical.choose hx
  have hn : g ^ n = x := Classical.choose_spec hx
  rw [<- hn, Units.val_pow_eq_pow_val, map_pow, map_pow, hdg, heg]

/-- A quartic character's square is the canonical quadratic character. -/
theorem quartic_sq_eq_quadraticChar [DecidableEq F]
    (hF : Not (ringChar F = 2)) (chi : MulChar F Complex)
    (hfour : chi ^ 4 = 1) (htwo : Not (chi ^ 2 = 1)) :
    chi ^ 2 = (quadraticChar F).ringHomComp (Int.castRingHom Complex) := by
  apply quadraticCharacter_unique _ _ htwo
  . exact (MulChar.ringHomComp_ne_one_iff (Int.cast_injective)).mpr
      (quadraticChar_ne_one hF)
  . rw [<- pow_mul]
    exact hfour
  . exact ((quadraticChar_isQuadratic F).comp (Int.castRingHom Complex)).sq_eq_one

/-- Squaring fibers give the quadratic exponential sum, with zero included. -/
theorem sum_quadraticPhase_eq_gaussSum [DecidableEq F]
    (hF : Not (ringChar F = 2)) (psi : AddChar F Complex)
    (hpsi : Not (psi = 1)) :
    Finset.sum Finset.univ (fun r : F => psi (r ^ 2)) =
      gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom Complex)) psi := by
  classical
  have hfiber (a : F) :
      Finset.sum (Finset.univ.filter (fun r : F => r ^ 2 = a))
        (fun r : F => psi (r ^ 2)) =
        ((quadraticChar F a : Complex) + 1) * psi a := by
    calc
      _ = Finset.sum (Finset.univ.filter (fun r : F => r ^ 2 = a))
          (fun _ : F => psi a) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [(Finset.mem_filter.mp hr).2]
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hc := congrArg (fun z : Int => (z : Complex))
          (quadraticChar_card_sqrts hF a)
        simpa only [Int.cast_natCast, Int.cast_add, Int.cast_one,
          Set.toFinset_ofPred] using congrArg (fun z : Complex => z * psi a) hc
  rw [<- Finset.sum_fiberwise Finset.univ (fun r : F => r ^ 2)]
  simp_rw [hfiber, add_mul, one_mul]
  rw [Finset.sum_add_distrib, AddChar.sum_eq_zero_of_ne_one hpsi, add_zero]
  rfl

/-- Linear Gauss scaling includes the zero frequency. -/
theorem gaussSum_linearPhase (chi : MulChar F Complex)
    (hchi : Not (chi = 1)) (psi : AddChar F Complex) (a : F) :
    Finset.sum Finset.univ (fun r : F => chi r * psi (a * r)) =
      (Inv.inv chi) a * gaussSum chi psi := by
  classical
  by_cases ha : a = 0
  case pos =>
    subst a
    simpa [MulChar.map_zero] using MulChar.sum_eq_zero_of_ne_one hchi
  case neg =>
    simpa only [gaussSum, AddChar.mulShift_apply, Units.val_mk0] using
      gaussSum_mulShift_eq chi psi (Units.mk0 a ha)

/-- A nonzero quadratic phase is evaluated by the square of a quartic character. -/
theorem sum_scaledQuadraticPhase (hF : Not (ringChar F = 2))
    (chi : MulChar F Complex) (hfour : chi ^ 4 = 1)
    (htwo : Not (chi ^ 2 = 1)) (psi : AddChar F Complex)
    (hpsi : Not (psi = 1)) (a : F) (ha : Not (a = 0)) :
    Finset.sum Finset.univ (fun r : F => psi (a * r ^ 2)) =
      (chi ^ 2) a * gaussSum (chi ^ 2) psi := by
  classical
  have hshift : Not (psi.mulShift a = 1) := by
    intro h
    apply hpsi
    ext x
    have hx := congrArg (fun p : AddChar F Complex => p (x / a)) h
    have harg : a * (x / a) = x := by field_simp [ha]
    simpa [AddChar.mulShift_apply, harg] using hx
  have hs := sum_quadraticPhase_eq_gaussSum hF (psi.mulShift a) hshift
  rw [<- quartic_sq_eq_quadraticChar hF chi hfour htwo] at hs
  change Finset.sum Finset.univ (fun r : F => psi (a * r ^ 2)) =
    gaussSum (chi ^ 2) (psi.mulShift a) at hs
  have hinv : Inv.inv (chi ^ 2) = chi ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [<- pow_add]
    exact hfour
  rw [hs]
  simpa only [gaussSum, AddChar.mulShift_apply, hinv] using
    gaussSum_linearPhase (chi ^ 2) htwo psi a

/-- Completion of the square retains the discriminant phase exactly. -/
theorem sum_completeQuadraticPhase (hF : Not (ringChar F = 2))
    (chi : MulChar F Complex) (hfour : chi ^ 4 = 1)
    (htwo : Not (chi ^ 2 = 1)) (psi : AddChar F Complex)
    (hpsi : Not (psi = 1)) (h t nu : F) (hh : Not (h = 0)) :
    Finset.sum Finset.univ (fun r : F => psi (h * r ^ 2 + t * r + nu / h)) =
      psi ((nu - t ^ 2 / 4) / h) * (chi ^ 2) h * gaussSum (chi ^ 2) psi := by
  classical
  have htwoF : Not ((2 : F) = 0) := Ring.two_ne_zero hF
  have hfourF : Not ((4 : F) = 0) := by
    rw [show (4 : F) = 2 * 2 by ring]
    exact mul_ne_zero htwoF htwoF
  have hphase (r : F) : h * r ^ 2 + t * r + nu / h =
      (nu - t ^ 2 / 4) / h + h * (r + t / (2 * h)) ^ 2 := by
    field_simp [hh, htwoF, hfourF]
    ring
  simp_rw [hphase, AddChar.map_add_eq_mul]
  rw [<- Finset.mul_sum]
  have hsum : Finset.sum Finset.univ
      (fun r : F => psi (h * (r + t / (2 * h)) ^ 2)) =
      Finset.sum Finset.univ (fun r : F => psi (h * r ^ 2)) := by
    apply Fintype.sum_equiv (Equiv.addRight (t / (2 * h)))
    intro r
    rfl
  rw [hsum, sum_scaledQuadraticPhase hF chi hfour htwo psi hpsi h hh]
  ring

/-- The cusp-only local branch is an exact pair of Gauss sums. -/
theorem sum_cuspQuadraticPhase (hF : Not (ringChar F = 2))
    (chi : MulChar F Complex) (hfour : chi ^ 4 = 1)
    (htwo : Not (chi ^ 2 = 1)) (psi : AddChar F Complex)
    (hpsi : Not (psi = 1)) (t nu : F) :
    Finset.sum Finset.univ (fun h : F =>
      Finset.sum Finset.univ (fun r : F =>
        (Inv.inv chi) h * psi (h * r ^ 2 + t * r + nu / h))) =
      gaussSum (chi ^ 2) psi * gaussSum (Inv.inv chi) psi *
        chi (nu - t ^ 2 / 4) := by
  classical
  have hchi : Not (chi = 1) := by
    intro hc
    exact htwo (by rw [hc, one_pow])
  have hrow (h : F) :
      Finset.sum Finset.univ (fun r : F =>
        (Inv.inv chi) h * psi (h * r ^ 2 + t * r + nu / h)) =
      gaussSum (chi ^ 2) psi *
        (chi h * psi ((nu - t ^ 2 / 4) / h)) := by
    by_cases hh : h = 0
    case pos => simp [hh]
    case neg =>
      rw [<- Finset.mul_sum, sum_completeQuadraticPhase hF chi hfour htwo psi hpsi h t nu hh]
      have hprod : Inv.inv chi * chi ^ 2 = chi := by simp [pow_two, <- mul_assoc]
      have hp := congrArg (fun rho : MulChar F Complex => rho h) hprod
      simp only [MulChar.mul_apply] at hp
      calc
        _ = ((Inv.inv chi) h * (chi ^ 2) h) *
            (gaussSum (chi ^ 2) psi * psi ((nu - t ^ 2 / 4) / h)) := by ring
        _ = _ := by rw [hp]; ring
  simp_rw [hrow]
  rw [<- Finset.mul_sum]
  have hinvsum : Finset.sum Finset.univ
      (fun h : F => chi h * psi ((nu - t ^ 2 / 4) / h)) =
      Finset.sum Finset.univ
        (fun h : F => (Inv.inv chi) h * psi ((nu - t ^ 2 / 4) * h)) := by
    apply Fintype.sum_bijective (fun h : F => Inv.inv h) inv_involutive.bijective
    intro h
    simp only [MulChar.inv_apply', inv_inv, div_eq_mul_inv]
  rw [hinvsum, gaussSum_linearPhase (Inv.inv chi) (inv_ne_one.mpr hchi), inv_inv]
  ring

/-- The discriminant-zero cusp packet vanishes, including its r = 0 terms. -/
theorem sum_cuspQuadraticPhase_discriminant_zero
    (hF : Not (ringChar F = 2)) (chi : MulChar F Complex)
    (hfour : chi ^ 4 = 1) (htwo : Not (chi ^ 2 = 1))
    (psi : AddChar F Complex) (hpsi : Not (psi = 1)) (t : F) :
    Finset.sum Finset.univ (fun h : F =>
      Finset.sum Finset.univ (fun r : F =>
        (Inv.inv chi) h * psi (h * r ^ 2 + t * r + (t ^ 2 / 4) / h))) = 0 := by
  rw [sum_cuspQuadraticPhase hF chi hfour htwo psi hpsi]
  simp

/-- Independent row and cusp fields factor without dropping either zero case. -/
theorem sum_coprimeRootCuspPhase {E : Type*} [Field E] [Fintype E]
    (xi : MulChar E Complex) (hxi : Not (xi = 1))
    (rho : AddChar E Complex) (s : E)
    (hF : Not (ringChar F = 2)) (chi : MulChar F Complex)
    (hfour : chi ^ 4 = 1) (htwo : Not (chi ^ 2 = 1))
    (psi : AddChar F Complex) (hpsi : Not (psi = 1)) (t nu : F) :
    Finset.sum Finset.univ (fun u : E =>
      Finset.sum Finset.univ (fun h : F =>
        Finset.sum Finset.univ (fun r : F =>
          xi u * (Inv.inv chi) h * rho (s * u) *
            psi (h * r ^ 2 + t * r + nu / h)))) =
      gaussSum xi rho * gaussSum (chi ^ 2) psi *
        gaussSum (Inv.inv chi) psi * (Inv.inv xi) s * chi (nu - t ^ 2 / 4) := by
  classical
  have hsep :
      Finset.sum Finset.univ (fun u : E =>
        Finset.sum Finset.univ (fun h : F =>
          Finset.sum Finset.univ (fun r : F =>
            xi u * (Inv.inv chi) h * rho (s * u) *
              psi (h * r ^ 2 + t * r + nu / h)))) =
      (Finset.sum Finset.univ (fun u : E => xi u * rho (s * u))) *
        Finset.sum Finset.univ (fun h : F =>
          Finset.sum Finset.univ (fun r : F =>
            (Inv.inv chi) h * psi (h * r ^ 2 + t * r + nu / h))) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsep, gaussSum_linearPhase xi hxi rho s,
    sum_cuspQuadraticPhase hF chi hfour htwo psi hpsi]
  ring

end MulChar
