/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMajorMellinContour
import PrimeFactorOscillations.Helpers.LPFMajorPrincipal

/-!
# Centered contour kernel for every Dirichlet character

Fill the principal pole and retain nonprincipal L-functions. The resulting
function is entire and nonzero to the right of seven eighths. Its logarithmic
derivative has the common numerical bound 13312. The centered Perron integrand
is holomorphic there, and the principal rational contribution is exactly the
difference of two Perron kernels. No prime-prefix bound is asserted here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

noncomputable def lpfCharacterPoleFill {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) : Complex -> Complex := by
  classical
  exact if chi = 1 then lpfPrincipalPoleFill N else chi.LFunction

theorem lpf_character_poleFill_differentiable {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) :
    Differentiable Complex (lpfCharacterPoleFill chi) := by
  classical
  by_cases hchi : chi = 1
  next =>
    rw [lpfCharacterPoleFill, if_pos hchi]
    exact lpf_principal_poleFill_differentiable N
  next =>
    rw [lpfCharacterPoleFill, if_neg hchi]
    exact DirichletCharacter.differentiable_LFunction hchi

theorem lpf_character_poleFill_ne_zero {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (s : Complex) (hs : 7 / 8 < s.re) :
    Not (lpfCharacterPoleFill chi s = 0) := by
  classical
  by_cases hchi : chi = 1
  next =>
    rw [lpfCharacterPoleFill, if_pos hchi]
    exact lpf_principal_poleFill_ne_zero N s hs
  next =>
    rw [lpfCharacterPoleFill, if_neg hchi]
    exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
      chi hs (fun h => hchi h.1)

theorem lpf_character_poleFill_log_deriv_numeric {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (t : Real) (z : Complex)
    (hz : dist z (2 + Complex.I * (t : Complex)) <= 17 / 16) :
    norm (deriv (lpfCharacterPoleFill chi) z / lpfCharacterPoleFill chi z) <=
      13312 * (1 + Real.log (N : Real) + Real.log (abs t + 8)) := by
  classical
  by_cases hchi : chi = 1
  next =>
    rw [lpfCharacterPoleFill, if_pos hchi]
    exact lpf_principal_poleFill_log_deriv_numeric N t z hz
  next =>
    rw [lpfCharacterPoleFill, if_neg hchi]
    exact lpf_nonprincipal_log_deriv_numeric chi hchi t z hz

theorem lpf_character_poleFill_log_deriv_differentiableOn
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) :
    DifferentiableOn Complex
      (deriv (lpfCharacterPoleFill chi) / lpfCharacterPoleFill chi)
      {s : Complex | 7 / 8 < s.re} := by
  have ho : IsOpen {s : Complex | 7 / 8 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hA : AnalyticOnNhd Complex (lpfCharacterPoleFill chi)
      {s : Complex | 7 / 8 < s.re} :=
    (lpf_character_poleFill_differentiable chi).differentiableOn.analyticOnNhd ho
  exact hA.deriv.differentiableOn.div hA.differentiableOn
    (fun s hs => lpf_character_poleFill_ne_zero chi s hs)

theorem lpf_character_poleFill_log_deriv_identity {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (s : Complex) (hs : 7 / 8 < s.re)
    (hPole : Not (And (chi = 1) (s = 1))) :
    deriv chi.LFunction s / chi.LFunction s =
      deriv (lpfCharacterPoleFill chi) s / lpfCharacterPoleFill chi s -
        (@ite Complex (chi = 1) (Classical.propDecidable _) (1 / (s - 1)) 0) := by
  classical
  by_cases hchi : chi = 1
  next =>
    subst chi
    have hs1 : Not (s = 1) := fun h => hPole (And.intro rfl h)
    rw [lpfCharacterPoleFill, if_pos rfl, if_pos rfl]
    exact eq_sub_of_add_eq (lpf_principal_log_deriv_pole_identity N s hs hs1)
  next =>
    rw [lpfCharacterPoleFill, if_neg hchi, if_neg hchi, sub_zero]

noncomputable def lpfCenteredContourIntegrand {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (x : Real) : Complex -> Complex :=
  lpfMellinKernel (-(deriv (lpfCharacterPoleFill chi) / lpfCharacterPoleFill chi)) x

theorem lpf_centered_contour_integrand_differentiableOn
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Real) (hx : 0 < x) :
    DifferentiableOn Complex (lpfCenteredContourIntegrand chi x)
      {s : Complex | 7 / 8 < s.re} := by
  have hx0 : Not ((x : Complex) = 0) := by
    exact_mod_cast ne_of_gt hx
  have hPow : DifferentiableOn Complex (fun s : Complex => (x : Complex) ^ s)
      {s : Complex | 7 / 8 < s.re} := by
    intro s _
    exact (differentiableAt_id.const_cpow (Or.inl hx0)).differentiableWithinAt
  apply ((lpf_character_poleFill_log_deriv_differentiableOn chi).neg.mul hPow).div
    differentiableOn_id
  intro s hs h0
  have hr := congrArg Complex.re h0
  simp only [id_eq, Complex.zero_re] at hr
  change 7 / 8 < s.re at hs
  linarith

theorem lpf_principal_pole_kernel_identity (x : Real) (hx : 0 < x)
    (s : Complex) (hs0 : Not (s = 0)) (hs1 : Not (s = 1)) :
    (x : Complex) ^ s / ((s - 1) * s) =
      (x : Complex) * ((x : Complex) ^ (s - 1) / (s - 1)) -
        (x : Complex) ^ s / s := by
  have hx0 : Not ((x : Complex) = 0) := by exact_mod_cast ne_of_gt hx
  have hPower : (x : Complex) ^ s = (x : Complex) * (x : Complex) ^ (s - 1) := by
    calc
      _ = Complex.exp (Complex.log (x : Complex) * s) :=
        Complex.cpow_def_of_ne_zero hx0 s
      _ = Complex.exp (Complex.log (x : Complex)) *
          Complex.exp (Complex.log (x : Complex) * (s - 1)) := by
        rw [<- Complex.exp_add]
        congr 1
        ring
      _ = _ := by rw [Complex.exp_log hx0, Complex.cpow_def_of_ne_zero hx0]
  rw [hPower]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

end PrimeFactorOscillations.QRH

