/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMajorNonprincipal
import PrimeFactorOscillations.Helpers.LPFMajorZetaIntegral

/-!
# Numerical logarithmic derivative for every Dirichlet character

Finite Euler factors extend the pole-filled zeta estimate to every principal
character, including modulus one. The actual pole correction is retained.
Together with the nonprincipal bound this gives coefficient 16384 on the
specified disk away from the pole. The numerical prime-prefix and contour
transfer are separate consumers.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

noncomputable def lpfPrincipalEuler (N : Nat) (s : Complex) : Complex :=
  Finset.prod N.primeFactors (fun p => 1 - (p : Complex) ^ (-s))

noncomputable def lpfPrincipalPoleFill (N : Nat) (s : Complex) : Complex :=
  lpfZetaPoleFill s * lpfPrincipalEuler N s

theorem lpf_principal_euler_differentiable (N : Nat) :
    Differentiable Complex (lpfPrincipalEuler N) := by
  intro s
  have hd : DifferentiableAt Complex
      (Finset.prod N.primeFactors (fun p => fun w : Complex =>
        1 - (p : Complex) ^ (-w))) s := by
    apply DifferentiableAt.finset_prod
    intro p hp
    have hp0 : Not ((p : Complex) = 0) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    exact (differentiableAt_const (c := (1 : Complex))).sub
      (differentiableAt_id.neg.const_cpow (Or.inl hp0))
  have he : Finset.prod N.primeFactors (fun p => fun w : Complex =>
      1 - (p : Complex) ^ (-w)) = lpfPrincipalEuler N := by
    funext w
    simp only [Finset.prod_apply, lpfPrincipalEuler]
  rw [he] at hd
  exact hd

theorem lpf_principal_euler_norm_bound (N : Nat) [NeZero N]
    (s : Complex) (hs : 0 <= s.re) :
    norm (lpfPrincipalEuler N s) <= (N : Real) := by
  have hFactor (p : Nat) (hp : Membership.mem N.primeFactors p) :
      norm (1 - (p : Complex) ^ (-s)) <= (p : Real) := by
    have hp2 : (2 : Real) <= p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hPow : norm ((p : Complex) ^ (-s)) <= 1 := by
      rw [show (p : Complex) = Complex.ofReal (p : Real) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : Real) < p)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
        (by simpa only [Complex.neg_re] using neg_nonpos.mpr hs)
    have h := norm_sub_le (1 : Complex) ((p : Complex) ^ (-s))
    rw [norm_one] at h
    linarith
  unfold lpfPrincipalEuler
  rw [norm_prod]
  calc
    _ <= Finset.prod N.primeFactors (fun p => (p : Real)) := by
      have hProd : forall S : Finset Nat, S <= N.primeFactors ->
          Finset.prod S (fun p => norm (1 - (p : Complex) ^ (-s))) <=
            Finset.prod S (fun p => (p : Real)) := by
        intro S
        induction S using Finset.induction_on
        next => simp
        next p S hp ih =>
          intro hSub
          rw [Finset.prod_insert hp, Finset.prod_insert hp]
          apply mul_le_mul (hFactor p (hSub (Finset.mem_insert_self p S)))
            (ih (fun a ha => hSub (Finset.mem_insert_of_mem ha)))
            (Finset.prod_nonneg (fun a _ => norm_nonneg _)) (Nat.cast_nonneg p)
      exact hProd _ (fun _ h => h)
    _ = ((Finset.prod N.primeFactors id : Nat) : Real) := by simp
    _ <= (N : Real) := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos N) (Nat.prod_primeFactors_dvd N)

theorem lpf_principal_euler_ne_zero (N : Nat) (s : Complex) (hs : 0 < s.re) :
    Not (lpfPrincipalEuler N s = 0) := by
  unfold lpfPrincipalEuler
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp h
  have hp2 : (2 : Real) <= p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hPow : norm ((p : Complex) ^ (-s)) < 1 := by
    rw [show (p : Complex) = Complex.ofReal (p : Real) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : Real) < p)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith)
      (by simpa only [Complex.neg_re] using neg_neg_of_pos hs)
  have he : (p : Complex) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  rw [he, norm_one] at hPow
  exact (lt_irrefl 1) hPow

theorem lpf_principal_poleFill_differentiable (N : Nat) :
    Differentiable Complex (lpfPrincipalPoleFill N) := by
  exact lpf_zetaPoleFill_differentiable.mul (lpf_principal_euler_differentiable N)

theorem lpf_principal_poleFill_eq (N : Nat) [NeZero N]
    (s : Complex) (hs : Not (s = 1)) :
    lpfPrincipalPoleFill N s =
      (s - 1) * (1 : DirichletCharacter Complex N).LFunction s := by
  rw [lpfPrincipalPoleFill, lpfZetaPoleFill, if_neg hs]
  change (s - 1) * riemannZeta s * lpfPrincipalEuler N s =
    (s - 1) * DirichletCharacter.LFunctionTrivChar N s
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs]
  unfold lpfPrincipalEuler
  ring

theorem lpf_principal_poleFill_ne_zero (N : Nat) [NeZero N]
    (s : Complex) (hs : 7 / 8 < s.re) :
    Not (lpfPrincipalPoleFill N s = 0) := by
  by_cases hs1 : s = 1
  next =>
    subst s
    rw [lpfPrincipalPoleFill, lpf_zetaPoleFill_one, one_mul]
    exact lpf_principal_euler_ne_zero N 1 (by norm_num)
  next =>
    rw [lpf_principal_poleFill_eq N s hs1]
    apply mul_ne_zero (sub_ne_zero.mpr hs1)
    exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
      (1 : DirichletCharacter Complex N) hs (by simp [hs1])

theorem lpf_principal_poleFill_norm_bound (N : Nat) [NeZero N]
    (s : Complex) (T : Real) (hs : 7 / 8 <= s.re) (hT : 1 <= T)
    (hsNorm : norm s <= T) (hsOne : norm (s - 1) <= T) :
    norm (lpfPrincipalPoleFill N s) <= 4 * (N : Real) * T ^ 2 := by
  rw [lpfPrincipalPoleFill, norm_mul]
  have hz := lpf_zetaPoleFill_norm_bound s T hs hT hsNorm hsOne
  have he := lpf_principal_euler_norm_bound N s (by linarith)
  calc
    _ <= (4 * T ^ 2) * N := mul_le_mul hz he (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem lpf_principal_poleFill_center_lower (N : Nat) [NeZero N] (t : Real) :
    1 / 4 <= norm (lpfPrincipalPoleFill N (2 + Complex.I * (t : Complex))) := by
  let c : Complex := 2 + Complex.I * (t : Complex)
  have hcRe : c.re = 2 := by simp [c]
  have hc1 : Not (c = 1) := by
    intro h
    have hr := congrArg Complex.re h
    rw [hcRe] at hr
    norm_num at hr
  change 1 / 4 <= norm (lpfPrincipalPoleFill N c)
  rw [lpf_principal_poleFill_eq N c hc1, norm_mul]
  have hDist : 1 <= norm (c - 1) := by
    have h := Complex.abs_re_le_norm (c - 1)
    norm_num [Complex.sub_re, hcRe] at h
    exact h
  have hL : 1 / 4 <= norm ((1 : DirichletCharacter Complex N).LFunction c) :=
    lpf_LFunction_center_lower _ t
  calc
    (1 / 4 : Real) = 1 * (1 / 4) := by ring
    _ <= _ := mul_le_mul hDist hL (by norm_num) (norm_nonneg _)

theorem lpf_principal_poleFill_log_deriv_numeric
    (N : Nat) [NeZero N] (t : Real) (z : Complex)
    (hz : dist z (2 + Complex.I * (t : Complex)) <= 17 / 16) :
    norm (deriv (lpfPrincipalPoleFill N) z / lpfPrincipalPoleFill N z) <=
      13312 * (1 + Real.log (N : Real) + Real.log (abs t + 8)) := by
  let c : Complex := 2 + Complex.I * (t : Complex)
  let T : Real := abs t + 8
  let B0 : Real := 1 + Real.log (N : Real) + Real.log T
  have hN : 1 <= (N : Real) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hT : 1 <= T := by dsimp [T]; linarith [abs_nonneg t]
  have hLogN : 0 <= Real.log (N : Real) := Real.log_nonneg hN
  have hLogT : 0 <= Real.log T := Real.log_nonneg hT
  have hB : 0 < 4 * B0 := by dsimp [B0]; linarith
  have hcRe : c.re = 2 := by simp [c]
  have hRe (w : Complex) (hw : Membership.mem (Metric.ball c (9 / 8)) w) :
      7 / 8 < w.re := by
    have hd := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at hd
    have hl := (abs_le.mp (Complex.abs_re_le_norm (w - c))).1
    simp only [Complex.sub_re, hcRe] at hl
    linarith
  have hAnalytic : AnalyticOnNhd Complex (lpfPrincipalPoleFill N)
      (Metric.ball c (9 / 8)) :=
    (lpf_principal_poleFill_differentiable N).differentiableOn.analyticOnNhd
      Metric.isOpen_ball
  have hNonzero : forall w, Membership.mem (Metric.ball c (9 / 8)) w ->
      Not (lpfPrincipalPoleFill N w = 0) := by
    intro w hw
    exact lpf_principal_poleFill_ne_zero N w (hRe w hw)
  have hcBound : norm c <= 2 + abs t := by
    have h := norm_add_le (2 : Complex) (Complex.I * (t : Complex))
    simpa [c, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs] using h
  have hcOne : norm (c - 1) <= 1 + abs t := by
    have he : c - 1 = 1 + Complex.I * (t : Complex) := by dsimp [c]; ring
    rw [he]
    simpa [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs] using
      norm_add_le (1 : Complex) (Complex.I * (t : Complex))
  have hLogSixteen : Real.log (16 : Real) <= 4 := by
    have hTwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    have he : Real.log (16 : Real) = 4 * Real.log (2 : Real) := by
      rw [show (16 : Real) = 2 ^ (4 : Nat) by norm_num, Real.log_pow]
      norm_num
    rw [he]
    linarith
  have hProdPos : 0 < 16 * (N : Real) * T ^ 2 := by positivity
  have hExp : 16 * (N : Real) * T ^ 2 <= Real.exp (4 * B0) := by
    calc
      _ = Real.exp (Real.log (16 * (N : Real) * T ^ 2)) :=
        (Real.exp_log hProdPos).symm
      _ <= _ := by
        apply Real.exp_le_exp.mpr
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        dsimp [B0]
        norm_num
        linarith
  have hCenter : 1 / 4 <= norm (lpfPrincipalPoleFill N c) :=
    lpf_principal_poleFill_center_lower N t
  have hGrowth : forall w, Membership.mem (Metric.ball c (9 / 8)) w ->
      norm (lpfPrincipalPoleFill N w) <=
        Real.exp (4 * B0) * norm (lpfPrincipalPoleFill N c) := by
    intro w hw
    have hd := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at hd
    have hwNorm : norm w <= T := by
      have h := norm_add_le (w - c) c
      rw [sub_add_cancel] at h
      dsimp [T]
      linarith
    have hwOne : norm (w - 1) <= T := by
      have h := norm_add_le (w - c) (c - 1)
      rw [sub_add_sub_cancel] at h
      dsimp [T]
      linarith
    have hRaw := lpf_principal_poleFill_norm_bound N w T
      (hRe w hw).le hT hwNorm hwOne
    calc
      _ <= 4 * (N : Real) * T ^ 2 := hRaw
      _ <= Real.exp (4 * B0) * (1 / 4) := by linarith only [hExp]
      _ <= _ := mul_le_mul_of_nonneg_left hCenter (Real.exp_pos _).le
  have h := lpf_log_deriv_disc_growth_bound (lpfPrincipalPoleFill N) c z (4 * B0)
    hB hAnalytic hNonzero hGrowth hz
  dsimp [B0, T] at h
  linarith only [h]

theorem lpf_principal_log_deriv_pole_identity
    (N : Nat) [NeZero N] (z : Complex) (hz : 7 / 8 < z.re)
    (hz1 : Not (z = 1)) :
    deriv ((1 : DirichletCharacter Complex N).LFunction) z /
        (1 : DirichletCharacter Complex N).LFunction z + 1 / (z - 1) =
      deriv (lpfPrincipalPoleFill N) z / lpfPrincipalPoleFill N z := by
  let L : Complex -> Complex := (1 : DirichletCharacter Complex N).LFunction
  have hLd : DifferentiableAt Complex L z :=
    DirichletCharacter.differentiableAt_LFunction _ z (Or.inl hz1)
  have hEq : Filter.EventuallyEq (nhds z) (lpfPrincipalPoleFill N)
      (fun w => (w - 1) * L w) := by
    filter_upwards [eventually_ne_nhds hz1] with w hw
    exact lpf_principal_poleFill_eq N w hw
  have hDeriv : deriv (lpfPrincipalPoleFill N) z =
      L z + (z - 1) * deriv L z := by
    rw [hEq.deriv_eq]
    have he : ((fun w : Complex => w - 1) * L) =
        (fun w => (w - 1) * L w) := by
      funext w
      simp only [Pi.mul_apply]
    rw [<- he]
    simpa only [one_mul, id_eq] using
      (((hasDerivAt_id z).sub_const 1).mul hLd.hasDerivAt).deriv
  have hL0 : Not (L z = 0) :=
    OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
      (1 : DirichletCharacter Complex N) hz (by simp [hz1])
  change deriv L z / L z + 1 / (z - 1) =
    deriv (lpfPrincipalPoleFill N) z / lpfPrincipalPoleFill N z
  rw [hDeriv, lpf_principal_poleFill_eq N z hz1]
  change deriv L z / L z + 1 / (z - 1) =
    (L z + (z - 1) * deriv L z) / ((z - 1) * L z)
  field_simp [hL0, sub_ne_zero.mpr hz1]
  ring

theorem lpf_log_deriv_numeric
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (t : Real) (z : Complex)
    (hz : dist z (2 + Complex.I * (t : Complex)) <= 17 / 16)
    (hzPole : 1 / 16 <= norm (z - 1)) :
    norm (deriv chi.LFunction z / chi.LFunction z) <=
      16384 * (1 + Real.log (N : Real) + Real.log (abs t + 8)) := by
  let B : Real := 1 + Real.log (N : Real) + Real.log (abs t + 8)
  have hN : 1 <= (N : Real) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hB : 1 <= B := by
    have h1 := Real.log_nonneg hN
    have h2 := Real.log_nonneg (show 1 <= abs t + 8 by linarith [abs_nonneg t])
    dsimp [B]
    linarith
  by_cases hchi : chi = 1
  next =>
    subst chi
    have hzRe : 7 / 8 < z.re := by
      have hl := (abs_le.mp (Complex.abs_re_le_norm
        (z - (2 + Complex.I * (t : Complex))))).1
      rw [dist_eq_norm] at hz
      have hcRe : (2 + Complex.I * (t : Complex)).re = 2 := by simp
      simp only [Complex.sub_re, hcRe] at hl
      linarith
    have hz1 : Not (z = 1) := by intro h; rw [h, sub_self, norm_zero] at hzPole; norm_num at hzPole
    have hPole : norm (1 / (z - 1)) <= (16 : Real) := by
      rw [norm_div, norm_one]
      calc
        _ <= 1 / (1 / 16 : Real) := div_le_div_of_nonneg_left
          (by norm_num) (by norm_num) hzPole
        _ = _ := by norm_num
    have hFill := lpf_principal_poleFill_log_deriv_numeric N t z hz
    have hIdentity := lpf_principal_log_deriv_pole_identity N z hzRe hz1
    have hEq : deriv ((1 : DirichletCharacter Complex N).LFunction) z /
        (1 : DirichletCharacter Complex N).LFunction z =
      deriv (lpfPrincipalPoleFill N) z / lpfPrincipalPoleFill N z - 1 / (z - 1) :=
      eq_sub_of_add_eq hIdentity
    rw [hEq]
    have hTri := norm_sub_le
      (deriv (lpfPrincipalPoleFill N) z / lpfPrincipalPoleFill N z) (1 / (z - 1))
    change _ <= 16384 * B
    change _ <= 13312 * B at hFill
    linarith
  next =>
    have h := lpf_nonprincipal_log_deriv_numeric chi hchi t z hz
    change _ <= 16384 * B
    change _ <= 13312 * B at h
    linarith

end PrimeFactorOscillations.QRH

