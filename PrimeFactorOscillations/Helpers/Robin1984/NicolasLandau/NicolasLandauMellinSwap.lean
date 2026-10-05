/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandau.lean
Original source lines 753-1136. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauFrullani

/-!
# The absolutely integrable three-variable Mellin identity

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Asymptotics Filter MeasureTheory Set

noncomputable section

/-- Mellin transform of Nicolas's complete `J` tail from the fixed startup
frontier three. -/
def nicolasJMellin (z : Complex) : Complex :=
  integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
    (x : Complex) ^ (z - 1) * (nicolasJ x : Complex))

/-- Absolute integrability of the complete three-variable carrier
`3 < x < t`, `u > 0`.  This is the Fubini license for lifting the shifted-tail
identity through the Frullani mixture defining `J`. -/
theorem nicolasJMellinTriple_integrable
    {z : Complex} (hzRe : z.re < 0) :
    Integrable
      ({p : Prod Real (Prod Real Real) | p.1 < p.2.1}.indicator
        (fun p : Prod Real (Prod Real Real) =>
          (p.1 : Complex) ^ (z - 1) *
            ((nicolasPsiError p.2.1 * (p.2.2 + 1) *
              p.2.1 ^ (-(p.2.2 + 2)) : Real) : Complex)))
      ((volume.restrict (Ioi (3 : Real))).prod
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))) := by
  have hG : Integrable
      (fun x : Real => (x : Complex) ^ (z - 1))
      (volume.restrict (Ioi (3 : Real))) := by
    exact integrableOn_Ioi_cpow_of_lt
      (by simp only [Complex.sub_re, Complex.one_re]; linarith) (by norm_num)
  have hBaseReal : Integrable
      (fun p : Prod Real Real =>
        nicolasPsiError p.1 * (p.2 + 1) * p.1 ^ (-(p.2 + 2)))
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) :=
    nicolasFrullaniDouble_integrable (by norm_num)
  have hBaseComplex : Integrable
      (fun p : Prod Real Real =>
        ((nicolasPsiError p.1 * (p.2 + 1) *
          p.1 ^ (-(p.2 + 2)) : Real) : Complex))
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) := by
    exact Complex.ofRealCLM.integrable_comp hBaseReal
  have hProduct := hG.mul_prod hBaseComplex
  have hDomain : MeasurableSet
      {p : Prod Real (Prod Real Real) | p.1 < p.2.1} :=
    measurableSet_lt measurable_fst (measurable_fst.comp measurable_snd)
  exact hProduct.indicator hDomain

theorem nicolasJMellinTriple_inner_eq
    {z : Complex} {x : Real} (hx : 3 <= x) :
    integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (fun p : Prod Real Real =>
          {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
            (fun q : Prod Real (Prod Real Real) =>
              (q.1 : Complex) ^ (z - 1) *
                ((nicolasPsiError q.2.1 * (q.2.2 + 1) *
                  q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
            (x, p)) =
      (x : Complex) ^ (z - 1) * (nicolasJ x : Complex) := by
  let g : Complex := (x : Complex) ^ (z - 1)
  let baseReal : Prod Real Real -> Real := fun p =>
    nicolasPsiError p.1 * (p.2 + 1) * p.1 ^ (-(p.2 + 2))
  let baseComplex : Prod Real Real -> Complex := fun p =>
    (baseReal p : Complex)
  let dx : Set (Prod Real Real) := {p | x < p.1}
  have hBaseReal : Integrable baseReal
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) := by
    dsimp [baseReal]
    exact nicolasFrullaniDouble_integrable (by norm_num)
  have hBaseComplex : Integrable baseComplex
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) := by
    dsimp [baseComplex]
    exact Complex.ofRealCLM.integrable_comp hBaseReal
  have hdx : MeasurableSet dx := by
    dsimp [dx]
    exact measurableSet_lt measurable_const measurable_fst
  have hSection : Integrable (dx.indicator (fun p => g * baseComplex p))
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) :=
    (hBaseComplex.const_mul g).indicator hdx
  have hCast :
      integral (volume.restrict (Ioi x)) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseComplex (t, u))) =
        ((integral (volume.restrict (Ioi x)) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseReal (t, u))) : Real) : Complex) := by
    calc
      integral (volume.restrict (Ioi x)) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseComplex (t, u))) =
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            ((integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
              baseReal (t, u)) : Real) : Complex)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp [baseComplex]
        exact integral_ofReal
      _ = ((integral (volume.restrict (Ioi x)) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseReal (t, u))) : Real) : Complex) := by
        exact integral_ofReal
  change integral
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real))))
      (dx.indicator (fun p => g * baseComplex p)) =
    g * (nicolasJ x : Complex)
  calc
    integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (dx.indicator (fun p => g * baseComplex p)) =
        integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            dx.indicator (fun p => g * baseComplex p) (t, u))) := by
      exact integral_prod _ hSection
    _ = integral (volume.restrict (Ioi (3 : Real)))
        ((Ioi x).indicator (fun t : Real =>
          g * integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseComplex (t, u)))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      by_cases hxt : x < t
      . simp [dx, Set.indicator, hxt, integral_const_mul]
      . simp [dx, Set.indicator, hxt]
    _ = integral (volume.restrict (Set.inter (Ioi (3 : Real)) (Ioi x)))
        (fun t : Real =>
          g * integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseComplex (t, u))) := by
      rw [setIntegral_indicator measurableSet_Ioi]
      rfl
    _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
        g * integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
          baseComplex (t, u))) := by
      have hInter : Set.inter (Ioi (3 : Real)) (Ioi x) = Ioi x :=
        inter_eq_right.mpr (Ioi_subset_Ioi hx)
      rw [hInter]
    _ = g * integral (volume.restrict (Ioi x)) (fun t : Real =>
        integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
          baseComplex (t, u))) := by
      rw [integral_const_mul]
    _ = g * (nicolasJ x : Complex) := by
      rw [hCast]
      rw [nicolasJ_eq_frullaniDouble (le_trans (by norm_num) hx)]

theorem nicolasJMellinTriple_x_inner_eq
    {z : Complex} {t u : Real} (hzRe : z.re < 0) (ht : 3 < t) :
    integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
        {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
          (fun q : Prod Real (Prod Real Real) =>
            (q.1 : Complex) ^ (z - 1) *
              ((nicolasPsiError q.2.1 * (q.2.2 + 1) *
                q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
          (x, (t, u))) =
      ((nicolasPsiError t * (u + 1) * t ^ (-(u + 2)) : Real) : Complex) *
        (((t : Complex) ^ z - (3 : Complex) ^ z) / z) := by
  let c : Complex :=
    ((nicolasPsiError t * (u + 1) * t ^ (-(u + 2)) : Real) : Complex)
  let g : Real -> Complex := fun x => (x : Complex) ^ (z - 1)
  let dt : Set Real := Iio t
  change integral (volume.restrict (Ioi (3 : Real)))
      (dt.indicator (fun x : Real => g x * c)) =
    c * (((t : Complex) ^ z - (3 : Complex) ^ z) / z)
  rw [setIntegral_indicator measurableSet_Iio]
  have hInter : Set.inter (Ioi (3 : Real)) (Iio t) = Ioo 3 t := by
    ext x
    simp [Set.inter]
  change integral
      (volume.restrict (Set.inter (Ioi (3 : Real)) (Iio t)))
      (fun x : Real => g x * c) = _
  rw [hInter]
  calc
    integral (volume.restrict (Ioo (3 : Real) t)) (fun x : Real =>
        g x * c) =
        integral (volume.restrict (Ioo (3 : Real) t)) (fun x : Real =>
          c * g x) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      ring
    _ = c * integral (volume.restrict (Ioo (3 : Real) t)) g := by
      rw [integral_const_mul]
    _ = c * integral (volume.restrict (Ioc (3 : Real) t)) g := by
      rw [integral_Ioc_eq_integral_Ioo]
    _ = c * (((t : Complex) ^ z - (3 : Complex) ^ z) / z) := by
      dsimp [g]
      rw [integral_Ioc_cpow_sub_one (by norm_num) ht.le (by
        intro hz
        subst z
        norm_num at hzRe)]
      norm_num

theorem nicolasJMellin_eq_tripleSwapped
    {z : Complex} (hzRe : z.re < 0) :
    nicolasJMellin z =
      integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (fun p : Prod Real Real =>
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
              (fun q : Prod Real (Prod Real Real) =>
                (q.1 : Complex) ^ (z - 1) *
                  ((nicolasPsiError q.2.1 * (q.2.2 + 1) *
                    q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
              (x, p))) := by
  have hUncurried : Integrable
      (Function.uncurry (fun x : Real => fun p : Prod Real Real =>
        {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
          (fun q : Prod Real (Prod Real Real) =>
            (q.1 : Complex) ^ (z - 1) *
              ((nicolasPsiError q.2.1 * (q.2.2 + 1) *
                q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
          (x, p)))
      ((volume.restrict (Ioi (3 : Real))).prod
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))) := by
    change Integrable
      ({p : Prod Real (Prod Real Real) | p.1 < p.2.1}.indicator
        (fun p : Prod Real (Prod Real Real) =>
          (p.1 : Complex) ^ (z - 1) *
            ((nicolasPsiError p.2.1 * (p.2.2 + 1) *
              p.2.1 ^ (-(p.2.2 + 2)) : Real) : Complex)))
      ((volume.restrict (Ioi (3 : Real))).prod
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real)))))
    exact nicolasJMellinTriple_integrable hzRe
  unfold nicolasJMellin
  calc
    integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
        (x : Complex) ^ (z - 1) * (nicolasJ x : Complex)) =
        integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          integral
            ((volume.restrict (Ioi (3 : Real))).prod
              (volume.restrict (Ioi (0 : Real))))
            (fun p : Prod Real Real =>
              {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
                (fun q : Prod Real (Prod Real Real) =>
                  (q.1 : Complex) ^ (z - 1) *
                    ((nicolasPsiError q.2.1 * (q.2.2 + 1) *
                      q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
                (x, p))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (nicolasJMellinTriple_inner_eq hx.le).symm
    _ = integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (fun p : Prod Real Real =>
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
              (fun q : Prod Real (Prod Real Real) =>
                (q.1 : Complex) ^ (z - 1) *
                  ((nicolasPsiError q.2.1 * (q.2.2 + 1) *
                    q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
              (x, p))) := integral_integral_swap hUncurried

theorem nicolasJMellinTriple_t_inner_eq
    {z : Complex} {u : Real} (hzRe : z.re < 0) (hu : 0 < u) :
    integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        ((nicolasPsiError t * (u + 1) * t ^ (-(u + 2)) : Real) : Complex) *
          (((t : Complex) ^ z - (3 : Complex) ^ z) / z)) =
      ((u + 1 : Real) : Complex) *
        ((nicolasPsiMellinTailContinuation 3
            (((u + 1 : Real) : Complex) - z) -
          (3 : Complex) ^ z * nicolasPsiMellinTailContinuation 3
            ((u + 1 : Real) : Complex)) / z) := by
  let s : Complex := ((u + 1 : Real) : Complex)
  let c : Complex := ((u + 1 : Real) : Complex)
  have hs : 1 < s.re := by
    dsimp [s]
    linarith
  have hPoint : forall t : Real, 3 < t ->
      ((nicolasPsiError t * (u + 1) * t ^ (-(u + 2)) : Real) : Complex) *
          (((t : Complex) ^ z - (3 : Complex) ^ z) / z) =
        c * (((nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) *
            (((t : Complex) ^ z - (3 : Complex) ^ z) / z)) := by
    intro t ht
    have htPos : 0 < t := lt_trans (by norm_num) ht
    have hPower :
        ((t ^ (-(u + 2)) : Real) : Complex) =
          (t : Complex) ^ (-(s + 1)) := by
      rw [Complex.ofReal_cpow htPos.le]
      congr 1
      dsimp [s]
      push_cast
      ring
    dsimp [c]
    push_cast
    rw [hPower]
    ring
  calc
    integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        ((nicolasPsiError t * (u + 1) * t ^ (-(u + 2)) : Real) : Complex) *
          (((t : Complex) ^ z - (3 : Complex) ^ z) / z)) =
        integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          c * (((nicolasPsiError t : Complex) *
            (t : Complex) ^ (-(s + 1))) *
              (((t : Complex) ^ z - (3 : Complex) ^ z) / z))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact hPoint t ht
    _ = c * integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        ((nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) *
            (((t : Complex) ^ z - (3 : Complex) ^ z) / z)) := by
      rw [integral_const_mul]
    _ = c *
        ((nicolasPsiMellinTailContinuation 3 (s - z) -
          (3 : Complex) ^ z * nicolasPsiMellinTailContinuation 3 s) / z) := by
      congr 1
      simpa using (nicolasPsiErrorMellinCell_eq_shift
        (a := (3 : Real)) (s := s) (z := z) (by norm_num) hs hzRe)
    _ = ((u + 1 : Real) : Complex) *
        ((nicolasPsiMellinTailContinuation 3
            (((u + 1 : Real) : Complex) - z) -
          (3 : Complex) ^ z * nicolasPsiMellinTailContinuation 3
            ((u + 1 : Real) : Complex)) / z) := by
      rfl

/-- Exact Mellin transform of Nicolas's `J` tail on its half-plane of
absolute convergence.  The shifted tail continuation is now explicit under
the complete Frullani parameter integral. -/
theorem nicolasJMellin_eq_integral_shift
    {z : Complex} (hzRe : z.re < 0) :
    nicolasJMellin z =
      integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
        ((u + 1 : Real) : Complex) *
          ((nicolasPsiMellinTailContinuation 3
              (((u + 1 : Real) : Complex) - z) -
            (3 : Complex) ^ z * nicolasPsiMellinTailContinuation 3
              ((u + 1 : Real) : Complex)) / z)) := by
  let triple : Prod Real (Prod Real Real) -> Complex := fun q =>
    {p : Prod Real (Prod Real Real) | p.1 < p.2.1}.indicator
      (fun p : Prod Real (Prod Real Real) =>
        (p.1 : Complex) ^ (z - 1) *
          ((nicolasPsiError p.2.1 * (p.2.2 + 1) *
            p.2.1 ^ (-(p.2.2 + 2)) : Real) : Complex)) q
  have hTriple : Integrable triple
      ((volume.restrict (Ioi (3 : Real))).prod
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))) := by
    dsimp [triple]
    exact nicolasJMellinTriple_integrable hzRe
  have hOuter : Integrable
      (fun p : Prod Real Real =>
        integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          triple (x, p)))
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) :=
    hTriple.integral_prod_right
  calc
    nicolasJMellin z = integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (fun p : Prod Real Real =>
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            triple (x, p))) := by
      rw [nicolasJMellin_eq_tripleSwapped hzRe]
    _ = integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
        integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            triple (x, (t, u))))) := by
      exact integral_prod_symm _ hOuter
    _ = integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
        integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          ((nicolasPsiError t * (u + 1) * t ^ (-(u + 2)) : Real) : Complex) *
            (((t : Complex) ^ z - (3 : Complex) ^ z) / z))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp [triple]
      exact nicolasJMellinTriple_x_inner_eq hzRe ht
    _ = integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
        ((u + 1 : Real) : Complex) *
          ((nicolasPsiMellinTailContinuation 3
              (((u + 1 : Real) : Complex) - z) -
            (3 : Complex) ^ z * nicolasPsiMellinTailContinuation 3
              ((u + 1 : Real) : Complex)) / z)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact nicolasJMellinTriple_t_inner_eq hzRe hu

end

end Robin1984

